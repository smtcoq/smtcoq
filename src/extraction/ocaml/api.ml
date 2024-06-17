(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Smtcoq_plugin


(** SMT-LIB2 sorts and function symbols **)
type sort = string
type funsym = string * sort list * sort


(** SMT-LIB2 terms and formulas **)
(* TODO: add bit vectors and arrays *)

type expr =
  (* Variables and applied functions and predicates *)
  | EFun of funsym * expr list

  (* True *)
  | ETrue
  (* False *)
  | EFalse
  (* Negation *)
  | ENeg of expr
  (* N-ary and *)
  | EAnd of expr list
  (* Binary and *)
  | EBAnd of expr * expr
  (* N-ary or *)
  | EOr of expr list
  (* Binary or *)
  | EBor of expr * expr
  (* Xor *)
  | EXor of expr * expr
  (* -> *)
  | EImp of expr * expr

  (* Equality *)
  | EEq of expr * expr
  (* Distinct (applies to terms only) *)
  | EDistinct of expr list

  (* Integer constants *)
  | EInt of int
  | EBigInt of Big_int.big_int
  (* Addition *)
  | EAdd of expr * expr
  (* Unary substraction *)
  | EOpp of expr
  (* Binary substraction *)
  | EMinus of expr * expr
  (* Multiplication *)
  | EMult of expr * expr
  (* Less than *)
  | ELt of expr * expr
  (* Less or equal *)
  | ELe of expr * expr
  (* Greater than *)
  | EGt of expr * expr
  (* Greater or equal *)
  | EGe of expr * expr


(** Pretty_printers **)

let pp_sort fmt (s:sort) = Format.fprintf fmt "%s" s

let pp_funsym fmt (f:funsym) =
  let (n, _, _) = f in
  Format.fprintf fmt "%s" n

let rec pp_expr fmt = function
  | EFun (f, l) ->
     let pp fmt l =
       if List.compare_length_with l 0 = 0 then
         ()
       else
         Smt_utils.pp_list pp_expr ", " "(" ")" fmt l
     in
     Format.fprintf fmt "%a%a" pp_funsym f pp l
  | ETrue  -> Format.fprintf fmt "true"
  | EFalse -> Format.fprintf fmt "false"
  | ENeg f -> Format.fprintf fmt "(not %a)" pp_expr f
  | EAnd l ->
     let pp fmt l = Smt_utils.pp_list pp_expr " " "" "" fmt l in
     Format.fprintf fmt "(and %a)" pp l
  | EBAnd (a, b) -> Format.fprintf fmt "(and %a %a)" pp_expr a pp_expr b
  | EOr l ->
     let pp fmt l = Smt_utils.pp_list pp_expr " " "" "" fmt l in
     Format.fprintf fmt "(or %a)" pp l
  | EBor (a, b) -> Format.fprintf fmt "(or %a %a)" pp_expr a pp_expr b
  | EXor (a, b) -> Format.fprintf fmt "(xor %a %a)" pp_expr a pp_expr b
  | EImp (a, b) -> Format.fprintf fmt "(-> %a %a)" pp_expr a pp_expr b
  | EEq (a, b) -> Format.fprintf fmt "(= %a %a)" pp_expr a pp_expr b
  | EDistinct l ->
     let pp fmt l = Smt_utils.pp_list pp_expr " " "" "" fmt l in
     Format.fprintf fmt "(distinct %a)" pp l
  | EInt i -> Format.fprintf fmt "%d" i
  | EBigInt i -> Format.fprintf fmt "%s" (Big_int.string_of_big_int i)
  | EAdd (a, b) -> Format.fprintf fmt "(+ %a %a)" pp_expr a pp_expr b
  | EOpp a -> Format.fprintf fmt "(- %a)" pp_expr a
  | EMinus (a, b) -> Format.fprintf fmt "(- %a %a)" pp_expr a pp_expr b
  | EMult (a, b) -> Format.fprintf fmt "(* %a %a)" pp_expr a pp_expr b
  | ELt (a, b) -> Format.fprintf fmt "(< %a %a)" pp_expr a pp_expr b
  | ELe (a, b) -> Format.fprintf fmt "(<= %a %a)" pp_expr a pp_expr b
  | EGt (a, b) -> Format.fprintf fmt "(> %a %a)" pp_expr a pp_expr b
  | EGe (a, b) -> Format.fprintf fmt "(>= %a %a)" pp_expr a pp_expr b


(** Processing expressions **)

(* From smtlib2/smtlib2_genConstr.ml [make_root_*] *)
exception Ill_typed of expr

type atom_form = | Atom of SmtAtom.Atom.t | Form of SmtAtom.Form.t

let rec make_expr ra rf e =
  match e with
  | EFun ((f, _, _), l) ->
     let op = SmtMaps.get_fun f in
     let l' = List.map (make_atom ra rf) l in
     Atom (SmtAtom.Atom.get ra (Aapp (op, Array.of_list l')))
  | ETrue  -> Form (SmtAtom.Form.get rf SmtAtom.Form.pform_true)
  | EFalse -> Form (SmtAtom.Form.get rf SmtAtom.Form.pform_false)
  | ENeg f ->
     let f' = make_form ra rf f in
     let nf = SmtAtom.Form.neg f' in
     let r =
       if SmtAtom.Form.is_neg nf then
         nf
       else
         (match SmtAtom.Form.pform nf with
            | Fapp (Fnot2 i, a) -> SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.Fnot2 (i+1), a))
            | _ -> SmtAtom.Form.get rf (Fapp (Fnot2 1, [|nf|]))
         )
     in
     Form r
  | EAnd l ->
     let l' = List.map (make_form ra rf) l in
     let a = Array.of_list l' in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.Fand, a)))
  | EBAnd (a, b) ->
     let a' = make_form ra rf a in
     let b' = make_form ra rf b in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.Fand, [|a'; b'|])))
  | EOr l ->
     let l' = List.map (make_form ra rf) l in
     let a = Array.of_list l' in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.For, a)))
  | EBor (a, b) ->
     let a' = make_form ra rf a in
     let b' = make_form ra rf b in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.For, [|a'; b'|])))
  | EXor (a, b) ->
     let a' = make_form ra rf a in
     let b' = make_form ra rf b in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.Fxor, [|a'; b'|])))
  | EImp (a, b) ->
     let a' = make_form ra rf a in
     let b' = make_form ra rf b in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.Fimp, [|a'; b'|])))
  | EEq (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' ->
           let ta = SmtAtom.Atom.type_of a' in
           let tb = SmtAtom.Atom.type_of b' in
           if (ta <> tb) then
             raise (Ill_typed e)
           else if (ta <> Tbool) then
             Atom (SmtAtom.Atom.mk_eq_sym ra ta a' b')
           else
             let a2 = SmtAtom.Form.get rf (SmtForm.Fatom a') in
             let b2 = SmtAtom.Form.get rf (SmtForm.Fatom b') in
             Form (SmtAtom.Form.get rf (Fapp (Fiff, [|a2; b2|])))
        | Atom a', Form b' ->
           let ta = SmtAtom.Atom.type_of a' in
           if (ta <> Tbool) then
             raise (Ill_typed e)
           else
             let a2 = SmtAtom.Form.get rf (SmtForm.Fatom a') in
             Form (SmtAtom.Form.get rf (Fapp (Fiff, [|a2; b'|])))
        | Form a', Atom b' ->
           let tb = SmtAtom.Atom.type_of b' in
           if (tb <> Tbool) then
             raise (Ill_typed e)
           else
             let b2 = SmtAtom.Form.get rf (SmtForm.Fatom b') in
             Form (SmtAtom.Form.get rf (Fapp (Fiff, [|a'; b2|])))
        | Form a', Form b' ->
           Form (SmtAtom.Form.get rf (Fapp (Fiff, [|a'; b'|])))
     )
  | EDistinct l ->
     let make_h = make_atom ra rf in
     let a = Array.make (List.length l) (make_h (List.hd l)) in
     let i = ref 0 in
     List.iter (fun h ->
         incr i;
         a.(!i) <- make_h h) (List.tl l);
     Atom (SmtAtom.Atom.mk_distinct ra (SmtAtom.Atom.type_of a.(0)) a)
  | EInt i -> Atom (SmtAtom.Atom.hatom_Z_of_int ra i)
  | EBigInt i -> Atom (SmtAtom.Atom.hatom_Z_of_bigint ra i)
  | EAdd (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_plus ra a' b')
  | EOpp a ->
     let a' = make_atom ra rf a in
     Atom (SmtAtom.Atom.mk_opp ra a')
  | EMinus (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_minus ra a' b')
  | EMult (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_mult ra a' b')
  | ELt (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_lt ra a' b')
  | ELe (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_le ra a' b')
  | EGt (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_gt ra a' b')
  | EGe (a, b) ->
     let a' = make_atom ra rf a in
     let b' = make_atom ra rf b in
     Atom (SmtAtom.Atom.mk_ge ra a' b')

and make_atom ra rf e =
  match make_expr ra rf e with
    | Atom a -> a
    | Form _ -> raise (Ill_typed e)

and make_form ra rf e =
  match make_expr ra rf e with
    | Form f -> f
    | Atom a ->
       let ta = SmtAtom.Atom.type_of a in
       if (ta <> Tbool) then
         raise (Ill_typed e)
       else
         SmtAtom.Form.get rf (SmtForm.Fatom a)


(** SMT-LIB2 commands **)
(*** Sort declarations ***)
type sorts = sort list

let declare_sorts (sl:sorts) =
  List.iteri (fun i s ->
      let res = SmtBtype.Tindex (SmtBtype.dummy_indexed_type i) in
      SmtMaps.add_btype s res;
    ) sl


(*** Function symbols declarations ***)
type funsyms = funsym list

let declare_funsyms (fl:funsyms) =
  List.iteri (fun i (s, arg, cod) ->
      let tyl = List.map (fun s -> Smtlib2_genConstr.sort_of_string s []) arg in
      let ty = Smtlib2_genConstr.sort_of_string cod [] in
      let op = SmtAtom.dummy_indexed_op (SmtAtom.Index 0) (Array.of_list tyl) ty in
      SmtMaps.add_fun s op
    ) fl


(*** Assertions ***)
type assertions = expr array

let assertions_tbl = Hashtbl.create 17

let declare_assertions ra rf (a:assertions) =
  let cell = ref (-1) in
  List.rev (Array.fold_left (fun acc t ->
                incr cell;
                let aa = make_form ra rf t in
                Hashtbl.add assertions_tbl !cell aa;
                aa::acc
              ) [] a)


(*** Commands ***)
type smtlib2 = sorts * funsyms * assertions

let declare_smtlib2 ra rf (smt:smtlib2) =
  let (s, f, a) = smt in
  declare_sorts s;
  declare_funsyms f;
  declare_assertions ra rf a


(** Certificate
    It implements parts of the Alethe format as presented in
      https://verit.loria.fr/documentation/alethe-spec.pdf
    See in particular the description of the rules starting p.26

    Numbers in comments indicate the number of the rule in the document,
    and we keep the names.

    Note that the rule not_not is useless as SMTCoq reasons modulo
    double negation.

    It implements an additional rule: weakening.

    Warning: make sure not to produce clauses containing both a formula
    and its negation (even modulo double negation), as it is considered
    trivial by SMTCoq. It may be a cause of failure.
 **)
type node =
  (* 0. Given a proof of the clause {f1 ... fn} and formulas b1 ... bm,
        proves the clause {f1 ... fn b1 ... bm}
   *)
  | Cweakening of certif * expr list

  (* 1. Refer to an assertion by its index *)
  | Cassume of int

  (* 3. Proves the clause {(true)} *)
  | Ctrue

  (* 4. Proves the clause {(not false)} *)
  | Cfalse

  (* 6 & 7. Resolution of two or more clauses *)
  | Cresolution of certif list

  (* 12. Proves the given clause in the theory of Linear Integer Arithmetic *)
  | Clia_generic of expr list

  (* 23. Given a term t, proves the clause {(= t t)} *)
  | Ceq_reflexive of expr

  (* 24. Given the terms t1 ... tn,
         proves the clause {(not (= t1 t2)) ... (not (= t{n-1} tn)) (= t1 tn)}
   *)
  | Ceq_transitive of expr list

  (* 25. Given a function symbol f, the terms t1 ... tn, and the terms u1 ... un,
         proves the clause
           {(not (= t1 u1)) ... (not (= tn un)) (= f(t1, ..., tn) f(u1, ..., un))}
   *)
  | Ceq_congruent of funsym * expr list * expr list

  (* 26. Given a predicate symbol P, the terms t1 ... tn, and the terms u1 ... un,
         proves the clause
           {(not (= t1 u1)) ... (not (= tn un)) (= P(t1, ..., tn) P(u1, ..., un))}
   *)
  | Ceq_congruent_pred of funsym * expr list * expr list

  (* 28. Given a proof of the clause {(and f1 ... fn)} and a non-negative integer k,
         proves the clause {fk}
   *)
  | Cand of certif * int

  (* 29. Given a proof of the clause {(not (or f1 ... fn))} and a non-negative integer k,
         proves the clause {(not fk)}
   *)
  | Cnot_or of certif * int

  (* 30. Given a proof of the clause {(or f1 ... fn)},
         proves the clause {f1 ... fn}
   *)
  | Cor of certif

  (* 31. Given a proof of the clause {(not (and f1 ... fn))},
         proves the clause {(not f1) ... (not fn)}
   *)
  | Cnot_and of certif

  (* 32. Given a proof of the clause {(xor a b)},
         proves the clause {a b}
   *)
  | Cxor1 of certif

  (* 33. Given a proof of the clause {(xor a b)},
         proves the clause {(not a) (not b)}
   *)
  | Cxor2 of certif

  (* 34. Given a proof of the clause {(not (xor a b))},
         proves the clause {a (not b)}
   *)
  | Cnot_xor1 of certif

  (* 35. Given a proof of the clause {(not (xor a b))},
         proves the clause {(not a) b}
   *)
  | Cnot_xor2 of certif

  (* 36. Given a proof of the clause {(-> a b)},
         proves the clause {(not a) b}
   *)
  | Cimplies of certif

  (* 37. Given a proof of the clause {(not (-> a b))},
         proves the clause {a}
   *)
  | Cnot_implies1 of certif

  (* 38. Given a proof of the clause {(not (-> a b))},
         proves the clause {(not b)}
   *)
  | Cnot_implies2 of certif

  (* 39. Given a proof of the clause {(= a b)},
         proves the clause {(not a) b}
   *)
  | Cequiv1 of certif

  (* 40. Given a proof of the clause {(= a b)},
         proves the clause {a (not b)}
   *)
  | Cequiv2 of certif

  (* 41. Given a proof of the clause {(not (= a b))},
         proves the clause {a b}
   *)
  | Cnot_equiv1 of certif

  (* 42. Given a proof of the clause {(not (= a b))},
         proves the clause {(not a) (not b)}
   *)
  | Cnot_equiv2 of certif

  (* 43. Given the formulas f1 ... fn and a non-negative integer k,
         proves the clause {(not (and f1 ... fn)) fk}
   *)
  | Cand_pos of expr list * int

  (* 44. Given the formulas f1 ... fn,
         proves the clause {(and f1 ... fn) (not f1) ... (not fn)}
   *)
  | Cand_neg of expr list

  (* 45. Given the formulas f1 ... fn,
         proves the clause {(not (or f1 ... fn)) f1 ... fn}
   *)
  | Cor_pos of expr list

  (* 46. Given the formulas f1 ... fn and a non-negative integer k,
         proves the clause {(or f1 ... fn) (not fk)}
   *)
  | Cor_neg of expr list * int

  (* 47. Given the formulas a and b,
         proves the clause {(not (xor a b)) a b}
   *)
  | Cxor_pos1 of expr * expr

  (* 48. Given the formulas a and b,
         proves the clause {(not (xor a b)) (not a) (not b)}
   *)
  | Cxor_pos2 of expr * expr

  (* 49. Given the formulas a and b,
         proves the clause {(xor a b) a (not b)}
   *)
  | Cxor_neg1 of expr * expr

  (* 50. Given the formulas a and b,
         proves the clause {(xor a b) (not a) b}
   *)
  | Cxor_neg2 of expr * expr

  (* 51. Given the formulas a and b,
         proves the clause {(not (implies a b)) (not a) b}
   *)
  | Cimplies_pos of expr * expr

  (* 52. Given the formulas a and b,
         proves the clause {(implies a b) a}
   *)
  | Cimplies_neg1 of expr * expr

  (* 53. Given the formulas a and b,
         proves the clause {(implies a b) (not b)}
   *)
  | Cimplies_neg2 of expr * expr

  (* 54. Given the formulas a and b,
         proves the clause {(not (= a b)) a (not b)}
   *)
  | Cequiv_pos1 of expr * expr

  (* 55. Given the formulas a and b,
         proves the clause {(not (= a b)) (not a) b}
   *)
  | Cequiv_pos2 of expr * expr

  (* 56. Given the formulas a and b,
         proves the clause {(= a b) (not a) (not b)}
   *)
  | Cequiv_neg1 of expr * expr

  (* 57. Given the formulas a and b,
         proves the clause {(= a b) a b}
   *)
  | Cequiv_neg2 of expr * expr

and certif = string * node


type 'hform rule_kind =
  | RKind of 'hform SmtCertif.clause_kind
  | RRoot of int


let process_certif =
  let add_clause id cl =
    VeritSyntax.add_clause id cl;
    if id > 1 then SmtTrace.link (VeritSyntax.get_clause (id-1)) cl
  in
  let confl_num = ref 0 in

  (* Add roots *)
  let add_roots () =
    Hashtbl.iter (fun i a ->
        let id = i+1 in
        confl_num := id;
        let cl = SmtTrace.mkRootV [a] in
        add_clause id cl
      ) assertions_tbl;
    if !confl_num < 1 then failwith "The SMT problem should have at least one assertion";
  in

  (* Process the certificate *)
  let rec process_certif c =
    let (_, c) = c in
    let kind = match c with
        | Cweakening of certif * expr list
        | Cassume i -> RRoot (i+1)
        | Ctrue
        | Cfalse -> RKind(SmtCertif.Other SmtCertif.False)
        | Cresolution l ->
           (match List.map (fun cl -> VeritSyntax.get_clause (process_certif cl)) l with
              | cl1::cl2::q ->
                 let res = {SmtCertif.rc1 = cl1; SmtCertif.rc2 = cl2; SmtCertif.rtail = q} in
                 RKind (SmtCertif.Res res)
              | _ -> failwith "Resolution should contain at least two clauses"
           )
        | Clia_generic of expr list
        | Ceq_reflexive of expr
        | Ceq_transitive of expr list
        | Ceq_congruent of funsym * expr list * expr list
        | Ceq_congruent_pred of funsym * expr list * expr list
        | Cand of certif * int
        | Cnot_or of certif * int
        | Cor of certif
        | Cnot_and of certif
        | Cxor1 of certif
        | Cxor2 of certif
        | Cnot_xor1 of certif
        | Cnot_xor2 of certif
        | Cimplies of certif
        | Cnot_implies1 of certif
        | Cnot_implies2 of certif
        | Cequiv1 of certif
        | Cequiv2 of certif
        | Cnot_equiv1 of certif
        | Cnot_equiv2 of certif
        | Cand_pos of expr list * int
        | Cand_neg of expr list
        | Cor_pos of expr list
        | Cor_neg of expr list * int
        | Cxor_pos1 of expr * expr
        | Cxor_pos2 of expr * expr
        | Cxor_neg1 of expr * expr
        | Cxor_neg2 of expr * expr
        | Cimplies_pos of expr * expr
        | Cimplies_neg1 of expr * expr
        | Cimplies_neg2 of expr * expr
        | Cequiv_pos1 of expr * expr
        | Cequiv_pos2 of expr * expr
        | Cequiv_neg1 of expr * expr
        | Cequiv_neg2 of expr * expr
    in
    match kind with
      | RKind k ->
         incr confl_num;
         let id = !confl_num in
         let cl = SmtTrace.mk_scertif k None in
         add_clause id cl;
         id
      | RRoot i -> i
  in

  fun c -> add_roots (); process_certif c


(* From verit.ml *)
let import_trace (c:certif) =
  let confl_num = process_certif c in
  let cfirst = ref (VeritSyntax.get_clause 1) in
  let confl = ref (VeritSyntax.get_clause confl_num) in
  SmtTrace.select !confl;
  SmtTrace.occur !confl;
  (SmtTrace.alloc !cfirst, !confl)


(** The API checker **)

let clear_all () =
  Smt_utils.clear_all ();
  Hashtbl.clear assertions_tbl


(* From verit_checker.ml *)
let checker_exn (smt:smtlib2) (proof:certif) : bool =
  clear_all ();
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = declare_smtlib2 ra rf smt in
  let (max_id, confl) = import_trace proof in
  Smt_utils.checker ra rf roots max_id confl

let checker_string smt proof =
  try (checker_exn smt proof, "")
  with Ill_typed e ->
    let s = Format.asprintf "Expression %a is ill-typed or is not of the expected type" pp_expr e in
    (false, s)

let checker smt proof =
  let (b, s) = checker_string smt proof in
  if String.length s = 0 then
    b
  else failwith s


(** Callback from C to OCaml
    see https://ocaml.org/manual/4.09/intfc.html#sec426
 **)

let _ = Callback.register "checker" checker_string

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
  | ENot of expr
  (* N-ary and *)
  | EAnd of expr list
  (* N-ary or *)
  | EOr of expr list
  (* Xor *)
  | EXor of expr * expr
  (* => *)
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
       if not (List.compare_length_with l 0 = 0) then
         Smt_utils.pp_list pp_expr ", " "(" ")" fmt l
     in
     Format.fprintf fmt "%a%a" pp_funsym f pp l
  | ETrue  -> Format.fprintf fmt "true"
  | EFalse -> Format.fprintf fmt "false"
  | ENot f -> Format.fprintf fmt "(not %a)" pp_expr f
  | EAnd l ->
     let pp fmt l = Smt_utils.pp_list pp_expr " " "" "" fmt l in
     Format.fprintf fmt "(and %a)" pp l
  | EOr l ->
     let pp fmt l = Smt_utils.pp_list pp_expr " " "" "" fmt l in
     Format.fprintf fmt "(or %a)" pp l
  | EXor (a, b) -> Format.fprintf fmt "(xor %a %a)" pp_expr a pp_expr b
  | EImp (a, b) -> Format.fprintf fmt "(=> %a %a)" pp_expr a pp_expr b
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
  | ENot f ->
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
  | EOr l ->
     let l' = List.map (make_form ra rf) l in
     let a = Array.of_list l' in
     Form (SmtAtom.Form.get rf (SmtForm.Fapp (SmtForm.For, a)))
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
      let op = SmtAtom.dummy_indexed_op (SmtAtom.Index i) (Array.of_list tyl) ty in
      SmtMaps.add_fun s op
    ) fl


(*** Assertions ***)
type assertions = expr array

let declare_assertions ra rf (a:assertions) =
  Array.map (make_form ra rf) a


(*** Commands ***)
type smtlib2 = sorts * funsyms * assertions

let declare_smtlib2 ra rf (smt:smtlib2) =
  let (s, f, a) = smt in
  declare_sorts s;
  declare_funsyms f;
  declare_assertions ra rf a


(** Certificates
    It implements parts of the Alethe format as presented in
      https://verit.loria.fr/documentation/alethe-spec.pdf
    See in particular the description of the rules starting p.26

    Numbers in comments indicate the number of the rule in the document,
    and we keep the names.

    Note that the context is not supported.

    Note that the rule not_not is useless as SMTCoq reasons modulo
    double negation.

    It implements an additional rule: weakening.

    Warning: make sure not to produce clauses containing both a formula
    and its negation (even modulo double negation), as it is considered
    trivial by SMTCoq. It may be a cause of failure.
 **)
type node =
  (* 0. Given a proof of the clause {f1 ... fn}
          and a possibly larger clause {f1 ... fn b1 ... bm},
        proves the clause {f1 ... fn b1 ... bm}
        The order does not matter
        The initial clause may contain the additional literals
          `not false` and `true` as well
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

  (* 23. Given a term t, proves the clause {(= t t)}
         Applies only to a non-Boolean term.
   *)
  | Ceq_reflexive of expr

  (* 24. Given the terms t1 ... tn,
           proves the clause {(not (= t1 t2)) ... (not (= t{n-1} tn)) (= t1 tn)}
         The tis must be non-Boolean terms.
   *)
  | Ceq_transitive of expr list

  (* 25. Proves the clause
           {(not (= t1 u1)) ... (not (= tn un)) (= f(t1, ..., tn) f(u1, ..., un))}
         The tis and uis must be non-Boolean terms, and the codomain of f must not be Bool.
   *)
  | Ceq_congruent of expr list

  (* 26. Proves the clause
           {(not (= t1 u1)) ... (not (= tn un)) (= P(t1, ..., tn) P(u1, ..., un))}
         The tis and uis must be non-Boolean terms, and the codomain of P must be Bool.
   *)
  | Ceq_congruent_pred of expr list

  (* 26b. A small variant
          Proves the clause
            {(not (= t1 u1)) ... (not (= tn un)) (not P(t1, ..., tn)) P(u1, ..., un)}
         The tis and uis must be non-Boolean terms, and the codomain of P must be Bool.
   *)
  | Ceq_congruent_pred_b of expr list

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

  (* 36. Given a proof of the clause {(=> a b)},
         proves the clause {(not a) b}
   *)
  | Cimplies of certif

  (* 37. Given a proof of the clause {(not (=> a b))},
         proves the clause {a}
   *)
  | Cnot_implies1 of certif

  (* 38. Given a proof of the clause {(not (=> a b))},
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


let process_certif rootsa ra rf =
  let add_clause id cl =
    VeritSyntax.add_clause id cl;
    if id > 1 then SmtTrace.link (VeritSyntax.get_clause (id-1)) cl
  in
  let confl_num = ref 0 in

  (* Add roots *)
  let add_roots () =
    Array.iteri (fun i a ->
        let id = i+1 in
        confl_num := id;
        let cl = SmtTrace.mkRootV [a] in
        add_clause id cl
      ) rootsa;
    if !confl_num < 1 then failwith "The SMT problem should have at least one assertion";
  in

  (* Process the certificate *)
  let other c = RKind (SmtCertif.Other c) in
  let builddef h = other (SmtCertif.BuildDef h) in
  let builddef2 h = other (SmtCertif.BuildDef2 h) in
  let buildproj h i = other (SmtCertif.BuildProj (h, i-1)) in
  let immbuilddef c = other (SmtCertif.ImmBuildDef c) in
  let immbuilddef2 c = other (SmtCertif.ImmBuildDef2 c) in
  let immbuildproj c i = other (SmtCertif.ImmBuildProj (c, i-1)) in

  let rec process_certif c =
    let (_, c) = c in
    let kind =
      match c with
        | Cweakening (c, l) ->
           let c' = pc c in
           let l' = List.map (make_form ra rf) l in
           other (SmtCertif.Weaken (c', l'))
        | Cassume i -> RRoot (i+1)
        | Ctrue -> other SmtCertif.True
        | Cfalse -> other SmtCertif.False
        | Cresolution l ->
           (match List.map pc l with
              | cl1::cl2::q ->
                 let res = {SmtCertif.rc1 = cl1; SmtCertif.rc2 = cl2; SmtCertif.rtail = q} in
                 RKind (SmtCertif.Res res)
              | _ -> failwith "resolution should contain at least two clauses"
           )
        | Clia_generic l ->
           let cl = List.map (make_form ra rf) l in
           let k = VeritSyntax.mkMicromega cl in
           RKind k
        | Ceq_reflexive t ->
           let f = make_form ra rf (EEq (t, t)) in
           other (SmtCertif.EqTr (f, []))
        | Ceq_transitive l ->
           (match l with
              | a::b::q ->
                 let last = ref b in
                 let l' =
                   List.fold_left (
                       fun acc t ->
                       let c = !last in
                       last := t;
                       (make_form ra rf (ENot (EEq (c, t))))::acc
                     ) [make_form ra rf (ENot (EEq (a, b)))] q
                 in
                 let l' = List.rev l' in
                 let r = make_form ra rf (EEq (a, !last)) in
                 other (SmtCertif.EqTr (r, l'))
              | _ -> failwith "eq_transitive should contain at least two terms"
           )
        | Ceq_congruent l ->
           let l' = List.map (make_form ra rf) l in
           RKind (VeritSyntax.mkCongr l')
        | Ceq_congruent_pred l ->
           (let (concl, prem) = List.partition (function ENot _ -> false | _ -> true) l in
            match concl with
              | [EEq (pt, pu)] ->
                 let c4  = ("dummy_eq_congruent_pred_1",
                              Ceq_congruent_pred_b ((ENot pt)::pu::prem))
                 in
                 let c5  = ("dummy_eq_congruent_pred_2",
                              Ceq_congruent_pred_b ((ENot pu)::pt::prem))
                 in
                 let c6  = ("dummy_eq_congruent_pred_3", Cequiv_neg2 (pt, pu)) in
                 let c7  = ("dummy_eq_congruent_pred_4", Cequiv_neg1 (pt, pu)) in
                 let c8  = ("dummy_eq_congruent_pred_5", Cresolution [c6; c5]) in
                 let c9  = ("dummy_eq_congruent_pred_6", Cresolution [c4; c8]) in
                 let c7' = pc c7 in
                 let c8' = pc c8 in
                 let c9' = pc c9 in
                 let res =
                   {SmtCertif.rc1 = c7'; SmtCertif.rc2 = c8'; SmtCertif.rtail = [c9']}
                 in
                 RKind (SmtCertif.Res res)
              | _ -> failwith "invalid eq_congruent_pred"
           )
        | Ceq_congruent_pred_b l ->
           let l' = List.map (make_form ra rf) l in
           RKind (VeritSyntax.mkCongrPred l')
        | Cand_neg l -> builddef (make_form ra rf (EAnd l))
        | Cor_pos l -> builddef (make_form ra rf (ENot (EOr l)))
        | Cimplies_pos (a, b) -> builddef (make_form ra rf (ENot (EImp (a, b))))
        | Cxor_pos1 (a, b) -> builddef (make_form ra rf (ENot (EXor (a, b))))
        | Cxor_neg1 (a, b) -> builddef (make_form ra rf (EXor (a, b)))
        | Cequiv_pos1 (a, b) -> builddef (make_form ra rf (ENot (EEq (a, b))))
        | Cequiv_neg1 (a, b) -> builddef (make_form ra rf (EEq (a, b)))

        | Cxor_pos2 (a, b) -> builddef2 (make_form ra rf (ENot (EXor (a, b))))
        | Cxor_neg2 (a, b) -> builddef2 (make_form ra rf (EXor (a, b)))
        | Cequiv_pos2 (a, b) -> builddef2 (make_form ra rf (ENot (EEq (a, b))))
        | Cequiv_neg2 (a, b) -> builddef2 (make_form ra rf (EEq (a, b)))

        | Cor_neg (l, i) -> buildproj (make_form ra rf (EOr l)) i
        | Cand_pos (l, i) -> buildproj (make_form ra rf (ENot (EAnd l))) i
        | Cimplies_neg1 (a, b) -> buildproj (make_form ra rf (EImp (a, b))) 1
        | Cimplies_neg2 (a, b) -> buildproj (make_form ra rf (EImp (a, b))) 2

        | Cnot_and c
        | Cor c
        | Cimplies c
        | Cxor1 c
        | Cnot_xor1 c
        | Cequiv2 c
        | Cnot_equiv2 c -> immbuilddef (pc c)

        | Cxor2 c
        | Cnot_xor2 c
        | Cequiv1 c
        | Cnot_equiv1 c -> immbuilddef2 (pc c)

        | Cand (c, i)
        | Cnot_or (c, i) -> immbuildproj (pc c) i
        | Cnot_implies1 c -> immbuildproj (pc c) 1
        | Cnot_implies2 c -> immbuildproj (pc c) 2
    in
    match kind with
      | RKind k ->
         incr confl_num;
         let id = !confl_num in
         let cl = SmtTrace.mk_scertif k None in
         add_clause id cl;
         id
      | RRoot i -> i

  and pc c =
    VeritSyntax.get_clause (process_certif c)
  in

  fun c -> add_roots (); process_certif c


(* From verit.ml *)
let import_trace rootsa ra rf (c:certif) =
  let confl_num = process_certif rootsa ra rf c in
  let cfirst = ref (VeritSyntax.get_clause 1) in
  let confl = ref (VeritSyntax.get_clause confl_num) in
  (* SmtCertif.print_certif SmtAtom.Form.to_smt !confl "/tmp/before.log"; *)
  SmtTrace.select !confl;
  SmtTrace.occur !confl;
  let res = (SmtTrace.alloc !cfirst, !confl) in
  (* SmtCertif.print_certif SmtAtom.Form.to_smt !confl "/tmp/after.log"; *)
  res


(** The API checker **)

let clear_all () = Smt_utils.clear_all ()


(* From verit_checker.ml *)
let checker_exn (smt:smtlib2) (proof:certif) : bool =
  clear_all ();
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let rootsa = declare_smtlib2 ra rf smt in
  let roots = Array.to_list rootsa in
  let (max_id, confl) = import_trace rootsa ra rf proof in
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

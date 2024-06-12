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
  | EFun of funsym * term list

  (* False *)
  | EFalse
  (* Negation *)
  | ENeg of form

  (* Equality *)
  | EEq of term * term
  (* Distinct *)
  | EDistinct of term list

  (* Integer constants *)
  | EInt of int
  | EBigInt of Big_int.big_int
  (* Addition *)
  | EAdd of term * term
  (* Unary substraction *)
  | EOpp of term
  (* Binary substraction *)
  | EMinus of term * term
  (* Multiplication *)
  | EMult of term * term
  (* Less than *)
  | ELt of term * term
  (* Less or equal *)
  | ELe of term * term
  (* Greater than *)
  | EGt of term * term
  (* Greater or equal *)
  | EGe of term * term


(* From smtlib2/smtlib2_genConstr.ml [make_root_*] *)
exception Ill_typed of expr

let rec make_expr ra rf e =
  match e with
  | TFun ((f, _, _), l) ->
     let op = SmtMaps.get_fun f in
     let l' = List.map (
                  fun t -> match make_expr t with
                             | SmtAtom.Atom h -> h
                             | SmtAtom.Form _ -> raise (Ill_typed t)
                ) l
     in
     SmtAtom.Atom (SmtAtom.Atom.get ra (Aapp (op, Array.of_list l')))
  | TInt i -> SmtAtom.Atom (SmtAtom.Atom.hatom_Z_of_int ra i)
  | TBigInt i -> SmtAtom.Atom (SmtAtom.Atom.hatom_Z_of_bigint ra i)
  | TAdd (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_plus ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TOpp a ->
     (match make_expr ra rf a with
        | SmtAtom.Atom a' -> SmtAtom.Atom (SmtAtom.Atom.mk_opp ra a')
        | _, _ -> raise (Ill_typed e)
     )
  | TMinus (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_minus ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TMult (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_mult ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TLt (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_lt ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TLe (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_le ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TGt (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_gt ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TGe (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' -> SmtAtom.Atom (SmtAtom.Atom.mk_ge ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | TEq (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | SmtAtom.Atom a', SmtAtom.Atom b' ->
           let ta = SmtAtom.Atom.type_of a' in
           let tb = SmtAtom.Atom.type_of b' in
           if (ta <> tb) then
             raise (Ill_typed e)
           else if (ta <> Tbool) then
             SmtAtom.Atom (SmtAtom.Atom.mk_eq_sym ra ta a' b')
           else
             SmtAtom.Form (SmtAtom.Form.get rf (Fapp (Fiff, [|Fatom a'; Fatom b'|])))
        | TODO
     )
  | TDistinct of term list


(*** Formulas ***)
type form =
  | FTerm of term
  | FFalse
  | FNeg of form

(* From smtlib2_genConstr.ml *)
let make_form ra rf f =
  let rec make_form = function
    | FTerm t -> SmtAtom.Form.get rf (Fatom (make_term ra rf t))
    | FFalse -> SmtAtom.Form.get rf SmtAtom.Form.pform_false
    | FNeg f -> SmtAtom.Form.neg (make_form f)
  in
  make_form f


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
type assertions = form array

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


(** Certificate **)
type node =
  | CAssert of int
  | CFalse
  | CResolution of certif list
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
        | CAssert i -> RRoot (i+1)
        | CFalse -> RKind(SmtCertif.Other SmtCertif.False)
        | CResolution l ->
           (match List.map (fun cl -> VeritSyntax.get_clause (process_certif cl)) l with
              | cl1::cl2::q ->
                 let res = {SmtCertif.rc1 = cl1; SmtCertif.rc2 = cl2; SmtCertif.rtail = q} in
                 RKind (SmtCertif.Res res)
              | _ -> failwith "Resolution should contain at least two clauses"
           )
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
let checker (smt:smtlib2) (proof:certif) : bool =
  clear_all ();
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = declare_smtlib2 ra rf smt in
  let (max_id, confl) = import_trace proof in
  Smt_utils.checker ra rf roots max_id confl


(** Callback from C to OCaml
    see https://ocaml.org/manual/4.09/intfc.html#sec426
 **)

let _ = Callback.register "checker" checker


(** Pretty_printers **)

let pp_sort fmt (s:sort) = Format.fprintf fmt "%s" s

let pp_funsym fmt (f:funsym) =
  let (n, _, _) = f in
  Format.fprintf fmt "%s" n

let rec pp_term fmt = function
  | TFun(f, l) ->
     let pp fmt l =
       if List.compare_length_with l 0 = 0 then
         ()
       else
         Smt_utils.pp_list pp_term ", " "(" ")" fmt l
     in
     Format.fprintf fmt "%a%a" pp_funsym f pp l

let rec pp_form fmt = function
  | FTerm t -> pp_term fmt t
  | FFalse -> Format.fprintf fmt "⊥"
  | FNeg f -> Format.fprintf fmt "(¬%a)" pp_form f

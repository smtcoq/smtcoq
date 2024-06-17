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

  (* False *)
  | EFalse
  (* Negation *)
  | ENeg of expr

  (* Equality *)
  | EEq of expr * expr
  (* Distinct *)
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
  | EFalse -> Format.fprintf fmt "false"
  | ENeg f -> Format.fprintf fmt "(not %a)" pp_expr f
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
     let l' = List.map (
                  fun t -> match make_expr ra rf t with
                             | Atom h -> h
                             | Form _ -> raise (Ill_typed e)
                ) l
     in
     Atom (SmtAtom.Atom.get ra (Aapp (op, Array.of_list l')))
  | EFalse -> Form (SmtAtom.Form.get rf SmtAtom.Form.pform_false)
  | ENeg f ->
     let f' = make_form ra rf f in
     Form (SmtAtom.Form.neg f')
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
     let make_h h =
       match make_expr ra rf h with
         | Atom h' -> h'
         | _ -> raise (Ill_typed e)
     in
     let a = Array.make (List.length l) (make_h (List.hd l)) in
     let i = ref (-1) in
     List.iter (fun h ->
         incr i;
         a.(!i) <- make_h h) l;
     Atom (SmtAtom.Atom.mk_distinct ra (SmtAtom.Atom.type_of a.(0)) a)
  | EInt i -> Atom (SmtAtom.Atom.hatom_Z_of_int ra i)
  | EBigInt i -> Atom (SmtAtom.Atom.hatom_Z_of_bigint ra i)
  | EAdd (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_plus ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | EOpp a ->
     (match make_expr ra rf a with
        | Atom a' -> Atom (SmtAtom.Atom.mk_opp ra a')
        | _ -> raise (Ill_typed e)
     )
  | EMinus (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_minus ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | EMult (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_mult ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | ELt (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_lt ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | ELe (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_le ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | EGt (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_gt ra a' b')
        | _, _ -> raise (Ill_typed e)
     )
  | EGe (a, b) ->
     (match make_expr ra rf a, make_expr ra rf b with
        | Atom a', Atom b' -> Atom (SmtAtom.Atom.mk_ge ra a' b')
        | _, _ -> raise (Ill_typed e)
     )

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
let checker_exn (smt:smtlib2) (proof:certif) : bool =
  clear_all ();
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = declare_smtlib2 ra rf smt in
  let (max_id, confl) = import_trace proof in
  Smt_utils.checker ra rf roots max_id confl

let checker_string smt proof =
  try (checker_exn smt proof, None)
  with Ill_typed e ->
    let s = Format.asprintf "Expression %a is ill-typed" pp_expr e in
    (false, Some s)

let checker smt proof =
  let (b, s) = checker_string smt proof in
  match s with
    | Some s' -> failwith s'
    | None -> b


(** Callback from C to OCaml
    see https://ocaml.org/manual/4.09/intfc.html#sec426
 **)

let _ = Callback.register "checker" checker_string

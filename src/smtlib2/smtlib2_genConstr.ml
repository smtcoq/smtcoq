(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Smtlib2_ast
open SmtAtom
open SmtForm
open SmtMisc
open CoqTerms


(* For debugging *)

let pp_symbol s =
  let pp_position p = "{pos_fname = "^p.Lexing.pos_fname^"; pos_lnum = "^(string_of_int p.Lexing.pos_lnum)^"; pos_bol = "^(string_of_int p.Lexing.pos_bol)^"; pos_cnum = "^(string_of_int p.Lexing.pos_cnum)^"}" in

  let pp_loc (p1,p2) = "("^(pp_position p1)^", "^(pp_position p2)^")" in

  match s with
    | Symbol (l,s) -> "Symbol ("^(pp_loc l)^", "^s^")"
    | SymbolWithOr (l,s) -> "SymbolWithOr ("^(pp_loc l)^", "^s^")"


(* Main functions *)

let string_of_symbol = function | Symbol (_,s) | SymbolWithOr (_,s) -> s


let identifier_of_qualidentifier = function
  | QualIdentifierId (_,id) | QualIdentifierAs (_,id,_) -> id


let string_type s = match s with
  | "Bool" -> Tbool
  | "Int" -> TZ
  | _ ->
     let l = String.length s in
     if l >= 7 && String.sub s 0 7 = "BitVec_" then
       let size = int_of_string (String.sub s 7 (l-7)) in
       TBV size
     else
       VeritSyntax.get_btype s


let sort_of_string s = (string_type s, [])


let sort_of_symbol s = sort_of_string (string_of_symbol s)


let string_of_identifier = function
  | IdSymbol (_,s) -> (string_of_symbol s)
  | IdUnderscoreSymNum (_,s,(_,l)) ->
    List.fold_left (fun c c' -> c^"_"^c') (string_of_symbol s) l


let string_of_qualidentifier id = string_of_identifier (identifier_of_qualidentifier id)


let rec sort_of_sort = function
  | SortIdentifier (_,id) -> sort_of_string (string_of_identifier id)
  | SortIdSortMulti (_,id,(_,l)) ->
    (string_type (string_of_identifier id), List.map sort_of_sort l)


let declare_sort rt sym =
  let s = string_of_symbol sym in
  let cons_t = declare_new_type (Names.id_of_string ("Smt_sort_"^s)) in
  let eq_t = declare_new_variable (Names.id_of_string ("eq_"^s)) (Term.mkArrow cons_t (Term.mkArrow cons_t (Lazy.force cbool))) in
  let x = mkName "x" in
  let y = mkName "y" in
  let rx = Term.mkRel 2 in
  let ry = Term.mkRel 1 in
  let eq_refl = Term.mkProd (x,cons_t,Term.mkProd (y,cons_t,mklApp creflect [|mklApp ceq [|cons_t;rx;ry|];mklApp (lazy eq_t) [|rx;ry|]|])) in
  let eq_refl_v = declare_new_variable (Names.id_of_string ("eq_refl_"^s)) eq_refl in
  let ce = mklApp cTyp_eqb [|cons_t;eq_t;eq_refl_v|] in
  let res = Btype.declare rt cons_t ce in
  VeritSyntax.add_btype s res;
  res


let declare_fun rt ro sym arg cod =
  let s = string_of_symbol sym in
  let tyl = List.map sort_of_sort arg in
  let ty = sort_of_sort cod in

  let coqTy = List.fold_right (fun typ c -> Term.mkArrow (Btype.interp_to_coq rt (fst typ)) c) tyl (Btype.interp_to_coq rt (fst ty)) in
  let cons_v = declare_new_variable (Names.id_of_string ("Smt_var_"^s)) coqTy in

  let op = Op.declare ro cons_v (Array.of_list (List.map fst tyl)) (fst ty) in
  VeritSyntax.add_fun s op;
  op



let parse_smt2bv s =
  let l = ref [] in
  for i = 2 to String.length s - 1 do
    match s.[i] with
    | '0' -> l := false :: !l
    | '1' -> l := true :: !l
    | _ -> assert false
  done;
  !l


let make_root_specconstant ra = function
  | SpecConstsDec _ -> failwith "Smtlib2_genConstr.make_root_specconstant: decimals not implemented yet"
  | SpecConstNum (_,s) ->
    (try
      let i = int_of_string s in
      Atom.hatom_Z_of_int ra i
    with
      | Failure _ ->
        let i = Big_int.big_int_of_string s in
        Atom.hatom_Z_of_bigint ra i)
  | SpecConstString _ -> failwith "Smtlib2_genConstr.make_root_specconstant: strings not implemented yet"
  | SpecConstsHex _ -> failwith "Smtlib2_genConstr.make_root_specconstant: hexadecimals not implemented yet"
  | SpecConstsBinary (_, s) -> Atom.mk_bvconst ra (parse_smt2bv s)
    
    


type atom_form = | Atom of SmtAtom.Atom.t | Form of SmtAtom.Form.t


let make_root ra rf t =

  let hlets = Hashtbl.create 17 in

  let rec make_root_term = function
    | TermSpecConst (_,c) -> Atom (make_root_specconstant ra c)
    | TermQualIdentifier (_,id) ->
      let v = string_of_qualidentifier id in
      (try Hashtbl.find hlets v with
        | Not_found ->
          make_root_app v [])
    | TermQualIdTerm (_,id,(_,l)) ->
      let v = string_of_qualidentifier id in
      make_root_app v l
    | TermLetTerm (_,(_,l),t) ->
      List.iter (fun (VarBindingSymTerm (_, sym, u)) ->
        let u' = make_root_term u in
        let s' = string_of_symbol sym in
        Hashtbl.add hlets s' u') l;
      make_root_term t
    | TermForAllTerm _ -> failwith "Smtlib2_genConstr.make_root_term: ForAll not implemented yet"
    | TermExistsTerm _ -> failwith "Smtlib2_genConstr.make_root_term: Exists not implemented yet"
    | TermExclimationPt (_,t,_) -> make_root_term t

  and make_root_app v l =
    match (v,l) with
      | "=", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' ->
            (match Atom.type_of a' with
              | Tbool -> Form (Form.get rf (Fapp (Fiff, [|Form.get rf (Fatom a'); Form.get rf (Fatom b')|])))
              | ty -> Atom (Atom.mk_eq ra ty a' b'))
          | _, _ -> assert false)
      | "<", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_lt ra a' b')
          | _, _ -> assert false)
      | "<=", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_le ra a' b')
          | _, _ -> assert false)
      | ">", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_gt ra a' b')
          | _, _ -> assert false)
      | ">=", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_ge ra a' b')
          | _, _ -> assert false)
      | "+", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_plus ra a' b')
          | _, _ -> assert false)
      | "-", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_minus ra a' b')
          | _, _ -> assert false)
      | "*", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' -> Atom (Atom.mk_mult ra a' b')
          | _, _ -> assert false)
      | "-", [a] ->
        (match make_root_term a with
          | Atom a' -> Atom (Atom.mk_opp ra a')
          | _ -> assert false)
      | "bvand", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' ->
             (match Atom.type_of a' with
               | TBV s -> Atom (Atom.mk_bvand ra s a' b')
               | _ -> assert false)
          | _, _ -> assert false)
      | "bvor", [a;b] ->
        (match make_root_term a, make_root_term b with
          | Atom a', Atom b' ->
             (match Atom.type_of a' with
               | TBV s -> Atom (Atom.mk_bvor ra s a' b')
               | _ -> assert false)
          | _, _ -> assert false)
      | "bvxor", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvxor ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "bvadd", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvadd ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "bvmul", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvmult ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "distinct", _ ->
        let make_h h =
          match make_root_term h with
            | Atom h' -> h'
            | _ -> assert false in
        let a = Array.make (List.length l) (make_h (List.hd l)) in
        let i = ref (-1) in
        List.iter (fun h ->
          incr i;
          a.(!i) <- make_h h) l;
        Atom (Atom.mk_distinct ra (Atom.type_of a.(0)) a)
      | "true", _ -> Form (Form.get rf Form.pform_true)
      | "false", _ -> Form (Form.get rf Form.pform_false)
      | "and", _ ->
        Form (Form.get rf (Fapp (Fand, Array.of_list (List.map make_root l))))
      | "or", _ ->
        Form (Form.get rf (Fapp (For, Array.of_list (List.map make_root l))))
      | "xor", _ ->
        Form (Form.get rf (Fapp (Fxor, Array.of_list (List.map make_root l))))
      | "=>", _ ->
        Form (Form.get rf (Fapp (Fimp, Array.of_list (List.map make_root l))))
      | "ite", _ ->
        Form (Form.get rf (Fapp (Fite, Array.of_list (List.map make_root l))))
      | "not", [a] -> Form (Form.neg (make_root a))
      | _, _ ->
        let op = VeritSyntax.get_fun v in
        let l' = List.map (fun t -> match make_root_term t with
          | Atom h -> h | Form _ -> assert false) l in
        Atom (Atom.get ra (Aapp (op, Array.of_list l')))

  and make_root t =
    match make_root_term t with
      | Atom h -> Form.get rf (Fatom h)
      | Form f -> f in

  make_root t


let declare_commands rt ro ra rf acc = function
  | CDeclareSort (_,sym,_) -> let _ = declare_sort rt sym in acc
  | CDeclareFun (_,sym, (_, arg), cod) ->
    let _ = declare_fun rt ro sym arg cod in acc
  | CAssert (_, t) -> (make_root ra rf t)::acc
  | _ -> acc


(* Import function *)

let import_smtlib2 rt ro ra rf filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let commands = Smtlib2_parse.main Smtlib2_lex.token lexbuf in
  close_in chan;
  match commands with
    | None -> []
    | Some (Smtlib2_ast.Commands (_,(_,res))) ->
      List.rev (List.fold_left (declare_commands rt ro ra rf) [] res)

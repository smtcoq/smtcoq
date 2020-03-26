(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Smtlib2_ast
open SmtAtom
open SmtForm
open SmtMisc
open CoqTerms
open SmtBtype

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


let string_type st s =
  match s with
  | "Bool" -> fun _ -> Tbool
  | "Int" -> fun _ -> TZ
  | "Array" -> (function [ti;te] -> TFArray (ti, te) | _ -> assert false)
  | _ ->
    try Scanf.sscanf s "BitVec_%d%!" (fun size -> fun _ -> TBV size)
    with _ -> fun _ -> LocalState.get_btype st s

let sort_of_string st s = string_type st s


(* let sort_of_symbol s = sort_of_string (string_of_symbol s) *)


let rec bigint_binary_size acc i size =
  let open Big_int in
  if size = 0 then "#b" ^ String.concat "" acc
  else
  if eq_big_int i zero_big_int then
    bigint_binary_size ("0" :: acc) i (size - 1)
  else begin
    assert (gt_big_int i zero_big_int && size > 0);
    bigint_binary_size (string_of_big_int (and_big_int i unit_big_int) :: acc)
      (shift_right_big_int i 1) (size - 1)
  end

let bigint_bv i size = bigint_binary_size [] i size


exception DecimalBv of string

let string_of_identifier = function
  | IdSymbol (_,s) -> (string_of_symbol s)
  | IdUnderscoreSymNum (_,s,(_,l)) ->
    let s = string_of_symbol s in
    let isbvdec =
      try s.[0] = 'b' && s.[1]= 'v' with Invalid_argument _ -> false in
    (match isbvdec, l with
     (* rewrite bitvectors decimal constants *)
     | true, [size] ->
       let sbv =
         Scanf.sscanf s "bv%s" (fun n ->
             bigint_bv (Big_int.big_int_of_string n) (int_of_string size)) in
       raise (DecimalBv sbv)
     | _ -> List.fold_left (fun c c' -> c^"_"^c') s l
    )


let string_of_qualidentifier id = string_of_identifier (identifier_of_qualidentifier id)


let rec sort_of_sort st = function
  | SortIdentifier (_,id) -> sort_of_string st (string_of_identifier id) []
  | SortIdSortMulti (_,id,(_,l)) ->
    sort_of_string st (string_of_identifier id) (List.map (sort_of_sort st) l)


let declare_sort_from_name st s =
  let rt = LocalState.get_type_tbl st in

  let cons_t = Structures.declare_new_type (Structures.mkId ("Smt_sort_"^s)) in
  let compdec_type = mklApp cCompDec [| cons_t |] in
  let compdec_var =
    Structures.declare_new_variable (Structures.mkId ("CompDec_"^s)) compdec_type in
  let ce = mklApp cTyp_compdec [|cons_t; compdec_var|] in
  let res = SmtBtype.declare rt cons_t ce in
  LocalState.add_btype st s res;
  res

let declare_sort st sym = declare_sort_from_name st (string_of_symbol sym)


let declare_fun_from_name st s tyl ty =
  let rt = LocalState.get_type_tbl st in
  let ro = LocalState.get_op_tbl st in

  let coqTy = List.fold_right (fun typ c ->
      Term.mkArrow (interp_to_coq rt typ) c)
      tyl (interp_to_coq rt ty) in
  let cons_v = Structures.declare_new_variable (Structures.mkId ("Smt_var_"^s)) coqTy in
  let op = Op.declare ro cons_v (Array.of_list tyl) ty None in
  LocalState.add_fun st s op;
  op

let declare_fun st sym arg cod =
  let tyl = List.map (sort_of_sort st) arg in
  let ty = sort_of_sort st cod in
  declare_fun_from_name st (string_of_symbol sym) tyl ty



let parse_smt2bv s =
  let l = ref [] in
  for i = 2 to String.length s - 1 do
    match s.[i] with
    | '0' -> l := false :: !l
    | '1' -> l := true :: !l
    | _ -> failwith "Not a bitvector"
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

let startwith prefix s =
  try Scanf.sscanf s (prefix ^^ "%_s") true with _ -> false

let make_root ra rf st t =

  let hlets = Hashtbl.create 17 in

  let rec make_root_term = function
    | TermSpecConst (_,c) -> Atom (make_root_specconstant ra c)
    | TermQualIdentifier (loc,id) ->
      (try
        let v = string_of_qualidentifier id in
        (try Hashtbl.find hlets v with Not_found -> make_root_app v [])
       with
       | DecimalBv sbv ->
         make_root_term (TermSpecConst (loc, SpecConstsBinary (loc, sbv)))
      )
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
         | Atom a', Atom b' when Atom.type_of a' <> Tbool ->
           Atom (Atom.mk_eq ra (Atom.type_of a') a' b')
         | _ -> Form (Form.get rf (Fapp (Fiff, [|make_root a; make_root b|])))
        )
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
      | "bvnot", [a] ->
        (match make_root_term a with
          | Atom a' ->
             (match Atom.type_of a' with
               | TBV s -> Atom (Atom.mk_bvnot ra s a')
               | _ -> assert false)
          | _ -> assert false)
      | "bvneg", [a] ->
        (match make_root_term a with
          | Atom a' ->
             (match Atom.type_of a' with
               | TBV s -> Atom (Atom.mk_bvneg ra s a')
               | _ -> assert false)
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
      | "bvult", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvult ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "bvslt", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvslt ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "bvule", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom h1, Atom h2 ->
           (match Atom.type_of h1 with
            | TBV s ->
              let a = Atom.mk_bvult ra s h2 h1 in
              Form (Form.neg (Form.get rf (Fatom a)))
            | _ -> assert false)
         | _,_ -> assert false
        )
      | "bvsle", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom h1, Atom h2 ->
           (match Atom.type_of h1 with
            | TBV s ->
              let a = Atom.mk_bvslt ra s h2 h1 in
              Form (Form.neg (Form.get rf (Fatom a)))
            | _ -> assert false)
         | _,_ -> assert false
        )
      | "bvshl", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvshl ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "bvlshr", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a' with
            | TBV s -> Atom (Atom.mk_bvshr ra s a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "concat", [a;b] ->
        (match make_root_term a, make_root_term b with
         | Atom a', Atom b' ->
           (match Atom.type_of a', Atom.type_of b' with
            | TBV s1, TBV s2 -> Atom (Atom.mk_bvconcat ra s1 s2 a' b')
            | _ -> assert false)
         | _, _ -> assert false)
      | "select", [a;i] ->
        (match make_root_term a, make_root_term i with
         | Atom a', Atom i' ->
           (match Atom.type_of a' with
            | TFArray (ti, te) -> Atom (Atom.mk_select ra ti te a' i')
            | _ -> assert false)
         | _ -> assert false)

      | "store", [a;i;v] ->
        (match make_root_term a, make_root_term i, make_root_term v with
         | Atom a', Atom i', Atom v' ->
           (match Atom.type_of a' with
            | TFArray (ti, te) -> Atom (Atom.mk_store ra ti te a' i' v')
            | _ -> assert false)
         | _ -> assert false)

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

      | _, [a] when startwith "extract_" v ->
        (try
          Scanf.sscanf v "extract_%s@_%d" (fun s i ->
            let j = int_of_string s in
            (match make_root_term a with
             | Atom a' ->
               (match Atom.type_of a' with
                | TBV s -> Atom (Atom.mk_bvextr ra ~s ~i ~n:(j-i+1) a')
                | _ -> assert false)
             | _ -> assert false)
             )
         with _ -> assert false)

      | _, [a] when startwith "zero_extend_" v ->
        (try
           Scanf.sscanf v "zero_extend_%d" (fun n ->
               (match make_root_term a with
                | Atom a' ->
                  (match Atom.type_of a' with
                   | TBV s -> Atom (Atom.mk_bvzextn ra ~s ~n a')
                   | _ -> assert false)
                | _ -> assert false)
             )
         with _ -> assert false)

      | _, [a] when startwith "sign_extend_" v ->
        (try
           Scanf.sscanf v "sign_extend_%d" (fun n ->
               (match make_root_term a with
                | Atom a' ->
                  (match Atom.type_of a' with
                   | TBV s -> Atom (Atom.mk_bvsextn ra ~s ~n a')
                   | _ -> assert false)
                | _ -> assert false)
             )
         with _ -> assert false)

      | _, _ ->
        let op = LocalState.get_fun st v in
        let l' = List.map (fun t ->
            match make_root_term t with
            | Atom h -> h | Form _ -> assert false) l in
        Atom (Atom.get ra (Aapp (op, Array.of_list l')))

  and make_root t =
    match make_root_term t with
    | Atom h -> Form.get rf (Fatom h)
    | Form f -> f in
  make_root t


let declare_commands st acc decl =
  let ra = LocalState.get_atom_tbl_to_add st in
  let rf = LocalState.get_form_tbl_to_add st in
  match decl with
    | CDeclareSort (_,sym,_) -> let _ = declare_sort st sym in acc
    | CDeclareFun (_,sym, (_, arg), cod) ->
       let _ = declare_fun st sym arg cod in acc
    | CAssert (_, t) -> (make_root ra rf st t)::acc
    | _ -> acc


(* Import function *)

let import_smtlib2 st filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let commands = Smtlib2_parse.main Smtlib2_lex.token lexbuf in
  close_in chan;
  match commands with
    | None -> []
    | Some (Smtlib2_ast.Commands (_,(_,res))) ->
      List.rev (List.fold_left (declare_commands st) [] res)

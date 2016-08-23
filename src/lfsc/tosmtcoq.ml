(**************************************************************************)
(*                                                                        *)
(*                            LFSCtoSmtCoq                                *)
(*                                                                        *)
(*                         Copyright (C) 2016                             *)
(*          by the Board of Trustees of the University of Iowa            *)
(*                                                                        *)
(*                    Alain Mebsout and Burak Ekici                       *)
(*                       The University of Iowa                           *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open SmtAtom
open SmtForm
open SmtCertif
open SmtTrace
open VeritSyntax
open Ast
open Builtin
open Format
open Translator_sig  

type lit = SmtAtom.Form.t

type clause = lit list


module HS = Hashtbl
module HT = Hashtbl.Make (Term)
module HCl = Hashtbl


let clauses_ids = HCl.create 201
let ids_clauses = Hashtbl.create 201
let propvars = HT.create 201
let inputs : (string, int) Hashtbl.t = HS.create 13
let diffarray_tbl = HS.create 17

let cl_cpt = ref 0


let get_rule = function
  | Reso -> VeritSyntax.Reso
  | Weak -> VeritSyntax.Weak
  | Or -> VeritSyntax.Or
  | Orp -> VeritSyntax.Orp
  | Imp -> VeritSyntax.Imp
  | Impp -> VeritSyntax.Impp
  | Nand -> VeritSyntax.Nand
  | Andn -> VeritSyntax.Andn
  | Nimp1 -> VeritSyntax.Nimp1
  | Nimp2 -> VeritSyntax.Nimp2
  | Impn1 -> VeritSyntax.Impn1
  | Impn2 -> VeritSyntax.Impn2
  | Nor -> VeritSyntax.Nor
  | Orn -> VeritSyntax.Orn
  | And -> VeritSyntax.And
  | Andp -> VeritSyntax.Andp
  | Equ1 -> VeritSyntax.Equ1
  | Equ2 -> VeritSyntax.Equ2
  | Nequ1 -> VeritSyntax.Nequ1
  | Nequ2 -> VeritSyntax.Nequ2
  | Equp1 -> VeritSyntax.Equp1
  | Equp2 -> VeritSyntax.Equp2
  | Equn1 -> VeritSyntax.Equn1
  | Equn2 -> VeritSyntax.Equn2
  | Xor1 -> VeritSyntax.Xor1
  | Xor2 -> VeritSyntax.Xor2
  | Xorp1 -> VeritSyntax.Xorp1
  | Xorp2 -> VeritSyntax.Xorp2
  | Xorn1 -> VeritSyntax.Xorn1
  | Xorn2 -> VeritSyntax.Xorn2
  | Nxor1 -> VeritSyntax.Nxor1
  | Nxor2 -> VeritSyntax.Nxor2
  | Itep1 -> VeritSyntax.Itep1
  | Itep2 -> VeritSyntax.Itep2
  | Iten1 -> VeritSyntax.Iten1
  | Iten2 -> VeritSyntax.Iten2
  | Ite1 -> VeritSyntax.Ite1
  | Ite2 -> VeritSyntax.Ite2
  | Nite1 -> VeritSyntax.Nite1
  | Nite2 -> VeritSyntax.Nite2
  | Eqtr -> VeritSyntax.Eqtr
  | Eqcp -> VeritSyntax.Eqcp
  | Eqco -> VeritSyntax.Eqco
  | Eqre -> VeritSyntax.Eqre
  | Lage -> VeritSyntax.Lage
  | Flat -> VeritSyntax.Flat
  | Hole -> VeritSyntax.Hole
  | True -> VeritSyntax.True
  | Fals -> VeritSyntax.Fals
  | Bbva -> VeritSyntax.Bbva
  | Bbconst -> VeritSyntax.Bbconst
  | Bbeq -> VeritSyntax.Bbeq
  | Bbop -> VeritSyntax.Bbop
  | Bbadd -> VeritSyntax.Bbadd
  | Bbmul -> VeritSyntax.Bbmul
  | Bbult -> VeritSyntax.Bbult
  | Bbslt -> VeritSyntax.Bbslt
  | Bbnot -> VeritSyntax.Bbnot
  | Bbneg -> VeritSyntax.Bbneg
  | Bbconc -> VeritSyntax.Bbconc
  | Row1 -> VeritSyntax.Row1
  | Row2 -> VeritSyntax.Row2
  | Exte -> VeritSyntax.Exte

let string_of_rule = function
  | Reso -> "resolution"
  | Weak -> "weaken"
  | Or -> "or"
  | Orp -> "or_pos"
  | Imp -> "implies"
  | Impp -> "implies_pos"
  | Nand -> "not_and"
  | Andn -> "and_neg"
  | Nimp1 -> "not_implies1"
  | Nimp2 -> "not_implies2"
  | Impn1 -> "implies_neg1"
  | Impn2 -> "implies_neg2"
  | Nor -> "not_or"
  | Orn -> "or_neg"
  | And -> "and"
  | Andp -> "and_pos"
  | Equ1 -> "equiv1"
  | Equ2 -> "equiv2"
  | Nequ1 -> "not_equiv1"
  | Nequ2 -> "not_equiv2"
  | Equp1 -> "equiv_pos1"
  | Equp2 -> "equiv_pos2"
  | Equn1 -> "equiv_neg1"
  | Equn2 -> "equiv_neg2"
  | Xor1 -> "xor1"
  | Xor2 -> "xor2"
  | Xorp1 -> "xor_pos1"
  | Xorp2 -> "xor_pos2"
  | Xorn1 -> "xor_neg1"
  | Xorn2 -> "xor_neg2"
  | Nxor1 -> "not_xor1"
  | Nxor2 -> "not_xor2"
  | Itep1 -> "ite_pos1"
  | Itep2 -> "ite_pos2"
  | Iten1 -> "ite_neg1"
  | Iten2 -> "ite_neg2"
  | Ite1 -> "ite1"
  | Ite2 -> "ite2"
  | Nite1 -> "not_ite1"
  | Nite2 -> "not_ite2"
  | Eqtr -> "eq_transitive"
  | Eqcp -> "eq_congruent_pred"
  | Eqco -> "eq_congruent"
  | Eqre -> "eq_reflexive"
  | Lage -> "la_generic"
  | Flat -> "flatten"
  | Hole -> "hole"
  | True -> "true"
  | Fals -> "false"
  | Bbva -> "bbvar"
  | Bbconst -> "bbconst"
  | Bbeq -> "bbeq"
  | Bbop -> "bbop"
  | Bbadd -> "bbadd"
  | Bbmul -> "bbmul"
  | Bbult -> "bbult"
  | Bbslt -> "bbslt"
  | Bbnot -> "bbnot"
  | Bbneg -> "bbneg"
  | Bbconc -> "bbconcat"
  | Row1 -> "row1"
  | Row2 -> "row2" 
  | Exte -> "ext" 


let bit_to_bool t = match name t with
  | Some "b0" -> false
  | Some "b1" -> true
  | _ -> assert false

let rec const_bv_aux acc t = match name t with
  | Some "bvn" -> acc
  | _ ->
    match app_name t with
    | Some ("bvc", [b; t]) -> const_bv_aux (bit_to_bool b :: acc) t
    | _ -> assert false

let const_bv t =
  let bv_list = const_bv_aux [] t in
  Atom (Atom.mk_bvconst ra bv_list)


let rec term_smtcoq t = match value t with
  | Const {sname=Name "true"} -> Form Form.pform_true
  | Const {sname=Name "false"} -> Form Form.pform_false
  | Const {sname=Name "bvn"} -> const_bv t
  | Const {sname=Name n} ->
    begin
      try
        term_smtcoq  (HS.find diffarray_tbl n)
      with Not_found -> Atom (Atom.get ra (Aapp (get_fun n,[||])))
    end
  | Int bi -> Atom (Atom.hatom_Z_of_bigint ra bi)
  | App _ ->
    begin match app_name t with
      | Some ("not", [f]) ->
        Lit (Form.neg (lit_of_atom_form_lit rf (term_smtcoq f)))
      | Some ("and", args) -> Form (Fapp (Fand, args_smtcoq args))
      | Some ("or", args) -> Form (Fapp (For, args_smtcoq args))
      | Some ("impl", args) -> Form (Fapp (Fimp, args_smtcoq args))
      | Some ("xor", args) -> Form (Fapp (Fxor, args_smtcoq args))
      | Some (("ite"|"ifte"), args) -> Form (Fapp (Fite, args_smtcoq args))
      | Some ("iff", args) -> Form (Fapp (Fiff, args_smtcoq args))
      | Some ("=", [_; a; b]) ->
        let h1, h2 = term_smtcoq_atom a, term_smtcoq_atom b in
        Atom (Atom.mk_eq ra (Atom.type_of h1) h1 h2)
      | Some ("apply", _) -> uncurry [] t
      | Some ("p_app", [p]) -> term_smtcoq p
      | Some ("a_int", [{value = Int bi}]) ->
        Atom (Atom.hatom_Z_of_bigint ra bi)
      | Some ("a_int", [ni]) ->
        begin match app_name ni with
          | Some ("~", [{value = Int bi}]) ->
            Atom (Atom.hatom_Z_of_bigint ra (Big_int.minus_big_int bi))
          | _ -> assert false
        end
      | Some ("a_var_bv", [_; v]) -> term_smtcoq v
      | Some ("bvc", _) -> const_bv t
      | Some ("a_bv", [_; v]) -> term_smtcoq v
      | Some ("bitof", [a; {value = Int n}]) ->
         (let ha = term_smtcoq_atom a in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bitof ra s (Big_int.int_of_big_int n) ha)
            | _ -> assert false)
      | Some ("bblast_term", [_; a; bb]) ->
        Form (FbbT ((term_smtcoq_atom a), bblt_lits [] bb))
      | Some ("bvnot", [_; a]) ->
         (let ha = term_smtcoq_atom a in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvnot ra s ha)
            | _ -> assert false)
      | Some ("bvneg", [_; a]) ->
         (let ha = term_smtcoq_atom a in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvneg ra s ha)
            | _ -> assert false)
      | Some ("bvand", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvand ra s ha hb)
            | _ -> assert false)
      | Some ("bvor", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvor ra s ha hb)
            | _ -> assert false)
      | Some ("bvxor", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvxor ra s ha hb)
            | _ -> assert false)
      | Some ("bvadd", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvadd ra s ha hb)
            | _ -> assert false)
      | Some ("bvmul", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvmult ra s ha hb)
            | _ -> assert false)
      | Some ("bvult", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvult ra s ha hb)
            | _ -> assert false)
      | Some ("bvslt", [_; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha with
            | TBV s -> Atom (Atom.mk_bvslt ra s ha hb)
            | _ -> assert false)
      | Some ("concat", [_; _; _; a; b]) ->
         (let ha = term_smtcoq_atom a in
          let hb = term_smtcoq_atom b in
          match Atom.type_of ha, Atom.type_of hb with
            | TBV s1, TBV s2 -> Atom (Atom.mk_bvconcat ra s1 s2 ha hb)
            | _ -> assert false)
      | Some ("<_Int", [a; b]) ->
        Atom (Atom.mk_lt ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some ("<=_Int", [a; b]) ->
        Atom (Atom.mk_le ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some (">_Int", [a; b]) ->
        Atom (Atom.mk_gt ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some (">=_Int", [a; b]) ->
        Atom (Atom.mk_ge ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some ("+_Int", [a; b]) ->
        Atom (Atom.mk_plus ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some ("-_Int", [a; b]) ->
        Atom (Atom.mk_minus ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some ("*_Int", [a; b]) ->
        Atom (Atom.mk_mult ra (term_smtcoq_atom a) (term_smtcoq_atom b))
      | Some ("u-_Int", [a]) -> Atom (Atom.mk_opp ra (term_smtcoq_atom a))
      | Some (n, _) ->
        Format.eprintf "\nTerm: %a\n@." print_term t;
        failwith ("LFSC function symbol "^n^" not supported.")
      | _ -> assert false
    end

  | Rat _ -> failwith ("LFSC rationals not supported")
  | Type -> failwith ("LFSC Type not supported")
  | Kind -> failwith ("LFSC Kind not supported")
  | Mpz -> failwith ("LFSC mpz not supported")
  | Mpq -> failwith ("LFSC mpq not supported")
  | Pi _ -> failwith ("LFSC pi abstractions not supported")
  | Lambda _ -> failwith ("LFSC lambda abstractions not supported")
  | Hole _ -> failwith ("LFSC holes not supported")
  | Ptr _ -> failwith ("LFSC Ptr not supported")
  | SideCond _ -> failwith ("LFSC side conditions not supported")
  | _ -> assert false


and term_smtcoq_atom a = match term_smtcoq a with
  | Atom h -> h
  | _ ->  assert false

and args_smtcoq args =
  List.map (fun t -> lit_of_atom_form_lit rf (term_smtcoq t)) args
  |> Array.of_list

and uncurry acc t = match app_name t, acc with
  | Some ("apply", [_; _; f; a]), _ -> uncurry (term_smtcoq_atom a :: acc) f
  | Some ("read", [_; _]), [h1; h2] ->
    (match Atom.type_of h1 with
     | TFArray (ti,te) -> Atom (Atom.mk_select ra ti te h1 h2)
     | _ -> assert false)
  | Some ("write", [_; _]), [h1; h2; h3] ->
    (match Atom.type_of h1 with
     | TFArray (ti,te) -> Atom (Atom.mk_store ra ti te h1 h2 h3)
     | _ -> assert false)
  | Some ("diff", [_; _]), [h1; h2] ->
    (match Atom.type_of h1 with
     | TFArray (ti,te) -> Atom (Atom.mk_diffarray ra ti te h1 h2)
     | _ -> assert false)
  | None, _ ->
    (match name t with
     | Some n ->
       let args = Array.of_list acc in
       Atom (Atom.get ra (Aapp (get_fun n, args)))
     | _ -> assert false)
  | _ ->
    eprintf "uncurry fail: %a@." Ast.print_term t;
    assert false

(* Endianness dependant: LFSC big endian -> SMTCoq little endian *)
and bblt_lits acc t = match name t with
  | Some "bbltn" -> acc
  | _ -> match app_name t with
    | Some ("bbltc", [f; r]) ->
      bblt_lits (lit_of_atom_form_lit rf (term_smtcoq f) :: acc) r
    | _ -> assert false


let term_smtcoq t =
  (* eprintf "translate term %a@." Ast.print_term t; *)
  lit_of_atom_form_lit rf (term_smtcoq t)


let rec clause_smtcoq acc t = match name t with
  | Some "cln" | Some "false" -> acc
  | Some _ -> term_smtcoq t :: acc
  | None ->
    match app_name t with
    | Some ("pos", [v]) ->
      let t = HT.find propvars (deref v) in
      term_smtcoq t :: acc
    | Some ("neg", [v]) ->
      let t = HT.find propvars (deref v) in
      Form.neg (term_smtcoq t) :: acc
    | Some ("clc", [a; cl]) -> clause_smtcoq (clause_smtcoq acc a) cl
    | Some ("or", [a; b]) -> clause_smtcoq (clause_smtcoq acc a) b
    | _ -> term_smtcoq t :: acc


let to_clause = clause_smtcoq [] 


let print_clause fmt cl =
  fprintf fmt "(";
  List.iter (fprintf fmt "%a " (Form.to_smt Atom.to_smt)) cl;
  fprintf fmt ")"



type clause_res_id = NewCl of int | OldCl of int


let register_clause_id cl id =
  HCl.add clauses_ids cl id;
  Hashtbl.add ids_clauses id cl


let register_termclause_id t id =
  register_clause_id (to_clause t) id


let new_clause_id ?(reuse=true) cl =
  try
    if not reuse then raise Not_found;
    OldCl (HCl.find clauses_ids cl)
  with Not_found ->
    (* eprintf "new clause : [%a]@." (fun fmt -> List.iter (fprintf fmt "%a, " (Form.to_smt Atom.to_smt))) cl; *)
    incr cl_cpt;
    let id = !cl_cpt in
    (* eprintf "new clause %d@." id; *)
    register_clause_id cl id;
    NewCl id


let mk_clause ?(reuse=true) rule cl args =
  match new_clause_id ~reuse cl with
  | NewCl id ->
    (* Format.eprintf "mk_clause %d : %a@." id print_clause cl; *)
    (* Format.eprintf "mk_clause %d@." id; *)
    eprintf "%d:(%s %a %a)@." id (string_of_rule rule)
      print_clause cl
    (fun fmt -> List.iter (fprintf fmt " %d")) args;
    VeritSyntax.mk_clause (id, (get_rule rule), cl, args)
  | OldCl id ->
    (* Format.eprintf "old_clause %d@." id; *)
    id


let mk_clause_cl ?(reuse=true) rule cl args =
  mk_clause ~reuse rule (List.map term_smtcoq cl) args


let mk_input name formula =
  let cl = [term_smtcoq formula] in
  match new_clause_id cl with
   | NewCl id ->
     register_clause_id cl id;
     HS.add inputs name id;
     eprintf "%d:input  %a@." id print_clause cl;
     (* Format.eprintf "mk_input %d@." id; *)
     VeritSyntax.mk_clause (id, VeritSyntax.Inpu, cl, []) |> ignore
   | OldCl _ -> ()


let mk_admit_preproc name formula =
  let cl = [term_smtcoq formula] in
  match new_clause_id cl with
   | NewCl id ->
     register_clause_id cl id;
     HS.add inputs name id;
     eprintf "%d:hole  %a@." id print_clause cl;
     VeritSyntax.mk_clause (id, VeritSyntax.Hole, cl, []) |> ignore
   | OldCl _ -> ()


let register_prop_abstr vt formula = HT.add propvars vt formula


let register_diff name_index t = HS.add diffarray_tbl name_index t


let get_clause_id cl =
  try HCl.find clauses_ids cl with Not_found -> assert false


let get_input_id h = HS.find inputs h


let register_decl name formula =
  let cl = [term_smtcoq formula] in
  match new_clause_id cl with
  | NewCl id | OldCl id ->
    (* eprintf "register decl %d@." id; *)
    HS.add inputs name id

let register_decl_id name id =
  (* eprintf "register_decl %s : %d@." name id; *)
  HS.add inputs name id



let clear () =
  HCl.clear clauses_ids;
  Hashtbl.clear ids_clauses;
  HT.clear propvars;
  HS.clear inputs;
  HS.clear diffarray_tbl;
  cl_cpt := 0
  

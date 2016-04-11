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
let inputs = HS.create 13

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
  | Eqtr -> VeritSyntax.Eqtr
  | Eqcp -> VeritSyntax.Eqcp
  | Eqco -> VeritSyntax.Eqco
  | Eqre -> VeritSyntax.Eqre



let rec term_smtcoq t = match value t with
  | Const {sname=Name "true"} -> Form Form.pform_true
  | Const {sname=Name "false"} -> Form Form.pform_false
  | Const {sname=Name n} -> Atom (Atom.get ra (Aapp (get_fun n,[||])))
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
        let h1, h2 =
          match term_smtcoq a, term_smtcoq b with
          | Atom h1, Atom h2 -> h1, h2
          | _ -> assert false
        in
        Atom (Atom.mk_eq ra (Atom.type_of h1) h1 h2)
      | Some ("apply", _) -> uncurry [] t
      | Some ("p_app", [p]) -> term_smtcoq p
      | Some (n, _) -> failwith (n ^ " not implemented")        
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

and args_smtcoq args =
  List.map (fun t -> lit_of_atom_form_lit rf (term_smtcoq t)) args
  |> Array.of_list

and uncurry acc t = match app_name t with
  | Some ("apply", [_; _; f; a]) ->
    (match term_smtcoq a with
     | Atom h -> uncurry (h :: acc) f
     | _ ->  assert false
    )
  | None ->
    (match name t with
     | Some n ->
       let args = Array.of_list acc in
       Atom (Atom.get ra (Aapp (get_fun n, args)))
     | _ -> assert false
    )
  | _ ->
    eprintf "uncurry fail: %a@." Ast.print_term t;
    assert false



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
    (* eprintf "new clause : [%a]@." (fun fmt -> List.iter (fprintf fmt "%a, " Ast.print_term)) cl; *)
    incr cl_cpt;
    let id = !cl_cpt in
    register_clause_id cl id;
    NewCl id


let mk_clause ?(reuse=true) rule cl args =
  match new_clause_id ~reuse cl with
  | NewCl id ->
    (* Format.eprintf "mk_clause %d : %a@." id print_clause cl; *)
    VeritSyntax.mk_clause (id, (get_rule rule), cl, args)
  | OldCl id -> id


let mk_clause_cl ?(reuse=true) rule cl args =
  mk_clause ~reuse rule (List.map term_smtcoq cl) args


let mk_input name formula =
  let cl = [term_smtcoq formula] in
  match new_clause_id cl with
   | NewCl id ->
     register_clause_id cl id;
     HS.add inputs name id;
     (* Format.eprintf "mk_input %d@." id; *)
     VeritSyntax.mk_clause (id, VeritSyntax.Inpu, cl, []) |> ignore
   | OldCl _ -> ()


let register_prop_abstr vt formula = HT.add propvars vt formula


let get_clause_id cl = HCl.find clauses_ids cl


let get_input_id h = HS.find inputs h


let clear () =
  HCl.clear clauses_ids;
  Hashtbl.clear ids_clauses;
  HT.clear propvars;
  Hashtbl.clear inputs;
  cl_cpt := 0
  

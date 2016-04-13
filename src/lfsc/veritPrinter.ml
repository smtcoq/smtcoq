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

open Format
open Ast
open Builtin
open Translator_sig  


type lit = term

type clause = term list


module HS = Hashtbl
module HT = Hashtbl.Make (Term)
module HCl = Hashtbl.Make (struct
    type t = clause
    let equal c1 c2 = compare_term_list c1 c2 = 0
    let hash = List.fold_left (fun acc t -> Term.hash t + acc) 0 
  end)


let fmt = std_formatter

let clauses_ids = HCl.create 201
let ids_clauses = Hashtbl.create 201
let propvars = HT.create 201
let sharp_tbl = HT.create 13
let inputs : (string, int) Hashtbl.t = HS.create 13

let cpt = ref 0
let cl_cpt = ref 0


let get_rule = function
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
  | Eqtr -> "eq_transitive"
  | Eqcp -> "eq_congruent_pred"
  | Eqco -> "eq_congruent"
  | Eqre -> "eq_reflexive"
  | Lage -> "la_generic"


let print_sharps () =
  HT.iter (fun t id ->
      printf "#%d --> %a@." id Ast.print_term_type t) sharp_tbl


let smt2_of_lfsc = function
  | "iff" -> "="
  | "ifte" -> "ite"
  | "flet" -> "let"
  | "impl" -> "=>"
  | ">_Int" -> ">"
  | ">=_Int" -> ">="
  | "<_Int" -> "<"
  | "<=_Int" -> "<="
  | "+_Int" -> "+"
  | "-_Int" -> "-"
  | "*_Int" -> "*"
  | "/_Int" -> "/" (* Maybe div? *)
  | "u-_Int" -> "-"
  | t -> t


let rec print_apply fmt t = match app_name t with
  | Some ("apply", [_; _; f; a]) ->
    fprintf fmt "%a %a" print_apply f print_term a
  | _ -> print_term fmt t
  

and print_term fmt t =
  try HT.find sharp_tbl t |> fprintf fmt "#%d"
  with Not_found ->
    match name t with
    | Some n -> pp_print_string fmt (smt2_of_lfsc n)
    | None -> match app_name t with

      | Some ("=", [ty; a; b]) ->
        let eqt = match value t with App (eqt, _ ) -> eqt | _ -> assert false in
        incr cpt;
        let eq_b_a = mk_app eqt [ty; b; a] in
        HT.add sharp_tbl t !cpt;
        HT.add sharp_tbl eq_b_a !cpt;
        (* let a, b = if compare_term a b <= 0 then a, b else b, a in *)
        fprintf fmt "#%d:(= %a %a)" !cpt print_term a print_term b


      | Some ("not", [a]) -> fprintf fmt "(not %a)" print_term a
                               
      | Some ("apply", _) ->
        incr cpt;
        HT.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(%a)" !cpt print_apply t

      | Some ("p_app", [a]) -> print_term fmt a

      | Some ("a_int", [{value = Int n}]) ->
        fprintf fmt "%s" (Big_int.string_of_big_int n)

      | Some (n, l) ->
        let n = smt2_of_lfsc n in
        incr cpt;
        HT.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(%s%a)" !cpt n
          (fun fmt -> List.iter (fprintf fmt " %a" print_term)) l

      | None -> assert false


let print_term fmt t = print_term fmt t (* (get_real t) *)


let rec print_clause elim_or fmt t = match name t with
  | Some "cln" | Some "false" -> ()
  | Some n -> pp_print_string fmt (smt2_of_lfsc n)
  | None ->
    match app_name t with
    | Some ("pos", [v]) ->
      let t = HT.find propvars (deref v) in
      fprintf fmt "%a" print_term t
    | Some ("neg", [v]) ->
      let t = HT.find propvars (deref v) in
      fprintf fmt "(not %a)" print_term t
    | Some ("clc", [a; cl]) ->
      fprintf fmt "%a %a" (print_clause elim_or) a (print_clause elim_or) cl
    | Some ("or", [a; b]) when elim_or ->
      fprintf fmt "%a %a" (print_clause elim_or) a (print_clause elim_or) b
    | _ -> fprintf fmt "%a" print_term t


let print_clause_elim_or fmt t = fprintf fmt "(%a)" (print_clause true) t

let print_clause fmt t = fprintf fmt "(%a)" (print_clause false) t
  

let rec to_clause acc t = match name t with
  | Some "cln" | Some "false" -> acc
  | Some n -> t :: acc
  | None ->
    match app_name t with
    | Some ("pos", [v]) ->
      let t = HT.find propvars (deref v) in
      t :: acc
    | Some ("neg", [v]) ->
      let t = HT.find propvars (deref v) |> not_ in
      t :: acc
    | Some ("clc", [a; cl]) ->
      to_clause (to_clause acc a) cl
    | Some ("or", [a; b]) ->
      to_clause (to_clause acc a) b
    | _ -> t :: acc


let to_clause = to_clause [] 


let rec print_clause fmt = function
  | [] -> ()
  | [t] -> print_term fmt t
  | t :: cl -> fprintf fmt "%a %a" print_term t print_clause cl

let print_clause fmt = fprintf fmt "(%a)" print_clause


let th_res p = match app_name (deref p).ttype with
  | Some ("th_holds", [r]) -> r
  | _ -> assert false


type clause_res_id = NewCl of int | OldCl of int


let register_clause_id cl id =
  HCl.add clauses_ids cl id;
  Hashtbl.add ids_clauses id cl


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
    fprintf fmt "%d:(%s %a%a)@." id (get_rule rule) print_clause cl
      (fun fmt -> List.iter (fprintf fmt " %d")) args;
    id
  | OldCl id -> id


let mk_clause_cl = mk_clause


let mk_input name formula =
  let cl = [formula] in
  match new_clause_id cl with
   | NewCl id ->
     register_clause_id cl id;
     HS.add inputs name id;
     fprintf fmt "%d:(input (%a))@." id print_term formula
   | OldCl _ -> ()



let register_prop_abstr vt formula = HT.add propvars vt formula


let get_clause_id cl = HCl.find clauses_ids cl


let get_input_id h = HS.find inputs h


let clear () =
  HCl.clear clauses_ids;
  Hashtbl.clear ids_clauses;
  HT.clear propvars;
  HT.clear sharp_tbl;
  Hashtbl.clear inputs;
  cl_cpt := 0;
  cpt := 0
  

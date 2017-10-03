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


(*** Linking SMT Terms to Micromega Terms ***)
open Term
open Coqlib
open Declare
open Decl_kinds
open Entries
open Util
(* open Micromega *)
(* open Coq_micromega *)

open SmtMisc
open SmtForm
open SmtAtom

(* morphism for expression over Z *)

let rec pos_of_int i =
  if i <= 1
  then Micromega_plugin.Micromega.XH
  else
    if i land 1 = 0
    then Micromega_plugin.Micromega.XO(pos_of_int (i lsr 1))
    else Micromega_plugin.Micromega.XI(pos_of_int (i lsr 1))

let z_of_int i =
  if i = 0
  then Micromega_plugin.Micromega.Z0
  else
    if i > 0
    then Micromega_plugin.Micromega.Zpos (pos_of_int i)
    else Micromega_plugin.Micromega.Zneg (pos_of_int (-i))

type my_tbl =
    {tbl:(hatom,int) Hashtbl.t; mutable count:int}

let get_atom_var tbl ha =
  try Hashtbl.find tbl.tbl ha
  with Not_found ->
    let v = tbl.count in
    Hashtbl.add tbl.tbl ha v;
    tbl.count <- v + 1;
    v

let create_tbl n = {tbl=Hashtbl.create n;count=1}

let rec smt_Atom_to_micromega_pos ha =
  match Atom.atom ha with
  | Auop(UO_xO, ha) ->
      Micromega_plugin.Micromega.XO (smt_Atom_to_micromega_pos ha)
  | Auop(UO_xI, ha) ->
      Micromega_plugin.Micromega.XI (smt_Atom_to_micromega_pos ha)
  | Acop CO_xH -> Micromega_plugin.Micromega.XH
  | _ -> raise Not_found

let smt_Atom_to_micromega_Z ha =
  match Atom.atom ha with
  | Auop(UO_Zpos, ha) ->
      Micromega_plugin.Micromega.Zpos (smt_Atom_to_micromega_pos ha)
  | Auop(UO_Zneg, ha) ->
      Micromega_plugin.Micromega.Zneg (smt_Atom_to_micromega_pos ha)
  | Acop CO_Z0 -> Micromega_plugin.Micromega.Z0
  | _ -> raise Not_found

let rec smt_Atom_to_micromega_pExpr tbl ha =
  match Atom.atom ha with
  | Abop (BO_Zplus, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      Micromega_plugin.Micromega.PEadd(a, b)
  | Abop (BO_Zmult, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      Micromega_plugin.Micromega.PEmul(a, b)
  | Abop (BO_Zminus, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      Micromega_plugin.Micromega.PEsub(a, b)
  | Auop (UO_Zopp, ha) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      Micromega_plugin.Micromega.PEopp a
  | _ ->
      try Micromega_plugin.Micromega.PEc (smt_Atom_to_micromega_Z ha)
      with Not_found ->
	let v = get_atom_var tbl ha in
	Micromega_plugin.Micromega.PEX (pos_of_int v)


(* morphism for LIA proposition (=, >, ...) *)

let smt_binop_to_micromega_formula tbl op ha hb =
  let op =
    match op with
    | BO_Zlt -> Micromega_plugin.Micromega.OpLt
    | BO_Zle -> Micromega_plugin.Micromega.OpLe
    | BO_Zge -> Micromega_plugin.Micromega.OpGe
    | BO_Zgt -> Micromega_plugin.Micromega.OpGt
    | BO_eq _ -> Micromega_plugin.Micromega.OpEq
    | _ -> Structures.error
	  "lia.ml: smt_binop_to_micromega_formula expecting a formula"
  in
  let lhs = smt_Atom_to_micromega_pExpr tbl ha in
  let rhs = smt_Atom_to_micromega_pExpr tbl hb in
  {Micromega_plugin.Micromega.flhs = lhs; Micromega_plugin.Micromega.fop = op; Micromega_plugin.Micromega.frhs = rhs }

let rec smt_Atom_to_micromega_formula tbl ha =
  match Atom.atom ha with
    | Abop (op,ha,hb) -> smt_binop_to_micromega_formula tbl op ha hb
    | _ -> Structures.error
	  "lia.ml: smt_Atom_to_micromega_formula was expecting an LIA formula"

(* specialized fold *)

let default_constr = mkInt 0
let default_tag = Micromega_plugin.Mutils.Tag.from 0
(* morphism for general formulas *)

let binop_array g tbl op def t =
  let n = Array.length t in
  if n = 0 then
    def
  else
    let aux = ref (g tbl t.(0)) in
    for i = 1 to (n-1) do
      aux := op !aux (g tbl t.(i))
    done;
    !aux

let rec smt_Form_to_coq_micromega_formula tbl l =
  let v =
    match Form.pform l with
      | Fatom ha ->
	Micromega_plugin.Coq_micromega.A (smt_Atom_to_micromega_formula tbl ha,
	   default_tag,default_constr)
      | Fapp (Ftrue, _) -> Micromega_plugin.Coq_micromega.TT
      | Fapp (Ffalse, _) -> Micromega_plugin.Coq_micromega.FF
      | Fapp (Fand, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> Micromega_plugin.Coq_micromega.C (x,y)) Micromega_plugin.Coq_micromega.TT l
      | Fapp (For, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> Micromega_plugin.Coq_micromega.D (x,y)) Micromega_plugin.Coq_micromega.FF l
      | Fapp (Fxor, l) -> failwith "todo:Fxor"
      | Fapp (Fimp, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> Micromega_plugin.Coq_micromega.I (x,None,y)) Micromega_plugin.Coq_micromega.TT l
      | Fapp (Fiff, l) -> failwith "todo:Fiff"
      | Fapp (Fite, l) -> failwith "todo:Fite"
      | Fapp (Fnot2 _, l) ->
        if Array.length l <> 1 then
          failwith "Lia.smt_Form_to_coq_micromega_formula: wrong number of arguments for Fnot2"
        else
          smt_Form_to_coq_micromega_formula tbl l.(0)
  in
  if Form.is_pos l then v
  else Micromega_plugin.Coq_micromega.N(v)

let binop_list tbl op def l =
  match l with
  | [] -> def
  | f::l -> List.fold_left (fun x y -> op x (smt_Form_to_coq_micromega_formula tbl y)) (smt_Form_to_coq_micromega_formula tbl f) l


(* let rec binop_list tbl op def l = *)
(*   match l with *)
(*   | [] -> def *)
(*   | [f] -> smt_Form_to_coq_micromega_formula tbl f *)
(*   | f::l -> *)
(*       op (smt_Form_to_coq_micromega_formula tbl f) (binop_list tbl op def l) *)

(* and smt_Form_to_coq_micromega_formula tbl l = *)
(*   let v = *)
(*     match Form.pform l with *)
(*       | Fatom ha -> *)
(* 	A (smt_Atom_to_micromega_formula tbl ha, *)
(* 	   default_tag,default_constr) *)
(*       | Fapp (Ftrue, _) -> TT *)
(*       | Fapp (Ffalse, _) -> FF *)
(*       | Fapp (Fand, l) -> binop_list tbl (fun x y -> C (x,y)) TT l *)
(*       | Fapp (For, l) -> binop_list tbl (fun x y -> D (x,y)) FF l *)
(*       | Fapp (Fxor, l) -> failwith "todo:Fxor" *)
(*       | Fapp (Fimp, l) -> binop_list tbl (fun x y -> I (x,None,y)) TT l *)
(*       | Fapp (Fiff, l) -> failwith "todo:Fiff" *)
(*       | Fapp (Fite, l) -> failwith "todo:Fite" *)
(*       | Fapp (Fnot2 _, l) -> smt_Form_to_coq_micromega_formula tbl l *)
(*   in *)
(*   if Form.is_pos l then v *)
(*   else N(v) *)


let smt_clause_to_coq_micromega_formula tbl cl =
  binop_list tbl (fun x y -> Micromega_plugin.Coq_micromega.C(x,y)) Micromega_plugin.Coq_micromega.TT (List.map Form.neg cl)

(* call to micromega solver *)
let build_lia_certif cl =
  let tbl = create_tbl 13 in
  let f = Micromega_plugin.Coq_micromega.I(smt_clause_to_coq_micromega_formula tbl cl, None, Micromega_plugin.Coq_micromega.FF) in
  tbl, f, Micromega_plugin.Coq_micromega.tauto_lia f


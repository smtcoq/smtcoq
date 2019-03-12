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


(*** Linking SMT Terms to Micromega Terms ***)
open Util
open Structures.Micromega_plugin_Micromega
open Structures.Micromega_plugin_Coq_micromega

open SmtMisc
open SmtForm
open SmtAtom

(* morphism for expression over Z *)

let rec pos_of_int i =
  if i <= 1
  then XH
  else
    if i land 1 = 0
    then XO(pos_of_int (i lsr 1))
    else XI(pos_of_int (i lsr 1))

let z_of_int i =
  if i = 0
  then Z0
  else
    if i > 0
    then Zpos (pos_of_int i)
    else Zneg (pos_of_int (-i))

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
      XO (smt_Atom_to_micromega_pos ha)
  | Auop(UO_xI, ha) ->
      XI (smt_Atom_to_micromega_pos ha)
  | Acop CO_xH -> XH
  | _ -> raise Not_found

let smt_Atom_to_micromega_Z ha =
  match Atom.atom ha with
  | Auop(UO_Zpos, ha) ->
      Zpos (smt_Atom_to_micromega_pos ha)
  | Auop(UO_Zneg, ha) ->
      Zneg (smt_Atom_to_micromega_pos ha)
  | Acop CO_Z0 -> Z0
  | _ -> raise Not_found

let rec smt_Atom_to_micromega_pExpr tbl ha =
  match Atom.atom ha with
  | Abop (BO_Zplus, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      PEadd(a, b)
  | Abop (BO_Zmult, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      PEmul(a, b)
  | Abop (BO_Zminus, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      PEsub(a, b)
  | Auop (UO_Zopp, ha) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      PEopp a
  | _ ->
      try PEc (smt_Atom_to_micromega_Z ha)
      with Not_found ->
	let v = get_atom_var tbl ha in
	PEX (pos_of_int v)


(* morphism for LIA proposition (=, >, ...) *)

let smt_binop_to_micromega_formula tbl op ha hb =
  let op =
    match op with
    | BO_Zlt -> OpLt
    | BO_Zle -> OpLe
    | BO_Zge -> OpGe
    | BO_Zgt -> OpGt
    | BO_eq _ -> OpEq
    | _ -> Structures.error
	  "lia.ml: smt_binop_to_micromega_formula expecting a formula"
  in
  let lhs = smt_Atom_to_micromega_pExpr tbl ha in
  let rhs = smt_Atom_to_micromega_pExpr tbl hb in
  {flhs = lhs; fop = op; frhs = rhs }

let smt_Atom_to_micromega_formula tbl ha =
  match Atom.atom ha with
    | Abop (op,ha,hb) -> smt_binop_to_micromega_formula tbl op ha hb
    | _ -> Structures.error
	  "lia.ml: smt_Atom_to_micromega_formula was expecting an LIA formula"

(* specialized fold *)

let default_constr = Structures.econstr_of_constr (mkInt 0)
let default_tag = Structures.Micromega_plugin_Mutils.Tag.from 0
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
	A (smt_Atom_to_micromega_formula tbl ha,
	   default_tag,default_constr)
      | Fapp (Ftrue, _) -> TT
      | Fapp (Ffalse, _) -> FF
      | Fapp (Fand, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> C (x,y)) TT l
      | Fapp (For, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> D (x,y)) FF l
      | Fapp (Fxor, l) -> failwith "todo:Fxor"
      | Fapp (Fimp, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> I (x,None,y)) TT l
      | Fapp (Fiff, l) -> failwith "todo:Fiff"
      | Fapp (Fite, l) -> failwith "todo:Fite"
      | Fapp (Fnot2 _, l) ->
        if Array.length l <> 1 then
          failwith "Lia.smt_Form_to_coq_micromega_formula: wrong number of arguments for Fnot2"
        else
          smt_Form_to_coq_micromega_formula tbl l.(0)
      | FbbT _ -> assert false
      | Fapp (Fforall _, _) -> assert false
  in
  if Form.is_pos l then v
  else N(v)

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
  binop_list tbl (fun x y -> C(x,y)) TT (List.map Form.neg cl)

(* backported from Coq-8.8.2 *)
let tauto_lia ff =
  let prover = linear_Z in
  let cnf_ff,_ = cnf Mc.negate Mc.normalise Mc.zunsat Mc.zdeduce  ff in
  match witness_list_tags [prover] cnf_ff with
    | None -> None
    | Some l -> Some (List.map fst l)

(* call to micromega solver *)
let build_lia_certif cl =
  let tbl = create_tbl 13 in
  let f = I(smt_clause_to_coq_micromega_formula tbl cl, None, FF) in
  tbl, f, tauto_lia f


(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand    *                                                *)
(*     Benjamin Grégoire *                                                *)
(*     Chantal Keller    *                                                *)
(*     Alain Mebsout     ♯                                                *)
(*     Burak Ekici       ♯                                                *)
(*                                                                        *)
(*     * Inria - École Polytechnique - Université Paris-Sud               *)
(*     ♯ The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(** Sharing of coq Int *)
let cInt_tbl = Hashtbl.create 17 

let mkInt i = 
  try Hashtbl.find cInt_tbl i 
  with Not_found ->
    let ci = Structures.mkInt i in
    Hashtbl.add cInt_tbl i ci;
    ci

(** Generic representation of shared object *)
type 'a gen_hashed = { index : int; hval : 'a }

(** Functions over constr *)

let mklApp f args = Term.mkApp (Lazy.force f, args)

(* TODO : Set -> Type *)
let declare_new_type = Structures.declare_new_type
let declare_new_variable = Structures.declare_new_variable

let mkName s =
  let id = Names.id_of_string s in
  Names.Name id


let string_coq_constr t =
  let rec fix rf x = rf (fix rf) x in
  let pr = fix
      Ppconstr.modular_constr_pr Pp.mt Structures.ppconstr_lsimpleconstr in
  Pp.string_of_ppcmds (pr (Structures.constrextern_extern_constr t))


let string_of_name = function
    Names.Name id -> Names.string_of_id id
  | _ -> failwith "unnamed rel"


(** Logics *)

type logic_item =
  | LUF
  | LLia
  | LBitvectors
  | LArrays

module SL = Set.Make (struct
    type t = logic_item
    let compare = Pervasives.compare
  end)

type logic = SL.t


(* Reification *)

open CoqTerms

let mk_bool b =
  let c, args = Term.decompose_app b in
  if Term.eq_constr c (Lazy.force ctrue) then true
  else if Term.eq_constr c (Lazy.force cfalse) then false
  else assert false

let rec mk_bool_list bs =
  let c, args = Term.decompose_app bs in
  if Term.eq_constr c (Lazy.force cnil) then []
  else if Term.eq_constr c (Lazy.force ccons) then
    match args with
    | [_; b; bs] -> mk_bool b :: mk_bool_list bs
    | _ -> assert false
  else assert false

let rec mk_nat n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cO) then
    0
  else if Term.eq_constr c (Lazy.force cS) then
    match args with
    | [n] -> (mk_nat n) + 1
    | _ -> assert false
  else assert false

let rec mk_positive n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cxH) then
    1
  else if Term.eq_constr c (Lazy.force cxO) then
    match args with
    | [n] -> 2 * (mk_positive n)
    | _ -> assert false
  else if Term.eq_constr c (Lazy.force cxI) then
    match args with
    | [n] -> 2 * (mk_positive n) + 1
    | _ -> assert false
  else assert false


let mk_N n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cN0) then
    0
  else if Term.eq_constr c (Lazy.force cNpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else assert false


let mk_Z n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cZ0) then 0
  else if Term.eq_constr c (Lazy.force cZpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else if Term.eq_constr c (Lazy.force cZneg) then
    match args with
    | [n] -> - mk_positive n
    | _ -> assert false
  else assert false


(* size of bivectors are either N.of_nat (length l) or an N *)
let mk_bvsize n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cof_nat) then
    match args with
    | [nl] ->
      let c, args = Term.decompose_app nl in
      if Term.eq_constr c (Lazy.force clength) then
        match args with
        | [_; l] -> List.length (mk_bool_list l)
        | _ -> assert false
      else assert false
    | _ -> assert false
  else mk_N n

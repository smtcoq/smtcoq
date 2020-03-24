(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2020                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtAtom


(* The state shared by all pre-processors, containing:
   - type_tbl : uninterpreted sorts
   - op_tbl : uninterpreted function symbols
   - atom_tbl_to_add : hash-consed atoms to be added in the deep embedding
   - form_tbl_to_add : hash-consed formulas to be added in the deep embedding
   - atom_tbl_no_add : hash-consed atoms no to be added in the deep embedding (for quantifiers)
   - form_tbl_no_add : hash-consed formulas no to be added in the deep embedding (for quantifiers)
 *)

type type_tbl = SmtBtype.reify_tbl
type op_tbl = SmtAtom.Op.reify_tbl
type atom_tbl_to_add = SmtAtom.Atom.reify_tbl
type form_tbl_to_add = SmtAtom.Form.reify
type atom_tbl_no_add = SmtAtom.Atom.reify_tbl
type form_tbl_no_add = SmtAtom.Form.reify

type smt_state =
  type_tbl
  * op_tbl
  * atom_tbl_to_add
  * form_tbl_to_add
  * atom_tbl_no_add
  * form_tbl_no_add

let get_type_tbl st =
  let (rt, _, _, _, _, _) = st in
  rt
let get_op_tbl st =
  let (_, ro, _, _, _, _) = st in
  ro
let get_atom_tbl_to_add st =
  let (_, _, ra, _, _, _) = st in
  ra
let get_form_tbl_to_add st =
  let (_, _, _, rf, _, _) = st in
  rf
let get_atom_tbl_no_add st =
  let (_, _, _, _, ra', _) = st in
  ra'
let get_form_tbl_no_add st =
  let (_, _, _, _, _, rf') = st in
  rf'

let create_smt_state () : smt_state =
  (SmtBtype.create (),
   SmtAtom.Op.create (),
   Atom.create (),
   Form.create (),
   Atom.create (),
   Form.create ()
  )


(* The state shared by SMT-LIB parsers and printers, containing:
   - the names of uninterpreted sorts
   - the names of uninterpreted function symbols
 *)

type type_names = (string, SmtBtype.btype) Hashtbl.t
type op_names = (string, SmtAtom.indexed_op) Hashtbl.t
type smtlib_state = type_names * op_names

let create_smtlib_state () : smtlib_state =
  (Hashtbl.create 17, Hashtbl.create 17)

(* Names of uninterpreted sorts *)
let get_btype (st:smtlib_state) id =
  let (btypes, _) = st in
  try Hashtbl.find btypes id
  with | Not_found -> failwith ("State.get_btype : sort symbol \""^id^"\" not found\n")

let add_btype (st:smtlib_state) id cl =
  let (btypes, _) = st in
  Hashtbl.add btypes id cl

(* Names of uninterpreted function symbols *)
let get_fun (st:smtlib_state) id =
  let (_, funs) = st in
  try Hashtbl.find funs id
  with | Not_found -> failwith ("State.get_fun : function symbol \""^id^"\" not found\n")

let add_fun (st:smtlib_state) id cl =
  let (_, funs) = st in
  Hashtbl.add funs id cl

let remove_fun (st:smtlib_state) id =
  let (_, funs) = st in
  Hashtbl.remove funs id

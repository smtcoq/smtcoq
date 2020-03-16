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

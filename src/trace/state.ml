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


type atom_tbl_to_add = SmtAtom.Atom.reify_tbl
type form_tbl_to_add = SmtAtom.Form.reify
type atom_tbl_no_add = SmtAtom.Atom.reify_tbl
type form_tbl_no_add = SmtAtom.Form.reify

type smt_state =
  atom_tbl_to_add
  * form_tbl_to_add
  * atom_tbl_no_add
  * form_tbl_no_add

let get_atom_tbl_to_add st =
  let (ra, _, _, _) = st in
  ra
let get_form_tbl_to_add st =
  let ( _, rf, _, _) = st in
  rf
let get_atom_tbl_no_add st =
  let (_, _, ra', _) = st in
  ra'
let get_form_tbl_no_add st =
  let (_, _, _, rf') = st in
  rf'

let create_smt_state () : smt_state =
  (Atom.create (),
   Form.create (),
   Atom.create (),
   Form.create ()
  )

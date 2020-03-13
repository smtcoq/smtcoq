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


(* The state shared by all pre-processors:
   - atom_tbl_to_add : hash-consed atoms to be added in the deep embedding
   - form_tbl_to_add : hash-consed formulas to be added in the deep embedding
   - atom_tbl_no_add : hash-consed atoms no to be added in the deep embedding (for quantifiers)
   - form_tbl_no_add : hash-consed formulas no to be added in the deep embedding (for quantifiers)
 *)

type atom_tbl_to_add = SmtAtom.Atom.reify_tbl
type form_tbl_to_add = SmtAtom.Form.reify
type atom_tbl_no_add = SmtAtom.Atom.reify_tbl
type form_tbl_no_add = SmtAtom.Form.reify

type smt_state
val create_smt_state : unit -> smt_state

val get_atom_tbl_to_add : smt_state -> atom_tbl_to_add
val get_form_tbl_to_add : smt_state -> form_tbl_to_add
val get_atom_tbl_no_add : smt_state -> atom_tbl_no_add
val get_form_tbl_no_add : smt_state -> form_tbl_no_add

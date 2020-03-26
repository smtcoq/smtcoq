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


(* The state shared by pre-processors, SMT-LIB parsers and printers, containing:
   - type_tbl : reified uninterpreted sorts
   - type_names : names of uninterpreted sorts

   - op_tbl : reified uninterpreted function symbols
   - op_names : names of uninterpreted function symbols

   - atom_tbl_to_add : reified, hash-consed atoms to be added in the deep embedding
   - form_tbl_to_add : reified, hash-consed formulas to be added in the deep embedding
   - atom_tbl_no_add : reified, hash-consed atoms no to be added in the deep embedding (for quantifiers)
   - form_tbl_no_add : reified, hash-consed formulas no to be added in the deep embedding (for quantifiers)

   - trace_state : state of the optimizer
 *)

type type_tbl = SmtBtype.reify_tbl
type op_tbl = SmtAtom.Op.reify_tbl
type atom_tbl_to_add = SmtAtom.Atom.reify_tbl
type form_tbl_to_add = SmtAtom.Form.reify
type atom_tbl_no_add = SmtAtom.Atom.reify_tbl
type form_tbl_no_add = SmtAtom.Form.reify

type smt_state
val create_smt_state : unit -> smt_state

val get_type_tbl : smt_state -> type_tbl
val get_op_tbl : smt_state -> op_tbl
val get_atom_tbl_to_add : smt_state -> atom_tbl_to_add
val get_form_tbl_to_add : smt_state -> form_tbl_to_add
val get_atom_tbl_no_add : smt_state -> atom_tbl_no_add
val get_form_tbl_no_add : smt_state -> form_tbl_no_add
val get_trace_state : smt_state -> SmtTrace.trace_state

(* Names of uninterpreted sorts *)
val get_btype : smt_state -> string -> SmtBtype.btype
val add_btype : smt_state -> string -> SmtBtype.btype -> unit

(* Names of uninterpreted function symbols *)
val get_fun : smt_state -> string -> SmtAtom.indexed_op
val add_fun : smt_state -> string -> SmtAtom.indexed_op -> unit
val remove_fun : smt_state -> string -> unit

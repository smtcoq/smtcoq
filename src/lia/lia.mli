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


val pos_of_int : int -> Structures.Micromega_plugin_Micromega.positive
val z_of_int : int -> Structures.Micromega_plugin_Micromega.z
type my_tbl
val get_atom_var : my_tbl -> SmtAtom.hatom -> int
val create_tbl : int -> my_tbl
val smt_Atom_to_micromega_pos :
  SmtAtom.hatom -> Structures.Micromega_plugin_Micromega.positive
val smt_Atom_to_micromega_Z :
  SmtAtom.hatom -> Structures.Micromega_plugin_Micromega.z
val smt_Atom_to_micromega_pExpr :
  my_tbl ->
  SmtAtom.hatom ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Micromega.pExpr
val smt_binop_to_micromega_formula :
  my_tbl ->
  SmtAtom.bop ->
  SmtAtom.hatom ->
  SmtAtom.hatom ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Micromega.formula
val smt_Atom_to_micromega_formula :
  my_tbl ->
  SmtAtom.hatom ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Micromega.formula
val binop_array :
  ('a -> 'b -> 'c) -> 'a -> ('c -> 'c -> 'c) -> 'c -> 'b array -> 'c
val smt_Form_to_coq_micromega_formula :
  my_tbl ->
  SmtAtom.Form.t ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Coq_micromega.formula
val binop_list :
  my_tbl ->
  (Structures.Micromega_plugin_Micromega.z
   Structures.Micromega_plugin_Coq_micromega.formula ->
   Structures.Micromega_plugin_Micromega.z
   Structures.Micromega_plugin_Coq_micromega.formula ->
   Structures.Micromega_plugin_Micromega.z
   Structures.Micromega_plugin_Coq_micromega.formula) ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Coq_micromega.formula ->
  SmtAtom.Form.t list ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Coq_micromega.formula
val smt_clause_to_coq_micromega_formula :
  my_tbl ->
  SmtAtom.Form.t list ->
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Coq_micromega.formula
val build_lia_certif :
  SmtAtom.Form.t list ->
  my_tbl *
  Structures.Micromega_plugin_Micromega.z
  Structures.Micromega_plugin_Coq_micromega.formula *
  Structures.Micromega_plugin_Certificate.Mc.zArithProof list option

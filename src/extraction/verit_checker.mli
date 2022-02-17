(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


module Mc = CoqInterface.Micromega_plugin_Certificate.Mc
val mkInt : int -> ExtrNative.uint
val mkArray : 'a array -> 'a ExtrNative.parray
val dump_nat : Mc.nat -> Smt_checker.nat
val dump_positive : Mc.positive -> Smt_checker.positive
val dump_z : Mc.z -> Smt_checker.z
val dump_pol : Mc.z Mc.pol -> Smt_checker.z Smt_checker.pol
val dump_psatz : Mc.z Mc.psatz -> Smt_checker.z Smt_checker.psatz
val dump_list : ('a -> 'b) -> 'a list -> 'b Smt_checker.list
val dump_proof_term : Micromega.zArithProof -> Smt_checker.zArithProof
val to_coq :
  ('a -> Smt_checker.int) ->
  'a SmtCertif.clause ->
  Smt_checker.Euf_Checker.step ExtrNative.parray ExtrNative.parray *
  'a SmtCertif.clause
val btype_to_coq : SmtBtype.btype -> Smt_checker.Typ.coq_type
val c_to_coq : SmtAtom.cop -> Smt_checker.Atom.cop
val u_to_coq : SmtAtom.uop -> Smt_checker.Atom.unop
val b_to_coq : SmtAtom.bop -> Smt_checker.Atom.binop
val n_to_coq : SmtAtom.nop -> Smt_checker.Typ.coq_type
val i_to_coq : SmtAtom.indexed_op -> ExtrNative.uint
val a_to_coq : SmtAtom.atom -> Smt_checker.Atom.atom
val atom_interp_tbl :
  SmtAtom.Atom.reify_tbl -> Smt_checker.Atom.atom ExtrNative.parray
val form_to_coq : SmtAtom.Form.t -> ExtrNative.uint
val args_to_coq : SmtAtom.Form.t array -> ExtrNative.uint ExtrNative.parray
val pf_to_coq :
  (SmtAtom.hatom, SmtAtom.Form.t) SmtForm.gen_pform -> Smt_checker.Form.form
val form_interp_tbl :
  SmtAtom.Form.reify -> Smt_checker.Form.form ExtrNative.parray
val count_btype : int ref
val count_op : int ref
val declare_sort : Smtlib2_ast.symbol -> SmtBtype.btype
val declare_fun :
  Smtlib2_ast.symbol ->
  Smtlib2_ast.sort list -> Smtlib2_ast.sort -> SmtAtom.indexed_op
val declare_commands :
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  SmtAtom.Form.t list -> Smtlib2_ast.command -> SmtAtom.Form.t list
val import_smtlib2 :
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify -> string -> SmtAtom.Form.t list
val this_clear_all : unit -> unit
val checker : string -> string -> bool

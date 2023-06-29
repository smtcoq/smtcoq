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


val parse_certif :
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id -> CoqInterface.id -> string -> string -> unit
val checker_debug : string -> string -> 'a
val theorem : CoqInterface.id -> string -> string -> unit
val checker : string -> string -> unit
val call_cvc4_file :
  Environ.env ->
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  'a ->
  'b ->
  SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
  int * SmtAtom.Form.t SmtCertif.clause
val tactic : unit -> CoqInterface.tactic
val tactic_no_check : unit -> CoqInterface.tactic

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
  CoqInterface.id -> CoqInterface.id -> CoqInterface.id -> string -> string -> unit
val checker : string -> string -> unit
val checker_debug : string -> string -> unit
val theorem : CoqInterface.id -> string -> string -> unit
val tactic : int option -> EConstr.t -> CoqInterface.constr_expr list -> CoqInterface.tactic
val tactic_no_check : int option -> EConstr.t -> CoqInterface.constr_expr list -> CoqInterface.tactic

(* For extraction *)
val clear_all : unit -> unit
val import_trace :
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  string ->
  bool ->
  SmtAtom.Form.t list -> int * SmtAtom.Form.t SmtCertif.clause

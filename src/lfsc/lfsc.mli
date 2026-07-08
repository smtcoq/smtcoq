(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Common

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
  int ->
  Environ.env ->
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  'a ->
  'b ->
  SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
  int * SmtAtom.Form.t SmtCertif.clause
val tactic : unit -> CoqInterface.tactic
val tactic_no_check : unit -> CoqInterface.tactic
val tactic_abduct : int -> EConstr.t -> CoqInterface.constr_expr list -> CoqInterface.tactic

module Ast : module type of Ast
module Converter : module type of Converter
module Lexer : module type of Lexer
module Parser : module type of Parser
module VeritPrinter : module type of VeritPrinter

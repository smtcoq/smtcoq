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


val parse_certif :
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  LocalState.smt_state * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> unit


val checker_debug :
  LocalState.smt_state * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> 'a

val theorem :
  Structures.id ->
  LocalState.smt_state * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> unit

val checker :
  LocalState.smt_state * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> unit

val tactic :
  (Environ.env ->
   SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
   SmtAtom.Form.t list -> int * SmtAtom.Form.t SmtCertif.clause) ->
  SmtMisc.logic ->
  LocalState.smt_state ->
  (Environ.env -> Structures.constr -> Structures.constr) ->
  Structures.constr list ->
  Structures.constr_expr list -> Structures.tactic

val model_string : Environ.env -> SExpr.t -> string

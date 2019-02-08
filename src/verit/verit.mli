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
  Structures.names_id ->
  Structures.names_id ->
  Structures.names_id ->
  Structures.names_id ->
  Structures.names_id -> Structures.names_id -> Structures.names_id -> string -> string -> unit
val checker : string -> string -> unit
val checker_debug : string -> string -> unit
val theorem : Structures.names_id -> string -> string -> unit
val tactic : Term.constr list -> Structures.constr_expr list -> Structures.tactic
val tactic_no_check : Term.constr list -> Structures.constr_expr list -> Structures.tactic

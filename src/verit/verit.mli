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
  Structures.id -> Structures.id -> Structures.id -> string -> string -> unit
val checker : string -> string -> unit
val checker_debug : string -> string -> unit
val theorem : Structures.id -> string -> string -> unit
val tactic : EConstr.t -> Structures.constr_expr list -> Structures.tactic
val tactic_no_check : EConstr.t -> Structures.constr_expr list -> Structures.tactic

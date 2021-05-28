(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


val pp_trace : Format.formatter -> SatAtom.Form.t SmtCertif.clause -> unit
val parse_certif : CoqInterface.id -> CoqInterface.id -> string -> string -> unit
val checker : string -> string -> unit
val theorem : CoqInterface.id -> string -> string -> unit
val theorem_abs : CoqInterface.id -> string -> string -> unit
val tactic : unit -> CoqInterface.tactic
val tactic_no_check : unit -> CoqInterface.tactic

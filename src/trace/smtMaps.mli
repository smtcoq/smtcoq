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


(** Maps that store SMT objects **)

(* SMT types *)
val get_btype : string -> SmtBtype.btype
val add_btype : string -> SmtBtype.btype -> unit

(* SMT function symbols *)
val get_fun : string -> SmtAtom.indexed_op
val add_fun : string -> SmtAtom.indexed_op -> unit
val remove_fun : string -> unit

(* Clean-up of all the maps *)
val clear : unit -> unit

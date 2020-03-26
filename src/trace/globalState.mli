(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2020                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* The global state contains the theorems that will be sent to the
   provers, added using the [Add_lemma] vernacular command *)

val add_lemmas : Structures.constr_expr list -> unit
val clear_lemmas : unit -> unit
val get_lemmas : unit -> Structures.constr_expr list

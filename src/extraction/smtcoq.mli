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


type solver = Zchaff | Verit
val usage : string
val string_of_solver : solver -> string
val verifier_of_solver : solver -> string -> string -> bool
val run : solver -> string -> string -> unit

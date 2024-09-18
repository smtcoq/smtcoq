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


val mkInt : int -> Uint63.t
val mkArray : (Uint63.t -> 'a -> 'b) -> ('b -> Uint63.t -> 'a -> 'b) -> 'a array -> 'b
val mkTrace : 'a -> ('b * 'a -> 'a) -> ('c -> 'b) -> ('c -> 'c) -> int -> 'd -> 'c ref -> 'a * 'd

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


type comparison = Eq | Lt | Gt
type 'a carry = C0 of 'a | C1 of 'a

(*s Unsigned Int *)
type uint 

(* Conversion with int *)
val to_int : uint -> int
val of_int : int -> uint
val of_uint : int -> uint

(* Conversion with string *)
val to_string : uint -> string
val of_string : string -> uint

(* logical operations *)
val l_sl : uint -> uint -> uint
val l_sr : uint -> uint -> uint
val l_and : uint -> uint -> uint
val l_or : uint -> uint -> uint
val l_xor : uint -> uint -> uint

(* arithmetic operations *)
val add : uint -> uint -> uint
val sub : uint -> uint -> uint
val mul : uint -> uint -> uint
val mulc : uint -> uint -> uint * uint
val div : uint -> uint -> uint
val rem : uint -> uint -> uint

val lt : uint -> uint -> bool
val le : uint -> uint -> bool
val eq : uint -> uint -> bool
val compare : uint -> uint -> comparison

val head0 : uint -> uint
val tail0 : uint -> uint

val addc : uint -> uint -> uint carry
val addcarryc : uint -> uint -> uint carry
val subc : uint -> uint -> uint carry
val subcarryc : uint -> uint -> uint carry
val diveucl : uint -> uint -> uint * uint
val diveucl_21 : uint -> uint -> uint -> uint * uint
val addmuldiv : uint -> uint -> uint -> uint

val foldi_cont :
  (uint -> ('a -> 'b) -> 'a -> 'b) -> uint -> uint -> ('a -> 'b) -> 'a -> 'b
val foldi_down_cont :
  (uint -> ('a -> 'b) -> 'a -> 'b) -> uint -> uint -> ('a -> 'b) -> 'a -> 'b
val print_uint : uint -> uint


(*s Persistant array *)

type 'a parray 

val of_array : 'a array -> 'a parray

val parray_make : uint -> 'a -> 'a parray
val parray_get : 'a parray -> uint -> 'a
val parray_default : 'a parray -> 'a
val parray_length : 'a parray -> uint
val parray_set : 'a parray -> uint -> 'a -> 'a parray
val parray_copy : 'a parray -> 'a parray
val parray_reroot : 'a parray -> 'a parray


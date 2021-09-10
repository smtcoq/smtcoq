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


(** Hash-consed strings

    Hash-consing is a technique to share values that are structurally
    equal. More details on 
    {{:http://en.wikipedia.org/wiki/Hash_consing} Wikipedia} and
    {{:http://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf} here}.

    This module provides an easy way to use hash-consing for strings.
*)

open Shashcons 

type t = string hash_consed
(** The type of Hash-consed string *)

val make : string -> t
(** [make s] builds ans returns a hash-consed string from [s].*)

val view : t -> string
(** [view hs] returns the string corresponding to [hs].*)

val equal : t -> t -> bool
(** [equal x y] returns [true] if [x] and [y] are the same hash-consed string
    (constant time).*)

val compare : t -> t -> int
(** [compares x y] returns [0] if [x] and [y] are equal, and is unspecified
    otherwise but provides a total ordering on hash-consed strings.*)

val hash : t -> int
(** [hash x] returns the integer (hash) associated to [x].*)

val empty : t
(** the empty ([""]) hash-consed string.*)

val list_assoc : t -> (t * 'a) list -> 'a
(** [list_assoc x l] returns the element associated with [x] in the list of
    pairs [l].
    @raise Not_found if there is no value associated with [x] in the list [l].*)

val list_assoc_inv : t -> ('a * t) list -> 'a
(** [list_assoc_inv x l] returns the first element which is associated to [x]
    in the list of pairs [l].
    @raise Not_found if there is no value associated to [x] in the list [l].*)

val list_mem_assoc : t -> (t * 'a) list -> bool
(** Same as {! list_assoc}, but simply returns [true] if a binding exists, and
    [false] if no bindings exist for the given key.*)

val list_mem : t -> t list -> bool
(** [list_mem x l] is [true] if and only if [x] is equal to an element of [l].*)

val list_mem_couple : t * t -> (t * t) list -> bool
(** [list_mem_couple (x,y) l] is [true] if and only if [(x,y)] is equal to an
    element of [l].*)

val compare_list : t list -> t list -> int
(** [compare_list l1 l2] returns [0] if and only if [l1] is equal to [l2].*)

val list_equal : t list -> t list -> bool
(** [list_equal l1 l2] returns [true] if and only if [l1] is equal to [l2].*)

val print : Format.formatter -> t -> unit
(** Prints a hash-consed strings on a formatter. *)

val print_list : string -> Format.formatter -> t list -> unit
(** Prints a list of hash-consed strings on a formatter. *)

module H : Hashtbl.S with type key = t
(** Hash-tables indexed by hash-consed strings *)

module HSet : Set.S with type elt = t
(** Sets of hash-consed strings *)

module HMap : Map.S with type key = t
(** Maps indexed by hash-consed strings *)

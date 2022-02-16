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


(** Hash tables for hash consing *)

(*s Hash tables for hash consing.

    Hash consed values are of the
    following type [hash_consed]. The field [tag] contains a unique
    integer (for values hash consed with the same table). The field
    [hkey] contains the hash key of the value (without modulo) for
    possible use in other hash tables (and internally when hash
    consing tables are resized). The field [node] contains the value
    itself.

    Hash consing tables are using weak pointers, so that values that are no
    more referenced from anywhere else can be erased by the GC. *)

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val tag : int -> t -> t
  end

module type S =
  sig
    type t

    val hashcons : t -> t
      (** [hashcons n f] hash-cons the value [n] using function [f] i.e. returns
	  any existing value in the table equal to [n], if any;
	  otherwise, creates a new value with function [f], stores it
	  in the table and returns it. Function [f] is passed
	  the node [n] as first argument and the unique id as second argument.
      *)

    val iter : (t -> unit) -> unit
      (** [iter f] iterates [f] over all elements of the table . *)
    val stats : unit -> int * int * int * int * int * int
      (** Return statistics on the table.  The numbers are, in order:
	  table length, number of entries, sum of bucket lengths,
	  smallest bucket length, median bucket length, biggest
	  bucket length. *)
  end

module Make(H : HashedType) : (S with type t = H.t)


(* For simple use *)
type 'a hash_consed = private {
  tag : int;
  node : 'a }

module type HashedType_consed =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type S_consed =
  sig
    type key

    val hashcons : key -> key hash_consed
      (** [hashcons n f] hash-cons the value [n] using function [f] i.e. returns
	  any existing value in the table equal to [n], if any;
	  otherwise, creates a new value with function [f], stores it
	  in the table and returns it. Function [f] is passed
	  the node [n] as first argument and the unique id as second argument.
      *)

    val iter : (key hash_consed -> unit) -> unit
      (** [iter f] iterates [f] over all elements of the table . *)
    val stats : unit -> int * int * int * int * int * int
      (** Return statistics on the table.  The numbers are, in order:
	  table length, number of entries, sum of bucket lengths,
	  smallest bucket length, median bucket length, biggest
	  bucket length. *)
  end

module Make_consed(H : HashedType_consed) : (S_consed with type key = H.t)

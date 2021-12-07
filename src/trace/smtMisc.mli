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


val cInt_tbl : (int, CoqInterface.constr) Hashtbl.t
val mkInt : int -> CoqInterface.constr
type 'a gen_hashed = { index : int; mutable hval : 'a; }
val mklApp : CoqInterface.constr Lazy.t -> CoqInterface.constr array -> CoqInterface.constr
val string_of_name_def : string -> CoqInterface.name -> string
val string_coq_constr : CoqInterface.constr -> string
type logic_item = LUF | LLia | LBitvectors | LArrays
module SL : Set.S with type elt = logic_item
type logic = SL.t

(** Utils *)
val filter_map : ('a -> 'b option) -> 'a list -> 'b list

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


val cInt_tbl : (int, Structures.constr) Hashtbl.t
val mkInt : int -> Structures.constr
type 'a gen_hashed = { index : int; hval : 'a; }
val mklApp : Structures.constr Lazy.t -> Structures.constr array -> Structures.constr
val string_of_name_def : string -> Structures.name -> string
val string_coq_constr : Structures.constr -> string
type logic_item = LUF | LLia | LBitvectors | LArrays
module SL : Set.S with type elt = logic_item
type logic = SL.t

(** Utils *)
val filter_map : ('a -> 'b option) -> 'a list -> 'b list

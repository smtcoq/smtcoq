(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type indexed_type

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | Tindex of indexed_type
  | TFArray of btype * btype

val equal : btype -> btype -> bool

val to_coq : btype -> Term.constr

val to_smt : Format.formatter -> btype -> unit

type reify_tbl

val create : unit -> reify_tbl

val declare : reify_tbl -> Term.constr -> Term.constr -> btype

val of_coq : reify_tbl -> logic -> Term.constr -> btype

val get_coq_type_op : int -> Term.constr

val interp_tbl : reify_tbl -> Term.constr

val to_list : reify_tbl ->  (int * indexed_type) list

val interp_to_coq : reify_tbl -> btype -> Term.constr

val get_cuts : reify_tbl -> (Structures.names_id_t * Term.types) list

val logic : btype -> logic

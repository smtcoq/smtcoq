(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtMisc


type indexed_type

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int
val indexed_type_compdec : indexed_type -> RocqInterface.constr

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | TFArray of btype * btype
  | Tindex of indexed_type

val indexed_type_of_int : int -> indexed_type

module HashedBtype : Hashtbl.HashedType with type t = btype

val to_coq : btype -> RocqInterface.constr

val to_smt : Format.formatter -> btype -> unit

type reify_tbl

val create : unit -> reify_tbl
val copy : reify_tbl -> reify_tbl

val of_coq : reify_tbl -> logic -> RocqInterface.constr -> btype
val of_coq_compdec : reify_tbl -> RocqInterface.constr -> RocqInterface.constr -> btype

val get_coq_type_op : int -> RocqInterface.constr

val interp_tbl : reify_tbl -> RocqInterface.constr

val to_list : reify_tbl ->  (int * indexed_type) list

val make_t_i : reify_tbl -> RocqInterface.constr

val dec_interp : RocqInterface.constr -> btype -> RocqInterface.constr
val ord_interp : RocqInterface.constr -> btype -> RocqInterface.constr
val comp_interp : RocqInterface.constr -> btype -> RocqInterface.constr
val inh_interp : RocqInterface.constr -> btype -> RocqInterface.constr
val interp : RocqInterface.constr -> btype -> RocqInterface.constr

val interp_to_coq : reify_tbl -> btype -> RocqInterface.constr

val get_cuts : reify_tbl -> (RocqInterface.id * RocqInterface.types) list

val logic : btype -> logic

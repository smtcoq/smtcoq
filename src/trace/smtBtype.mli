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


open SmtMisc


type indexed_type

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int
val indexed_type_compdec : indexed_type -> Structures.constr

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | TFArray of btype * btype
  | Tindex of indexed_type

val indexed_type_of_int : int -> indexed_type

module HashedBtype : Hashtbl.HashedType with type t = btype

val to_coq : btype -> Structures.constr

val to_smt : Format.formatter -> btype -> unit

type reify_tbl

val create : unit -> reify_tbl
val copy : reify_tbl -> reify_tbl

val of_coq : reify_tbl -> logic -> Structures.constr -> btype
val of_coq_compdec : reify_tbl -> Structures.constr -> Structures.constr -> btype

val get_coq_type_op : int -> Structures.constr

val interp_tbl : reify_tbl -> Structures.constr

val to_list : reify_tbl ->  (int * indexed_type) list

val make_t_i : reify_tbl -> Structures.constr

val dec_interp : Structures.constr -> btype -> Structures.constr
val ord_interp : Structures.constr -> btype -> Structures.constr
val comp_interp : Structures.constr -> btype -> Structures.constr
val inh_interp : Structures.constr -> btype -> Structures.constr
val interp : Structures.constr -> btype -> Structures.constr

val interp_to_coq : reify_tbl -> btype -> Structures.constr

val get_cuts : reify_tbl -> (Structures.id * Structures.types) list

val logic : btype -> logic

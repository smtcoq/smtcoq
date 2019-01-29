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


type indexed_type = Term.constr gen_hashed

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int
val indexed_type_hval : indexed_type -> Term.constr

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | TFArray of btype * btype
  | Tindex of indexed_type

val indexed_type_of_int : int -> Term.constr SmtMisc.gen_hashed

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

val make_t_i : reify_tbl -> Term.constr

val dec_interp : Term.constr -> btype -> Term.constr
val ord_interp : Term.constr -> btype -> Term.constr
val comp_interp : Term.constr -> btype -> Term.constr
val inh_interp : Term.constr -> btype -> Term.constr
val interp : Term.constr -> btype -> Term.constr

val interp_to_coq : reify_tbl -> btype -> Term.constr

val get_cuts : reify_tbl -> (Structures.names_id * Term.types) list

val logic : btype -> logic

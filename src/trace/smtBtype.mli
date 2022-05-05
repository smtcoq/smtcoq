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


open SmtMisc


type indexed_type

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int
val indexed_type_compdec : indexed_type -> CoqInterface.constr

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | TFArray of btype * btype
  | Tindex of indexed_type

val indexed_type_of_int : int -> indexed_type

module HashedBtype : Hashtbl.HashedType with type t = btype

val to_coq : btype -> CoqTerms.coqTerm

val to_smt : Format.formatter -> btype -> unit

type reify_tbl

val create : unit -> reify_tbl
val copy : reify_tbl -> reify_tbl

val of_coq : reify_tbl -> logic -> CoqInterface.constr -> btype
val of_coq_compdec : reify_tbl -> CoqInterface.constr -> CoqInterface.constr -> btype

val get_coq_type_op : int -> CoqInterface.constr

val interp_tbl : reify_tbl -> CoqTerms.coqTerm

val to_list : reify_tbl ->  (int * indexed_type) list

val make_t_i : reify_tbl -> CoqTerms.coqTerm

val dec_interp : CoqInterface.constr -> btype -> CoqTerms.coqTerm
val ord_interp : CoqInterface.constr -> btype -> CoqTerms.coqTerm
val comp_interp : CoqInterface.constr -> btype -> CoqTerms.coqTerm
val inh_interp : CoqInterface.constr -> btype -> CoqTerms.coqTerm
val interp : CoqInterface.constr -> btype -> CoqTerms.coqTerm

val interp_to_coq : reify_tbl -> btype -> CoqTerms.coqTerm

val get_cuts : reify_tbl -> (CoqInterface.id * CoqInterface.types) list

val logic : btype -> logic

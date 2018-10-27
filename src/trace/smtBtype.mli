type indexed_type
val dummy_indexed_type : int -> indexed_type
val indexed_type_index : indexed_type -> int
val indexed_type_hval : indexed_type -> Term.constr
type btype = TZ | Tbool | Tpositive | Tindex of indexed_type
val indexed_type_of_int : int -> indexed_type
val equal : btype -> btype -> bool
val to_coq : btype -> Term.constr
val to_string : btype -> string
val to_smt : Format.formatter -> btype -> unit
type reify_tbl
val create : unit -> reify_tbl
val get_cuts : reify_tbl -> (Structures.names_id_t * Term.types) list
val declare : reify_tbl -> Term.constr -> Term.constr -> btype
val of_coq : reify_tbl -> Term.types -> btype
val interp_tbl : reify_tbl -> Term.constr
val to_list : reify_tbl -> (int * indexed_type) list
val interp_to_coq : 'a -> btype -> Term.constr

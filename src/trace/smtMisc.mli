val cInt_tbl : (int, Term.constr) Hashtbl.t
val mkInt : int -> Term.constr
type 'a gen_hashed = { index : int; hval : 'a; }
val mklApp : Term.constr Lazy.t -> Term.constr array -> Term.constr
val declare_new_type : Names.variable -> Term.constr
val declare_new_variable : Names.variable -> Term.types -> Term.constr
val mkName : string -> Names.name
val string_of_name : Names.name -> string
type logic_item = LUF | LLia | LBitvectors | LArrays
module SL : Set.S with type elt = logic_item
type logic = SL.t

(* Reification *)
val mk_bool_list : Term.constr -> bool list
val mk_nat : Term.constr -> int
val mk_N : Term.constr -> int
val mk_bvsize : Term.constr -> int

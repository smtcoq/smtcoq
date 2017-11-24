val cInt_tbl : (int, Term.constr) Hashtbl.t
val mkInt : int -> Term.constr
type 'a gen_hashed = { index : int; hval : 'a; }
val mklApp : Term.constr Lazy.t -> Term.constr array -> Term.constr
val declare_new_type : Names.variable -> Term.constr
val declare_new_variable : Names.variable -> Term.types -> Term.constr
val mkName : string -> Names.name

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


val cInt_tbl : (int, Term.constr) Hashtbl.t
val mkInt : int -> Term.constr
type 'a gen_hashed = { index : int; hval : 'a; }
val mklApp : Term.constr Lazy.t -> Term.constr array -> Term.constr
val declare_new_type : Names.variable -> Term.constr
val declare_new_variable : Names.variable -> Term.types -> Term.constr
val mkName : string -> Names.name
val string_coq_constr : Term.constr -> string
val string_of_name : Names.name -> string
type logic_item = LUF | LLia | LBitvectors | LArrays
module SL : Set.S with type elt = logic_item
type logic = SL.t

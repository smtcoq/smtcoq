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
val declare_new_type : Names.variable -> Structures.constr
val declare_new_variable : Names.variable -> Structures.types -> Structures.constr
val mkName : string -> Structures.name
val string_coq_constr : Structures.constr -> string
val string_of_name : Structures.name -> string
type logic_item = LUF | LLia | LBitvectors | LArrays
module SL : Set.S with type elt = logic_item
type logic = SL.t

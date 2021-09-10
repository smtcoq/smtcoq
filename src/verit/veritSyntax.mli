(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtAtom

exception Sat

type typ = 
  | Assume (* Inpu *)
  | True
  | Fals
  | Notnot (* New *)
  | Threso (* New *)
  | Reso
  | Taut (* New *)
  | Cont (* New *)
  | Refl (* New *)
  | Trans (* New *)
  | Cong (* New *)
  | Eqre
  | Eqtr
  | Eqco
  | Eqcp
  | And
  | Nor
  | Or
  | Nand
  | Xor1 
  | Xor2
  | Nxor1 
  | Nxor2
  | Imp
  | Nimp1
  | Nimp2
  | Equ1
  | Equ2
  | Nequ1
  | Nequ2
  | Andp
  | Andn
  | Orp
  | Orn
  | Xorp1
  | Xorp2
  | Xorn1
  | Xorn2
  | Impp
  | Impn1
  | Impn2
  | Equp1
  | Equp2
  | Equn1
  | Equn2
  | Ite1
  | Ite2
  | Itep1
  | Itep2
  | Iten1
  | Iten2
  | Nite1
  | Nite2
  | Conndef (* New *)
  | Andsimp (* New *)
  | Orsimp (* New *)
  | Notsimp (* New *)
  | Impsimp (* New *)
  | Eqsimp (* New *)
  | Boolsimp (* New *)
  | Acsimp (* New *)
  | Itesimp (* New *)
  | Equalsimp (* New *)

val get_clause : int -> SmtAtom.Form.t SmtCertif.clause
val add_clause : int -> SmtAtom.Form.t SmtCertif.clause -> unit

val add_ref : int -> int -> unit
val get_ref : int -> int
val to_add : (int * SmtAtom.Form.t list) list ref

val mk_clause : SmtCertif.clause_id * typ * SmtAtom.Form.t list * SmtCertif.clause_id list -> SmtCertif.clause_id

val apply_dec_atom : (?declare:bool -> SmtAtom.hatom -> SmtAtom.hatom) ->
                     bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_bdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_tdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit

val apply_dec : ('a -> 'b) -> bool * 'a -> bool * 'b
(* From the boolean of each element, decides the boolean for the entire list *)
val list_dec : (bool * 'a) list -> bool * 'a list


val get_solver : int -> bool * Form.atom_form_lit
val add_solver : int -> bool * Form.atom_form_lit -> unit

val find_opt_qvar : string -> SmtBtype.btype option 
val add_qvar : string -> SmtBtype.btype -> unit
val clear_qvar : unit -> unit

val init_index : SmtAtom.Form.t list -> (SmtAtom.Form.t -> SmtAtom.Form.t) ->
                 SmtAtom.Form.t -> int

val qf_to_add : SmtAtom.Form.t SmtCertif.clause list -> (SmtAtom.Form.t SmtCertif.clause_kind * SmtAtom.Form.t list option * SmtAtom.Form.t SmtCertif.clause) list

val ra : SmtAtom.Atom.reify_tbl
val rf : SmtAtom.Form.reify
val ra_quant : SmtAtom.Atom.reify_tbl
val rf_quant : SmtAtom.Form.reify

val hlets : (string, Form.atom_form_lit) Hashtbl.t

val clear : unit -> unit

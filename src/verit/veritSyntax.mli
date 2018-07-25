(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


exception Sat

type typ = | Inpu | Deep | True | Fals | Andp | Andn | Orp | Orn | Xorp1 | Xorp2 | Xorn1 | Xorn2 | Impp | Impn1 | Impn2 | Equp1 | Equp2 | Equn1 | Equn2 | Itep1 | Itep2 | Iten1 | Iten2 | Eqre | Eqtr | Eqco | Eqcp | Dlge | Lage | Lata | Dlde | Lade | Fins | Eins | Skea | Skaa | Qnts | Qntm | Reso | And | Nor | Or | Nand | Xor1 | Xor2 | Nxor1 | Nxor2 | Imp | Nimp1 | Nimp2 | Equ1 | Equ2 | Nequ1 | Nequ2 | Ite1 | Ite2 | Nite1 | Nite2 | Tpal | Tlap | Tple | Tpne | Tpde | Tpsa | Tpie | Tpma | Tpbr | Tpbe | Tpsc | Tppp | Tpqt | Tpqs | Tpsk | Subp | Hole

val get_clause : int -> SmtAtom.Form.t SmtCertif.clause
val add_clause : int -> SmtAtom.Form.t SmtCertif.clause -> unit

val add_ref : int -> int -> unit
val get_ref : int -> int
val to_add : (int * SmtAtom.Form.t list) list ref

val mk_clause : SmtCertif.clause_id * typ * SmtAtom.Form.t list * SmtCertif.clause_id list -> SmtCertif.clause_id

type atom_form_lit =
  | Atom of SmtAtom.Atom.t
  | Form of SmtAtom.Form.pform
  | Lit of SmtAtom.Form.t
val lit_of_atom_form_lit : SmtAtom.Form.reify -> bool * atom_form_lit ->
                           SmtAtom.Form.t

val apply_dec_atom : (bool -> SmtAtom.hatom -> SmtAtom.hatom) ->
                     bool * atom_form_lit -> bool * atom_form_lit
val apply_bdec_atom :
  (bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * atom_form_lit -> bool * atom_form_lit -> bool * atom_form_lit

val apply_dec : ('a -> 'b) -> bool * 'a -> bool * 'b
val list_dec : (bool * 'a) list -> bool * 'a list


val get_solver : int -> bool * atom_form_lit
val add_solver : int -> bool * atom_form_lit -> unit

val get_btype : string -> SmtBtype.btype
val add_btype : string -> SmtBtype.btype -> unit

val get_fun : string -> SmtAtom.indexed_op
val add_fun : string -> SmtAtom.indexed_op -> unit

val find_opt_qvar : string -> SmtBtype.btype option 
val add_qvar : string -> SmtBtype.btype -> unit
val clear_qvar : unit -> unit

val string_hform : SmtAtom.Form.t -> string

val init_index : SmtAtom.Form.t list -> (SmtAtom.Form.t -> SmtAtom.Form.t) ->
                 SmtAtom.Form.t -> int

val qf_to_add : SmtAtom.Form.t SmtCertif.clause list -> (SmtAtom.Form.t SmtCertif.clause_kind * SmtAtom.Form.t list option * SmtAtom.Form.t SmtCertif.clause) list
                                     
val ra : SmtAtom.Atom.reify_tbl
val rf : SmtAtom.Form.reify
val ra' : SmtAtom.Atom.reify_tbl
val rf' : SmtAtom.Form.reify
           
val hlets : (string, atom_form_lit) Hashtbl.t

val clear : unit -> unit

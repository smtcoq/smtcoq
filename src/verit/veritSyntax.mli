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


open SmtAtom

exception Sat

type typ = | Inpu | Deep | True | Fals | Andp | Andn | Orp | Orn | Xorp1 | Xorp2 | Xorn1 | Xorn2 | Impp | Impn1 | Impn2 | Equp1 | Equp2 | Equn1 | Equn2 | Itep1 | Itep2 | Iten1 | Iten2 | Eqre | Eqtr | Eqco | Eqcp | Dlge | Lage | Lata | Dlde | Lade | Fins | Eins | Skea | Skaa | Qnts | Qntm | Reso | Weak | And | Nor | Or | Nand | Xor1 | Xor2 | Nxor1 | Nxor2 | Imp | Nimp1 | Nimp2 | Equ1 | Equ2 | Nequ1 | Nequ2 | Ite1 | Ite2 | Nite1 | Nite2 | Tpal | Tlap | Tple | Tpne | Tpde | Tpsa | Tpie | Tpma | Tpbr | Tpbe | Tpsc | Tppp | Tpqt | Tpqs | Tpsk | Subp | Flat | Hole | Bbva | Bbconst | Bbeq | Bbdis | Bbop | Bbadd | Bbmul | Bbult | Bbslt | Bbnot | Bbneg | Bbconc | Bbextr | Bbzext | Bbsext | Bbshl | Bbshr | Row1 | Row2 | Exte

type verit_state
val create_verit_state : unit -> verit_state

val get_smt_state : verit_state -> State.smt_state

val get_type_tbl : verit_state -> State.type_tbl
val get_op_tbl : verit_state -> State.op_tbl
val get_atom_tbl_to_add : verit_state -> State.atom_tbl_to_add
val get_form_tbl_to_add : verit_state -> State.form_tbl_to_add
val get_atom_tbl_no_add : verit_state -> State.atom_tbl_no_add
val get_form_tbl_no_add : verit_state -> State.form_tbl_no_add

val get_clause : int -> verit_state -> SmtAtom.Form.t SmtCertif.clause
val add_clause : int -> SmtAtom.Form.t SmtCertif.clause -> verit_state -> unit

val get_ref : int -> verit_state -> int
val add_ref : int -> int -> verit_state -> unit

val mk_clause : SmtCertif.clause_id * typ * SmtAtom.Form.t list * SmtCertif.clause_id list -> verit_state -> SmtCertif.clause_id

val apply_dec_atom : (?declare:bool -> SmtAtom.hatom -> SmtAtom.hatom) ->
                     bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_bdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit
val apply_tdec_atom :
  (?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) ->
  bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit -> bool * Form.atom_form_lit

val apply_dec : ('a -> 'b) -> bool * 'a -> bool * 'b
val list_dec : (bool * 'a) list -> bool * 'a list

val get_solver : int -> verit_state -> (bool * Form.atom_form_lit)
val add_solver : int -> bool * Form.atom_form_lit -> verit_state -> unit

val init_index : SmtAtom.Form.t list -> (SmtAtom.Form.t -> SmtAtom.Form.t) ->
                 SmtAtom.Form.t -> int

val qf_to_add : SmtAtom.Form.t SmtCertif.clause list -> (SmtAtom.Form.t SmtCertif.clause_kind * SmtAtom.Form.t list option * SmtAtom.Form.t SmtCertif.clause) list

val get_hlet : string -> verit_state -> Form.atom_form_lit
val add_hlet : string -> Form.atom_form_lit -> verit_state -> unit

type quant_state
val create_quant_state : unit -> quant_state
val find_opt_qvar : string -> quant_state -> SmtBtype.btype option
val add_qvar : string -> SmtBtype.btype -> quant_state -> unit

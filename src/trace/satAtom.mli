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


module Atom : sig
  type t = int
  val index : t -> int

  val equal : t -> t -> bool

  val is_bool_type : t -> bool
  val is_bv_type : t -> bool
  val to_smt : Format.formatter -> t -> unit
  val logic : t -> SmtMisc.logic

  type reify_tbl = {
      mutable count : int;
      tbl : (Structures.constr, t) Hashtbl.t;
    }
  val create : unit -> reify_tbl
  val declare : reify_tbl -> Structures.constr -> t
  val get : reify_tbl -> Structures.constr -> t
  val atom_tbl : reify_tbl -> Structures.constr array
  val interp_tbl : reify_tbl -> Structures.constr
end


module Form : SmtForm.FORM with type hatom = Atom.t


module Trace :
  sig
    val share_prefix : Form.t SmtCertif.clause -> int -> unit
  end
module Cnf :
  sig
    type form_info =
      SmtCnf.MakeCnf(Form).form_info =
        Immediate of bool
      | Done
      | Todo
    val info : (int, form_info) Hashtbl.t
    val init_last : Form.t SmtCertif.clause
    val last : Form.t SmtCertif.clause ref
    val cnf_todo : Form.t array list ref
    val clear : unit -> unit
    val push_cnf : Form.t array -> unit
    val get_info : Form.t -> form_info
    val set_done : Form.t -> unit
    val set_immediate : Form.t -> unit
    val test_immediate : Form.t -> bool
    val check_trivial : Form.t list -> bool
    val link_Other : Form.t SmtCertif.rule -> Form.t list -> unit
    val both_lit : Form.t -> Form.t * Form.t
    val or_of_imp : Form.t array -> Form.t array
    val cnf : Form.t -> unit
    exception Cnf_done
    val imm_link_Other : Form.t SmtCertif.rule -> Form.t -> unit
    val imm_cnf : Form.t SmtCertif.clause -> unit
    val make_cnf :
      Form.reify -> Form.t SmtCertif.clause -> Form.t SmtCertif.clause
  end

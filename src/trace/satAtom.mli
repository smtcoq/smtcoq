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


module Atom : sig
  type t = int
  val index : t -> int

  val equal : t -> t -> bool

  val is_bool_type : t -> bool
  val is_bv_type : t -> bool
  val to_smt : Format.formatter -> t -> unit
  val logic : t -> SmtMisc.logic

  val is_bool_type : t -> bool
  type reify_tbl = {
      mutable count : int;
      tbl : (Term.constr, t) Hashtbl.t;
    }
  val create : unit -> reify_tbl
  val declare : reify_tbl -> Term.constr -> t
  val get : reify_tbl -> Term.constr -> t
  val atom_tbl : reify_tbl -> Term.constr array
  val interp_tbl : reify_tbl -> Term.constr
end


module Form : SmtForm.FORM with type hatom = Atom.t


module Trace :
  sig
    val share_value : Form.t SmtCertif.clause -> unit
    module HashedHeadRes :
      sig
        type t = Form.t SmtCertif.resolution
        val equal :
          'a SmtCertif.resolution -> 'b SmtCertif.resolution -> bool
        val hash : 'a SmtCertif.resolution -> int
      end
    module HRtbl :
      sig
        type key = HashedHeadRes.t
        type 'a t = 'a Hashtbl.Make(HashedHeadRes).t
        val create : int -> 'a t
        val clear : 'a t -> unit
        val reset : 'a t -> unit
        val copy : 'a t -> 'a t
        val add : 'a t -> key -> 'a -> unit
        val remove : 'a t -> key -> unit
        val find : 'a t -> key -> 'a
        val find_all : 'a t -> key -> 'a list
        val replace : 'a t -> key -> 'a -> unit
        val mem : 'a t -> key -> bool
        val iter : (key -> 'a -> unit) -> 'a t -> unit
        val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
        val length : 'a t -> int
        val stats : 'a t -> Hashtbl.statistics
      end
    val common_head :
      'a SmtCertif.clause list ->
      'b SmtCertif.clause list ->
      'a SmtCertif.clause list * 'a SmtCertif.clause list *
      'b SmtCertif.clause list
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

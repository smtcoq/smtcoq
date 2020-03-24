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


module MakeCnf :
  functor (Form : SmtForm.FORM) ->
    sig
      type form_info = Immediate of bool | Done | Todo
      val info : (int, form_info) Hashtbl.t
      val cnf_todo : Form.t array list ref
      val clear : unit -> unit
      val push_cnf : Form.t array -> unit
      val get_info : Form.t -> form_info
      val set_done : Form.t -> unit
      val set_immediate : Form.t -> unit
      val test_immediate : Form.t -> bool
      val check_trivial : Form.t list -> bool
      (* val link_Other : Form.t SmtCertif.rule -> Form.t list -> unit *)
      val both_lit : Form.t -> Form.t * Form.t
      val or_of_imp : Form.t array -> Form.t array
      (* val cnf : Form.t -> unit *)
      exception Cnf_done
      (* val imm_link_Other : Form.t SmtCertif.rule -> Form.t -> unit *)
      (* val imm_cnf : Form.t SmtCertif.clause -> unit *)
      val make_cnf :
        SmtTrace.trace_state -> Form.reify -> Form.t SmtCertif.clause -> Form.t SmtCertif.clause
    end

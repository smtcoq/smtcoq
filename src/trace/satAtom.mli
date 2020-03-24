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
    val share_prefix : SmtTrace.trace_state -> Form.t SmtCertif.clause -> int -> unit
  end

module Cnf :
  sig
    val make_cnf :
      SmtTrace.trace_state -> Form.reify -> Form.t SmtCertif.clause -> Form.t SmtCertif.clause
  end

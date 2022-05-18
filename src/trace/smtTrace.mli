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


(* Traces *)
val notUsed : int
val clear : unit -> unit
val next_id : unit -> SmtCertif.clause_id
val mk_scertif :
  'a SmtCertif.clause_kind -> 'a list option -> 'a SmtCertif.clause
val mkRootGen : 'a list option -> 'a SmtCertif.clause
val mkRootV : 'a list -> 'a SmtCertif.clause
val isRoot : 'a SmtCertif.clause_kind -> bool
val mkRes :
  'a SmtCertif.clause ->
  'a SmtCertif.clause -> 'a SmtCertif.clause list -> 'a SmtCertif.clause
val isRes : 'a SmtCertif.clause_kind -> bool
val mkOther : 'a SmtCertif.rule -> 'a list option -> 'a SmtCertif.clause
val next : 'a SmtCertif.clause -> 'a SmtCertif.clause
val has_prev : 'a SmtCertif.clause -> bool
val prev : 'a SmtCertif.clause -> 'a SmtCertif.clause
val link : 'a SmtCertif.clause -> 'a SmtCertif.clause -> unit
val clear_links : 'a SmtCertif.clause -> unit
val skip : 'a SmtCertif.clause -> unit
val insert_before : 'a SmtCertif.clause -> 'a SmtCertif.clause -> unit
val get_res : 'a SmtCertif.clause -> string -> 'a SmtCertif.resolution
val get_other : 'a SmtCertif.clause -> string -> 'a SmtCertif.rule
val get_val : 'a SmtCertif.clause -> 'a list
val repr : 'a SmtCertif.clause -> 'a SmtCertif.clause
val set_same : 'a SmtCertif.clause -> 'a SmtCertif.clause -> unit
val get_pos : 'a SmtCertif.clause -> int
val eq_clause : 'a SmtCertif.clause -> 'b SmtCertif.clause -> bool
val order_roots : ('a -> int) -> 'a SmtCertif.clause ->
                  'a SmtCertif.clause * 'a SmtCertif.clause list
val add_scertifs : ('a SmtCertif.clause_kind * 'a list option * 'a SmtCertif.clause) list -> 
                   'a SmtCertif.clause -> 'a SmtCertif.clause
val select : 'a SmtCertif.clause -> unit
val occur : 'a SmtCertif.clause -> unit
val alloc : 'a SmtCertif.clause -> int
val naive_alloc : 'a SmtCertif.clause -> int
val build_certif : 'a SmtCertif.clause -> 'b SmtCertif.clause -> int
val to_coq :
  ('a -> CoqInterface.constr) ->
  ('a list list * 'a list -> CoqInterface.types) ->
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t *
  CoqInterface.constr Lazy.t * CoqInterface.constr Lazy.t ->
  'a SmtCertif.clause ->
  ('a SmtCertif.clause -> CoqInterface.types * CoqInterface.constr) option ->
  CoqInterface.constr * 'a SmtCertif.clause *
    (CoqInterface.id * CoqInterface.types) list


module MakeOpt :
  functor (Form : SmtForm.FORM) ->
    sig
      val share_prefix : Form.t SmtCertif.clause -> int -> unit
    end

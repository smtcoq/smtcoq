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
  ('a -> Term.constr) ->
  ('a list list * 'a list -> Term.types) ->
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t * Term.constr Lazy.t *
  Term.constr Lazy.t * Term.constr Lazy.t ->
  'a SmtCertif.clause ->
  ('a SmtCertif.clause -> Term.types * Term.constr) option ->
  Term.constr * 'a SmtCertif.clause *
    (Names.identifier * Term.types) list
module MakeOpt :
  functor (Form : SmtForm.FORM) ->
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

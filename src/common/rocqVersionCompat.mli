(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type constr_expr = Constrexpr.constr_expr
val ppconstr_modular_constr_pr :
  ((unit -> Pp.t) ->
   int option ->
   Constrexpr.entry_relative_level -> constr_expr -> Pp.t) ->
  (unit -> Pp.t) ->
  int option ->
  Constrexpr.entry_relative_level -> constr_expr -> Pp.t
val constrextern_extern_constr :
  ?inctx:bool ->
  ?scope:Notation_term.scope_name ->
  Environ.env -> Evd.evar_map -> EConstr.constr -> constr_expr

val evd_univ_entry : Evd.evar_map -> UState.named_universes_entry

val empty_named_universes_entry : UState.named_universes_entry

val hash_constr : Constr.t -> int

module Summary :
sig
  module Ref :
  sig
    type 'a t
    val get : 'a t -> 'a
    val set : 'a t -> 'a -> unit
    val (!) : 'a t -> 'a
    val (:=) : 'a t -> 'a -> unit
  end
  val ref : name:string -> 'a -> 'a Ref.t
end

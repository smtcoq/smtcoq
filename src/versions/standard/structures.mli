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


(* Constr generation and manipulation *)
(* WARNING: currently, we map all the econstr into constr: we suppose
   that the goal does not contain existencial variables *)
val mklApp : Constr.t Lazy.t -> Constr.t array -> Constr.t
val gen_constant : string list list -> string -> Constr.t lazy_t

(* Int63 *)
val int63_modules : string list list
val int31_module : string list list
val cD0 : Constr.t lazy_t
val cD1 : Constr.t lazy_t
val cI31 : Constr.t lazy_t
val mkInt : int -> Constr.t
val cint : Constr.t lazy_t

(* PArray *)
val parray_modules : string list list
val cmake : Constr.t lazy_t
val cset : Constr.t lazy_t
val max_array_size : int
val mkArray : Constr.types * Constr.t array -> Constr.t

(* Traces *)
val mkTrace :
  ('a -> Constr.t) ->
  ('a -> 'a) ->
  'b ->
  Constr.t Lazy.t ->
  Constr.t Lazy.t ->
  Constr.t Lazy.t ->
  Constr.t Lazy.t ->
  int -> Constr.t -> Constr.t -> 'a ref -> Constr.t

(* Differences between the two versions of Coq *)
val mkUConst :
  Constr.t -> Safe_typing.private_constants Entries.definition_entry
val mkTConst :
  Constr.t ->
  Constr.t ->
  Constr.types -> Safe_typing.private_constants Entries.definition_entry
val error : string -> 'a
val coqtype : Constr.types Future.computation
val declare_new_type : Names.variable -> Constr.t
val declare_new_variable : Names.variable -> Constr.t -> Constr.t
val extern_constr : Constr.t -> Constrexpr.constr_expr
val vernacentries_interp : Constrexpr.constr_expr -> unit
val pr_constr_env : Environ.env -> Constr.t -> Pp.t
val lift : int -> Constr.constr -> Constr.constr
val destruct_rel_decl : Context.Rel.Declaration.t -> Names.Name.t * Constr.t
val interp_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Constr.t
val tclTHEN :
  unit Proofview.tactic -> unit Proofview.tactic -> unit Proofview.tactic
val tclTHENLAST :
  unit Proofview.tactic -> unit Proofview.tactic -> unit Proofview.tactic
val assert_before : Names.Name.t -> Constr.types -> unit Proofview.tactic

val vm_conv : Reduction.conv_pb -> Constr.types Reduction.kernel_conversion_function
val vm_cast_no_check : Constr.t -> unit Proofview.tactic
val cbv_vm : Environ.env -> Constr.t -> Constr.types -> Constr.t

val mk_tactic :
  (Environ.env -> Evd.evar_map -> Constr.t -> unit Proofview.tactic) ->
  unit Proofview.tactic
val set_evars_tac : Constr.t -> unit Proofview.tactic
val ppconstr_lsimpleconstr : Notation_term.tolerability
val constrextern_extern_constr : Constr.t -> Constrexpr.constr_expr
val get_rel_dec_name : Context.Rel.Declaration.t -> Names.Name.t
val retyping_get_type_of : Environ.env -> Evd.evar_map -> Constr.t -> Constr.t


(* Micromega *)
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
module Micromega_plugin_Coq_micromega = Micromega_plugin.Coq_micromega
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Mutils = Micromega_plugin.Mutils

val micromega_coq_proofTerm : Constr.t lazy_t
val micromega_dump_proof_term : Micromega_plugin_Certificate.Mc.zArithProof -> Constr.t


(* Types in the Coq source code *)
type tactic = unit Proofview.tactic
type names_id = Names.Id.t
type constr_expr = Constrexpr.constr_expr

(* EConstr *)
type econstr = EConstr.t
val econstr_of_constr : Constr.t -> econstr

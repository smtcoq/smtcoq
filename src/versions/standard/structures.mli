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


(* WARNING: currently, we map all the econstr into constr: we suppose
   that the goal does not contain existencial variables *)

(* Constr generation and manipulation *)
type constr
type types = constr
val eq_constr : constr -> constr -> bool
val hash_constr : constr -> int
val mkApp : constr * constr array -> constr
val mklApp : constr Lazy.t -> constr array -> constr
val decompose_app : constr -> constr * constr list
val mkProp : types
val mkArrow : types -> types -> types
val mkRel : int -> constr
val isRel : constr -> bool
val destRel : constr -> int
val pr_constr : constr -> Pp.t

type id
val mkId : string -> id
val mkVar : id -> constr

type name
val mkName : string -> name
val string_of_name : name -> string

type cast_kind
val vmcast : cast_kind
val mkCast : constr * cast_kind * constr -> constr

val gen_constant : string list list -> string -> constr lazy_t

(* Int63 *)
val int63_modules : string list list
val int31_module : string list list
val cD0 : constr lazy_t
val cD1 : constr lazy_t
val cI31 : constr lazy_t
val mkInt : int -> constr
val cint : constr lazy_t

(* PArray *)
val parray_modules : string list list
val cmake : constr lazy_t
val cset : constr lazy_t
val max_array_size : int
val mkArray : types * constr array -> constr

(* Traces *)
val mkTrace :
  ('a -> constr) ->
  ('a -> 'a) ->
  'b ->
  constr Lazy.t ->
  constr Lazy.t ->
  constr Lazy.t ->
  constr Lazy.t ->
  int -> constr -> constr -> 'a ref -> constr

(* Differences between the two versions of Coq *)
val mkUConst :
  constr -> Safe_typing.private_constants Entries.definition_entry
val mkTConst :
  constr ->
  constr ->
  types -> Safe_typing.private_constants Entries.definition_entry
val error : string -> 'a
val coqtype : types Future.computation
val declare_new_type : Names.variable -> types
val declare_new_variable : Names.variable -> types -> constr
val extern_constr : constr -> Constrexpr.constr_expr
val pr_constr_env : Environ.env -> constr -> Pp.t
val lift : int -> Constr.constr -> Constr.constr
val destruct_rel_decl : Context.Rel.Declaration.t -> name * constr
val interp_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> constr
val tclTHEN :
  unit Proofview.tactic -> unit Proofview.tactic -> unit Proofview.tactic
val tclTHENLAST :
  unit Proofview.tactic -> unit Proofview.tactic -> unit Proofview.tactic
val assert_before : Names.Name.t -> types -> unit Proofview.tactic

val vm_conv : Reduction.conv_pb -> types Reduction.kernel_conversion_function
val vm_cast_no_check : constr -> unit Proofview.tactic
val cbv_vm : Environ.env -> constr -> types -> constr

val mk_tactic :
  (Environ.env -> Evd.evar_map -> constr -> unit Proofview.tactic) ->
  unit Proofview.tactic
val set_evars_tac : constr -> unit Proofview.tactic
val ppconstr_lsimpleconstr : Notation_term.tolerability
val constrextern_extern_constr : constr -> Constrexpr.constr_expr
val get_rel_dec_name : Context.Rel.Declaration.t -> Names.Name.t
val retyping_get_type_of : Environ.env -> Evd.evar_map -> constr -> constr


(* Micromega *)
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
module Micromega_plugin_Coq_micromega = Micromega_plugin.Coq_micromega
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Mutils = Micromega_plugin.Mutils

val micromega_coq_proofTerm : constr lazy_t
val micromega_dump_proof_term : Micromega_plugin_Certificate.Mc.zArithProof -> constr


(* Types in the Coq source code *)
type tactic = unit Proofview.tactic
type constr_expr = Constrexpr.constr_expr

(* EConstr *)
type econstr = EConstr.t
val econstr_of_constr : constr -> econstr

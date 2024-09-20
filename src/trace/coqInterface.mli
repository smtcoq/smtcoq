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


(* WARNING: currently, we map all the econstr into constr: we suppose
   that the goal does not contain existencial variables *)

(* Constr generation and manipulation *)
type id = Names.variable
val mkId : string -> id

type name
val name_of_id : id -> name
val mkName : string -> name
val string_of_name : name -> string

type constr = Constr.t
type types = constr
val eq_constr : constr -> constr -> bool
val hash_constr : constr -> int
val mkProp : types
val mkConst : Names.Constant.t -> constr
val mkVar : id -> constr
val mkRel : int -> constr
val isRel : constr -> bool
val destRel : constr -> int
val lift : int -> constr -> constr
val mkApp : constr * constr array -> constr
val decompose_app_list : constr -> constr * constr list
val mkLambda : name * types * constr -> constr
val mkProd : name * types * types -> types
val mkLetIn : name * constr * types * constr -> constr
val mkArrow : types -> types -> constr

val pr_constr_env : Environ.env -> constr -> Pp.t
val pr_constr : constr -> Pp.t

val mkUConst : constr -> Declare.proof_entry
val mkTConst : constr -> constr -> types -> Declare.proof_entry
val declare_new_type : id -> types
val declare_new_variable : id -> types -> constr
val declare_constant : id -> Declare.proof_entry -> Names.Constant.t

type cast_kind
val vmcast : cast_kind
val mkCast : constr * cast_kind * constr -> constr


(* EConstr *)
type econstr = EConstr.t
val econstr_of_constr : constr -> econstr


(* Int63 *)
val mkInt : int -> constr


(* PArray *)
val max_array_size : int


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


(* Micromega *)
module Micromega_plugin_Micromega = Micromega_core_plugin.Micromega
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
val micromega_dump_proof_term : Micromega_plugin_Micromega.zArithProof -> constr


(* Tactics *)
type tactic = unit Proofview.tactic
val tclIDTAC : tactic
val tclTHEN : tactic -> tactic -> tactic
val tclTHENLAST : tactic -> tactic -> tactic
val assert_before : name -> types -> tactic
val vm_cast_no_check : constr -> tactic
val mk_tactic : (Environ.env -> Evd.evar_map -> constr -> tactic) -> tactic
val set_evars_tac : constr -> tactic


(* Other differences between the two versions of Coq *)
type constr_expr = Constrexpr.constr_expr
val error : string -> 'a
val anomaly : string -> 'a

val smtcoq_cat : CWarnings.category

val destruct_rel_decl : Constr.rel_declaration -> name * types
val interp_constr : Environ.env -> Evd.evar_map -> constr_expr -> constr
val ppconstr_lsimpleconstr : Constrexpr.entry_relative_level
val constrextern_extern_constr : constr -> constr_expr
val get_rel_dec_name : Constr.rel_declaration -> name
val retyping_get_type_of : Environ.env -> Evd.evar_map -> constr -> constr

val vm_conv : Conversion.conv_pb -> types Conversion.kernel_conversion_function
val cbv_vm : Environ.env -> constr -> types -> constr

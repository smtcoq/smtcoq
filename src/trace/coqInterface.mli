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

(* EConstr generation and manipulation *)
type id = Names.variable
val mkId : string -> id

type name
val name_of_id : id -> name
val mkName : string -> name
val string_of_name : name -> string

type constr = EConstr.t
type types = constr
val eq_constr : Evd.evar_map -> constr -> constr -> bool
(* val hash_constr : constr -> int *)
val mkProp : types
val mkConst : Names.Constant.t -> constr
val mkVar : id -> constr
val mkRel : int -> constr
val isRel : Evd.evar_map -> constr -> bool
val destRel : Evd.evar_map -> constr -> int
val lift : int -> constr -> constr
val mkApp : constr * constr array -> constr
val decompose_app : Evd.evar_map -> constr -> constr * constr list
val mkLambda : name * types * constr -> constr
val mkProd : name * types * types -> types
val mkLetIn : name * constr * types * constr -> constr
val mkArrow : types -> types -> constr

val pr_constr : Environ.env -> Evd.evar_map -> EConstr.t -> Pp.t

(* val mkUConst : constr -> Evd.side_effects Declare.proof_entry
 * val mkTConst : constr -> constr -> types -> Evd.side_effects Declare.proof_entry *)
(* val declare_new_type : id -> types
 * val declare_new_variable : id -> types -> constr
 * val declare_constant : id -> Evd.side_effects Declare.proof_entry -> Names.Constant.t *)

type cast_kind
val vmcast : cast_kind
val mkCast : constr * cast_kind * constr -> constr


(* Int63 *)
val mkInt : int -> constr


(* PArray *)
val max_array_size : int


(* Micromega *)
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
val micromega_dump_proof_term : Micromega_plugin_Micromega.zArithProof -> constr


(* Tactics *)
type tactic = unit Proofview.tactic
val tclTHEN : tactic -> tactic -> tactic
val tclTHENLAST : tactic -> tactic -> tactic
val assert_before : name -> types -> tactic
val vm_cast_no_check : constr -> tactic
val mk_tactic : (Environ.env -> Evd.evar_map -> constr -> tactic) -> tactic
(* val set_evars_tac : constr -> tactic *)


(* Errors and warnings *)
val error : string -> 'a
val anomaly : string -> 'a
val warning : string -> string -> unit


(* VM conversion *)
(* val vm_conv : Reduction.conv_pb -> types Reduction.kernel_conversion_function *)
val cbv_vm : Environ.env -> Evd.evar_map -> constr -> types -> constr


(* Other differences between the two versions of Coq *)
(* type constr_expr = Constrexpr.constr_expr
 * val destruct_rel_decl : (constr, types) Context.Rel.Declaration.pt -> name * types
 * val interp_constr : Environ.env -> Evd.evar_map -> constr_expr -> constr
 * val ppconstr_lsimpleconstr : Constrexpr.entry_relative_level
 * val constrextern_extern_constr : constr -> constr_expr
 * val get_rel_dec_name : (constr, types) Context.Rel.Declaration.pt -> name
 * val retyping_get_type_of : Environ.env -> Evd.evar_map -> constr -> constr *)

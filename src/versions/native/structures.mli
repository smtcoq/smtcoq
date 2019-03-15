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
type id = Names.variable
val mkId : string -> id

type name
val name_of_id : id -> name
val mkName : string -> name
val string_of_name : name -> string

type constr = Term.constr
type types = constr
val eq_constr : constr -> constr -> bool
val hash_constr : constr -> int
val mkProp : types
val mkConst : Names.constant -> constr
val mkVar : id -> constr
val mkRel : int -> constr
val isRel : constr -> bool
val destRel : constr -> int
val lift : int -> constr -> constr
val mkApp : constr * constr array -> constr
val decompose_app : constr -> constr * constr list
val mkLambda : name * types * constr -> constr
val mkProd : name * types * types -> types
val mkLetIn : name * constr * types * constr -> constr

val pr_constr_env : Environ.env -> constr -> Pp.std_ppcmds
val pr_constr : constr -> Pp.std_ppcmds

val mkUConst : constr -> Entries.definition_entry
val mkTConst : constr -> 'a -> types -> Entries.definition_entry
val declare_new_type : id -> types
val declare_new_variable : id -> types -> constr
val declare_constant : id -> Entries.definition_entry -> Names.constant

type cast_kind
val vmcast : cast_kind
val mkCast : constr * cast_kind * constr -> constr


(* EConstr *)
type econstr = constr
val econstr_of_constr : constr -> econstr


(* Modules *)
val gen_constant : string list list -> string -> constr lazy_t


(* Int63 *)
val int63_modules : string list list
val mkInt : int -> constr
val cint : constr lazy_t


(* PArray *)
val parray_modules : string list list
val max_array_size : int
val mkArray : types * constr array -> constr


(* Traces *)
val mkTrace :
  ('a -> constr) ->
  ('a -> 'a) ->
  constr Lazy.t ->
  'b ->
  'c -> 'd -> 'e -> int -> types -> constr -> 'a ref -> constr


(* Micromega *)
module Micromega_plugin_Micromega = Micromega
module Micromega_plugin_Mutils = Mutils
module Micromega_plugin_Certificate = Certificate
module Micromega_plugin_Coq_micromega = Coq_micromega

val micromega_coq_proofTerm : constr lazy_t
val micromega_dump_proof_term : Micromega_plugin_Certificate.Mc.zArithProof -> constr


(* Tactics *)
type tactic = Proof_type.tactic
val tclTHEN : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
val tclTHENLAST : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
val assert_before : name -> types -> Proof_type.tactic
val vm_cast_no_check : constr -> Proof_type.tactic
val mk_tactic :
  (Environ.env ->
   Evd.evar_map -> types -> Proof_type.goal Tacmach.sigma -> 'a) ->
  Proof_type.goal Tacmach.sigma -> 'a
val set_evars_tac : 'a -> Proof_type.tactic


(* Other differences between the two versions of Coq *)
type constr_expr = Topconstr.constr_expr
val error : string -> 'a
val extern_constr : constr -> Topconstr.constr_expr
val destruct_rel_decl : Term.rel_declaration -> name * types
val interp_constr : Environ.env -> Evd.evar_map -> Topconstr.constr_expr -> constr
val ppconstr_lsimpleconstr : Ppconstr.precedence
val constrextern_extern_constr : constr -> Topconstr.constr_expr
val get_rel_dec_name : 'a -> name
val retyping_get_type_of : Environ.env -> Evd.evar_map -> constr -> constr

val vm_conv : Reduction.conv_pb -> types Reduction.conversion_function
val cbv_vm : Environ.env -> constr -> types -> constr

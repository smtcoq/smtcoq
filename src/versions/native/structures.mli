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
type constr
type types = constr
val mklApp : constr Lazy.t -> constr array -> constr
val decompose_app : constr -> constr * constr list
val eq_constr : constr -> constr -> bool

type name
val mkName : string -> name
val string_of_name : name -> string

type cast_kind
val vmcast : cast_kind
val mkCast : constr * cast_kind * constr -> constr

val gen_constant : string list list -> string -> constr lazy_t

(* Int63 *)
val int63_modules : string list list
val mkInt : int -> constr
val cint : constr lazy_t
val parray_modules : string list list
val max_array_size : int
val mkArray : types * constr array -> constr
val mkTrace :
  ('a -> constr) ->
  ('a -> 'a) ->
  constr Lazy.t ->
  'b ->
  'c -> 'd -> 'e -> int -> types -> constr -> 'a ref -> constr
type names_id_t = Names.identifier
val mkUConst : constr -> Entries.definition_entry
val mkTConst : constr -> 'a -> types -> Entries.definition_entry
val error : string -> 'a
val coqtype : types lazy_t
val declare_new_type : Names.variable -> types
val declare_new_variable : Names.variable -> types -> constr
val extern_constr : constr -> Topconstr.constr_expr
val pr_constr_env : Environ.env -> constr -> Pp.std_ppcmds
val lift : int -> constr -> constr
val destruct_rel_decl : Term.rel_declaration -> Names.name * constr
val interp_constr : Environ.env -> Evd.evar_map -> Topconstr.constr_expr -> constr
val tclTHEN : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
val tclTHENLAST : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
val assert_before : Names.name -> types -> Proof_type.tactic

val vm_conv : Reduction.conv_pb -> types Reduction.conversion_function
val vm_cast_no_check : constr -> Proof_type.tactic
val cbv_vm : Environ.env -> constr -> types -> constr

val mk_tactic :
  (Environ.env ->
   Evd.evar_map -> types -> Proof_type.goal Tacmach.sigma -> 'a) ->
  Proof_type.goal Tacmach.sigma -> 'a
val set_evars_tac : 'a -> Proof_type.tactic
val ppconstr_lsimpleconstr : Ppconstr.precedence
val constrextern_extern_constr : constr -> Topconstr.constr_expr
val get_rel_dec_name : 'a -> Names.name
val retyping_get_type_of : Environ.env -> Evd.evar_map -> constr -> constr


(* Micromega *)
module Micromega_plugin_Certificate = Certificate
module Micromega_plugin_Coq_micromega = Coq_micromega
module Micromega_plugin_Micromega = Micromega
module Micromega_plugin_Mutils = Mutils

val micromega_coq_proofTerm : constr lazy_t
val micromega_dump_proof_term : Micromega_plugin_Certificate.Mc.zArithProof -> constr


(* Types in the Coq source code *)
type tactic = Proof_type.tactic
type names_id = Names.identifier
type constr_expr = Topconstr.constr_expr

(* EConstr *)
type econstr = constr
val econstr_of_constr : constr -> econstr

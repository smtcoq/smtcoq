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
type types
type name
type id

val names_id_of_string : string -> id
val names_string_of_id : id -> string

(* WARNING: currently, we map all the econstr into constr: we suppose
   that the goal does not contain existencial variables *)
val mklApp : constr Lazy.t -> constr array -> constr
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
val declare_new_type : Names.variable -> constr
val declare_new_variable : Names.variable -> constr -> constr
val extern_constr : constr -> Constrexpr.constr_expr
val pr_constr_env : Environ.env -> constr -> Pp.t
val lift : int -> Constr.constr -> Constr.constr
val destruct_rel_decl : Context.Rel.Declaration.t -> Names.Name.t * constr
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
type names_id = Names.Id.t
type constr_expr = Constrexpr.constr_expr

(* EConstr *)
type econstr = EConstr.t
val econstr_of_constr : constr -> econstr

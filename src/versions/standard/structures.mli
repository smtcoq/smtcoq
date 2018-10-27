val mklApp : Term.constr Lazy.t -> Term.constr array -> Term.constr
val gen_constant : string list list -> string -> Term.constr lazy_t
val int63_modules : string list list
val int31_module : string list list
val cD0 : Term.constr lazy_t
val cD1 : Term.constr lazy_t
val cI31 : Term.constr lazy_t
val mkInt : int -> Term.constr
val cint : Term.constr lazy_t
val parray_modules : string list list
val cmake : Term.constr lazy_t
val cset : Term.constr lazy_t
val max_array_size : int
val mkArray : Term.types * Term.constr array -> Term.constr
val mkTrace :
  ('a -> Term.constr) ->
  ('a -> 'a) ->
  'b ->
  Term.constr Lazy.t ->
  Term.constr Lazy.t ->
  Term.constr Lazy.t ->
  Term.constr Lazy.t ->
  int -> Term.constr -> Term.constr -> 'a ref -> Term.constr
type names_id_t = Names.Id.t
val dummy_loc : Loc.t
val mkUConst :
  Term.constr -> Safe_typing.private_constants Entries.definition_entry
val mkTConst :
  Term.constr ->
  Term.constr ->
  Term.types -> Safe_typing.private_constants Entries.definition_entry
val error : string -> 'a
val coqtype : Term.types Future.computation
val declare_new_type : Names.variable -> Term.constr
val declare_new_variable : Names.variable -> Term.constr -> Term.constr
val extern_constr : Term.constr -> Constrexpr.constr_expr
val vernacentries_interp : Constrexpr.constr_expr -> unit
val pr_constr_env : Environ.env -> Term.constr -> Pp.std_ppcmds
val lift : int -> Constr.constr -> Constr.constr
type rel_decl = Context.Rel.Declaration.t                                     
val destruct_rel_decl : rel_decl -> Names.Name.t * Constr.t
type constr_expr = Constrexpr.constr_expr
val interp_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Term.constr
val tclTHEN :
  unit Proofview.tactic -> unit Proofview.tactic -> unit Proofview.tactic
val tclTHENLAST :
  unit Proofview.tactic -> unit Proofview.tactic -> unit Proofview.tactic
val assert_before : Names.Name.t -> Term.types -> unit Proofview.tactic
val vm_cast_no_check : Term.constr -> unit Proofview.tactic
val mk_tactic :
  (Environ.env -> Evd.evar_map -> Term.constr -> unit Proofview.tactic) ->
  unit Proofview.tactic
val set_evars_tac : Term.constr -> unit Proofview.tactic
val ppconstr_lsimpleconstr : Ppconstr.precedence
val constrextern_extern_constr : Term.constr -> Constrexpr.constr_expr
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
module Micromega_plugin_Coq_micromega = Micromega_plugin.Coq_micromega
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Mutils = Micromega_plugin.Mutils
type tactic = unit Proofview.tactic

val gen_constant : string list list -> string -> Term.constr lazy_t
val int63_modules : string list list
val mkInt : int -> Term.constr
val cint : Term.constr lazy_t
val parray_modules : string list list
val max_array_size : int
val mkArray : Term.types * Term.constr array -> Term.constr
val mkTrace :
  ('a -> Term.constr) ->
  ('a -> 'a) ->
  Term.constr Lazy.t ->
  'b ->
  'c -> 'd -> 'e -> int -> Term.types -> Term.constr -> 'a ref -> Term.constr
type names_id_t = Names.identifier
val dummy_loc : Pp.loc
val mkUConst : Term.constr -> Entries.definition_entry
val mkTConst : Term.constr -> 'a -> Term.types -> Entries.definition_entry
val error : string -> 'a
val coqtype : Term.types lazy_t
val declare_new_type : Names.variable -> Term.constr
val declare_new_variable : Names.variable -> Term.types -> Term.constr
val extern_constr : Term.constr -> Topconstr.constr_expr
val vernacentries_interp : Topconstr.constr_expr -> unit
val pr_constr_env : Environ.env -> Term.constr -> Pp.std_ppcmds
val lift : int -> Term.constr -> Term.constr
val tclTHEN : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
val tclTHENLAST : Proof_type.tactic -> Proof_type.tactic -> Proof_type.tactic
val assert_before : Names.name -> Term.types -> Proof_type.tactic
val vm_cast_no_check : Term.constr -> Proof_type.tactic
val mk_tactic :
  (Environ.env ->
   Evd.evar_map -> Term.types -> Proof_type.goal Tacmach.sigma -> 'a) ->
  Proof_type.goal Tacmach.sigma -> 'a
val set_evars_tac : 'a -> Proof_type.tactic
val ppconstr_lsimpleconstr : Ppconstr.precedence
val constrextern_extern_constr : Term.constr -> Topconstr.constr_expr
module Micromega_plugin_Certificate = Certificate
module Micromega_plugin_Coq_micromega = Coq_micromega
module Micromega_plugin_Micromega = Micromega
module Micromega_plugin_Mutils = Mutils

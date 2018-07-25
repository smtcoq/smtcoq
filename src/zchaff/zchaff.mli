val is_trivial : SatAtom.Form.t list -> bool
val string_of_op : SmtForm.fop -> string
val pp_form : Format.formatter -> SatAtom.Form.t -> unit
val pp_sign : Format.formatter -> SatAtom.Form.t -> unit
val pp_pform : Format.formatter -> SatAtom.Form.pform -> unit
val pp_value : Format.formatter -> SatAtom.Form.t SmtCertif.clause -> unit
val pp_kind : Format.formatter -> SatAtom.Form.t SmtCertif.clause -> unit
val pp_trace : Format.formatter -> SatAtom.Form.t SmtCertif.clause -> unit
val import_cnf :
  string ->
  int * SatAtom.Form.t SmtCertif.clause * SatAtom.Form.t SmtCertif.clause *
  (int, SatAtom.Form.t SmtCertif.clause) Hashtbl.t
val import_cnf_trace :
  (int, 'a SmtCertif.clause) Hashtbl.t ->
  string ->
  SatAtom.Form.t SmtCertif.clause ->
  'a SmtCertif.clause -> int * 'a SmtCertif.clause
val make_roots :
  SatAtom.Form.t SmtCertif.clause -> 'a SmtCertif.clause -> Term.constr
val interp_roots :
  SatAtom.Form.t SmtCertif.clause -> 'a SmtCertif.clause -> Term.constr
val sat_checker_modules : string list list
val parse_certif :
  Names.identifier -> Names.identifier -> string -> string -> unit
val cdimacs : Term.constr lazy_t
val ctheorem_checker : Term.constr lazy_t
val cchecker : Term.constr lazy_t
val theorems :
  (Term.constr ->
   SatAtom.Form.t SmtCertif.clause ->
   SatAtom.Form.t SmtCertif.clause -> Term.constr) ->
  Names.identifier -> string -> string -> unit
val theorem : Names.identifier -> string -> string -> unit
val theorem_abs : Names.identifier -> string -> string -> unit
val checker : string -> string -> unit
val export_clause : Format.formatter -> SatAtom.Form.t list -> unit
val export :
  out_channel ->
  int ->
  SatAtom.Form.t SmtCertif.clause ->
  (int, SatAtom.Form.t SmtCertif.clause) Hashtbl.t *
  SatAtom.Form.t SmtCertif.clause
val call_zchaff :
  int ->
  SatAtom.Form.t SmtCertif.clause ->
  (int, SatAtom.Form.t SmtCertif.clause) Hashtbl.t * string * string *
  SatAtom.Form.t SmtCertif.clause
val cnf_checker_modules : string list list
val certif_ops :
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t
val ccertif : Term.constr lazy_t
val cCertif : Term.constr lazy_t
val cchecker_b_correct : Term.constr lazy_t
val cchecker_b : Term.constr lazy_t
val cchecker_eq_correct : Term.constr lazy_t
val cchecker_eq : Term.constr lazy_t
val build_body :
  SatAtom.Atom.reify_tbl ->
  SatAtom.Form.reify ->
  Term.constr ->
  Term.constr ->
  int * SatAtom.Form.t SmtCertif.clause -> Term.constr * Term.constr
val build_body_eq :
  SatAtom.Atom.reify_tbl ->
  SatAtom.Form.reify ->
  Term.constr ->
  Term.constr ->
  Term.constr ->
  int * SatAtom.Form.t SmtCertif.clause -> Term.constr * Term.constr
val get_arguments : Term.constr -> Term.constr * Term.constr
exception Sat of int list
exception Finished
val input_int : in_channel -> int
val check_unsat : string -> unit
val make_proof :
  (int, 'a) SmtForm.gen_pform array ->
  Term.constr array ->
  Environ.env ->
  SatAtom.Form.reify ->
  SatAtom.Form.t -> int * SatAtom.Form.t SmtCertif.clause
val core_tactic : Environ.env -> 'a -> Term.types -> Structures.tactic
val tactic : unit -> Structures.tactic

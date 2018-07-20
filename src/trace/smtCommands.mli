val euf_checker_modules : string list list
val certif_ops :
  Term.constr array option ->
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
  Term.constr lazy_t
val cCertif : Term.constr lazy_t
val ccertif : Term.constr lazy_t
val cchecker : Term.constr lazy_t
val cchecker_correct : Term.constr lazy_t
val cchecker_b_correct : Term.constr lazy_t
val cchecker_b : Term.constr lazy_t
val cchecker_eq_correct : Term.constr lazy_t
val cchecker_eq : Term.constr lazy_t
val compute_roots :
  SmtAtom.Form.t list -> SmtAtom.Form.t SmtCertif.clause -> int list
val interp_uf :
  (int, Term.constr) Hashtbl.t ->
  (int, Term.constr) Hashtbl.t -> SmtAtom.Form.t list -> Term.constr
val interp_conseq_uf :
  SmtAtom.Form.t list list * SmtAtom.Form.t list -> Term.types
val print_assm : Term.constr -> unit
val parse_certif :
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  SmtAtom.Btype.reify_tbl * SmtAtom.Op.reify_tbl * SmtAtom.Atom.reify_tbl *
  SmtAtom.Form.reify * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> unit
val interp_roots : SmtAtom.Form.t list -> Term.constr
val theorem :
  Names.identifier ->
  SmtAtom.Btype.reify_tbl * SmtAtom.Op.reify_tbl * SmtAtom.Atom.reify_tbl *
  SmtAtom.Form.reify * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> unit
val checker :
  SmtAtom.Btype.reify_tbl * SmtAtom.Op.reify_tbl * SmtAtom.Atom.reify_tbl *
  SmtAtom.Form.reify * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause -> unit
val build_body :
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  Term.constr ->
  Term.constr ->
  int * SmtAtom.Form.t SmtCertif.clause ->
  Term.constr * Term.constr * (Names.identifier * Term.types) list
val build_body_eq :
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  Term.constr ->
  Term.constr ->
  Term.constr ->
  int * SmtAtom.Form.t SmtCertif.clause ->
  Term.constr * Term.constr * (Names.identifier * Term.types) list
val get_arguments : Term.constr -> Term.constr * Term.constr
val make_proof :
  ('a ->
   'b ->
   SmtAtom.Form.t -> SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t -> 'c) ->
  'a -> 'b -> SmtAtom.Form.reify -> SmtAtom.Form.t -> 'c
val core_tactic :
  (SmtAtom.Btype.reify_tbl ->
   SmtAtom.Op.reify_tbl ->
   SmtAtom.Form.t ->
   SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
   int * SmtAtom.Form.t SmtCertif.clause) ->
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  Environ.env -> Evd.evar_map -> Term.constr -> Structures.tactic
val tactic :
  (SmtAtom.Btype.reify_tbl ->
   SmtAtom.Op.reify_tbl ->
   SmtAtom.Form.t ->
   SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
   int * SmtAtom.Form.t SmtCertif.clause) ->
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl -> SmtAtom.Form.reify -> Structures.tactic

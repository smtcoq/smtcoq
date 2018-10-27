val debug : bool
val import_trace :
  SmtAtom.Atom.reify_tbl -> SmtAtom.Form.reify -> string ->
  (SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t) option ->
  SmtAtom.Form.t list -> int * SmtAtom.Form.t SmtCertif.clause
val clear_all : unit -> unit
val import_all :
  string ->
  string ->
  SmtBtype.reify_tbl * SmtAtom.Op.reify_tbl * SmtAtom.Atom.reify_tbl *
  SmtAtom.Form.reify * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause
val parse_certif :
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier ->
  Names.identifier -> Names.identifier -> string -> string -> unit
val theorem : Names.identifier -> string -> string -> unit
val checker : string -> string -> unit
val export :
  out_channel ->
  SmtBtype.reify_tbl -> SmtAtom.Op.reify_tbl ->
  SmtAtom.Form.t list -> unit
val call_verit :
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  (SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t) option ->
  SmtAtom.Form.t list ->
  int * SmtAtom.Form.t SmtCertif.clause
val tactic : Term.constr list -> Structures.constr_expr list -> Structures.tactic

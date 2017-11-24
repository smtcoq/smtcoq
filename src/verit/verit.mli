val debug : bool
val import_trace :
  string ->
  (SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t) option ->
  int * SmtAtom.Form.t SmtCertif.clause
val clear_all : unit -> unit
val import_all :
  string ->
  string ->
  SmtAtom.Btype.reify_tbl * SmtAtom.Op.reify_tbl * SmtAtom.Atom.reify_tbl *
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
  SmtAtom.Btype.reify_tbl -> SmtAtom.Op.reify_tbl -> SmtAtom.Form.t -> unit
val call_verit :
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Form.t ->
  SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
  int * SmtAtom.Form.t SmtCertif.clause
val tactic : unit -> Proof_type.tactic

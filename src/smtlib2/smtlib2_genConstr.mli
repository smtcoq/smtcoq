val pp_symbol : Smtlib2_ast.symbol -> string
val string_of_symbol : Smtlib2_ast.symbol -> string
val identifier_of_qualidentifier :
  Smtlib2_ast.qualidentifier -> Smtlib2_ast.identifier
val string_type : string -> SmtAtom.btype
val sort_of_string : string -> SmtAtom.btype * 'a list
val sort_of_symbol : Smtlib2_ast.symbol -> SmtAtom.btype * 'a list
val string_of_identifier : Smtlib2_ast.identifier -> string
val string_of_qualidentifier : Smtlib2_ast.qualidentifier -> string
val sort_of_sort : Smtlib2_ast.sort -> (SmtAtom.btype * 'a list as 'a)
val declare_sort :
  SmtAtom.Btype.reify_tbl -> Smtlib2_ast.symbol -> SmtAtom.btype
val declare_fun :
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  Smtlib2_ast.symbol ->
  Smtlib2_ast.sort list -> Smtlib2_ast.sort -> SmtAtom.indexed_op
val make_root_specconstant :
  SmtAtom.Atom.reify_tbl -> Smtlib2_ast.specconstant -> SmtAtom.hatom
type atom_form = Atom of SmtAtom.Atom.t | Form of SmtAtom.Form.t
val make_root :
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify -> Smtlib2_ast.term -> SmtAtom.Form.t
val declare_commands :
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  SmtAtom.Form.t list -> Smtlib2_ast.command -> SmtAtom.Form.t list
val import_smtlib2 :
  SmtAtom.Btype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify -> string -> SmtAtom.Form.t list

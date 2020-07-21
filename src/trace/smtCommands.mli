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


val parse_certif :
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  Structures.id ->
  SmtBtype.reify_tbl * SmtAtom.Op.reify_tbl *
  SmtAtom.Atom.reify_tbl * SmtAtom.Form.reify *
  SmtAtom.Form.t list * int * SmtAtom.Form.t SmtCertif.clause ->
  unit

val checker_debug :
  SmtBtype.reify_tbl * SmtAtom.Op.reify_tbl *
  SmtAtom.Atom.reify_tbl * SmtAtom.Form.reify *
  SmtAtom.Form.t list * int * SmtAtom.Form.t SmtCertif.clause -> 'a

val theorem :
  Structures.id ->
  SmtBtype.reify_tbl * SmtAtom.Op.reify_tbl *
  SmtAtom.Atom.reify_tbl * SmtAtom.Form.reify *
  SmtAtom.Form.t list * int * SmtAtom.Form.t SmtCertif.clause ->
  unit

val checker :
  SmtBtype.reify_tbl * SmtAtom.Op.reify_tbl *
  SmtAtom.Atom.reify_tbl * SmtAtom.Form.reify *
  SmtAtom.Form.t list * int * SmtAtom.Form.t SmtCertif.clause ->
  unit

val tactic :
  (Environ.env ->
   SmtBtype.reify_tbl ->
   SmtAtom.Op.reify_tbl ->
   SmtAtom.Atom.reify_tbl ->
   SmtAtom.Form.reify ->
   SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
   SmtAtom.Form.t list ->
   (int * SmtAtom.Form.t SmtCertif.clause) option) ->
  SmtMisc.logic ->
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  SmtAtom.Atom.reify_tbl ->
  SmtAtom.Form.reify ->
  (Environ.env -> Structures.constr -> Structures.constr) ->
  Structures.constr list ->
  Structures.constr_expr list -> Structures.tactic


val model_string : Environ.env -> SmtBtype.reify_tbl -> 'a -> 'b -> 'c -> SExpr.t -> string

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


val skip_comment : SatParser.lex_buff -> unit
val parse_p_cnf : SatParser.lex_buff -> int
val mklit : int -> SatAtom.Form.reify -> int -> SatAtom.Form.t
val parse_clause :
  int -> SatAtom.Form.reify -> SatParser.lex_buff -> SatAtom.Form.t list
val parse_clauses :
  int ->
  SatAtom.Form.reify ->
  SatParser.lex_buff ->
  SatAtom.Form.t SmtCertif.clause -> SatAtom.Form.t SmtCertif.clause
val parse_cnf :
  string ->
  int * SatAtom.Form.t SmtCertif.clause * SatAtom.Form.t SmtCertif.clause

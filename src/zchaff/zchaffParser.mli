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


val _CL : string
val _INF : string
val _VAR : string
val _L : string
val _V : string
val _A : string
val _LITS : string
val _CONF : string
val _EQ : string
val alloc_res :
  SmtTrace.trace_state ->
  'a SmtCertif.clause ->
  'a SmtCertif.clause ->
  'a SmtCertif.clause ->
  'a SmtCertif.clause list -> 'a SmtCertif.clause
val parse_tailres : (int, 'a) Hashtbl.t -> SatParser.lex_buff -> 'a list
val parse_resolution :
  SmtTrace.trace_state ->
  (int, 'a SmtCertif.clause) Hashtbl.t ->
  SatParser.lex_buff -> 'a SmtCertif.clause -> 'a SmtCertif.clause
val parse_CL :
  SmtTrace.trace_state ->
  (int, 'a SmtCertif.clause) Hashtbl.t ->
  SatParser.lex_buff -> 'a SmtCertif.clause -> 'a SmtCertif.clause
type var_key = Var of int | Level of int
type 'hform var_decl = {
  var : int;
  ante : 'hform SmtCertif.clause;
  ante_val : int list;
  mutable vclause : 'hform SmtCertif.clause option;
}
type 'hform parse_var_info = (var_key, 'hform var_decl) Hashtbl.t
val var_of_lit : int -> int
val parse_zclause : SatParser.lex_buff -> int list
val parse_VAR_CONF :
  SmtTrace.trace_state ->
  (int, 'a SmtCertif.clause) Hashtbl.t ->
  SatParser.lex_buff -> 'a SmtCertif.clause -> 'a SmtCertif.clause
val parse_proof :
  SmtTrace.trace_state ->
  (int, 'a SmtCertif.clause) Hashtbl.t ->
  string -> 'a SmtCertif.clause -> 'a SmtCertif.clause

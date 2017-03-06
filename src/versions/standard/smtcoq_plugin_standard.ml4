(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand    *                                                *)
(*     Benjamin Grégoire *                                                *)
(*     Chantal Keller    *                                                *)
(*     Alain Mebsout     ♯                                                *)
(*     Burak Ekici       ♯                                                *)
(*                                                                        *)
(*     * Inria - École Polytechnique - Université Paris-Sud               *)
(*     ♯ The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


DECLARE PLUGIN "smtcoq_plugin"

VERNAC COMMAND EXTEND Vernac_zchaff
| [ "Parse_certif_zchaff" 
    ident(dimacs) ident(trace) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.parse_certif dimacs trace fdimacs fproof
  ]
| [ "Zchaff_Checker" string(fdimacs) string(fproof) ] ->
  [
    Zchaff.checker fdimacs fproof
  ]
| [ "Zchaff_Theorem" ident(name) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.theorem name fdimacs fproof
  ]
END

VERNAC COMMAND EXTEND Vernac_verit
| [ "Parse_certif_verit"
    ident(t_i) ident(t_func) ident(t_atom) ident(t_form) ident(root) ident(used_roots) ident(trace) string(fsmt) string(fproof) ] ->
  [
    Verit.parse_certif t_i t_func t_atom t_form root used_roots trace fsmt fproof
  ]
| [ "Verit_Checker" string(fsmt) string(fproof) ] ->
  [
    Verit.checker fsmt fproof
  ]
| [ "Verit_Checker_Debug" string(fsmt) string(fproof) ] ->
  [
    Verit.checker_debug fsmt fproof
  ]
| [ "Verit_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Verit.theorem name fsmt fproof
  ]
END

VERNAC COMMAND EXTEND Vernac_lfsc
| [ "Parse_certif_lfsc"
    ident(t_i) ident(t_func) ident(t_atom) ident(t_form) ident(root) ident(used_roots) ident(trace) string(fsmt) string(fproof) ] ->
  [
    Lfsc.parse_certif t_i t_func t_atom t_form root used_roots trace fsmt fproof
  ]
| [ "Lfsc_Checker" string(fsmt) string(fproof) ] ->
  [
    Lfsc.checker fsmt fproof
  ]
| [ "Lfsc_Checker_Debug" string(fsmt) string(fproof) ] ->
  [
    Lfsc.checker_debug fsmt fproof
  ]
| [ "Lfsc_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Lfsc.theorem name fsmt fproof
  ]
END

TACTIC EXTEND Tactic_zchaff
| [ "zchaff_bool" ] -> [ Zchaff.tactic () ]
| [ "zchaff_bool_no_check" ] -> [ Zchaff.tactic_no_check () ]
END

TACTIC EXTEND Tactic_verit
| [ "verit_bool" ] -> [ Verit.tactic () ]
| [ "verit_bool_no_check" ] -> [ Verit.tactic_no_check () ]
END

TACTIC EXTEND Tactic_cvc4
| [ "cvc4_bool" ] -> [ Lfsc.tactic () ]
| [ "cvc4_bool_no_check" ] -> [ Lfsc.tactic_no_check () ]
END

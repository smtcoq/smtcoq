(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


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

VERNAC COMMAND EXTEND Vernac_zchaff_abs
| [ "Zchaff_Theorem_Abs" ident(name) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.theorem_abs name fdimacs fproof
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
| [ "Verit_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Verit.theorem name fsmt fproof
  ]
END


TACTIC EXTEND Tactic_zchaff
| [ "zchaff" ] -> [ Zchaff.tactic () ]
END

let lemmas_list = ref []

VERNAC COMMAND EXTEND Add_lemma
| [ "Add_lemmas" constr_list(lems) ] -> [ lemmas_list := lems @ !lemmas_list ]
| [ "Clear_lemmas" ] -> [ lemmas_list := [] ]
END


TACTIC EXTEND Tactic_verit
| [ "verit_base" constr_list(lpl) ] -> [ Verit.tactic lpl !lemmas_list ]
END

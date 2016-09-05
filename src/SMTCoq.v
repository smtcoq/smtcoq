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


Require Export Int63 List PArray.
Require Export SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace.
Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.

Declare ML Module "smtcoq_plugin".

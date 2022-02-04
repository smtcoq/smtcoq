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


Require Export Int63 List.
Require Export SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances.
Require Export Tactics.
Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.
From Trakt Require Export Trakt.
Require Export Database_trakt.

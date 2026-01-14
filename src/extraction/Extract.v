(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import ExtrOCamlInt63.
From SMTCoq Require Import SMTCoq.

Set Extraction AccessOpaque.

Extraction "extraction/sat_checker.ml" Sat_Checker.checker.
Extraction "extraction/smt_checker.ml" Checker_Ext.checker_ext.

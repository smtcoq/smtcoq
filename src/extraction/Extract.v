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


Require Int63Native.
Require Import ExtractNative.
Require Import SMTCoq.

Extract Constant Int63Native.eqb => "fun i j -> ExtrNative.compare i j = ExtrNative.Eq".

Set Extraction AccessOpaque.

Extraction "extraction/sat_checker.ml" Sat_Checker.checker.
Extraction "extraction/smt_checker.ml" Euf_Checker.checker_ext.

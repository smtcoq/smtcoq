(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*     Burak Ekici                                                        *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*     The University of Iowa                                             *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import PropToBool.

Declare ML Module "smtcoq_plugin".

Ltac zchaff := (prop2bool; zchaff_bool; bool2prop).
Ltac verit := (prop2bool; verit_bool; bool2prop).
Ltac cvc4 := (prop2bool; cvc4_bool; bool2prop).

Ltac smt := (prop2bool; try verit; cvc4_bool; try verit_bool; bool2prop).

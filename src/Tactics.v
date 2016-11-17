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

Ltac zchaff := (prop2bool; zchaff_bool). 
Ltac verit := (prop2bool; verit_bool). 
Ltac cvc4 := (prop2bool; cvc4_bool). 

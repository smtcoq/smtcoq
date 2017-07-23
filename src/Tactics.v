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

Require Import SMT_classes SMT_terms PropToBool BoolToProp.

Declare ML Module "smtcoq_plugin".

Ltac zchaff          := prop2bool; zchaff_bool; bool2prop.
Ltac zchaff_no_check := prop2bool; zchaff_bool_no_check; bool2prop.

Ltac verit           := prop2bool; verit_bool; bool2prop.
Ltac verit_no_check  := prop2bool; verit_bool_no_check; bool2prop.

Ltac cvc4            := prop2bool; cvc4_bool; bool2prop.
Ltac cvc4_no_check   := prop2bool; cvc4_bool_no_check; bool2prop.


(* Ltac smt := prop2bool; *)
(*             repeat *)
(*               match goal with *)
(*                 | [ |- context[ CompDec ?t ] ] => try assumption *)
(*                 | [ |- _ : bool] => verit_bool *)
(*                 | [ |- _ : bool] => try (cvc4_bool; verit_bool) *)
(*               end; *)
(*             bool2prop. *)
(* Ltac smt_no_check := prop2bool; *)
(*             repeat *)
(*               match goal with *)
(*                 | [ |- context[ CompDec ?t ] ] => try assumption *)
(*                 | [ |- _ : bool] => verit_bool_no_check *)
(*                 | [ |- _ : bool] => try (cvc4_bool_no_check; verit_bool_no_check) *)
(*               end; *)
(*             bool2prop. *)

Ltac smt := (prop2bool; try verit_bool; cvc4_bool; try verit_bool; bool2prop).
Ltac smt_no_check := (prop2bool; try verit_bool_no_check; cvc4_bool_no_check; try verit_bool_no_check; bool2prop).

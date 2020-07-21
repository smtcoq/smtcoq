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


Require Import PropToBool BoolToProp.  (* Before SMTCoq.State *)
Require Import Int63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.

Declare ML Module "smtcoq_plugin".


Tactic Notation "verit_bool" constr_list(h) :=
  verit_bool_base h; vauto.

Tactic Notation "verit_bool_no_check" constr_list(h) :=
  verit_bool_no_check_base h; vauto.


(** Tactics in Prop **)

Ltac zchaff          := prop2bool; zchaff_bool; bool2prop.
Ltac zchaff_no_check := prop2bool; zchaff_bool_no_check; bool2prop.

Tactic Notation "verit" constr_list(h) := prop2bool; verit_bool h; bool2prop.
Tactic Notation "verit_no_check" constr_list(h) := prop2bool; verit_bool_no_check h; bool2prop.

Ltac cvc4            := prop2bool; cvc4_bool; bool2prop.
Ltac cvc4_no_check   := prop2bool; cvc4_bool_no_check; bool2prop.
Ltac cvc4_admit      := prop2bool; cvc4_bool_admit; bool2prop.


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

Tactic Notation "smt" constr_list(h) := (prop2bool; try verit_bool h; cvc4_bool; try verit_bool h; bool2prop).
Tactic Notation "smt_no_check" constr_list(h) := (prop2bool; try verit_bool_no_check h; cvc4_bool_no_check; try verit_bool_no_check h; bool2prop).



(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

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
Require Import Int63 List PArray Bool.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances.

Declare ML Module "smtcoq_plugin".


(** Handling quantifiers with veriT **)

(* verit silently transforms an <implb a b> into a <or (not a) b> when
 instantiating a quantified theorem with <implb> *)
Lemma impl_split a b:
  implb a b = true -> orb (negb a) b = true.
Proof.
  intro H.
  destruct a; destruct b; trivial.
(* alternatively we could do <now verit_base H.> but it forces us to have veriT
   installed when we compile SMTCoq. *)
Qed.

Hint Resolve impl_split.

(* verit silently transforms an <implb (a || b) c> into a <or (not a) c>
   or into a <or (not b) c> when instantiating such a quantified theorem *)
Lemma impl_or_split_right a b c:
  implb (a || b) c = true -> negb b || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma impl_or_split_left a b c:
  implb (a || b) c = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

(* verit considers equality modulo its symmetry, so we have to recover the
   right direction in the instances of the theorems *)
Definition hidden_eq a b := a =? b.
Ltac all_rew :=
  repeat match goal with
         | [ |- context [ ?A =? ?B]] =>
           change (A =? B) with (hidden_eq A B)
         end;
  repeat match goal with
         | [ |- context [ hidden_eq ?A ?B] ] =>
           replace (hidden_eq A B) with (B =? A);
           [ | now rewrite Z.eqb_sym]
         end.

(* An automatic tactic that takes into account all those transformations *)
Ltac vauto :=
  try (let H := fresh "H" in
       intro H; try (all_rew; apply H);
       match goal with
       | [ |- is_true (negb ?A || ?B) ] =>
         try (eapply impl_or_split_right; apply H);
         eapply impl_or_split_left; apply H
       end;
       apply H);
  auto.

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

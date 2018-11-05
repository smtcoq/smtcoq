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


Require Export PropToBool BoolToProp.  (* Before SMTCoq.State *)
Require Export Int63 List PArray.
Require Export SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances.
Require Export Tactics.
Require Export Conversion_tactics.
Export Atom Form Sat_Checker Cnf_Checker Euf_Checker.

(* Declare ML Module "smtcoq_plugin". *)

Require Import Bool.
Open Scope Z_scope.

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
  implb (a || b) c -> negb b || c.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma impl_or_split_left a b c:
  implb (a || b) c -> negb a || c.
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

Ltac verit :=
  verit_base; vauto.

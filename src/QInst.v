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


Require Import Bool ZArith.
Require Import State SMT_classes.


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
Lemma eqb_of_compdec_sym (A:Type) (HA:CompDec A) (a b:A) :
  eqb_of_compdec HA b a = eqb_of_compdec HA a b.
Proof.
  destruct (@eq_dec _ (@Decidable _ HA) a b) as [H|H].
  - now rewrite H.
  - case_eq (eqb_of_compdec HA a b).
    + now rewrite <- !(@compdec_eq_eqb _ HA).
    + intros _. case_eq (eqb_of_compdec HA b a); auto.
      intro H1. elim H. symmetry. now rewrite compdec_eq_eqb.
Qed.

Definition hidden_eq_Z (a b : Z) := (a =? b)%Z.
Definition hidden_eq_U (A:Type) (HA:CompDec A) (a b : A) := eqb_of_compdec HA a b.
Ltac apply_sym_hyp T :=
  repeat match T with
         | context [ (?A =? ?B)%Z] =>
           change (A =? B)%Z with (hidden_eq_Z A B) in T
         end;
  repeat match T with
         | context [ @eqb_of_compdec ?A ?HA ?a ?b ] =>
           change (eqb_of_compdec HA a b) with (hidden_eq_U A HA a b) in T
         end;
  repeat match T with
         | context [ hidden_eq_Z ?A ?B] =>
           replace (hidden_eq_Z A B) with (B =? A)%Z in T;
           [ | now rewrite Z.eqb_sym]
         end;
  repeat match T with
         | context [ hidden_eq_U ?A ?HA ?a ?b] =>
           replace (hidden_eq_U A HA a b) with (eqb_of_compdec HA b a) in T;
           [ | now rewrite eqb_of_compdec_sym]
         end.
Ltac apply_sym_goal :=
  repeat match goal with
         | [ |- context [ (?A =? ?B)%Z] ] =>
           change (A =? B)%Z with (hidden_eq_Z A B)
         end;
  repeat match goal with
         | [ |- context [ @eqb_of_compdec ?A ?HA ?a ?b ] ] =>
           change (eqb_of_compdec HA a b) with (hidden_eq_U A HA a b)
         end;
  repeat match goal with
         | [ |- context [ hidden_eq_Z ?A ?B] ] =>
           replace (hidden_eq_Z A B) with (B =? A)%Z;
           [ | now rewrite Z.eqb_sym]
         end;
  repeat match goal with
         | [ |- context [ hidden_eq_U ?A ?HA ?a ?b] ] =>
           replace (hidden_eq_U A HA a b) with (eqb_of_compdec HA b a);
           [ | now rewrite eqb_of_compdec_sym]
         end.

(* An automatic tactic that takes into account all those transformations *)
Ltac vauto :=
  try (let H := fresh "H" in
       intro H;
       try apply H;
       try (apply_sym_goal; apply H);
       try (apply_sym_hyp H; apply H);
       try (apply_sym_goal; apply_sym_hyp H; apply H);
       match goal with
       | [ |- is_true (negb ?A || ?B) ] =>
         try (eapply impl_or_split_right; apply H);
         eapply impl_or_split_left; apply H
       end
      );
  auto.



(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

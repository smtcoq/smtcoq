(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
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

Lemma impl2_split a b c:
  implb a (implb b c) = true -> (negb a) || (negb b) || c = true.
Proof.
  intro H.
  destruct a; destruct b; destruct c; trivial.
Qed.

Lemma impl_split2 a b c:
  implb a (b || c) = true -> (negb a) || b || c = true.
Proof.
  intro H.
  destruct a; destruct b; trivial.
(* alternatively we could do <now verit_base H.> but it forces us to have veriT
   installed when we compile SMTCoq. *)
Qed.

Lemma impl_split211 a b1 b2 c1 c2 :
  implb a ((b1 && b2) || (c1 && c2)) = true -> (negb a) || b1 || c1 = true.
Proof.
  intro H.
  destruct a; destruct b1; destruct b2; destruct c1; destruct c2; trivial.
Qed.

Lemma impl_split212 a b1 b2 c1 c2 :
  implb a ((b1 && b2) || (c1 && c2)) = true -> (negb a) || b1 || c2 = true.
Proof.
  intro H.
  destruct a; destruct b1; destruct b2; destruct c1; destruct c2; trivial.
Qed.

Lemma impl_split221 a b1 b2 c1 c2 :
  implb a ((b1 && b2) || (c1 && c2)) = true -> (negb a) || b2 || c1 = true.
Proof.
  intro H.
  destruct a; destruct b1; destruct b2; destruct c1; destruct c2; trivial.
Qed.

Lemma impl_split222 a b1 b2 c1 c2 :
  implb a ((b1 && b2) || (c1 && c2)) = true -> (negb a) || b2 || c2 = true.
Proof.
  intro H.
  destruct a; destruct b1; destruct b2; destruct c1; destruct c2; trivial.
Qed.


(** verit silently transforms an <implb (a || b) c> into a <or (not a) c>
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

(** same for Boolean equivalence, modulo symmetry *)
Lemma eqb_sym_or_split_right a b c:
  Bool.eqb c (a || b) = true -> negb b || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_sym_or_split_left a b c:
  Bool.eqb c (a || b) = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_or_split_right a b c:
  Bool.eqb (a || b) c = true -> negb b || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_or_split_left a b c:
  Bool.eqb (a || b) c = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_or_split a b c:
  Bool.eqb c (a || b) = true -> negb c || a || b = true.
Proof.
  intro H.
  destruct a; destruct b; destruct c; intuition.
Qed.

(** verit silently transforms an <implb a (b && c)> into a <or (not a)
    b> or into a <or (not a) c> when instantiating such a quantified
    theorem. *)
Lemma impl_and_split_right a b c:
  implb a (b && c) = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
  now rewrite andb_false_r in H.
Qed.

Lemma impl_and_split_left a b c:
  implb a (b && c) = true -> negb a || b = true.
Proof.
  intro H.
  destruct a; destruct b; intuition.
Qed.


(** verit considers equality modulo its symmetry, so we have to recover the
    right direction in the instances of the theorems *)
(* TODO: currently incomplete *)

(* An auxiliary lemma to rewrite an eqb_of_compdec into its the symmetrical version *)
Lemma eqb_of_compdec_sym (A:Type) (HA:CompDec A) (a b:A) :
  eqb_of_compdec HA b a = eqb_of_compdec HA a b.
Proof. apply eqb_sym2. Qed.

(* Strategy: change or not the order of each equality in the goal
   Complete but exponential in some cases *)
Definition hidden_eq_Z (a b : Z) := (a =? b)%Z.
Definition hidden_eq_U (A:Type) (HA:CompDec A) (a b : A) := eqb_of_compdec HA a b.
Ltac apply_sym H :=
  lazymatch goal with
  | [ |- context [ (?A =? ?B)%Z ] ] =>
    first [ change (A =? B)%Z with (hidden_eq_Z A B); apply_sym H
          | replace (A =? B)%Z with (hidden_eq_Z B A); [apply_sym H | now rewrite Z.eqb_sym] ]
  | [ |- context [ @eqb_of_compdec ?A ?HA ?a ?b ] ] =>
    first [ change (eqb_of_compdec HA a b) with (hidden_eq_U A HA a b); apply_sym H
          | replace (eqb_of_compdec HA a b) with (hidden_eq_U A HA b a); [apply_sym H | now rewrite eqb_of_compdec_sym] ]
  | _ => apply H
  end.


(* An automatic tactic that takes into account all those transformations *)
Ltac vauto :=
  try (unfold is_true;
       let H := fresh "H" in
       intro H;
       first [ apply_sym H
             | match goal with
               | [ |- (negb ?A || ?B) = true ] =>
                 first [ eapply impl_split; apply_sym H
                       | eapply impl_or_split_right; apply_sym H
                       | eapply impl_or_split_left; apply_sym H
                       | eapply eqb_sym_or_split_right; apply_sym H
                       | eapply eqb_sym_or_split_left; apply_sym H
                       | eapply eqb_or_split_right; apply_sym H
                       | eapply eqb_or_split_left; apply_sym H
                       | eapply impl_and_split_right; apply_sym H
                       | eapply impl_and_split_left; apply_sym H
                       ]
               | [ |- (negb ?A || ?B || ?C) = true ] =>
                 first [ eapply impl2_split; apply_sym H
                       | eapply eqb_or_split; apply_sym H
                       | eapply impl_split2; apply_sym H
                       | eapply impl_split211; apply_sym H
                       | eapply impl_split212; apply_sym H
                       | eapply impl_split221; apply_sym H
                       | eapply impl_split222; apply_sym H
                       ]
               end
             ]
      );
  auto with smtcoq_core.



(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

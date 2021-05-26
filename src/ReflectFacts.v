(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import
        Bool ZArith BVList Logic.

Local Coercion is_true : bool >-> Sortclass.

Section ReflectFacts.

Infix "-->" := implb (at level 60, right associativity) : bool_scope.

Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof.
 intros; destruct H; intuition.
 discriminate H.
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof.
 intros.
 destr_bool; constructor; try now apply H.
 unfold not. intros. apply H in H0. destruct H. easy.
Qed.

Lemma reflect_dec : forall P b, reflect P b -> {P} + {~P}.
Proof. intros; destruct H; [now left | now right]. Qed.

 Lemma implyP : forall (b1 b2: bool), reflect (b1 -> b2) (b1 --> b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma iffP : forall (b1 b2: bool), reflect (b1 <-> b2) (eqb b1 b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma implyP2 : forall (b1 b2 b3: bool), reflect (b1 -> b2 -> b3) (b1 --> b2 --> b3).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma andP : forall (b1 b2: bool), reflect (b1 /\ b2) (b1 && b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma orP : forall (b1 b2: bool), reflect (b1 \/ b2) (b1 || b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *.
        destruct H1 as [H1a | H1b ]; easy. left. easy. left. easy.
        right. easy.
 Qed.

 Lemma negP : forall (b: bool), reflect (~ b) (negb b).
 Proof. intros; apply iff_reflect; split;
        case_eq b; intros; try easy; try compute in *.
        contradict H0. easy.
 Qed.

 Lemma eqP : forall (b1 b2: bool), reflect (b1 = b2) (Bool.eqb b1 b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma FalseB : (false = true) <-> False.
 Proof. split; auto. discriminate. Qed.

 Lemma TrueB : (true = true) <-> True.
 Proof. split; auto. Qed.

End ReflectFacts.

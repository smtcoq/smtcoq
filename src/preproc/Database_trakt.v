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


From Trakt Require Import Trakt.


(* Boolean equality *)

Lemma eqbool_Booleqb_embedding: forall n m : bool, n = m <-> (Bool.eqb n m) = true.
Proof. intros n m. now rewrite Bool.eqb_true_iff. Qed.
Trakt Add Relation 2 (@eq bool) (Bool.eqb) (eqbool_Booleqb_embedding).


(* Boolean relations for Z *)

From Coq Require Import ZArith.


Lemma eqZ_Zeqb_embedding: forall n m : Z, n = m <-> (Z.eqb n m) = true.
Proof. intros n m. now rewrite Z.eqb_eq. Qed.
Trakt Add Relation 2 (@eq Z) (Z.eqb) (eqZ_Zeqb_embedding).

Lemma ltZ_Zltb_embedding: forall n m : Z, (n < m)%Z <-> (Z.ltb n m) = true.
Proof. intros n m. now rewrite Z.ltb_lt. Qed.
Trakt Add Relation 2 (@Z.lt) (Z.ltb) (ltZ_Zltb_embedding).

Lemma leZ_Zleb_embedding: forall n m : Z, (n <= m)%Z <-> (Z.leb n m) = true.
Proof. intros n m. now rewrite Z.leb_le. Qed.
Trakt Add Relation 2 (@Z.le) (Z.leb) (leZ_Zleb_embedding).

Lemma gtZ_Zgtb_embedding: forall n m : Z, (n > m)%Z <-> (Z.gtb n m) = true.
Proof. intros n m. rewrite Z.gtb_lt. now apply Z.gt_lt_iff. Qed.
Trakt Add Relation 2 (@Z.gt) (Z.gtb) (gtZ_Zgtb_embedding).

Lemma geZ_Zgeb_embedding: forall n m : Z, (n >= m)%Z <-> (Z.geb n m) = true.
Proof. intros n m. rewrite Z.geb_le. now apply Z.ge_le_iff. Qed.
Trakt Add Relation 2 (@Z.ge) (Z.geb) (geZ_Zgeb_embedding).

Goal forall (x y : Z), ((x < y)%Z \/ x = y \/ (x > y)%Z) /\ ((x <= y)%Z \/ (x >= y)%Z).
Proof.
  trakt Z bool.
Abort.


(* Embedding for nat *)

Section Relations_nat.

  (* Embedding *)
  Lemma nat_Z_FBInverseProof : forall (n : nat), n = Z.to_nat (Z.of_nat n).
  Proof. intro n; symmetry; apply Nat2Z.id. Qed.

  Lemma nat_Z_BFPartialInverseProof_bool : forall (z : Z), (0 <=? z)%Z = true ->
                                                           Z.of_nat (Z.to_nat z) = z.
  Proof. intros Z H; apply Z2Nat.id; apply Zle_is_le_bool; assumption. Qed.

  Lemma nat_Z_ConditionProof_bool : forall (n : nat), (0 <=? Z.of_nat n)%Z = true.
  Proof. intros n. rewrite <- Zle_is_le_bool. apply Zle_0_nat. Qed.

  (* Addition *)
  Lemma Natadd_Zadd_embedding_equality : forall (n m : nat),
      Z.of_nat (n + m)%nat = ((Z.of_nat n) + (Z.of_nat m))%Z.
  Proof. apply Nat2Z.inj_add. Qed.

  (* Subtraction *)
  Lemma Natsub_Zsub_embedding_equality : forall (n m : nat),
    Z.of_nat (n - m)%nat = (if Z.leb (Z.of_nat n) (Z.of_nat m) then 0%Z else (Z.of_nat n) - (Z.of_nat m))%Z.
  Proof. intros n m. destruct (Z.of_nat n <=? Z.of_nat m)%Z eqn:E.
      - apply Zle_is_le_bool in E. apply Nat2Z.inj_le in E. rewrite <- Nat.sub_0_le in E.
      rewrite E. reflexivity.
      - apply Nat2Z.inj_sub. rewrite Z.leb_nle in E. apply Znot_le_gt in E. apply
      Z.gt_lt in E. apply Z.lt_le_incl in E. rewrite Nat2Z.inj_le. assumption. Qed.

  (* Multiplication *)
  Lemma Natmul_Zmul_embedding_equality : forall (n m : nat),
      Z.of_nat (n * m)%nat = ((Z.of_nat n) * (Z.of_nat m))%Z.
  Proof. apply Nat2Z.inj_mul. Qed.

  (* Zero *)
  Lemma zero_nat_Z_embedding_equality : Z.of_nat O = 0%Z.
  Proof. reflexivity. Qed.

  (* Successor *)
  Lemma S_Zadd1_embedding_equality : forall (n : nat), Z.of_nat (S n) = Z.add 1%Z (Z.of_nat n).
  Proof. intros n.
  rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Z.add_comm. reflexivity. Qed.

  (* Equality *)
  Lemma eq_Zeqb_embedding : forall (n m : nat),
      n = m <-> (Z.eqb (Z.of_nat n) (Z.of_nat m)) = true.
  Proof. intros ; split.
    - intros H. apply inj_eq in H. rewrite <- Z.eqb_eq in H. assumption.
    - intros H. rewrite Z.eqb_eq in H. rewrite <- Nat2Z.inj_iff.
    assumption. Qed.

  Lemma Nateqb_Zeqb_embedding_equality : forall (n m : nat),
      Nat.eqb n m = (Z.eqb (Z.of_nat n) (Z.of_nat m)).
  Proof.
  intros n m. destruct (n =? m) eqn:E.
  rewrite Nat.eqb_eq in E. rewrite eq_Zeqb_embedding in E. symmetry. assumption.
  apply beq_nat_false in E. rewrite eq_Zeqb_embedding in E. destruct (Z.of_nat n =? Z.of_nat m)%Z.
  now elim E. reflexivity. Qed.

  (* Less or equal *)
  Lemma le_Zleb_embedding : forall (n m : nat),
      n <= m <-> (Z.leb (Z.of_nat n) (Z.of_nat m)) = true.
  Proof. intros n m. split.
    - intros H. apply Zle_imp_le_bool.
      apply Nat2Z.inj_le. assumption.
    - intros H. apply Zle_is_le_bool in H. apply Nat2Z.inj_le in H. assumption. Qed.

  Lemma Natleb_Zleb_embedding_equality : forall (n m : nat),
      n <=? m = (Z.leb (Z.of_nat n) (Z.of_nat m)).
  Proof.
  intros n m.
  destruct (n <=? m) eqn:E.
  - symmetry. apply leb_complete in E. apply Nat2Z.inj_le in E.
apply Zle_is_le_bool. assumption.
  - apply leb_iff_conv in E. symmetry. apply Z.leb_gt. apply inj_lt in E. assumption.
  Qed.

  (* Less than *)
  Lemma lt_Zltb_embedding : forall (n m : nat),
      n < m <-> (Z.ltb (Z.of_nat n) (Z.of_nat m)) = true.
  Proof. intros n m. rewrite Nat2Z.inj_lt. apply Zlt_is_lt_bool. Qed.


  Lemma Natltb_Zltb_embedding_equality : forall (n m : nat),
      n <? m = (Z.ltb (Z.of_nat n) (Z.of_nat m)).
  Proof. intros n m. destruct (n<?m) eqn: E.
  - symmetry. apply Zlt_is_lt_bool. apply Nat.ltb_lt in E.
apply Nat2Z.inj_lt. assumption.
  - symmetry. apply Z.ltb_nlt. apply Nat.ltb_nlt in E.
unfold not. intro H.
apply Nat2Z.inj_lt in H. unfold not in E. apply E in H. assumption. Qed.

  (* Greater or equal *)
  Lemma ge_Zgeb_embedding : forall (n m : nat),
      n >= m <-> (Z.geb (Z.of_nat n) (Z.of_nat m)) = true.
   Proof. intros n m. split.
    - intro H. apply geZ_Zgeb_embedding. apply Nat2Z.inj_ge. assumption.
    - intro H. apply geZ_Zgeb_embedding in H. apply Nat2Z.inj_ge. assumption.
  Qed.

  (* Greater than *)
  Lemma gt_Zgtb_embedding : forall (n m : nat),
      n > m <-> (Z.gtb (Z.of_nat n) (Z.of_nat m)) = true.
  Proof. intros n m. split.
    - intro H. apply Zgt_is_gt_bool. apply Nat2Z.inj_gt. assumption.
    - intro H. apply Zgt_is_gt_bool in H. apply Nat2Z.inj_gt. assumption.
  Qed.

End Relations_nat.

Trakt Add Embedding
      (nat) (Z) (Z.of_nat) (Z.to_nat) (nat_Z_FBInverseProof) (nat_Z_BFPartialInverseProof_bool)
      (nat_Z_ConditionProof_bool).

Trakt Add Symbol (Init.Nat.add) (Z.add) (Natadd_Zadd_embedding_equality).
(* TODO: add subtraction? *)
Trakt Add Symbol (Init.Nat.mul) (Z.mul) (Natmul_Zmul_embedding_equality).
Trakt Add Symbol (O) (0%Z) (zero_nat_Z_embedding_equality).
Trakt Add Symbol (S) (Z.add 1%Z) (S_Zadd1_embedding_equality).
Trakt Add Symbol (Nat.eqb) (Z.eqb) (Nateqb_Zeqb_embedding_equality).
Trakt Add Symbol (Nat.leb) (Z.leb) (Natleb_Zleb_embedding_equality).
Trakt Add Symbol (Nat.ltb) (Z.ltb) (Natltb_Zltb_embedding_equality).

Trakt Add Relation 2 (@eq nat) (Z.eqb) (eq_Zeqb_embedding).
Trakt Add Relation 2 (le) (Z.leb) (le_Zleb_embedding).
Trakt Add Relation 2 (lt) (Z.ltb) (lt_Zltb_embedding).
Trakt Add Relation 2 (ge) (Z.geb) (ge_Zgeb_embedding).
Trakt Add Relation 2 (gt) (Z.gtb) (gt_Zgtb_embedding).

(* Goal 3%nat = 3%nat. *)
(* Proof. trakt Z bool. Abort. *)

(* Goal Nat.eqb 3%nat 3%nat = true. *)
(* Proof. trakt Z bool. Abort. *)

(* Goal (3+4)%nat = 7%nat. *)
(* Proof. trakt Z bool. Abort. *)

(* Goal forall (x y:nat), x <= x + y. *)
(* Proof. trakt Z bool. Abort. *)


(* Embedding for positive *)

Require Import PArith.

Section Relations_positive.

  (* Embedding *)
  Lemma positive_Z_FBInverseProof : forall (n : positive), n = Z.to_pos (Z.pos n).
  Proof.
    intros n. reflexivity.
  Qed.

  Lemma positive_Z_BFPartialInverseProof_bool : forall (z : Z), (0 <? z)%Z = true ->
                                                           Z.pos (Z.to_pos z) = z.
  Proof.
    intros z.
    destruct z eqn: E.
    - discriminate.
    - reflexivity.
    - discriminate.
  Qed.

  Lemma positive_Z_ConditionProof_bool : forall (n : positive), (0 <? Z.pos n)%Z = true.
  Proof.
    intros n. reflexivity.
  Qed.

  (* Addition *)
  Lemma Positiveadd_Zadd_embedding_equality : forall (n m : positive),
      Z.pos (n + m)%positive = ((Z.pos n) + (Z.pos m))%Z.
  Proof.
    intros n m. reflexivity.
  Qed.

  (* Subtraction *)
  Lemma Positivesub_Zsub_embedding_equality : forall (n m : positive),
    Z.pos (n - m)%positive = (if Z.leb (Z.pos n) (Z.pos m) then 1%Z else (Z.pos n) - (Z.pos m))%Z.
  Proof.
    intros n m. destruct (Z.pos n <=? Z.pos m)%Z eqn:E.
    - rewrite <- Pos2Z.inj_leb in E. apply Pos.leb_le in E.
      apply Pos.sub_le in E.
      rewrite E. reflexivity.
    - apply Pos2Z.inj_sub.
      rewrite Z.leb_nle in E. apply Znot_le_gt in E.
      apply Z.gt_lt in E.
      assumption.
    Qed.

  (* Multiplication *)
  Lemma Positivemul_Zmul_embedding_equality : forall (n m : positive),
      Z.pos (n * m)%positive = ((Z.pos n) * (Z.pos m))%Z.
  Proof.
    intros n m. reflexivity.
  Qed.

  (* xH *)
  Lemma xH_one_Z_embedding_equality : Z.pos xH = 1%Z.
  Proof.
    reflexivity.
  Qed.

  (* xO *)
  Lemma xO_Zmul2_embedding_equality : forall (n : positive), Z.pos (xO n) = Z.mul 2%Z (Z.pos n).
  Proof.
    intros n. apply Pos2Z.pos_xO.
  Qed.

  (* xI *)
  Lemma xI_Zmul2Zadd1_embedding_equality : forall (n : positive), Z.pos (xI n) = Z.add 1%Z (Z.mul 2%Z (Z.pos n)).
  Proof.
    intros n.
    rewrite Z.add_comm.
    apply Pos2Z.pos_xI.
  Qed.


  (* Equality *)
  Lemma Positiveeq_Zeqb_embedding : forall (n m : positive),
      n = m <-> (Z.eqb (Z.pos n) (Z.pos m)) = true.

  Proof.
    intros n m .
    simpl.
    symmetry.
    apply Pos.eqb_eq.
  Qed.

  Lemma Positiveeqb_Zeqb_embedding_equality : forall (n m : positive),
      Pos.eqb n m = (Z.eqb (Z.pos n) (Z.pos m)).
  Proof.
    intros n m. simpl. reflexivity.
  Qed.

  (* Less or equal *)
  Lemma Positivele_Zleb_embedding : forall (n m : positive),
      (n <= m)%positive <-> (Z.leb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m .
    simpl.
    symmetry.
    apply Pos.leb_le.
  Qed.

  Lemma Positiveleb_Zleb_embedding_equality : forall (n m : positive),
      (n <=? m)%positive = (Z.leb (Z.pos n) (Z.pos m)).
  Proof.
    intros n m.
    unfold Z.leb. reflexivity.
  Qed.

  (* Less than *)
  Lemma Positivelt_Zltb_embedding : forall (n m : positive),
      (n < m)%positive <-> (Z.ltb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m .
    simpl.
    symmetry.
    apply Pos.ltb_lt.

  Qed.

  Lemma Positiveltb_Zltb_embedding_equality : forall (n m : positive),
      (n <? m)%positive = (Z.ltb (Z.pos n) (Z.pos m)).
  Proof.
    intros n m.
    reflexivity.
  Qed.

  (* Greater or equal *)
  Lemma Positivege_Zgeb_embedding : forall (n m : positive),
      (n >= m)%positive <-> (Z.geb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m.
    unfold Z.geb. simpl.
    rewrite Pos.ge_le_iff.
    rewrite <- Pos.compare_ge_iff.
    split; destruct (n ?= m)%positive eqn:E; congruence.
  Qed.

  (* Greater than *)
  Lemma Positivegt_Zgtb_embedding : forall (n m : positive),
      (n > m)%positive <-> (Z.gtb (Z.pos n) (Z.pos m)) = true.
  Proof.
    intros n m.
    unfold Z.gtb. simpl.
    rewrite Pos.gt_lt_iff.
    rewrite <- Pos.compare_gt_iff.
    split; destruct (n ?= m)%positive eqn:E; try reflexivity; discriminate.
  Qed.

End Relations_positive.

(* This would embed posities appearing in Z *)
(* Trakt Add Embedding *)
(*       (positive) (Z) (Z.pos) (Z.to_pos) (positive_Z_FBInverseProof) (positive_Z_BFPartialInverseProof_bool) *)
(*       (positive_Z_ConditionProof_bool). *)

(* Trakt Add Symbol (Pos.add) (Z.add) (Positiveadd_Zadd_embedding_equality). *)
(* (* TODO: add subtraction? *) *)
(* Trakt Add Symbol (Pos.mul) (Z.mul) (Positivemul_Zmul_embedding_equality). *)
(* Trakt Add Symbol (xH) (1%Z) (xH_one_Z_embedding_equality). *)
(* Trakt Add Symbol (xO) (Z.mul 2%Z) (xO_Zmul2_embedding_equality). *)
(* Trakt Add Symbol (xI) (fun z => Z.add 1%Z (Z.mul 2%Z z)) (xI_Zmul2Zadd1_embedding_equality). *)
(* Trakt Add Symbol (Pos.eqb) (Z.eqb) (Positiveeqb_Zeqb_embedding_equality). *)
(* Trakt Add Symbol (Pos.leb) (Z.leb) (Positiveleb_Zleb_embedding_equality). *)
(* Trakt Add Symbol (Pos.ltb) (Z.ltb) (Positiveltb_Zltb_embedding_equality). *)

(* Trakt Add Relation 2 (@eq positive) (Z.eqb) (Positiveeq_Zeqb_embedding). *)
(* Trakt Add Relation 2 (Pos.le) (Z.leb) (Positivele_Zleb_embedding). *)
(* Trakt Add Relation 2 (Pos.lt) (Z.ltb) (Positivelt_Zltb_embedding). *)
(* Trakt Add Relation 2 (Pos.ge) (Z.geb) (Positivege_Zgeb_embedding). *)
(* Trakt Add Relation 2 (Pos.gt) (Z.gtb) (Positivegt_Zgtb_embedding). *)


(* Embedding for N *)

Section Relations_N.

  (* Embedding *)
  Lemma N_Z_FBInverseProof : forall (n : N), n = Z.to_N (Z.of_N n).
  Proof. intros n ; symmetry ; apply N2Z.id. Qed.

  Lemma N_Z_BFPartialInverseProof_bool : forall (z : Z), (0 <=? z)%Z = true ->
                                                           Z.of_N (Z.to_N z) = z.
  Proof. intros z H. induction z.
  - reflexivity.
  - reflexivity.
  - assert (H1 : forall p : positive, (Z.neg p < 0)%Z) by apply Pos2Z.neg_is_neg.
    specialize (H1 p). apply Zle_bool_imp_le in H. apply Zle_not_lt in H.
    unfold not in H1. apply H in H1. elim H1. Qed.

  Lemma N_Z_ConditionProof_bool : forall (n : N), (0 <=? Z.of_N n)%Z = true.
  Proof. intros n. apply Zle_imp_le_bool. apply N2Z.is_nonneg. Qed.

  (* Addition *)
  Lemma Nadd_Zadd_embedding_equality : forall (n m : N),
      Z.of_N (n + m)%N = ((Z.of_N n) + (Z.of_N m))%Z.
  Proof.
    intros n m . apply N2Z.inj_add.
  Qed.

  (* Subtraction *)
  Lemma Nsub_Zsub_embedding_equality : forall (n m : N),
    Z.of_N (n - m)%N = (if Z.leb (Z.of_N n) (Z.of_N m) then 0%Z else (Z.of_N n) - (Z.of_N m))%Z.
  Proof.
    intros n m .
  destruct (Z.leb (Z.of_N n) (Z.of_N m)) eqn:E.
  - apply Zle_is_le_bool in E. apply N2Z.inj_le in E. rewrite <- N.sub_0_le in E.
      rewrite E. reflexivity.
  - apply N2Z.inj_sub. rewrite Z.leb_nle in E. apply Znot_le_gt in E. apply
      Z.gt_lt in E. apply Z.lt_le_incl in E. rewrite N2Z.inj_le. assumption.
  Qed.

  (* Multiplication *)
  Lemma Nmul_Zmul_embedding_equality : forall (n m : N),
      Z.of_N (n * m)%N = ((Z.of_N n) * (Z.of_N m))%Z.
  Proof.
    intros n m.
    apply N2Z.inj_mul.
  Qed.

  (* N0 *)
  Lemma N0_zero_Z_embedding_equality : Z.of_N N0 = 0%Z.
  Proof.
    reflexivity.
  Qed.

  (* Npos *)
  Lemma Npos_Z_embedding_equality : forall (n : positive), Z.of_N (Npos n) = Z.pos n.
  Proof.
    intros n. reflexivity.
  Qed.

  (* Equality *)
  Lemma Neq_Zeqb_embedding : forall (n m : N),
      n = m <-> (Z.eqb (Z.of_N n) (Z.of_N m)) = true.
  Proof.
  intros n m. split.
  - intros H. rewrite H.
    rewrite Z.eqb_refl. reflexivity.
  - intros H. apply Z.eqb_eq in H.
    apply N2Z.inj. assumption.
  Qed.


  Lemma Neqb_Zeqb_embedding_equality : forall (n m : N),
      N.eqb n m = (Z.eqb (Z.of_N n) (Z.of_N m)).
  Proof.
    intros n m.
    destruct ((n =? m)%N) eqn:E.
    - rewrite N.eqb_eq in E. rewrite Neq_Zeqb_embedding in E. symmetry. assumption.
    - apply N.eqb_neq in E. rewrite Neq_Zeqb_embedding in E.
      destruct (Z.of_N n =? Z.of_N m)%Z.
        * congruence.
        * reflexivity.
  Qed.

  (* Less or equal *)
  Lemma Nle_Zleb_embedding : forall (n m : N),
      (n <= m)%N <-> (Z.leb (Z.of_N n) (Z.of_N m)) = true.
  Proof.
    intros n m . split.
    - intros H. apply Zle_imp_le_bool.
      apply N2Z.inj_le. assumption.
    - intros H. apply Zle_is_le_bool in H. apply N2Z.inj_le in H. assumption.
  Qed.

  Lemma Nleb_Zleb_embedding_equality : forall (n m : N),
      (n <=? m)%N = (Z.leb (Z.of_N n) (Z.of_N m)).
  Proof.
    intros n m.
    destruct (n <=? m)%N eqn:E.
    - symmetry. apply N.leb_le in E. apply N2Z.inj_le in E.
      apply Zle_is_le_bool. assumption.
    - apply N.leb_gt in E. symmetry. apply Z.leb_gt. apply N2Z.inj_lt in E. assumption.
  Qed.

  (* Less than *)
  Lemma Nlt_Zltb_embedding : forall (n m : N),
      (n < m)%N <-> (Z.ltb (Z.of_N n) (Z.of_N m)) = true.
  Proof.
    intros n m. rewrite N2Z.inj_lt. apply Zlt_is_lt_bool.
  Qed.


  Lemma Nltb_Zltb_embedding_equality : forall (n m : N),
      (n <? m)%N = (Z.ltb (Z.of_N n) (Z.of_N m)).
  Proof.
    intros n m. destruct (n<?m)%N eqn: E.
    - symmetry. apply Zlt_is_lt_bool. apply N.ltb_lt in E.
      apply N2Z.inj_lt. assumption.
    - symmetry. apply Z.ltb_nlt. apply N.ltb_nlt in E.
      unfold not. intro H.
      apply N2Z.inj_lt in H. unfold not in E. apply E in H. assumption.
  Qed.

  (* Greater or equal *)
  Lemma Nge_Zgeb_embedding : forall (n m : N),
      (n >= m)%N <-> (Z.geb (Z.of_N n) (Z.of_N m)) = true.
  Proof.
    intros n m. split.
    - intro H. apply geZ_Zgeb_embedding. apply N2Z.inj_ge. assumption.
    - intro H. apply geZ_Zgeb_embedding in H. apply N2Z.inj_ge. assumption.
  Qed.

  (* Greater than *)
  Lemma Ngt_Zgtb_embedding : forall (n m : N),
      (n > m)%N <-> (Z.gtb (Z.of_N n) (Z.of_N m)) = true.
  Proof.
    intros n m. rewrite N2Z.inj_gt. apply Zgt_is_gt_bool.
  Qed.

End Relations_N.

Trakt Add Embedding
      (N) (Z) (Z.of_N) (Z.to_N) (N_Z_FBInverseProof) (N_Z_BFPartialInverseProof_bool)
      (N_Z_ConditionProof_bool).

Trakt Add Symbol (N.add) (Z.add) (Nadd_Zadd_embedding_equality).
(* TODO: add subtraction? *)
Trakt Add Symbol (N.mul) (Z.mul) (Nmul_Zmul_embedding_equality).
Trakt Add Symbol (N0) (0%Z) (N0_zero_Z_embedding_equality).
Trakt Add Symbol (Npos) (Z.pos) (Npos_Z_embedding_equality).
Trakt Add Symbol (N.eqb) (Z.eqb) (Neqb_Zeqb_embedding_equality).
Trakt Add Symbol (N.leb) (Z.leb) (Nleb_Zleb_embedding_equality).
Trakt Add Symbol (N.ltb) (Z.ltb) (Nltb_Zltb_embedding_equality).

Trakt Add Relation 2 (@eq N) (Z.eqb) (Neq_Zeqb_embedding).
Trakt Add Relation 2 (N.le) (Z.leb) (Nle_Zleb_embedding).
Trakt Add Relation 2 (N.lt) (Z.ltb) (Nlt_Zltb_embedding).
Trakt Add Relation 2 (N.ge) (Z.geb) (Nge_Zgeb_embedding).
Trakt Add Relation 2 (N.gt) (Z.gtb) (Ngt_Zgtb_embedding).


(* This is about Z, but it fails if we put it upper in the file...?? *)

(* Lemma Zneg_Zopp_embedding_equality : forall (x : positive), Zneg x = Z.opp (Zpos x).
Admitted.
Trakt Add Symbol (Zneg) (Z.opp) (Zneg_Zopp_embedding_equality). *)


(* Boolean predicates for other theories *)

Require Import BVList.

Lemma bv_eq_P2B (n:N) (a b:BITVECTOR_LIST.bitvector n) :
  a = b <-> BITVECTOR_LIST.bv_eq a b = true.
Proof. now rewrite BITVECTOR_LIST.bv_eq_reflect. Qed.

Lemma bv_ult_P2B (n:N) (a b:BITVECTOR_LIST.bitvector n) :
  BITVECTOR_LIST.bv_ultP (n:=n) a b <-> BITVECTOR_LIST.bv_ult (n:=n) a b = true.
Proof. now rewrite BITVECTOR_LIST.bv_ult_B2P. Qed.

Lemma bv_slt_P2B (n:N) (a b:BITVECTOR_LIST.bitvector n) :
  BITVECTOR_LIST.bv_sltP (n:=n) a b <-> BITVECTOR_LIST.bv_slt (n:=n) a b = true.
Proof. now rewrite BITVECTOR_LIST.bv_slt_B2P. Qed.

Trakt Add Relation 2
  (fun n => @eq (BITVECTOR_LIST.bitvector n))
  (@BITVECTOR_LIST.bv_eq)
  (bv_eq_P2B).

Trakt Add Relation 2
  (fun n => @BITVECTOR_LIST.bv_ultP n)
  (@BITVECTOR_LIST.bv_ult)
  (bv_ult_P2B).

Trakt Add Relation 2
  (fun n => @BITVECTOR_LIST.bv_sltP n)
  (@BITVECTOR_LIST.bv_slt)
  (bv_slt_P2B).


(* (* Tests *) *)
(* Import BITVECTOR_LIST. *)

(* Goal forall (a b : bitvector 42), *)
(*     a = b /\ bv_ultP a b /\ bv_sltP a b. *)
(* Proof. *)
(*   intros. trakt Z bool. *)
(* Abort. *)

(* Goal forall (a b c : bitvector 4), *)
(*     bv_and c a = c. *)
(* Proof. *)
(*   intros a b c. trakt Z bool. *)
(* Abort. *)


(* Require FArray. *)
(* Require Import SMT_classes. *)

(* Lemma farray_eq_P2B (key elt : Type) *)
(*   (keyC : CompDec key) (eltC : CompDec elt) *)
(*   (a b : FArray.farray key elt) : *)
(*   a = b <-> FArray.equal a b = true. *)
(* Proof. intros. now rewrite FArray.equal_iff_eq. Qed. *)

(* Trakt Add Relation 2 *)
(*   (fun key elt (keyC : CompDec key) (eltC : CompDec elt) => *)
(*      @eq (@FArray.farray key elt _ _)) *)
(*   (fun key elt (keyC : CompDec key) (eltC : CompDec elt) => *)
(*      @FArray.equal key elt _ _ _ _ _) *)
(*   (fun key elt (keyC : CompDec key) (eltC : CompDec elt) => *)
(*      farray_eq_P2B key elt keyC eltC). *)

(* (* Section Array. *) *)

(* (*   Variables (key elt : Type) *) *)
(* (*     (* (key_ord : SMT_classes.OrdType key) (key_comp : SMT_classes.Comparable key) *) *) *)
(* (*     (* (elt_ord : SMT_classes.OrdType elt) (elt_comp : SMT_classes.Comparable elt) *) *) *)
(* (*     (* (elt_inh : SMT_classes.Inhabited elt). *) *) *)
(* (*     (keyC : CompDec key) (eltC : CompDec elt). *) *)

(* (*   Lemma farray_eq_P2B (a b : FArray.farray key elt) : *) *)
(* (*     a = b <-> FArray.equal a b = true. *) *)
(* (*   Proof. intros. now rewrite FArray.equal_iff_eq. Qed. *) *)

(* (*   Trakt Add Relation 2 *) *)
(* (*     (@eq (@FArray.farray key elt _ _)) *) *)
(* (*     (FArray.equal (key:=key) (elt:=elt)) *) *)
(* (*     (farray_eq_P2B). *) *)

(* (*   Import FArray. *) *)

(* (*   Goal forall (a b : farray key elt), a = b. *) *)
(* (*     intros. trakt Z bool. *) *)
(* (*   Abort. *) *)

(* (* End Array. *) *)

(* (* Test *) *)
(* Import FArray. *)
(* Require Import SMT_classes_instances. *)

(* Goal forall (a b : farray Z Z), a = b. *)
(*   intros. trakt Z bool. *)
(* Abort. *)

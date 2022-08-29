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


From Trakt Require Import Trakt.


(* Boolean equality *)

Lemma eqbool_Booleqb_embedding: forall n m : bool, n = m <-> (Bool.eqb n m) = true.
Proof. intros n m. now rewrite Bool.eqb_true_iff. Qed.
Trakt Add Relation (@eq bool) (Bool.eqb) (eqbool_Booleqb_embedding).


(* Boolean relations for Z *)

From Coq Require Import ZArith.


Lemma eqZ_Zeqb_embedding: forall n m : Z, n = m <-> (Z.eqb n m) = true.
Proof. intros n m. now rewrite Z.eqb_eq. Qed.
Trakt Add Relation (@eq Z) (Z.eqb) (eqZ_Zeqb_embedding).

Lemma ltZ_Zltb_embedding: forall n m : Z, (n < m)%Z <-> (Z.ltb n m) = true.
Proof. intros n m. now rewrite Z.ltb_lt. Qed.
Trakt Add Relation (@Z.lt) (Z.ltb) (ltZ_Zltb_embedding).

Lemma leZ_Zleb_embedding: forall n m : Z, (n <= m)%Z <-> (Z.leb n m) = true.
Proof. intros n m. now rewrite Z.leb_le. Qed.
Trakt Add Relation (@Z.le) (Z.leb) (leZ_Zleb_embedding).

Lemma gtZ_Zgtb_embedding: forall n m : Z, (n > m)%Z <-> (Z.gtb n m) = true.
Proof. intros n m. rewrite Z.gtb_lt. now apply Z.gt_lt_iff. Qed.
Trakt Add Relation (@Z.gt) (Z.gtb) (gtZ_Zgtb_embedding).

Lemma geZ_Zgeb_embedding: forall n m : Z, (n >= m)%Z <-> (Z.geb n m) = true.
Proof. intros n m. rewrite Z.geb_le. now apply Z.ge_le_iff. Qed.
Trakt Add Relation (@Z.ge) (Z.geb) (geZ_Zgeb_embedding).

Goal forall (x y : Z), ((x < y)%Z \/ x = y \/ (x > y)%Z) /\ ((x <= y)%Z \/ (x >= y)%Z).
Proof.
  trakt Z bool.
Abort.

Lemma BinIntDeflebZ_eq_Zleb : forall x y, BinIntDef.Z.leb x y = Z.leb x y.
Proof. intros. reflexivity. Qed.

Trakt Add Relation (BinIntDef.Z.leb) (Z.leb) (BinIntDeflebZ_eq_Zleb).

Lemma BinIntDefltbZ_eq_Zltb : forall x y, BinIntDef.Z.ltb x y = Z.ltb x y.
Proof. intros. reflexivity. Qed.

Trakt Add Relation (BinIntDef.Z.ltb) (Z.ltb) (BinIntDefltbZ_eq_Zltb).

Lemma BinIntDefaddZ_eq_Zadd : forall x y, BinIntDef.Z.add x y = Z.add x y.
Proof. reflexivity. Qed.

Trakt Add Symbol (BinIntDef.Z.add) (Z.add) (BinIntDefaddZ_eq_Zadd).

Goal forall (x y : Z), ((BinIntDef.Z.ltb x y = true)%Z \/ (BinIntDef.Z.add x y > y)%Z) /\ ((BinIntDef.Z.leb x y = true)%Z).
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

  (* Successor *)
  Lemma S_Zadd1_embedding_equality : forall (n : nat), Z.of_nat (S n) = Z.add 1%Z (Z.of_nat n).
  Proof. intros n.
  rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Z.add_comm. reflexivity. Qed.

  (* Zero *)
  Lemma zero_nat_Z_embedding_equality : Z.of_nat O = 0%Z.
  Proof. reflexivity. Qed.

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
Trakt Add Symbol (Init.Nat.mul) (Z.mul) (Natmul_Zmul_embedding_equality).
Trakt Add Symbol (S) (Z.add 1%Z) (S_Zadd1_embedding_equality).
Trakt Add Symbol (O) (0%Z) (zero_nat_Z_embedding_equality).
Trakt Add Symbol (Nat.eqb) (Z.eqb) (Nateqb_Zeqb_embedding_equality).
Trakt Add Symbol (Nat.leb) (Z.leb) (Natleb_Zleb_embedding_equality).
Trakt Add Symbol (Nat.ltb) (Z.ltb) (Natltb_Zltb_embedding_equality).

Trakt Add Relation (@eq nat) (Z.eqb) (eq_Zeqb_embedding).
Trakt Add Relation (le) (Z.leb) (le_Zleb_embedding).
Trakt Add Relation (lt) (Z.ltb) (lt_Zltb_embedding).
Trakt Add Relation (ge) (Z.geb) (ge_Zgeb_embedding).
Trakt Add Relation (gt) (Z.gtb) (gt_Zgtb_embedding).

(* Goal 3%nat = 3%nat. *)
(* Proof. trakt Z bool. Abort. *)

(* Goal Nat.eqb 3%nat 3%nat = true. *)
(* Proof. trakt Z bool. Abort. *)

(* Goal (3+4)%nat = 7%nat. *)
(* Proof. trakt Z bool. Abort. *)

(* Goal forall (x y:nat), x <= x + y. *)
(* Proof. trakt Z bool. Abort. *)


(* Embedding for N (to be completed) *)

Section Relations_N.

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
  Proof.  intros n. apply Zle_imp_le_bool. apply N2Z.is_nonneg. Qed. 

End Relations_N.

Trakt Add Embedding
      (N) (Z) (Z.of_N) (Z.to_N) (N_Z_FBInverseProof) (N_Z_BFPartialInverseProof_bool)
      (N_Z_ConditionProof_bool).


(* This is about Z, but it fails if we put it upper in the file...?? *)

(* Lemma Zneg_Zopp_embedding_equality : forall (x : positive), Zneg x = Z.opp (Zpos x).
Admitted.
Trakt Add Symbol (Zneg) (Z.opp) (Zneg_Zopp_embedding_equality). *)

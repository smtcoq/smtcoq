(**************************************************************************)
(*                                                                        *)
(*     NDBitVector                                                        *)
(*     Copyright (C) 2016                                                 *)
(*                                                                        *)
(*     Tianyi  Liang                                                      *)
(*     Chantal Keller                                                     *)
(*     Alain   Mebsout                                                    *)
(*     Burak   Ekici                                                      *)
(*                                                                        *)
(*     The University of Iowa                                             *)
(*     LRI - Université Paris Sud - Université Paris Saclay               *)
(*                                                                        *)
(*   TODO: This file is distributed under the terms of SOME licence       *)
(*                                                                        *)
(**************************************************************************)


Require Import List Bool NArith Psatz.
Require Import Misc.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type RAWBITVECTOR.

Parameter bitvector: Type.
Parameter size     : bitvector -> N.
Parameter bits     : bitvector -> list bool.
(*property*)
Parameter bv_wf    : bitvector -> Prop.

(*equality*)
Parameter bv_eq    : bitvector -> bitvector -> bool.

(*binary operations*)
Parameter bv_concat: bitvector -> bitvector -> bitvector.
Parameter bv_and   : bitvector -> bitvector -> bitvector.
Parameter bv_add   : bitvector -> bitvector -> bitvector.
Parameter bv_mult  : bitvector -> bitvector -> bitvector.
(*
Parameter bv_subs  : bitvector -> bitvector -> bitvector.
Parameter bv_div   : bitvector -> bitvector -> bitvector.
Parameter bv_or    : bitvector -> bitvector -> bitvector.
*)
(*unary operations*)
Parameter bv_not   : bitvector -> bitvector.


(*axioms*)
Axiom a_bv_eq    : forall a b, bv_eq a b = true <-> a = b.
Axiom a_bv_concat: forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_concat a b).
Axiom a_bv_and   : forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_and a b).
Axiom a_bv_add   : forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_add a b).
(*
Axiom a_bv_subs  : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_subs a b).
Axiom a_bv_mult  : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_mult a b).
Axiom a_bv_div   : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_div a b).
Axiom a_bv_or    : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_or a b).
*)
Axiom a_bv_not   : forall a,   bv_wf a -> bv_wf (bv_not a).

End RAWBITVECTOR.

Module BITVECTOR_LIST <: RAWBITVECTOR.

Record bitvector_rec : Type := 
  mk_bitvector
  {
     size : N;
     bits : list bool
  }.

Definition bitvector := bitvector_rec.

Definition bv_wf (a: bitvector):= (@size a) = N.of_nat (length (@bits a)). 

Definition bv_mk (l : list bool) := mk_bitvector (N.of_nat (length l)) l.

Lemma bv_mk_wf l : bv_wf (bv_mk l).
Proof. unfold bv_mk, bv_wf. reflexivity. Qed.

Fixpoint beq_list (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => true
    | x :: l', y :: m' => (Bool.eqb x y) && (beq_list l' m')
    | _, _ => false
  end.

Definition bv_eq (a b: bitvector): bool:=
  if ((size a) =? (size b)) then beq_list (bits a) (bits b) else false.

(*
(************** remove when (Require Import Misc) ********************)

Definition Nat_eqb :=
  fix eqb (n m : nat) {struct n} : bool :=
    match n with
    | O => match m with
           | O => true
           | S _ => false
           end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.

(********************************************************************)
*)

Lemma bv_mk_eq l1 l2 : bv_eq (bv_mk l1) (bv_mk l2) = beq_list l1 l2.
Proof.
  unfold bv_mk, bv_eq. simpl.
  case_eq (Nat_eqb (length l1) (length l2)); intro Heq.
  - now rewrite (EqNat.beq_nat_true _ _ Heq), N.eqb_refl.
  - replace (N.of_nat (length l1) =? N.of_nat (length l2)) with false.
    * revert l2 Heq. induction l1 as [ |b1 l1 IHl1]; intros [ |b2 l2]; simpl in *; auto.
      intro Heq. now rewrite <- (IHl1 _ Heq), andb_false_r.
    * symmetry. rewrite N.eqb_neq. intro H. apply Nat2N.inj in H. rewrite H in Heq.
      rewrite <- EqNat.beq_nat_refl in Heq. discriminate.
Qed.


Definition bv_concat (a b: bitvector) : bitvector.
Proof. destruct a, b. refine (@mk_bitvector (size0 + size1) (bits0 ++ bits1)). Defined.

Section Map2.

  Variables A B C: Type.
  Variable f : A -> B -> C.

  Fixpoint map2 (l1 : list A) (l2 : list B) {struct l1} : list C :=
    match l1, l2 with
      | b1::tl1, b2::tl2 => (f b1 b2)::(map2 tl1 tl2)
      | _, _ => nil
    end.

End Map2.

Section Fold_left2.

  Variables A B: Type.
  Variable f : A -> B -> B -> A.

  Fixpoint fold_left2 (xs ys: list B) (acc:A) {struct xs} : A :=
    match xs, ys with
    | nil, _ | _, nil => acc
    | x::xs, y::ys    => fold_left2 xs ys (f acc x y)
    end.

  Lemma foo : forall (I: A -> Prop) acc, I acc -> 
              (forall a b1 b2, I a -> I (f a b1 b2)) -> 
              forall xs ys, I (fold_left2 xs ys acc).
  Proof. intros I acc H0 H1 xs. revert acc H0.
         induction xs as [| a xs IHxs]; intros acc H.
         simpl. auto.
         intros [| b ys].
            + simpl. exact H.
            + simpl. apply IHxs, H1. exact H.
  Qed.

End Fold_left2.

Definition bv_nth (n: nat) (a: bitvector): bool := nth n (bits a) false.

Definition bv_and (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (map2 andb (@bits a) (@bits b))
    | _    => mk_bitvector 0 nil
  end.

Definition bv_or (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (map2 orb (@bits a) (@bits b))
    | _    => mk_bitvector 0 nil
  end.

Definition bv_not (a: bitvector) : bitvector := mk_bitvector (size a) (map negb (@bits a)).

(*arithmetic operations*)

 (*addition*)

Definition add_carry b1 b2 c :=
  match b1, b2, c with
    | true,  true,  true  => (true, true)
    | true,  true,  false
    | true,  false, true
    | false, true,  true  => (false, true)
    | false, false, true
    | false, true,  false
    | true,  false, false => (true, false)
    | false, false, false => (false, false)
  end.

(* Truncating addition in little-endian, direct style *)

Fixpoint add_list_ingr bs1 bs2 c {struct bs1} :=
  match bs1, bs2 with
    | nil, _               => nil
    | _ , nil              => nil
    | b1 :: bs1, b2 :: bs2 =>
      let (r, c) := add_carry b1 b2 c in r :: (add_list_ingr bs1 bs2 c)
  end.

Definition add_list (a b: list bool) := add_list_ingr a b false.

Definition bv_add (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (add_list (@bits a) (@bits b))
    | _    => mk_bitvector 0 nil
  end.

  (*multiplication*)

Fixpoint mk_list_true_acc (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_true_acc t' (true::acc)
  end.

Fixpoint mk_list_true (t: nat) : list bool :=
  match t with
    | O    => []
    | S t' => true::(mk_list_true t')
  end.

Fixpoint mk_list_false_acc (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_false_acc t' (false::acc)
  end.

Fixpoint mk_list_false (t: nat) : list bool :=
  match t with
    | O    => []
    | S t' => false::(mk_list_false t')
  end.

Definition bv_1 (t : nat) : bitvector :=
  match t with
    | O    => mk_bitvector 0 nil
    | S t' => mk_bitvector (N.of_nat (t' + 1)) (mk_list_true_acc t' [true])
  end.

Definition bv_0 (t : nat) : bitvector :=
  match t with
    | O    => mk_bitvector 0 nil
    | S t' => mk_bitvector (N.of_nat (t' + 1)) (mk_list_false_acc t' [false])
  end.

Fixpoint mult_list_carry (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry xs (false :: b) n)
      else
        mult_list_carry xs (false :: b) n
  end.

Definition mult_list a b := mult_list_carry a b (length a).

(*Fixpoint mult_list_carry (a b :list bool) (acc : list bool) {struct a}: list bool :=
  match a with
    | nil      => acc
    | a' :: xs =>
      if a' then
        mult_list_carry xs (false :: b) (add_list b acc)
      else
        mult_list_carry xs (false :: b) acc
  end.

Definition mult_list a b := mult_list_carry a b (mk_list_false (min (length a) (length b))).*)

Definition bv_mult (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (mult_list (@bits a) (@bits b))
    | _    => mk_bitvector 0 nil
  end.

(* Theorems *)

Lemma List_eq : forall (l m: list bool), beq_list l m = true <-> l = m.
Proof.
    induction l; destruct m; simpl; split; intro; try (reflexivity || discriminate).
    - rewrite andb_true_iff in H. destruct H. rewrite eqb_true_iff in H. rewrite H.
    apply f_equal. apply IHl. exact H0.
    - inversion H. subst b. subst m. rewrite andb_true_iff. split.
      + apply eqb_reflx.
      + apply IHl; reflexivity.
Qed.

Lemma List_eq_refl : forall (l m: list bool), beq_list l l = true.
Proof.
    induction l; simpl; intro; try (reflexivity || discriminate).
    - rewrite andb_true_iff. split. apply eqb_reflx. apply IHl. exact m.
Qed.

Lemma a_bv_eq: forall a b, bv_eq a b = true <-> a = b.
Proof. split. destruct a. destruct b. unfold bitvector; simpl; auto. intro H.
       case_eq (N.compare size0 size1); intro H1.
       case_eq (beq_list bits0 bits1); intro H2.
         rewrite List_eq in H2.
         - apply (N.compare_eq size0 size1) in H1.
           rewrite H1, H2; reflexivity.
         - contradict H. unfold bv_eq. simpl. rewrite H2.
           rewrite N.eqb_compare. rewrite H1. easy.
         - contradict H. unfold bv_eq. simpl. rewrite N.eqb_compare.
           rewrite H1. easy.
         - contradict H.  unfold bv_eq. simpl. rewrite N.eqb_compare.
           rewrite H1. easy.
         - intro H. destruct a. destruct b. inversion H.
           rewrite <- H2. simpl.
           unfold bv_eq. simpl.
           rewrite N.eqb_compare. rewrite N.compare_refl.
           rewrite List_eq_refl; trivial.
Qed.

Lemma a_bv_concat: forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_concat a b).
Proof. intros a b H0 H1. destruct a. destruct b. simpl. unfold bv_wf in *. simpl in *.
       rewrite app_length. rewrite Nat2N.inj_add. rewrite H0, H1; reflexivity. 
Qed.


(*list bitwise AND properties*)

Lemma map2_and_comm: forall (a b: list bool), (map2 andb a b) = (map2 andb b a).
Proof. intros a. induction a as [| a' xs IHxs].
       intros [| b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [| b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' = b' && a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply andb_comm.
Qed.

Lemma map2_and_assoc: forall (a b c: list bool), (map2 andb a (map2 andb b c)) = (map2 andb (map2 andb a b) c).
Proof. intro a. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b' ys].
        -  simpl. auto.
        - intros [| c' zs].
          + simpl. auto.
          + simpl. cut (a' && (b' && c') = a' && b' && c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply andb_assoc.
Qed.

Lemma map2_and_idem1:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb a b).
Proof. intros a. induction a as [| a' xs IHxs].
       intros [| b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [| b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && a' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite andb_comm, andb_assoc, andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem1. Qed.

Lemma map2_and_idem2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb a b).
Proof. intros a. induction a as [| a' xs IHxs].
       intros [| b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [| b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && b' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite <- andb_assoc. rewrite andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem2. Qed.

Lemma map2_and_empty_empty1:  forall (a: list bool), (map2 andb a []) = [].
Proof. intros a. induction a as [| a' xs IHxs]; simpl; auto. Qed.

Lemma map2_and_empty_empty2:  forall (a: list bool), (map2 andb [] a) = [].
Proof. intros a. rewrite map2_and_comm. apply map2_and_empty_empty1. Qed.

Lemma map2_nth_empty_false:  forall (i: nat), nth i [] false = false.
Proof. intros i. induction i as [| IHi]; simpl; reflexivity. Qed.

(* Lemma mk_list_true_rev: forall n, (rev (mk_list_true n)) = mk_list_true n. *)

Lemma mk_list_true_equiv: forall t acc, mk_list_true_acc t acc = (List.rev (mk_list_true t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt.
       rewrite app_assoc_reverse.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma mk_list_false_equiv: forall t acc, mk_list_false_acc t acc = (List.rev (mk_list_false t)) ++ acc.
Proof. induction t as [ |t IHt]; auto; intro acc; simpl; rewrite IHt. 
       rewrite app_assoc_reverse.
       apply f_equal. simpl. reflexivity.
Qed.

Lemma len_mk_list_true_empty: length (mk_list_true_acc 0 []) = 0%nat.
Proof. simpl. reflexivity. Qed.

Lemma add_mk_list_true: forall n acc, length (mk_list_true_acc n acc) = (n + length acc)%nat.
Proof. intros n.
       induction n as [| n' IHn].
         + auto.
         + intro acc. simpl. rewrite IHn. simpl. lia.
Qed.

Lemma map2_and_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 andb a b) false = (nth i a false) && (nth i b false).
Proof. intro a.
       induction a as [| a xs IHxs].
         - intros [| b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_and_empty_empty2.
             rewrite map2_nth_empty_false. reflexivity.
         - intros [| b ys].
           + intros i H0 H1. rewrite map2_and_empty_empty1.
             rewrite map2_nth_empty_false. rewrite andb_false_r. reflexivity.
           + intros i H0 H1. simpl.
             revert i H1. intros [| i IHi].
             * simpl. auto.
             * apply IHxs.
                 inversion H0; reflexivity.
                 inversion IHi; lia.
Qed.

Lemma length_mk_list_true_full: forall n, length (mk_list_true_acc n []) = n.
Proof. intro n. rewrite (@add_mk_list_true n []). auto. Qed.

Lemma mk_list_app: forall n acc, mk_list_true_acc n acc = mk_list_true_acc n [] ++ acc.
Proof. intro n.
       induction n as [| n IHn].
         + auto.
         + intro acc. simpl in *. rewrite IHn. 
           cut (mk_list_true_acc n [] ++ [true] = mk_list_true_acc n [true]). intro H.
           rewrite <- H. rewrite <- app_assoc. unfold app. reflexivity.
           rewrite <- IHn. reflexivity.
Qed.

Lemma mk_list_ltrue: forall n, mk_list_true_acc n [true] = mk_list_true_acc (S n) [].
Proof. intro n. induction n as [| n IHn]; auto. Qed.

Lemma map2_and_1_neutral: forall (a: list bool), (map2 andb a (mk_list_true (length a))) = a.
Proof. intro a.
       induction a as [| a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite andb_true_r. reflexivity.
Qed.

Lemma map2_and_0_absorb: forall (a: list bool), (map2 andb a (mk_list_false (length a))) = (mk_list_false (length a)).
Proof. intro a. induction a as [| a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite andb_false_r; reflexivity.
Qed.

Lemma map2_and_length: forall (a b: list bool), length a = length b -> length a = length (map2 andb a b).
Proof. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

(*bitvector AND properties*)

Lemma a_bv_and: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_and a b).
Proof. intros a b H0 H1 H2. destruct a. destruct b. simpl in *. unfold bv_wf in *. simpl in *. 
       unfold bv_and. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       simpl. rewrite H1, H2 in H0. rewrite H2. rewrite  Nat2N.inj_iff in H0.
       specialize (@map2_and_length bits0 bits1 H0). intro H3. rewrite <- H3.
       apply f_equal; auto.
Qed.

Lemma bv_and_comm: forall a b, (size a) = (size b) -> bv_and a b = bv_and b a.
Proof. intros a b H0. destruct a. destruct b. simpl in *. simpl in *. 
       unfold bv_and. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_and_comm. rewrite <- H0; reflexivity.
Qed.

Lemma bv_and_assoc: forall a b c, (size a) = (size b) -> (size a) = (size c) ->  
                                  (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Proof. intros a b c H0 H1. destruct a. destruct b. destruct c. simpl in *. 
       inversion H0. rewrite H1 in H. symmetry in H. rewrite H. unfold bv_and. simpl.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl. simpl.
       rewrite N.compare_refl. rewrite N.eqb_compare. rewrite N.compare_refl. 
       rewrite map2_and_assoc; reflexivity. 
Qed.

Lemma bv_and_idem1:  forall a b, (size a) = (size b) -> (bv_and (bv_and a b) a) = (bv_and a b).
Proof. intros a b H0. destruct a. destruct b. simpl in *. simpl in *. 
       unfold bv_and. simpl. rewrite H0. do 2 rewrite N.eqb_compare.
       rewrite N.compare_refl. simpl. rewrite N.compare_refl. 
       rewrite map2_and_idem1; reflexivity.
Qed.

Lemma bv_and_idem2: forall a b, (size a) = (size b) -> (bv_and (bv_and a b) b) = (bv_and a b).
Proof. intros a b H0. destruct a. destruct b. simpl in *. simpl in *. 
       unfold bv_and. simpl. rewrite H0. do 2 rewrite N.eqb_compare.
       rewrite N.compare_refl. simpl. rewrite N.compare_refl. 
       rewrite map2_and_idem2; reflexivity.
Qed.

Definition bv_empty := mk_bitvector (0)%N nil.

Lemma bv_and_empty_empty1: forall a, (bv_and a bv_empty) = bv_empty.
Proof. intros a. destruct a. unfold bv_empty. 
       unfold bv_and. simpl.
       case_eq (N.compare size0 0); intro H; simpl.
         - apply (N.compare_eq size0 0) in H.
           rewrite H. simpl. rewrite map2_and_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_and_nth_bitOf: forall a b (i: nat), 
                          (size a) = (size b) ->
                          bv_wf a -> bv_wf b ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_and a b)) false = (nth i (bits a) false) && (nth i (bits b) false).
Proof. intros a b i H0 H1 H2 H3. destruct a. destruct b. unfold bv_wf in *. simpl in *.
       unfold bv_and. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl. simpl.
       apply map2_and_nth_bitOf. inversion H0. rewrite H1, H2 in H. apply Nat2N.inj in H; exact H.
       rewrite H1 in H3. rewrite Nat2N.id in H3; exact H3.
Qed.

Lemma bv_and_empty_empty2: forall a, (bv_and bv_empty a) = bv_empty.
Proof. intro a. destruct a. unfold bv_and, bv_empty. simpl.
         induction size0 as [| size0]; reflexivity.
Qed.

Lemma bv_and_1_neutral: forall a, (bv_and a (mk_bitvector (size a) (mk_list_true (length (bits a))))) = a.
Proof. intro a. destruct a. simpl. unfold bv_and. simpl.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_and_1_neutral. reflexivity.
Qed.

Lemma bv_and_0_absorb: forall a, (bv_and a (mk_bitvector (size a) (mk_list_false (length (bits a))))) = 
                                 (mk_bitvector (size a) (mk_list_false (length (bits a)))).
Proof. intro a. destruct a. simpl. unfold bv_and. simpl.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_and_0_absorb. reflexivity.
Qed.

(* lists bitwise OR properties *)

Lemma map2_or_comm: forall (a b: list bool), (map2 orb a b) = (map2 orb b a).
Proof. intros a. induction a as [| a' xs IHxs].
       intros [| b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [| b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' = b' || a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply orb_comm.
Qed.

Lemma map2_or_assoc: forall (a b c: list bool), (map2 orb a (map2 orb b c)) = (map2 orb (map2 orb a b) c).
Proof. intro a. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b' ys].
        -  simpl. auto.
        - intros [| c' zs].
          + simpl. auto.
          + simpl. cut (a' || (b' || c') = a' || b' || c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply orb_assoc.
Qed.

Lemma map2_or_length: forall (a b: list bool), length a = length b -> length a = length (map2 orb a b).
Proof. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_or_empty_empty1:  forall (a: list bool), (map2 orb a []) = [].
Proof. intros a. induction a as [| a' xs IHxs]; simpl; auto. Qed.

Lemma map2_or_empty_empty2:  forall (a: list bool), (map2 orb [] a) = [].
Proof. intros a. rewrite map2_or_comm. apply map2_or_empty_empty1. Qed.

Lemma map2_or_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 orb a b) false = (nth i a false) || (nth i b false).
Proof. intro a.
       induction a as [| a xs IHxs].
         - intros [| b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_or_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [| b ys].
           + intros i H0 H1. rewrite map2_or_empty_empty1.
             rewrite map2_nth_empty_false. rewrite orb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. intros [| i IHi].
             * simpl. auto.
             * apply IHxs.
                 inversion H0; reflexivity.
                 inversion IHi; lia.
Qed.

Lemma map2_or_0_neutral: forall (a: list bool), (map2 orb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [| a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite orb_false_r. reflexivity.
Qed.

Lemma map2_or_1_true: forall (a: list bool), (map2 orb a (mk_list_true (length a))) = (mk_list_true (length a)).
Proof. intro a. induction a as [| a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite orb_true_r; reflexivity.
Qed.

(*bitvector OR properties*)

Lemma a_bv_or: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_or a b).
Proof. intros a b H0 H1 H2. destruct a. destruct b. simpl in *. unfold bv_wf in *. simpl in *. 
       unfold bv_or. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       simpl. rewrite H1, H2 in H0. rewrite H2. rewrite  Nat2N.inj_iff in H0.
       specialize (@map2_or_length bits0 bits1 H0). intro H3. rewrite <- H3.
       apply f_equal; auto.
Qed.

Lemma bv_or_comm: forall a b, (size a) = (size b) -> bv_or a b = bv_or b a.
Proof. intros a b H0. destruct a. destruct b. simpl in *. simpl in *. 
       unfold bv_or. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_or_comm. rewrite <- H0; reflexivity.
Qed.

Lemma bv_or_assoc: forall a b c, (size a) = (size b) -> (size a) = (size c) ->  
                                  (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Proof. intros a b c H0 H1. destruct a. destruct b. destruct c. simpl in *. 
       inversion H0. rewrite H1 in H. symmetry in H. rewrite H. unfold bv_or. simpl.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl. simpl.
       rewrite N.compare_refl. rewrite N.eqb_compare. rewrite N.compare_refl. 
       rewrite map2_or_assoc; reflexivity. 
Qed.

Lemma bv_or_empty_empty1: forall a, (bv_or a bv_empty) = bv_empty.
Proof. intros a. destruct a. unfold bv_empty. 
       unfold bv_or. simpl.
       case_eq (N.compare size0 0); intro H; simpl.
         - apply (N.compare_eq size0 0) in H.
           rewrite H. simpl. rewrite map2_or_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_or_nth_bitOf: forall a b (i: nat), 
                          (size a) = (size b) ->
                          bv_wf a -> bv_wf b ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_or a b)) false = (nth i (bits a) false) || (nth i (bits b) false).
Proof. intros a b i H0 H1 H2 H3. destruct a. destruct b. unfold bv_wf in *. simpl in *.
       unfold bv_or. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl. simpl.
       apply map2_or_nth_bitOf. inversion H0. rewrite H1, H2 in H. apply Nat2N.inj in H; exact H.
       rewrite H1 in H3. rewrite Nat2N.id in H3; exact H3.
Qed.

Lemma bv_or_0_neutral: forall a, (bv_or a (mk_bitvector (size a) (mk_list_false (length (bits a))))) = a.
Proof. intro a. destruct a. simpl. unfold bv_or. simpl.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_or_0_neutral. reflexivity.
Qed.

Lemma bv_or_1_true: forall a, (bv_or a (mk_bitvector (size a) (mk_list_true (length (bits a))))) = 
                                 (mk_bitvector (size a) (mk_list_true (length (bits a)))).
Proof. intro a. destruct a. simpl. unfold bv_or. simpl.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_or_1_true. reflexivity.
Qed.

(*bitwise NOT properties*)

Lemma not_list_length: forall a, length a = length (map negb a).
Proof. intro a.
       induction a as [| a xs IHxs].
       - auto. 
       - simpl. apply f_equal. exact IHxs.
Qed.

Lemma not_list_involutative: forall a, map negb (map negb a) = a.
Proof. intro a.
       induction a as [| a xs IHxs]; auto.
       simpl. rewrite negb_involutive. apply f_equal. exact IHxs.
Qed.

Lemma not_list_false_true: forall n, map negb (mk_list_false n) = mk_list_true n.
Proof. intro n.
       induction n as [| n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_true_false: forall n, map negb (mk_list_true n) = mk_list_false n.
Proof. intro n.
       induction n as [| n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_and_or: forall a b, map negb (map2 andb a b) = map2 orb (map negb a) (map negb b).
Proof. intro a.
       induction a as [| a xs IHxs].
       - auto.
       - intros [| b ys].
         + auto.
         + simpl. rewrite negb_andb. apply f_equal. apply IHxs.
Qed.

Lemma not_list_or_and: forall a b, map negb (map2 orb a b) = map2 andb (map negb a) (map negb b).
Proof. intro a.
       induction a as [| a xs IHxs].
       - auto.
       - intros [| b ys].
         + auto.
         + simpl. rewrite negb_orb. apply f_equal. apply IHxs.
Qed.

(*bitvector NOT properties*)

Lemma a_bv_not   : forall a,   bv_wf a -> bv_wf (bv_not a).
Proof. intros a H. destruct a. unfold bv_not. simpl. unfold bv_wf in *. 
       simpl in *. rewrite <- not_list_length. exact H.
Qed.

Lemma bv_not_involutative: forall a, bv_not (bv_not a) = a.
Proof. intro a. destruct a. unfold bv_not. simpl.
       rewrite not_list_involutative. reflexivity.
Qed.

Lemma bv_not_false_true: forall n m, bv_not (mk_bitvector m (mk_list_false n)) = mk_bitvector m (mk_list_true n).
Proof. intros n m. unfold bv_not. simpl.
       rewrite not_list_false_true. reflexivity.
Qed.

Lemma bv_not_true_false: forall n m, bv_not (mk_bitvector m (mk_list_true n)) = mk_bitvector m (mk_list_false n).
Proof. intros n m. unfold bv_not. simpl.
       rewrite not_list_true_false. reflexivity.
Qed.

Lemma bv_not_and_or: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_not (bv_and a b) = bv_or (bv_not a) (bv_not b).
Proof. intros a b H0 H1 H2. destruct a. destruct b. unfold bv_wf in *. simpl in *.
       unfold bv_and in *. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or in *. simpl. rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not in *. simpl. rewrite not_list_and_or. reflexivity.
Qed.

Lemma bv_not_or_and: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_not (bv_or a b) = bv_and (bv_not a) (bv_not b).
Proof. intros a b H0 H1 H2. destruct a. destruct b. unfold bv_wf in *. simpl in *.
       unfold bv_and in *. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or in *. simpl. rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not in *. simpl. rewrite not_list_or_and. reflexivity.
Qed.

(* list bitwise ADD properties*)

Lemma add_list_empty_l: forall (a: list bool), (add_list [] a) = [].
Proof. intro a. induction a as [| a xs IHxs].
         - unfold add_list. simpl. reflexivity.
         - apply IHxs.
Qed.

Lemma add_list_empty_r: forall (a: list bool), (add_list a []) = [].
Proof. intro a. induction a as [| a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_r: forall (a: list bool) (c: bool), (add_list_ingr a [] c) = [].
Proof. intro a. induction a as [| a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_carry_comm: forall (a b:  list bool) (c: bool), add_list_ingr a b c = add_list_ingr b a c.
Proof. intros a. induction a as [| a' xs IHxs]; intros b c.
       - simpl. rewrite add_list_ingr_r. reflexivity.
       - case b as [| b' ys].
         + simpl. auto.
         + simpl in *. cut (add_carry a' b' c = add_carry b' a' c).
           * intro H. rewrite H. destruct (add_carry b' a' c) as (r, c0).
             rewrite IHxs. reflexivity.
           * case a', b', c;  auto.
Qed.

Lemma add_list_comm: forall (a b: list bool), (add_list a b) = (add_list b a).
Proof. intros a b. unfold add_list. apply (add_list_carry_comm a b false). Qed.

Lemma add_list_carry_assoc: forall (a b c:  list bool) (d1 d2 d3 d4: bool),
                            add_carry d1 d2 false = add_carry d3 d4 false ->
                            (add_list_ingr (add_list_ingr a b d1) c d2) = (add_list_ingr a (add_list_ingr b c d3) d4).
Proof. intros a. induction a as [| a' xs IHxs]; intros b c d1 d2 d3 d4.
       - simpl. reflexivity.
       - case b as [| b' ys].
         + simpl. auto.
         + case c as [| c' zs].
           * simpl. rewrite add_list_ingr_r. auto.
           * simpl.
             case_eq (add_carry a' b' d1); intros r0 c0 Heq0. simpl.
             case_eq (add_carry r0 c' d2); intros r1 c1 Heq1.
             case_eq (add_carry b' c' d3); intros r3 c3 Heq3.
             case_eq (add_carry a' r3 d4); intros r2 c2 Heq2.
             intro H. rewrite (IHxs _ _ c0 c1 c3 c2);
               revert Heq0 Heq1 Heq3 Heq2;
               case a', b', c', d1, d2, d3, d4; simpl; do 4 (intros H'; inversion_clear H'); 
               (*; intros H'; inversion_clear H'; intros H'; inversion_clear H'; intros H'; inversion_clear H'; *)
                 try reflexivity; simpl in H; discriminate.
Qed.

Lemma add_list_carry_length: forall (a b: list bool) c, length a = length b -> length a = length (add_list_ingr a b c).
Proof. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b ys].
       - simpl. intros. exact H.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity.
Qed.

Lemma add_list_length: forall (a b: list bool), length a = length b -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length a b false). exact H. Qed.

Lemma add_list_assoc: forall (a b c: list bool), (add_list (add_list a b) c) = (add_list a (add_list b c)).
Proof. intros a b c. unfold add_list.
       apply (@add_list_carry_assoc a b c false false false false).
       simpl; reflexivity.
Qed.

Lemma add_list_carry_empty_neutral_r: forall (a: list bool), (add_list_ingr a (mk_list_false (length a)) false) = a.
Proof. intro a. induction a as [| a' xs IHxs].
       - simpl. reflexivity.
       - simpl.
         cut(add_carry a' false false = (a', false)).
         + intro H. rewrite H. rewrite IHxs. reflexivity.
         + unfold add_carry. case a'; auto.
Qed.

Lemma add_list_empty_neutral_r: forall (a: list bool), (add_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_r a).
Qed.

Lemma add_list_carry_empty_neutral_l: forall (a: list bool), (add_list_ingr (mk_list_false (length a)) a false) = a.
Proof. intro a. induction a as [| a' xs IHxs].
       - simpl. reflexivity.
       - simpl. case a'; rewrite IHxs; reflexivity.
Qed.

Lemma add_list_empty_neutral_l: forall (a: list bool), (add_list (mk_list_false (length a)) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_l a).
Qed.

(*bitvector ADD properties*)


Lemma a_bv_add: forall a b, (@size a) = (@size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_add a b).
Proof. intros a b H0 H1 H2. destruct a. destruct b. simpl in *. unfold bv_wf in *. simpl in *. 
       unfold bv_add. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       simpl. rewrite H1, H2 in H0. rewrite H2. rewrite  Nat2N.inj_iff in H0.
       specialize (@add_list_length bits0 bits1). intro H3. rewrite <- H3.
       apply f_equal; auto. exact H0. 
Qed.

Lemma bv_add_comm: forall a b, (size a) = (size b) -> bv_add a b = bv_add b a.
Proof. intros a b H0. destruct a. destruct b. simpl in *. 
       unfold bv_add. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_comm. reflexivity.
Qed.

Lemma bv_add_assoc: forall a b c, (size a) = (size b) -> (size a) = (size c) ->  
                                  (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Proof. intros a b c H0 H1. destruct a. destruct b. destruct c. simpl in *. 
       inversion H0. rewrite H1 in H. symmetry in H. rewrite H. unfold bv_add. simpl.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl. simpl.
       rewrite N.compare_refl. rewrite N.eqb_compare. rewrite N.compare_refl. 
       rewrite add_list_assoc; reflexivity. 
Qed.

Lemma bv_add_empty_neutral_l: forall a, (bv_add (mk_bitvector (size a) (mk_list_false (length (bits a)))) a) = a.
Proof. intro a. destruct a. simpl. unfold bv_add. simpl.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_l. reflexivity.
Qed.

Lemma bv_add_empty_neutral_r: forall a, (bv_add a (mk_bitvector (size a) (mk_list_false (length (bits a))))) = a.
Proof. intro a. destruct a. simpl. unfold bv_add. simpl.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.

(* bitwise MULT properties *)

Lemma mult_list_empty_l: forall (a: list bool), (mult_list [] a) = [].
Proof. intro a. induction a as [| a xs IHxs].
         - unfold mult_list. simpl. reflexivity.
         - apply IHxs.
Qed.

Lemma mult_list_carry_0: forall a b, mult_list_carry a b 0 = [].
Proof. intro a. induction a as [| a' xs IHxs].
       - intro b. simpl. reflexivity.
       - intros [| b' ys].
         + simpl. case_eq a'.
           * simpl. intro H. rewrite add_list_empty_l; reflexivity.
           * simpl. intro H. apply IHxs.
         + simpl. case_eq a'.
           * simpl. intro H. rewrite IHxs. rewrite add_list_empty_r; reflexivity.
           * simpl. intro H. apply IHxs.
Qed.

Lemma mult_list_carry_empty_l: forall (a: list bool) (c: nat), mult_list_carry [] a c = mk_list_false c.
Proof. intro a. induction a as [| a' xs IHxs]; auto. Qed.

Lemma length_mk_list_false: forall n, length (mk_list_false n) = n.
Proof. intro n.
       induction n as [| n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma strictly_positive_0_unique: forall n: nat, (0 >= n)%nat <-> (n = 0)%nat.
Proof. intro n. induction n as [| n IHn].
       split; try auto.
       split; intro H; contradict H; easy.
Qed. 

Lemma mult_list_length: forall (a b: list bool) n, 
                        (*length a <= n ->*) ((length b) >= n)%nat -> n = length (mult_list_carry a b n).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H. rewrite mult_list_carry_empty_l, length_mk_list_false; reflexivity. 
       - intros [| b ys n]. intros n H. simpl in H. rewrite strictly_positive_0_unique in H.
         rewrite H. rewrite mult_list_carry_0. easy.
         intro H. simpl. case a.
         + specialize (@add_list_length (b :: ys) (mult_list_carry xs (false :: b :: ys) n)).
           intro H1. rewrite <- H1. (**) admit. (**)
           specialize (@IHxs (false :: b :: ys)). rewrite <- IHxs. (**) admit. (**) inversion H. simpl. lia. simpl in *. lia.
         + specialize (@IHxs (false :: b :: ys)). apply IHxs. inversion H. simpl. lia. simpl in *. lia.
Qed.
           
End BITVECTOR_LIST.

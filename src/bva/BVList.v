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
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type BITVECTOR.

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

(*
Parameter bv_add   : bitvector -> bitvector -> bitvector.
Parameter bv_subs  : bitvector -> bitvector -> bitvector.
Parameter bv_mult  : bitvector -> bitvector -> bitvector.
Parameter bv_div   : bitvector -> bitvector -> bitvector.
Parameter bv_or    : bitvector -> bitvector -> bitvector.
(*unary operations*)
Parameter bv_not   : bitvector -> bitvector.
*)

End BITVECTOR.

Module Type BITVECTOR_THEOREMS (BV:BITVECTOR).
  Import BV.

(*axioms*)
Axiom a_bv_eq: forall a b, bv_eq a b = true <-> a = b.
Axiom a_bv_concat: forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_concat a b).
Axiom a_bv_and: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_and a b).

(*
Axiom a_bv_add   : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_add a b).
Axiom a_bv_subs  : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_subs a b).
Axiom a_bv_mult  : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_mult a b).
Axiom a_bv_div   : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_div a b).
Axiom a_bv_or    : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_or a b).
Axiom a_bv_not   : forall a,   bv_wf a -> bv_wf (bv_not a).
*)

End BITVECTOR_THEOREMS.

Module BITVECTOR_LIST <: BITVECTOR.

Record bitvector_rec : Type := 
  mk_bitvector
  {
     size : N;
     bits : list bool
  }.

 Check size.

Definition bitvector := bitvector_rec.

Definition bv_wf (a: bitvector):= (@size a) = N.of_nat (length (@bits a)). 

Fixpoint beq_list (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => true
    | x :: l', y :: m' => (Bool.eqb x y) && (beq_list l' m')
    | _, _ => false
  end.

Definition bv_eq (a b: bitvector): bool:=
  match ((size a) =? (size b)) with
    | true  =>
    match beq_list (bits a) (bits b) with
      | true => true
      | _    => false
    end
    | _ => false
  end.

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
    | x::xs, y::ys => fold_left2 xs ys (f acc x y)
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

(*arithmetic operations*)

Definition add_list (b1 b2 : list bool) : list bool :=
  List.rev (fst (@fold_left2 (list bool * bool)%type _ (fun a x y => 
                         let (r, c) := a in
                         match x, y, c with
                         | false, false, false => (false::r, false)
                         | false, false, true
                         | false, true, false
                         | true, false, false => (true::r, false)
                         | true, true, false
                         | true, false, true
                         | false, true, true => (false::r, true)
                         | true, true, true => (true::r, true)
                         end
                      ) b1 b2 (nil, false))).

Definition bv_add (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (add_list (@bits a) (@bits b))
    | _    => mk_bitvector 0 nil
  end.

End BITVECTOR_LIST.

Module BITVECTOR_LIST_THEOREMS : BITVECTOR_THEOREMS (BITVECTOR_LIST).
Import BITVECTOR_LIST.

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
Check a_bv_eq.

Lemma a_bv_concat: forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_concat a b).
Proof. intros a b H0 H1. destruct a. destruct b. simpl. unfold bv_wf in *. simpl in *.
       rewrite app_length. rewrite Nat2N.inj_add. rewrite H0, H1; reflexivity. 
Qed.

Section Fold_left2.

  Variables A B: Type.
  Variable f : A -> B -> B -> A.

  Fixpoint fold_left2 (xs ys: list B) (acc:A) {struct xs} : A :=
    match xs, ys with
    | nil, _ | _, nil => acc
    | x::xs, y::ys => fold_left2 xs ys (f acc x y)
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

(*list bitwise-AND properties*)

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

(* Lemma map2_or_0_neutral: forall (a: list bool), (map2 andb a (mk_list_true (length a))) = a. *)

(*Lemma map2_and_1_acc_neutral: forall (a: list bool), (map2 andb a (mk_list_true_acc (length a) [])) = a.*)

Lemma map2_and_length: forall (a b: list bool), length a = length b -> length a = length (map2 andb a b).
Proof. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

(*bitvector bitwise-AND properties*)

Lemma a_bv_and: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_and a b).
Proof. intros a b H0 H1 H2. destruct a. destruct b. simpl in *. unfold bv_wf in *. simpl in *. 
       unfold bv_and. simpl. rewrite H0. rewrite N.eqb_compare. rewrite N.compare_refl.
       simpl. rewrite H1, H2 in H0. rewrite H2. rewrite  Nat2N.inj_iff in H0.
       specialize (@map2_and_length bits0 bits1 H0). intro H3. rewrite <- H3.
       apply f_equal; auto.
Qed.
Check a_bv_and.

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

(* lists bitwise-OR properties *)

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

(*bitvector bitwise-OR properties*)

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

(*TODO: bitvector ADD properties*)

(* Lemma a_bv_add: forall a b, (@size a) = (@size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_add a b). *)

End BITVECTOR_LIST_THEOREMS.


 
(** Some useful functions *)
Section Map2.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
    | b1::tl1, b2::tl2 => (f b1 b2)::(map2 f tl1 tl2)
    | _, _ => nil
  end.

Lemma l_rl: forall {A: Type} {a: A} (l: list A), length l =  length (List.removelast (a :: l)).
Proof. intros.
         induction l.
           - simpl; reflexivity.
           - unfold length in *. rewrite IHl. simpl in *. apply f_equal. induction l; reflexivity.
Qed.

End Map2.

(* Representation of bit vectors as a pair of boolean list and size; followed by implementation of standard operations *)

Module BV.

Import N.
Local Open Scope N_scope.

  (** The type of bit vectors *)
  Definition t := (list bool * N)%type.

  (** The empty bit vector *)
  Definition empty : t := (nil, 0).


  (** Test weither a bit vector is empty *)
  Definition is_empty (bv : t) : bool :=
    let (_, n) := bv in
    match n with
    | N0 => true
    | _ => false
    end.

  (** Test weither a bit vector is zero (this defines the semantics of
      the 0 bit vector) *)
  Definition is_zero (bv : t) : bool :=
    let (b, _) := bv in
    List.forallb (fun x => negb x) b.

  (** Concatenation of two bit vectors *)
  Definition concat (bv1 bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (b1 ++ b2, n1 + n2).

  (** Bitwise not *)
  Definition not (bv : t) : t :=
    let (b, n) := bv in
    (List.map negb b, n).

  (** Bitwise and *)
  Definition and (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 andb b1 b2, n1).

  (** Bitwise or *)
  Definition or (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 orb b1 b2, n1).

  (** Bitwise xor *)
  Definition xor (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 xorb b1 b2, n1).

  (** Lower weight bit *)
  Definition lower (bv : t) : bool :=
    let (b, _) := bv in
    List.hd false b.

  (** Higher weight bit *)
  Definition high (bv : t) : bool :=
    let (b, _) := bv in
    List.last b false.

  (** Left shift *)
  Definition shiftleft (bv : t) : t :=
    let (b, n) := bv in
    (false::(List.removelast b), n).

  (** Right shift *)
  Definition shiftright (bv : t) : t :=
    let (b, n) := bv in
    ((List.tl b) ++ (false::nil), n).

  (** Left shift of [n] bits *)
  Fixpoint shiftleft_n (bv : t) (n : nat) : t :=
    match n with
      | O => bv
      | S n2 => shiftleft_n (shiftleft bv) n2
    end.

  (** Right shift of [n] bits *)
  Fixpoint shiftright_n (bv : t) (n : nat) : t :=
    match n with
      | O => bv
      | S n2 => shiftright_n (shiftright bv) n2
    end.

  (** Computes the [i]th bit *)
  Definition bb_nth (i : nat) (bv : t) : bool :=
    let (b, _) := bv in
    nth i b false.

  (** Computation of the unsigned integer represented by a bit vector *)
  Fixpoint b2p (b : list bool) : option positive :=
    match b with
    | nil => None
    | false::b =>
      match b2p b with
      | Some p => Some (xO p)
      | None => None
      end
    | true::b =>
      match b2p b with
      | Some p => Some (xI p)
      | None => Some xH
      end
    end.

  Definition bv2n (bv : t) : N :=
    let (b, _) := bv in
    match b2p b with
    | None => N0
    | Some p => Npos p
    end.

  (** Computation of the bit vector representing an integer *)
  Fixpoint p2bv (p : positive) : t :=
    match p with
    | xO p =>
      let (b,n) := p2bv p in
      (false::b, n+1)
    | xI p =>
      let (b,n) := p2bv p in
      (true::b, n+1)
    | xH => (true::nil, 1)
    end.

  Definition n2bv (n : N) : t :=
    match n with
    | N0 => (false::nil, 1)
    | Npos p => p2bv p
    end.

  Definition n2b (n : N) : list bool :=
    let (b, _) := n2bv n in b.

  (* We may want to change the definition of arithmetic operations *)
  (** Addition *)
  Definition add (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 + n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Subtraction *)
  Definition sub (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 - n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Multiplication *)
  Definition mul (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 * n4) in
    let b3 := (n2b n5) in
    (b3, n1).

(* Eval compute in mul ((false :: true :: false :: true :: nil), 4) ((false :: true :: false :: false :: nil), 4). *)

  (** Negation *)
  Definition neg (bv1 : t) (n : N) : t :=
    let (b1, n1) := bv1 in
    let n2 := 2 ^ n in
    let n3 := (bv2n bv1) in
    let n4 := n2 - n3 in
    ((n2b n4), n).


  (** Division *)
  Definition udiv (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2b (n3 / n4)), n1)
    end.

  (** Reminder *)
  Definition urem (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2b (n3 mod n4)), n1)
    end.

  (** Unsigned less than *)
  Definition ult (bv1 : t) (bv2 : t) :=
    let n1 := (bv2n bv1) in
    let n2 := (bv2n bv2) in
    (n1 < n2).

  (** Drops the [n] bits of lowest weight *)
  Fixpoint drop_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => l
      | S n2 => drop_n (@List.tl bool l) n2
    end.

  (** Keep the [n] bits of lowest weight *)
  Fixpoint first_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => nil
      | S n2 =>
      match l with
        | nil => nil
        | x :: l2 => x :: (first_n l2 n2)
      end
    end.

  (** Extracts the bits between i (included) and j (excluded) *)
  Definition extract (l : list bool) (i : nat) (j : nat) : list bool :=
    let l2 := drop_n l i in
    (first_n l2 j).

End BV.



Module BVProof.

  Import BV.
  Local Open Scope N_scope.

  (** Bit vectors are well-formed when their length match the length of their list *)
  Definition wf (bv:t) : Prop :=
     let (b,n) := bv in N.of_nat (length b) = n.
(*  Eval compute in wf ((true::nil), 2). *)

  (** All the operations preserve well-foundness *)

  Lemma empty_wf : wf empty.
  Proof. reflexivity. Qed.

  Lemma concat_wf : forall (bv1 bv2:t), wf bv1 -> wf bv2 -> wf (concat bv1 bv2).
  Proof.
    intros [b1 n1] [b2 n2] H1 H2.
    simpl.
    rewrite app_length.
    rewrite Nat2N.inj_add.
    simpl in H1. simpl in H2.
    rewrite H1. rewrite H2.
    reflexivity.
  Qed.  

  (** Auxiliary lemmas *)

  Lemma nth_appendl A : forall (l1 l2:list A) (i:nat) (d:A),
    (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d.
  Proof.
    induction l1 as [ |a l1 IHl1].
    - simpl.
      intros l2 i d H. elim (Lt.lt_n_0 _ H).
    - simpl. intros l2 [ |i] d Hi.
      * reflexivity.
      * apply IHl1. apply Lt.lt_S_n. assumption.
  Qed.  

  Lemma Nat2N_inj_lt i j :
    (N.of_nat i < N.of_nat j) -> (i < j)%nat.
  Proof.
    now rewrite Compare_dec.nat_compare_lt, Nat2N.inj_compare.
  Qed.


  (** Properties of the operations on well-founded bit vectors *)

  Lemma nth_concat_l : forall(bv1 bv2:t) (i : nat),
    let (b1, n1) := bv1 in
    wf bv1 -> wf bv2 -> (N.of_nat i < n1) -> bb_nth i (concat bv1 bv2) = bb_nth i bv1.
  Proof.
    intros [b1 n1] [b2 n2]. simpl. intros i H1 H2 Hi.
    rewrite nth_appendl.
    - reflexivity.
    - rewrite <- H1 in Hi.
      apply Nat2N_inj_lt.
      assumption.
  Qed.

End BVProof.

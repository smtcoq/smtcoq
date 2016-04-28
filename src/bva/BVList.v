(**************************************************************************)
(*                                                                        *)
(*     NDBvector                                                          *)
(*     Copyright (C) 2016                                                 *)
(*                                                                        *)
(*     Tianyi Liang                                                       *)
(*     Chantal Keller                                                     *)
(*     Alain Mebsout                                                      *)
(*     Burak Ekici                                                        *)
(*                                                                        *)
(*     The University of Iowa                                             *)
(*     LRI - Université Paris Sud - Université Paris Saclay               *)
(*                                                                        *)
(*   TODO: This file is distributed under the terms of SOME licence       *)
(*                                                                        *)
(**************************************************************************)


Require Import List Bool NArith.
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
(*Lemma a_bv_and: forall a b, (size a) = (size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_and a b).*)

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

Definition bv_and (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (map2 andb (@bits a) (@bits b))
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

Lemma map2_empty_empty1:  forall (a: list bool), (map2 andb a []) = [].
Proof. intros a. induction a as [| a' xs IHxs]; simpl; auto. Qed.

Lemma map2_empty_empty2:  forall (a: list bool), (map2 andb [] a) = [].
Proof. intros a. rewrite map2_and_comm. apply map2_empty_empty1. Qed.

Lemma map2_nth_empty_false:  forall (i: nat), nth i [] false = false.
Proof. intros i. induction i as [| IHi]; simpl; reflexivity. Qed.


Fixpoint mk_list_true (t: nat) (acc: list bool) : list bool :=
  match t with
    | O    => acc
    | S t' => mk_list_true t' (true::acc)
  end.

Eval compute in length (mk_list_true 10 [false]).

Fixpoint mk_list_false (t: nat) (a: list bool) : list bool :=
  match t with
    | O    => a
    | S t' => mk_list_true t' (false::a)
  end.

Lemma len_mk_list_true_empty: length (mk_list_true 0 []) = 0%nat.
Proof. simpl. reflexivity. Qed.

(*
Lemma length_mk_list_true_full: forall n, length (mk_list_true n []) = n.
Proof. intro n. induction n as [| n IHn].
         - simpl. reflexivity.
         - 


Lemma lmk_list_true: forall n acc, length (mk_list_true n acc) = (n + (length acc))%nat.

Lemma map2_and_ltrue: forall (a: list bool),  (map2 andb a (mk_list_true (length a) [])) = a.
*)

(*
SearchAbout nth. 
Check length.

Lemma nt_bitOf_map2_and: forall (a b: list bool) (i: nat), 
                         (length a) = (length b) ->
                         (i <= (length a))%nat ->
                         nth i (map2 andb a b) false = (nth i a false) && (nth i b false).
Proof. intros a. 
       induction a as [| a' xs IHxs]; intros b i H0 H1.
        - do 2 rewrite map2_nth_empty_false. reflexivity.
        - revert b H0 IHxs. intros [| b' ys]; intro H0.
         + contradict H0. easy.
         + intros. here 
*)

Lemma map2_and_length: forall (a b: list bool), length a = length b -> length a = length (map2 andb a b).
Proof. induction a as [| a' xs IHxs].
       simpl. auto.
       intros [| b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

(*bit vectors properties*)

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
           rewrite H. simpl. rewrite map2_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

SearchAbout N.compare.

Lemma bv_and_empty_empty2: forall a, (bv_and bv_empty a) = bv_empty.
Proof. intro a. destruct a. unfold bv_and, bv_empty. simpl.
         induction size0 as [| size0]; reflexivity.
Qed.

Definition bv_1 (t : nat) : bitvector :=
  match t with
    | O    => mk_bitvector 0 nil
    | S t' => mk_bitvector (N.of_nat (t' + 1)) (mk_list_true t' [true])
  end.

Definition bv_0 (t : nat) : bitvector :=
  match t with
    | O    => mk_bitvector 0 nil
    | S t' => mk_bitvector (N.of_nat (t' + 1)) (mk_list_false t' [false])
  end.

(*
Lemma bv_and_1_neutral: forall a, (bv_and a (bv_1 (nat_of_N (size a)))) = a.
Proof. intro a. destruct a. unfold bv_1. simpl in *. simpl in *. 
       unfold bv_and. simpl. rewrite N.eqb_compare. simpl. 

*)

End BITVECTOR_LIST_THEOREMS.

(*
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

Compute (add_list (false::true::false::false::nil) (false::true::false::nil)).
Search (nat -> (nat -> bool)).

Definition bv_add (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mk_bitvector (size a) (add_list (@bits a) (@bits b))
    | _    => mk_bitvector 0 nil
  end.

Eval compute in bv_add (mk_bitvector 2 [true; true]) (mk_bitvector 2 [false; true; false]).

SearchAbout N.compare.

Lemma add_list_lenght: forall (a b: list bool), length (add_list a b) = (min (length a) (length b)).


Lemma a_bv_add': forall a b, (@size a) = (@size b) -> (@size (bv_add a b)) = (@size a).
Proof. intros a b H. unfold bv_add. rewrite <- N.compare_eq_iff in H.
       rewrite N.eqb_compare. rewrite H.
       simpl; reflexivity.
Qed.

Lemma a_bv_add'': forall a b, (@size a) = (@size b) -> bv_wf a -> bv_wf b -> bv_wf (bv_add a b).

Lemma a_bv_add   : forall a b, bv_wf a -> bv_wf b -> bv_wf (bv_add a b).
*)




 
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


(* Representation of bit vectors as a Coq Record and implementation of standard operations *)

End Map2.


Module DTBV.

Local Open Scope nat_scope.

(* Definition vsize := 5. *)

Record bv : Type :=
  mk_bv
  {
       size : nat;
       bits : list bool 
   (*  wf   : N.of_nat (length bits) = size *)
  }.
Check bv.
Check mk_bv. 
Check @bits.
Check bits.
Check size.
Check @size.
Check bits.
Print bv.
Print mk_bv.

Definition concat_bv (a b: bv) : bv.
Proof. destruct a, b. refine (@mk_bv (size0 + size1) (bits0 ++ bits1)). Defined.
Check concat_bv.


Definition empty_bv: bv.
Proof. refine (@mk_bv 0 nil). Defined.
Check empty_bv.

Definition is_empty_bv (a: bv) : bool :=
  match a with
    | mk_bv _ nil => true
    | _           => false
  end.
Check is_empty_bv.

Definition is_zero_bv (a: bv): bool :=
  match a with
    | mk_bv _ l1 => List.forallb (fun x => negb x) l1
  end.
Check is_zero_bv.

Definition not_bv (a: bv) : bv.
Proof. destruct a. refine (@mk_bv size0 (List.map negb bits0)). Defined.
Check not_bv.

Definition and_bv (a b: bv): bv.
Proof. intros. destruct a, b. refine (@mk_bv size0 (map2 andb bits0 bits1)). Defined.
Check and_bv.

Definition or_bv (a b: bv): bv.
Proof. intros. destruct a, b. refine (@mk_bv size0 (map2 orb bits0 bits1)). Defined.
Check or_bv.

Definition lower_bv (a: bv) : bool :=
  match a with
    | mk_bv _ l1 => List.hd false l1 
  end.
Check lower_bv.

Definition higher_bv (a: bv) : bool :=
  match a with
    | mk_bv _ l1 => List.last l1 false 
  end.
Check higher_bv.

Definition shiftleft_bv (a: bv): bv.
Proof. destruct a. refine (@mk_bv  size0 (List.removelast (false :: bits0))). Defined. 
Check shiftleft_bv.

Definition shiftright_bv (a: bv): bv.
Proof. destruct a. refine (@mk_bv size0 ((List.tl bits0) ++ (false::nil))). Defined.
Check shiftright_bv.

Fixpoint shiftleft_n_bv (n: nat) (a: bv) : bv :=
  match n with
    | 0%nat => a
    | S n'  => (@shiftleft_n_bv n' (@shiftleft_bv a) )
  end.
Check shiftleft_n_bv.

Fixpoint shiftright_n_bv (n: nat) (a: bv): bv :=
  match n with
    | 0%nat => a
    | S n'  => (@shiftright_n_bv n' (@shiftright_bv a))
  end.
Check shiftright_n_bv.

Definition bb_nth_bv (n: nat) (a: bv): bool :=
  match a with
    | mk_bv _ l => nth n l false
  end.
Check bb_nth_bv.

Fixpoint b2p_bv (b : list bool) : option positive :=
  match b with
    | nil => None
    | false::b =>
    match b2p_bv b with
      | Some p => Some (xO p)
      | None => None
    end
    | true::b =>
    match b2p_bv b with
      | Some p => Some (xI p)
      | None => Some xH
    end
  end.
Check b2p_bv.

Definition bv2n_bv (a: bv): nat :=
  match a with
    | mk_bv _ l =>
    match b2p_bv l with
      | None   => 0
      | Some p => Pos.to_nat p 
    end
  end.
Check bv2n_bv.

Fixpoint p2bv_bv (p: positive) (size: nat) : bv :=
  match p with
    | xO p => 
    match p2bv_bv p size with
      | mk_bv s l => (mk_bv size (false :: l))
    end
      | xI p =>
    match p2bv_bv p size with
      | mk_bv s l => (mk_bv size (true :: l))
    end
    | xH => mk_bv size (true :: nil) 
  end.

Eval compute in p2bv_bv 16 3.

(* Definition N_decrement (n: N) := n - 1. *)

Fixpoint first_N_bv (l : list bool) (n : nat) : list bool :=
  match n with
    | O => nil
    | S n2 =>
    match l with
      | nil => nil
      | x :: l2 => x :: (first_N_bv l2 (n - 1))
    end
  end.
Check first_N_bv.

Definition p2bv_bv' (p: positive) (size: nat) : bv :=
  match p2bv_bv p size with
    | mk_bv s l => mk_bv size (first_N_bv l size)
  end.

Eval compute in p2bv_bv' 15 3.
Eval compute in p2bv_bv' 26 6.
Eval compute in p2bv_bv' 26 5.
Eval compute in p2bv_bv' 26 4.
Eval compute in p2bv_bv' 26 3.
Eval compute in p2bv_bv' 15 1.

Definition n2bv_bv (m: nat) (size: nat) : bv :=
  match m with
    | O => (mk_bv size (nil))
    | p => p2bv_bv' (Pos.of_nat p) size
  end.
Check n2bv_bv.

Definition n2b_bv (m: nat) (size: nat) : list bool := 
  match n2bv_bv m size with
    | mk_bv _ l => l
  end.
Check n2b_bv.

Definition add_bv (a b: bv) (size: nat) : bv :=
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c + d in
    n2bv_bv e size.
Check add_bv.

Fixpoint compare_naturals (a b: nat): comparison :=
  match a with
    | O => 
    match b with
      | O => Eq
      | _ => Lt
    end
    | S n => 
    match b with
      | O   => Gt
      | S m => compare_naturals n m
    end
  end.

Eval compute in compare_naturals 10 12.

Fixpoint append_false (a: bv) (size: nat) {struct size} : bv :=
  match size with
    | O => a
    | S n =>  
    match a with
      | mk_bv s l =>
      match (compare_naturals (length l) (size + s + 1) ) with
        | Eq => a
        | Lt => append_false (mk_bv (length l + 1) (l ++ [false])) n
        | Gt => a
      end
    end
  end.

Definition append_false' (a: bv) (size: nat) :=
  match a with
    | mk_bv s l => append_false a (size - (length l))
  end.

Eval compute in append_false' (mk_bv 23 [true; true; true ; true ; true]) 21.

(*(N.to_nat (N.div (N.of_nat (length l)) 2) - 3)*)

Fixpoint beq_list (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => true
    | x :: l', y :: m' => (Bool.eqb x y) && (beq_list l' m')
    | _, _ => false
  end.

Search (nat -> (nat -> bool)).

Definition eq_bv (a b: bv): bool:=
  match a with
    | mk_bv s1 l1 =>
    match b with
      | mk_bv s2 l2 =>
      match EqNat.beq_nat s1 s2 with
       | true =>
       match beq_list l1 l2 with
         | true => true
         | _    => false
         end
       | _ => false
      end
    end
 end.

Eval compute in eq_bv (mk_bv 3 [true ; false ; true]) (mk_bv 3 [true; false; true]).
Eval compute in eq_bv (mk_bv 3 [true ; false ; true]) (mk_bv 3 [false ; true; false; true]).
Eval compute in eq_bv (mk_bv 3 [true ; false ; true]) (mk_bv 4 [true; false; true]).

About bool_eq.
SearchAbout EqNat.beq_nat. 

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

SearchAbout EqNat.beq_nat. 

Lemma Leq_bv: forall (x y: bv), eq_bv x y = true <-> x = y.
Proof. intros x y; split. destruct x. destruct y. simpl; auto. intro H.
       case_eq (EqNat.beq_nat size0 size1); intro H1.
       case_eq (beq_list bits0 bits1); intro H2.
         rewrite List_eq in H2.
         - apply EqNat.beq_nat_true in H1.
           rewrite H1, H2; reflexivity.
         - contradict H. rewrite H1, H2. easy.
         - contradict H. rewrite H1. easy.
         - intro H. destruct x. destruct y. inversion H.
           rewrite <- H1. rewrite <- H2. simpl.
           rewrite <- (EqNat.beq_nat_refl size0).
           rewrite List_eq_refl; trivial.
Qed.

Definition add_bv2 (a b: bv) (size: nat) : bv :=
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c + d in
    (append_false' (n2bv_bv e size) size).

Eval compute in add_bv2 (mk_bv 3 [true ; false ; true]) (mk_bv 3 [true; true; false]) 5.
Eval compute in add_bv (mk_bv 3 [false ; false ; false]) (mk_bv 3 [false; false; false]) 3.

(*Chantal's add*)

Fixpoint fold_left2 A B (f: A -> B -> B -> A) (xs ys: list B) (acc:A) : A :=
  match xs, ys with
  | nil, _ | _, nil => acc
  | x::xs, y::ys => @fold_left2 A B f xs ys (f acc x y)
  end.

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

Compute (add_list (false::true::false::false::nil) (false::true::true::false::nil)).
Search (nat -> (nat -> bool)).
Definition add_bv_Ch (b1 b2 : (list bool * nat)%type) : (list bool * nat)%type :=
  let (b1, n1) := b1 in
  let (b2, n2) := b2 in
  if EqNat.beq_nat n1 n2 then (add_list b1 b2, n1) else (nil, 0).

(**)

Eval compute in
  let a := (mk_bv 5 [false; false; true; true; true]) in
    let b := (mk_bv 3 [true; true; true; true; true]) in
      add_bv a b 6.

Definition sub_bv (a b: bv) (size: nat) : bv := 
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c - d in 
    n2bv_bv e size.
Check sub_bv.

Definition mul_bv (a b: bv) (size: nat) : bv :=
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c * d in
    n2bv_bv e size.
Check mul_bv.

Fixpoint exp (m n: nat) {struct n}: nat :=
  match n with
    | O    => 1%nat
    | S n' => m * (exp m n')
  end.
Notation "x ^ y" := (exp x y).

Definition neg_bv (a: bv) (size: nat): bv :=
  let b := exp 2 size in
  let c := bv2n_bv a in
  let d := b - c in
    n2bv_bv d size. 
Check neg_bv.

Definition div_bv (a b: bv) (size: nat): bv := 
  let c := (bv2n_bv b) in
    match c with
      | O => mk_bv 0 nil
      | _ => let d := (bv2n_bv a) in mk_bv size (n2b_bv size (N.to_nat (N.div (N.of_nat d) (N.of_nat c))))
    end.
Check div_bv.

Definition urem_bv (a b: bv) (size: nat) : bv :=
  let c := (bv2n_bv b) in
    match c with
      | O => mk_bv 0 nil
      | _ => let d := (bv2n_bv a) in mk_bv size (n2b_bv size (N.to_nat (N.modulo (N.of_nat d) (N.of_nat c))))
   end.
Check urem_bv.

Definition ult_bv (a b: bv) :=
  let c := (bv2n_bv a) in
  let d := (bv2n_bv b) in
    (c < d).
Check ult_bv.

Fixpoint drop_n_bv (l : list bool) (n : nat) : list bool :=
  match n with
    | O => l
    | S n2 => drop_n_bv (@List.tl bool l) n2
  end.
Check drop_n_bv.

Fixpoint first_n_bv (l : list bool) (n : nat) : list bool :=
  match n with
    | O => nil
    | S n2 =>
    match l with
      | nil => nil
      | x :: l2 => x :: (first_n_bv l2 n2)
    end
  end.
Check first_n_bv.

Definition extract_bv (l : list bool) (i : nat) (j : nat) : list bool :=
  let l2 := drop_n_bv l i in (first_n_bv l2 j).
Check extract_bv.

Definition wd (a: bv) : Prop :=
  match a with
    | mk_bv s l => length l = s
  end.
Check wd.
Eval compute in wd (mk_bv 6 [false ; false ; true ; true ; true]).

Lemma concat_wd : forall (m: nat) (a b: bv), wd a -> wd b -> wd (concat_bv a b).
Proof. intros.
         induction a. induction b. 
           simpl. rewrite app_length. destruct H, H0; reflexivity.
Qed.
Check concat_wd.

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
Check nth_appendl.


Lemma nth_concat_l_bv : forall (a b: bv) (i : nat),
      match a with
        | mk_bv s l1 => wd a -> wd b -> (i < s) -> bb_nth_bv i (concat_bv a b) = bb_nth_bv i a
      end.
Proof. intros.
         induction a. induction b.
           simpl. intros. rewrite nth_appendl.
             - reflexivity.
             - rewrite H. exact H1.
Qed.
Check nth_concat_l_bv. 


End DTBV.


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

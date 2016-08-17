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

Add Rec LoadPath "." as SMTCoq.

Require Import List Bool NArith Psatz Int63 Nnat.
Require Import Misc.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope bool_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* We temporarily assume proof irrelevance to handle dependently typed
   bit vectors *)
Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2.

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof. intros. lia. Qed.

Module Type BITVECTOR.

  Parameter bitvector : N -> Type.
  Parameter bits      : forall n, bitvector n -> list bool.
  Parameter of_bits   : forall (l:list bool), bitvector (N.of_nat (List.length l)).
  Parameter bitOf     : forall n, nat -> bitvector n -> bool.

  (* Constants *)
  Parameter zeros     : forall n, bitvector n.

  (*equality*)
  Parameter bv_eq     : forall n, bitvector n -> bitvector n -> bool.

  (*binary operations*)
  Parameter bv_concat : forall n m, bitvector n -> bitvector m -> bitvector (n + m).
  Parameter bv_and    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_or     : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_xor    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_add    : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_subt   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_mult   : forall n, bitvector n -> bitvector n -> bitvector n.
  Parameter bv_ult    : forall n, bitvector n -> bitvector n -> bool.
  Parameter bv_slt    : forall n, bitvector n -> bitvector n -> bool. 

    (*unary operations*)
  Parameter bv_not    : forall n, bitvector n -> bitvector n.
  Parameter bv_neg    : forall n, bitvector n -> bitvector n.

  (* Specification *)
  Axiom bits_size     : forall n (bv:bitvector n), List.length (bits bv) = N.to_nat n.
  Axiom bv_eq_reflect : forall n (a b:bitvector n), bv_eq a b = true <-> a = b.
  Axiom bv_and_comm   : forall n (a b:bitvector n), bv_eq (bv_and a b) (bv_and b a) = true.
  Axiom bv_or_comm    : forall n (a b:bitvector n), bv_eq (bv_or a b) (bv_or b a) = true.
  Axiom bv_add_comm   : forall n (a b:bitvector n), bv_eq (bv_add a b) (bv_add b a) = true. 
 (* Axiom bv_mult_comm  : forall n (a b:bitvector n), bv_eq (bv_mult a b) (bv_mult b a) = true. *)

  Axiom bv_and_assoc  : forall n (a b c: bitvector n), bv_eq (bv_and a (bv_and b c)) (bv_and (bv_and a b) c) = true.
  Axiom bv_or_assoc   : forall n (a b c: bitvector n), bv_eq (bv_or a (bv_or b c)) (bv_or (bv_or a b) c) = true.
  Axiom bv_xor_assoc  : forall n (a b c: bitvector n), bv_eq (bv_xor a (bv_xor b c)) (bv_xor (bv_xor a b) c) = true.
  Axiom bv_add_assoc  : forall n (a b c: bitvector n), bv_eq (bv_add a (bv_add b c)) (bv_add (bv_add a b) c) = true.
  Axiom bv_not_involutive: forall n (a: bitvector n), bv_eq (bv_not (bv_not a)) a = true.
  
  Parameter _of_bits : forall (l: list bool) (s : N), bitvector s.

End BITVECTOR.

Module Type RAWBITVECTOR.

Parameter bitvector  : Type.
Parameter size       : bitvector -> N.
Parameter bits       : bitvector -> list bool.
Parameter of_bits    : list bool -> bitvector.
Parameter _of_bits   : list bool -> N -> bitvector.
Parameter bitOf      : nat -> bitvector -> bool.

(* Constants *)
Parameter zeros      : N -> bitvector.

(*equality*)
Parameter bv_eq      : bitvector -> bitvector -> bool.

(*binary operations*)
Parameter bv_concat  : bitvector -> bitvector -> bitvector.
Parameter bv_and     : bitvector -> bitvector -> bitvector.
Parameter bv_or      : bitvector -> bitvector -> bitvector.
Parameter bv_xor     : bitvector -> bitvector -> bitvector.
Parameter bv_add     : bitvector -> bitvector -> bitvector.
Parameter bv_mult    : bitvector -> bitvector -> bitvector.
Parameter bv_subt    : bitvector -> bitvector -> bitvector.
Parameter bv_ult     : bitvector -> bitvector -> bool.
Parameter bv_slt     : bitvector -> bitvector -> bool.

(*unary operations*)
Parameter bv_not     : bitvector -> bitvector.
Parameter bv_neg     : bitvector -> bitvector.

(* All the operations are size-preserving *)

Axiom bits_size      : forall bv, List.length (bits bv) = N.to_nat (size bv).
Axiom of_bits_size   : forall l, N.to_nat (size (of_bits l)) = List.length l.
Axiom _of_bits_size  : forall l s,(size (_of_bits l s)) = s.
Axiom zeros_size     : forall n, size (zeros n) = n.
Axiom bv_concat_size : forall n m a b, size a = n -> size b = m -> size (bv_concat a b) = n + m.
Axiom bv_and_size    : forall n a b, size a = n -> size b = n -> size (bv_and a b) = n.
Axiom bv_or_size     : forall n a b, size a = n -> size b = n -> size (bv_or a b) = n.
Axiom bv_xor_size    : forall n a b, size a = n -> size b = n -> size (bv_xor a b) = n.
Axiom bv_add_size    : forall n a b, size a = n -> size b = n -> size (bv_add a b) = n.
Axiom bv_subt_size   : forall n a b, size a = n -> size b = n -> size (bv_subt a b) = n.
Axiom bv_mult_size   : forall n a b, size a = n -> size b = n -> size (bv_mult a b) = n.
Axiom bv_not_size    : forall n a, size a = n -> size (bv_not a) = n.
Axiom bv_neg_size    : forall n a, size a = n -> size (bv_neg a) = n.

(* Specification *)
Axiom bv_eq_reflect  : forall a b, bv_eq a b = true <-> a = b.
Axiom bv_and_comm    : forall n a b, size a = n -> size b = n -> bv_and a b = bv_and b a.
Axiom bv_or_comm     : forall n a b, size a = n -> size b = n -> bv_or a b = bv_or b a.
Axiom bv_add_comm    : forall n a b, size a = n -> size b = n -> bv_add a b = bv_add b a.
(*Axiom bv_mult_comm   : forall n a b, size a = n -> size b = n -> bv_mult a b = bv_mult b a.*)

Axiom bv_and_assoc  : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                   (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Axiom bv_or_assoc   : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                   (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Axiom bv_xor_assoc  : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                   (bv_xor a (bv_xor b c)) = (bv_xor (bv_xor a b) c).
Axiom bv_add_assoc  : forall n a b c, size a = n -> size b = n -> size c = n -> 
                                   (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Axiom bv_not_involutive: forall a, bv_not (bv_not a) = a.

End RAWBITVECTOR.

Module RAW2BITVECTOR (M:RAWBITVECTOR) <: BITVECTOR.

  Record bitvector_ (n:N) : Type :=
    MkBitvector
      { bv :> M.bitvector;
        wf : M.size bv = n
      }.
  Definition bitvector := bitvector_.

  Definition bits n (bv:bitvector n) := M.bits bv.

  Lemma of_bits_size l : M.size (M.of_bits l) = N.of_nat (List.length l).
  Proof. now rewrite <- M.of_bits_size, N2Nat.id. Qed.
  
  Lemma _of_bits_size l s: M.size (M._of_bits l s) = s.
  Proof. apply (M._of_bits_size l s). Qed. 

  Definition of_bits (l:list bool) : bitvector (N.of_nat (List.length l)) :=
    @MkBitvector _ (M.of_bits l) (of_bits_size l).
    
  Definition _of_bits (l: list bool) (s : N): bitvector s :=
  @MkBitvector _ (M._of_bits l s) (_of_bits_size l s).

  Definition bitOf n p (bv:bitvector n) : bool := M.bitOf p bv.

  Definition zeros (n:N) : bitvector n :=
    @MkBitvector _ (M.zeros n) (M.zeros_size n).

  Definition bv_eq n (bv1 bv2:bitvector n) := M.bv_eq bv1 bv2.

  Definition bv_and n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_and bv1 bv2) (M.bv_and_size (wf bv1) (wf bv2)).

  Definition bv_or n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_or bv1 bv2) (M.bv_or_size (wf bv1) (wf bv2)).

  Definition bv_add n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_add bv1 bv2) (M.bv_add_size (wf bv1) (wf bv2)).

  Definition bv_subt n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_subt bv1 bv2) (M.bv_subt_size (wf bv1) (wf bv2)).

  Definition bv_mult n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_mult bv1 bv2) (M.bv_mult_size (wf bv1) (wf bv2)).

  Definition bv_xor n (bv1 bv2:bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_xor bv1 bv2) (M.bv_xor_size (wf bv1) (wf bv2)).

  Definition bv_ult n (bv1 bv2:bitvector n) : bool := M.bv_ult bv1 bv2.

  Definition bv_slt n (bv1 bv2:bitvector n) : bool := M.bv_slt bv1 bv2.
  
  Definition bv_not n (bv1: bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_not bv1) (M.bv_not_size (wf bv1)).

  Definition bv_neg n (bv1: bitvector n) : bitvector n :=
    @MkBitvector n (M.bv_neg bv1) (M.bv_neg_size (wf bv1)).

  Definition bv_concat n m (bv1:bitvector n) (bv2: bitvector m) : bitvector (n + m) :=
    @MkBitvector (n + m) (M.bv_concat bv1 bv2) (M.bv_concat_size (wf bv1) (wf bv2)).

  Lemma bits_size n (bv:bitvector n) : List.length (bits bv) = N.to_nat n.
  Proof. unfold bits. now rewrite M.bits_size, wf. Qed.

  (* The next lemma is provable only if we assume proof irrelevance *)
  Lemma bv_eq_reflect n (a b: bitvector n) : bv_eq a b = true <-> a = b.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. split.
    - revert a b. intros [a Ha] [b Hb]. simpl. intros ->.
      rewrite (proof_irrelevance Ha Hb). reflexivity.
    - now intros ->.
  Qed.

  Lemma bv_and_comm n (a b:bitvector n) : bv_eq (bv_and a b) (bv_and b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_and_comm n); now rewrite wf.
  Qed.

  Lemma bv_or_comm n (a b:bitvector n) : bv_eq (bv_or a b) (bv_or b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_or_comm n); now rewrite wf.
  Qed.

  Lemma bv_add_comm n (a b:bitvector n) : bv_eq (bv_add a b) (bv_add b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_add_comm n); now rewrite wf.
  Qed.

(*
  Lemma bv_mult_comm n (a b:bitvector n) : bv_eq (bv_mult a b) (bv_mult b a) = true.
  Proof.
    unfold bv_eq. rewrite M.bv_eq_reflect. apply (@M.bv_mult_comm n); now rewrite wf.
  Qed.
*)

  Lemma bv_and_assoc : forall n (a b c :bitvector n), bv_eq (bv_and a (bv_and b c)) (bv_and (bv_and a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_and_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_or_assoc : forall n (a b c :bitvector n), bv_eq (bv_or a (bv_or b c)) (bv_or (bv_or a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_or_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_xor_assoc : forall n (a b c :bitvector n), bv_eq (bv_xor a (bv_xor b c)) (bv_xor (bv_xor a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_xor_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_add_assoc : forall n (a b c :bitvector n), bv_eq (bv_add a (bv_add b c)) (bv_add (bv_add a b) c) = true.
  Proof.
     intros n a b c.
     unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
     apply (@M.bv_add_assoc n a b c); now rewrite wf.
  Qed.

  Lemma bv_not_involutive: forall n (a: bitvector n), bv_eq (bv_not (bv_not a)) a = true.
  Proof.
       intros n a.
       unfold bv_eq. rewrite M.bv_eq_reflect. simpl. 
       apply (@M.bv_not_involutive a); now rewrite wf.
  Qed.


End RAW2BITVECTOR.

Module RAWBITVECTOR_LIST <: RAWBITVECTOR.

Definition bitvector := list bool.
Definition bits (a:bitvector) : list bool := a.
Definition size (a:bitvector) := N.of_nat (List.length a).
Definition of_bits (a:list bool) : bitvector := a.

Lemma bits_size bv : List.length (bits bv) = N.to_nat (size bv).
Proof. unfold bits, size. now rewrite Nat2N.id. Qed.

Lemma of_bits_size l : N.to_nat (size (of_bits l)) = List.length l.
Proof. unfold of_bits, size. now rewrite Nat2N.id. Qed.

Fixpoint beq_list (l m : list bool) {struct l} :=
  match l, m with
    | nil, nil => true
    | x :: l', y :: m' => (Bool.eqb x y) && (beq_list l' m')
    | _, _ => false
  end.

Definition bv_eq (a b: bitvector): bool:=
  if ((size a) =? (size b)) then beq_list (bits a) (bits b) else false.

Lemma bv_mk_eq l1 l2 : bv_eq l1 l2 = beq_list l1 l2.
Proof.
  unfold bv_eq, size, bits.
  case_eq (Nat_eqb (length l1) (length l2)); intro Heq.
  - now rewrite (EqNat.beq_nat_true _ _ Heq), N.eqb_refl.
  - replace (N.of_nat (length l1) =? N.of_nat (length l2)) with false.
    * revert l2 Heq. induction l1 as [ |b1 l1 IHl1]; intros [ |b2 l2]; simpl in *; auto.
      intro Heq. now rewrite <- (IHl1 _ Heq), andb_false_r.
    * symmetry. rewrite N.eqb_neq. intro H. apply Nat2N.inj in H. rewrite H in Heq.
      rewrite <- EqNat.beq_nat_refl in Heq. discriminate.
Qed.

Definition bv_concat (a b: bitvector) : bitvector := a ++ b.

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
         induction xs as [ | a xs IHxs]; intros acc H.
         simpl. auto.
         intros [ | b ys].
            + simpl. exact H.
            + simpl. apply IHxs, H1. exact H.
  Qed.

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

Definition zeros (n : N) : bitvector := mk_list_false (N.to_nat n).

End Fold_left2.

Definition bitOf (n: nat) (a: bitvector): bool := nth n a false.

Definition bv_and (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 andb (@bits a) (@bits b)
    | _    => nil
  end.

Definition bv_or (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 orb (@bits a) (@bits b)
    | _    => nil
  end.

Definition bv_xor (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => map2 xorb (@bits a) (@bits b)
    | _    => nil
  end.

Definition bv_not (a: bitvector) : bitvector := map negb (@bits a).


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
    | true => add_list a b
    | _    => nil
  end.

  (*substraction*)

Definition twos_complement b :=
  add_list_ingr (map negb b) (mk_list_false (length b)) true.
  
Definition bv_neg (a: bitvector) : bitvector := (twos_complement a).

Definition subst_list' a b := add_list a (twos_complement b).

Definition bv_subt' (a b : bitvector) : bitvector :=
   match (@size a) =? (@size b) with
     | true => (subst_list' (@bits a) (@bits b))
     | _    => nil
   end.

Definition subst_borrow b1 b2 b :=
  match b1, b2, b with
    | true,  true,  true  => (true, true)
    | true,  true,  false => (false, false)
    | true,  false, true  => (false, false)
    | false, true,  true  => (false, true)
    | false, false, true  => (true, true)
    | false, true,  false => (true, true)
    | true,  false, false => (true, false)
    | false, false, false => (false, false)
  end.

Fixpoint subst_list_borrow bs1 bs2 b {struct bs1} :=
  match bs1, bs2 with
    | nil, _               => nil
    | _ , nil              => nil
    | b1 :: bs1, b2 :: bs2 =>
      let (r, b) := subst_borrow b1 b2 b in r :: (subst_list_borrow bs1 bs2 b)
  end.

Definition subst_list (a b: list bool) := subst_list_borrow a b false.

Definition bv_subt (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with 
    | true => (subst_list (@bits a) (@bits b))
    | _    => nil 
  end.
  
(*less than*)

Fixpoint ult_list (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: nil, yi :: nil => (andb (negb xi) yi)
    | xi :: x', yi :: y' =>   (orb (andb (Bool.eqb xi yi) (ult_list x' y')) 
                              (andb (negb xi) yi))
  end.                    
     
Definition rev_ult_list (x y: list bool) := (ult_list (List.rev x) (List.rev y)).


Fixpoint slt_list (x y: list bool) :=
  match x, y with
    | nil, _  => false
    | _ , nil => false
    | xi :: nil, yi :: nil => (andb xi (negb yi))
    | xi :: x', yi :: y'   => (orb (andb (Bool.eqb xi yi) (ult_list x' y'))
                                  (andb xi (negb yi)))
  end.

Definition rev_slt_list (x y: list bool) := (slt_list (List.rev x) (List.rev y)).
Definition bv_ult (a b : bitvector) : bool :=
  if ((@size a) =? (@size b))
    then rev_ult_list a b
    else false.

Definition bv_slt (a b : bitvector) : bool :=
  if ((@size a) =? (@size b))
    then rev_slt_list a b
    else false.

  (*multiplication*)

Fixpoint mult_list_carry (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry xs (false :: b) n)
      else
        mult_list_carry xs (false :: b) n
  end.

Fixpoint mult_list_carry2 (a b :list bool) n {struct a}: list bool :=
  match a with
    | nil      => mk_list_false n
    | a' :: xs =>
      if a' then
        add_list b (mult_list_carry2 xs (false :: (removelast b)) n)
      else
        mult_list_carry2 xs (false :: (removelast b)) n
  end.
  
Fixpoint and_with_bool (a: list bool) (bt: bool) : list bool :=
  match a with
    | nil => nil
    | ai :: a' => (bt && ai) :: and_with_bool a' bt 
  end.


Fixpoint mult_bool_step_k_h (a b: list bool) (c: bool) (k: Z) : list bool :=
  match a, b with
    | nil , _ => nil
    | ai :: a', bi :: b' =>
      if (k - 1 <? 0)%Z then
        let carry_out := (ai && bi) || ((xorb ai bi) && c) in
        let curr := xorb (xorb ai bi) c in
        curr :: mult_bool_step_k_h a' b' carry_out (k - 1)
      else
        ai :: mult_bool_step_k_h a' b c (k - 1)
    | ai :: a' , nil => ai :: mult_bool_step_k_h a' b c k
  end.


Fixpoint top_k_bools (a: list bool) (k: int) : list bool :=
  if (k == 0)%int then nil
  else match a with
         | nil => nil
         | ai :: a' => ai :: top_k_bools a' (k - 1)
       end.


Fixpoint mult_bool_step (a b: list bool) (res: list bool) (k k': nat) : list bool :=
  let ak := List.firstn (S k') a in
  let b' := and_with_bool ak (nth k b false) in
  let res' := mult_bool_step_k_h res b' false (Z.of_nat k) in
  match k' with
    | O => res'
    (* | S O => res' *)
    | S pk' => mult_bool_step a b res' (S k) pk'
  end.


Definition bvmult_bool (a b: list bool) (n: nat) : list bool :=
  let res := and_with_bool a (nth 0 b false) in
  match n with
    | O => res
    | S O => res
    | S (S k) => mult_bool_step a b res 1 k
  end.

(*
Definition check_mult_bool (bs1 bs2 bsres: list bool) : bool :=
    let bvm12 := bvmult_bool bs1 bs2 (length bsres) in
    forallb2 eq_carry_lit bvm12 bsres.


Lemma prop_main: forall bs1 bs2 bsres,
                 check_mult bs1 bs2 bsres = true ->
                 (bvmult_bool bs1 bs2 (length bs1)) = bsres.
*)

Definition mult_list a b := bvmult_bool a b (length a).

Definition bv_mult (a b : bitvector) : bitvector :=
  if ((@size a) =? (@size b))
  then mult_list a b
  else zeros (@size a).

(*
Definition mult_list a b := mult_list_carry a b (length a).

Definition bv_mult (a b : bitvector) : bitvector :=
  match (@size a) =? (@size b) with
    | true => mult_list (@bits a) (@bits b)
    | _    => nil
  end.
*)

(* Theorems *)

Lemma length_mk_list_false: forall n, length (mk_list_false n) = n.
Proof. intro n.
       induction n as [ | n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Definition _of_bits (a:list bool) (s: N) := 
if (N.of_nat (length a) =? s) then a else zeros s.

Lemma _of_bits_size l s: (size (_of_bits l s)) = s.
Proof. unfold of_bits, size. unfold _of_bits.
       case_eq ( N.of_nat (length l) =? s).
       intros. now rewrite N.eqb_eq in H.
       intros. unfold zeros. rewrite length_mk_list_false.
       now rewrite N2Nat.id.
Qed.

Lemma length_mk_list_true: forall n, length (mk_list_true n) = n.
Proof. intro n.
       induction n as [ | n' IHn].
       - simpl. auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma zeros_size (n : N) : size (zeros n) = n.
Proof. unfold size, zeros. now rewrite length_mk_list_false, N2Nat.id. Qed. 

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

Lemma bv_eq_reflect a b : bv_eq a b = true <-> a = b.
Proof.
  unfold bv_eq. case_eq (size a =? size b); intro Heq; simpl.
  - apply List_eq.
  - split; try discriminate.
    intro H. rewrite H, N.eqb_refl in Heq. discriminate.
Qed.

Lemma bv_concat_size n m a b : size a = n -> size b = m -> size (bv_concat a b) = n + m.
Proof.
  unfold bv_concat, size. intros H0 H1.
  rewrite app_length, Nat2N.inj_add, H0, H1; reflexivity.
Qed.

(*list bitwise AND properties*)

Lemma map2_and_comm: forall (a b: list bool), (map2 andb a b) = (map2 andb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' = b' && a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply andb_comm.
Qed.

Lemma map2_and_assoc: forall (a b c: list bool), (map2 andb a (map2 andb b c)) = (map2 andb (map2 andb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (a' && (b' && c') = a' && b' && c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply andb_assoc.
Qed.

Lemma map2_and_idem1:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && a' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite andb_comm, andb_assoc, andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm:  forall (a b: list bool), (map2 andb (map2 andb a b) a) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem1. Qed.

Lemma map2_and_idem2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb a b).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' && b' && b' = a' && b'). intro H. rewrite H. apply f_equal.
           apply IHxs. rewrite <- andb_assoc. rewrite andb_diag. reflexivity. 
Qed.

Lemma map2_and_idem_comm2:  forall (a b: list bool), (map2 andb (map2 andb a b) b) = (map2 andb b a).
Proof. intros a b. symmetry. rewrite <- map2_and_comm. symmetry; apply map2_and_idem2. Qed.

Lemma map2_and_empty_empty1:  forall (a: list bool), (map2 andb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_and_empty_empty2:  forall (a: list bool), (map2 andb [] a) = [].
Proof. intros a. rewrite map2_and_comm. apply map2_and_empty_empty1. Qed.

Lemma map2_nth_empty_false:  forall (i: nat), nth i [] false = false.
Proof. intros i. induction i as [ | IHi]; simpl; reflexivity. Qed.

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
       induction n as [ | n' IHn].
         + auto.
         + intro acc. simpl. rewrite IHn. simpl. lia.
Qed.

Lemma map2_and_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 andb a b) false = (nth i a false) && (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_and_empty_empty2.
             rewrite map2_nth_empty_false. reflexivity.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_and_empty_empty1.
             rewrite map2_nth_empty_false. rewrite andb_false_r. reflexivity.
           + intros i H0 H1. simpl.
             revert i H1. intros [ | i IHi].
             * simpl. auto.
             * apply IHxs.
                 inversion H0; reflexivity.
                 inversion IHi; lia.
Qed.

Lemma length_mk_list_true_full: forall n, length (mk_list_true_acc n []) = n.
Proof. intro n. rewrite (@add_mk_list_true n []). auto. Qed.

Lemma mk_list_app: forall n acc, mk_list_true_acc n acc = mk_list_true_acc n [] ++ acc.
Proof. intro n.
       induction n as [ | n IHn].
         + auto.
         + intro acc. simpl in *. rewrite IHn. 
           cut (mk_list_true_acc n [] ++ [true] = mk_list_true_acc n [true]). intro H.
           rewrite <- H. rewrite <- app_assoc. unfold app. reflexivity.
           rewrite <- IHn. reflexivity.
Qed.

Lemma mk_list_ltrue: forall n, mk_list_true_acc n [true] = mk_list_true_acc (S n) [].
Proof. intro n. induction n as [ | n IHn]; auto. Qed.

Lemma map2_and_1_neutral: forall (a: list bool), (map2 andb a (mk_list_true (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite andb_true_r. reflexivity.
Qed.

Lemma map2_and_0_absorb: forall (a: list bool), (map2 andb a (mk_list_false (length a))) = (mk_list_false (length a)).
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite andb_false_r; reflexivity.
Qed.

Lemma map2_and_length: forall (a b: list bool), length a = length b -> length a = length (map2 andb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

(*bitvector AND properties*)

Lemma bv_and_size n a b : size a = n -> size b = n -> size (bv_and a b) = n.
Proof.
  unfold bv_and. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_and_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_comm n a b : size a = n -> size b = n -> bv_and a b = bv_and b a.
(* Lemma bv_and_comm: forall a b, (size a) = (size b) -> bv_and a b = bv_and b a. *)
Proof.
  intros H1 H2. unfold bv_and. rewrite H1, H2.
  rewrite N.eqb_compare, N.compare_refl.
  rewrite map2_and_comm. reflexivity.
Qed.

Lemma bv_and_assoc: forall n a b c, size a = n -> size b = n -> size c = n -> 
                                  (bv_and a (bv_and b c)) = (bv_and (bv_and a b) c).
Proof. intros n a b c H0 H1 H2.
       unfold bv_and, size, bits in *. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite H0. rewrite N.compare_refl.
       rewrite <- (@map2_and_length a b). rewrite <- map2_and_length. rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite map2_and_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_and_idem1:  forall a b n, size a = n -> size b = n -> (bv_and (bv_and a b) a) = (bv_and a b).
Proof. intros a b n H0 H1.
        unfold bv_and. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_and_length. rewrite N.compare_refl. 
       rewrite map2_and_idem1; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_and_idem2: forall a b n, size a = n ->  size b = n -> (bv_and (bv_and a b) b) = (bv_and a b).
Proof. intros a b n H0 H1.
       unfold bv_and. rewrite H0. do 2 rewrite N.eqb_compare.
       unfold size in *.
       rewrite H1. rewrite N.compare_refl.
       rewrite <- H0. unfold bits.
       rewrite <- map2_and_length. rewrite N.compare_refl. 
       rewrite map2_and_idem2; reflexivity.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Definition bv_empty: bitvector := nil.

Lemma bv_and_empty_empty1: forall a, (bv_and a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty, bv_and, size, bits. simpl.
       rewrite map2_and_empty_empty1.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a))) in H.
           rewrite H. simpl. reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_and_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_and a b)) false = (nth i (bits a) false) && (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_and. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_and_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_and_empty_empty2: forall a, (bv_and bv_empty a) = bv_empty.
Proof. intro a. unfold bv_and, bv_empty, size.
       case (length a); simpl; auto.
Qed.

Lemma bv_and_1_neutral: forall a, (bv_and a (mk_list_true (length (bits a)))) = a.
Proof. intro a. unfold bv_and.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_and_1_neutral. reflexivity.
Qed.

Lemma bv_and_0_absorb: forall a, (bv_and a (mk_list_false (length (bits a)))) = (mk_list_false (length (bits a))).
Proof. intro a. unfold bv_and.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false. 
       rewrite N.compare_refl.
       rewrite map2_and_0_absorb. reflexivity.
Qed.

(* lists bitwise OR properties *)

Lemma map2_or_comm: forall (a b: list bool), (map2 orb a b) = (map2 orb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (a' || b' = b' || a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply orb_comm.
Qed.

Lemma map2_or_assoc: forall (a b c: list bool), (map2 orb a (map2 orb b c)) = (map2 orb (map2 orb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (a' || (b' || c') = a' || b' || c'). intro H. rewrite <- H. apply f_equal.
            apply IHxs. apply orb_assoc.
Qed.

Lemma map2_or_length: forall (a b: list bool), length a = length b -> length a = length (map2 orb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_or_empty_empty1:  forall (a: list bool), (map2 orb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_or_empty_empty2:  forall (a: list bool), (map2 orb [] a) = [].
Proof. intros a. rewrite map2_or_comm. apply map2_or_empty_empty1. Qed.

Lemma map2_or_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 orb a b) false = (nth i a false) || (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_or_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_or_empty_empty1.
             rewrite map2_nth_empty_false. rewrite orb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. intros [ | i IHi].
             * simpl. auto.
             * apply IHxs.
                 inversion H0; reflexivity.
                 inversion IHi; lia.
Qed.

Lemma map2_or_0_neutral: forall (a: list bool), (map2 orb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite orb_false_r. reflexivity.
Qed.

Lemma map2_or_1_true: forall (a: list bool), (map2 orb a (mk_list_true (length a))) = (mk_list_true (length a)).
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs.
         rewrite orb_true_r; reflexivity.
Qed.

(*bitvector OR properties*)

Lemma bv_or_size n a b : size a = n -> size b = n -> size (bv_or a b) = n.
Proof.
  unfold bv_or. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_or_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_comm: forall n a b, (size a) = n -> (size b) = n -> bv_or a b = bv_or b a.
Proof. intros a b n H0 H1. unfold bv_or.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_or_comm. reflexivity.
Qed.

Lemma bv_or_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_or a (bv_or b c)) = (bv_or (bv_or a b) c).
Proof. intros n a b c H0 H1 H2. 
       unfold bv_or. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@map2_or_length b c).
       rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- (@map2_or_length a b).
       rewrite H0. rewrite N.compare_refl.
       rewrite map2_or_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_or_empty_empty1: forall a, (bv_or a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty. 
       unfold bv_or, bits, size. simpl.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a)) 0) in H.
           rewrite H. simpl. rewrite map2_or_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_or_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_or a b)) false = (nth i (bits a) false) || (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_or. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_or_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_or_0_neutral: forall a, (bv_or a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_or.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite map2_or_0_neutral. reflexivity.
Qed.

Lemma bv_or_1_true: forall a, (bv_or a (mk_list_true (length (bits a)))) = (mk_list_true (length (bits a))).
Proof. intro a. unfold bv_or.
       rewrite N.eqb_compare.  unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_or_1_true. reflexivity.
Qed.

(* lists bitwise XOR properties *)

Lemma map2_xor_comm: forall (a b: list bool), (map2 xorb a b) = (map2 xorb b a).
Proof. intros a. induction a as [ | a' xs IHxs].
       intros [ | b' ys].
       - simpl. auto.
       - simpl. auto.
       - intros [ | b' ys].
         + simpl. auto.
         + intros. simpl. 
           cut (xorb a' b' = xorb b' a'). intro H. rewrite <- H. apply f_equal.
           apply IHxs. apply xorb_comm.
Qed.

Lemma map2_xor_assoc: forall (a b c: list bool), (map2 xorb a (map2 xorb b c)) = (map2 xorb (map2 xorb a b) c).
Proof. intro a. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b' ys].
        -  simpl. auto.
        - intros [ | c' zs].
          + simpl. auto.
          + simpl. cut (xorb a' (xorb b' c') = (xorb (xorb a'  b')  c')). intro H. rewrite <- H. apply f_equal.
            apply IHxs. rewrite xorb_assoc_reverse. reflexivity.
Qed.

Lemma map2_xor_length: forall (a b: list bool), length a = length b -> length a = length (map2 xorb a b).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *. apply f_equal. apply IHxs.
         inversion H; auto.
Qed.

Lemma map2_xor_empty_empty1:  forall (a: list bool), (map2 xorb a []) = [].
Proof. intros a. induction a as [ | a' xs IHxs]; simpl; auto. Qed.

Lemma map2_xor_empty_empty2:  forall (a: list bool), (map2 xorb [] a) = [].
Proof. intros a. rewrite map2_xor_comm. apply map2_xor_empty_empty1. Qed.

Lemma map2_xor_nth_bitOf: forall (a b: list bool) (i: nat), 
                          (length a) = (length b) ->
                          (i <= (length a))%nat ->
                          nth i (map2 xorb a b) false = xorb (nth i a false) (nth i b false).
Proof. intro a.
       induction a as [ | a xs IHxs].
         - intros [ | b ys].
           + intros i H0 H1. do 2 rewrite map2_nth_empty_false. reflexivity.
           + intros i H0 H1. rewrite map2_xor_empty_empty2.
             rewrite map2_nth_empty_false. contradict H1. simpl. unfold not. intros. easy.
         - intros [ | b ys].
           + intros i H0 H1. rewrite map2_xor_empty_empty1.
             rewrite map2_nth_empty_false. rewrite xorb_false_r. rewrite H0 in H1.
             contradict H1. simpl. unfold not. intros. easy.
           + intros i H0 H1. simpl.
             revert i H1. intros [ | i IHi].
             * simpl. auto.
             * apply IHxs.
                 inversion H0; reflexivity.
                 inversion IHi; lia.
Qed.

Lemma map2_xor_0_neutral: forall (a: list bool), (map2 xorb a (mk_list_false (length a))) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]. 
         + auto.
         + simpl. rewrite IHxs.
           rewrite xorb_false_r. reflexivity.
Qed.

Lemma map2_xor_1_true: forall (a: list bool), (map2 xorb a (mk_list_true (length a))) = map negb a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl. rewrite IHxs. rewrite <- IHxs.
         rewrite xorb_true_r; reflexivity.
Qed.

(*bitvector OR properties*)

Lemma bv_xor_size n a b : size a = n -> size b = n -> size (bv_xor a b) = n.
Proof.
  unfold bv_xor. intros H1 H2. rewrite H1, H2.
  rewrite N.eqb_compare. rewrite N.compare_refl.
  unfold size in *. rewrite <- map2_xor_length.
  - exact H1.
  - unfold bits. now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_xor_comm: forall n a b, (size a) = n -> (size b) = n -> bv_xor a b = bv_xor b a.
Proof. intros n a b H0 H1. unfold bv_xor.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite map2_xor_comm. reflexivity.
Qed.

Lemma bv_xor_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_xor a (bv_xor b c)) = (bv_xor (bv_xor a b) c).
Proof. intros n a b c H0 H1 H2. 
       unfold bv_xor. rewrite H1, H2.  
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@map2_xor_length b c).
       rewrite H0, H1.
       rewrite N.compare_refl.
       rewrite N.eqb_compare. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- (@map2_xor_length a b).
       rewrite H0. rewrite N.compare_refl.
       rewrite map2_xor_assoc; reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_xor_empty_empty1: forall a, (bv_xor a bv_empty) = bv_empty.
Proof. intros a. unfold bv_empty. 
       unfold bv_xor, bits, size. simpl.
       case_eq (N.compare (N.of_nat (length a)) 0); intro H; simpl.
         - apply (N.compare_eq (N.of_nat (length a)) 0) in H.
           rewrite H. simpl. rewrite map2_xor_empty_empty1; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
         - rewrite N.eqb_compare. rewrite H; reflexivity.
Qed.

Lemma bv_xor_nth_bitOf: forall a b n (i: nat), 
                          (size a) = n -> (size b) = n ->
                          (i <= (nat_of_N (size a)))%nat ->
                          nth i (bits (bv_xor a b)) false = xorb (nth i (bits a) false) (nth i (bits b) false).
Proof. intros a b n i H0 H1 H2. 
       unfold bv_xor. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       apply map2_xor_nth_bitOf; unfold size in *; unfold bits.
       now rewrite <- Nat2N.inj_iff, H1. rewrite Nat2N.id in H2; exact H2.
Qed.

Lemma bv_xor_0_neutral: forall a, (bv_xor a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_xor.
       rewrite N.eqb_compare. unfold size, bits. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite map2_xor_0_neutral. reflexivity.
Qed.

Lemma bv_xor_1_true: forall a, (bv_xor a (mk_list_true (length (bits a)))) = map negb a.
Proof. intro a. unfold bv_xor.
       rewrite N.eqb_compare.  unfold size, bits. rewrite length_mk_list_true.
       rewrite N.compare_refl.
       rewrite map2_xor_1_true. reflexivity.
Qed.

(*bitwise NOT properties*)

Lemma not_list_length: forall a, length a = length (map negb a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto. 
       - simpl. apply f_equal. exact IHxs.
Qed.

Lemma not_list_involutative: forall a, map negb (map negb a) = a.
Proof. intro a.
       induction a as [ | a xs IHxs]; auto.
       simpl. rewrite negb_involutive. apply f_equal. exact IHxs.
Qed.

Lemma not_list_false_true: forall n, map negb (mk_list_false n) = mk_list_true n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_true_false: forall n, map negb (mk_list_true n) = mk_list_false n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. apply f_equal. exact IHn.
Qed.

Lemma not_list_and_or: forall a b, map negb (map2 andb a b) = map2 orb (map negb a) (map negb b).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - intros [ | b ys].
         + auto.
         + simpl. rewrite negb_andb. apply f_equal. apply IHxs.
Qed.

Lemma not_list_or_and: forall a b, map negb (map2 orb a b) = map2 andb (map negb a) (map negb b).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - intros [ | b ys].
         + auto.
         + simpl. rewrite negb_orb. apply f_equal. apply IHxs.
Qed.

(*bitvector NOT properties*)

Lemma bv_not_size: forall n a, (size a) = n -> size (bv_not a) = n.
Proof. intros n a H. unfold bv_not.
       unfold size, bits in *. rewrite <- not_list_length. exact H.
Qed.

Lemma bv_not_involutive: forall a, bv_not (bv_not a) = a.
Proof. intro a. unfold bv_not.
       unfold size, bits. rewrite not_list_involutative. reflexivity.
Qed.

Lemma bv_not_false_true: forall n, bv_not (mk_list_false n) = (mk_list_true n).
Proof. intros n. unfold bv_not.
       unfold size, bits. rewrite not_list_false_true. reflexivity.
Qed.

Lemma bv_not_true_false: forall n, bv_not (mk_list_true n) = (mk_list_false n).
Proof. intros n. unfold bv_not.
       unfold size, bits. rewrite not_list_true_false. reflexivity.
Qed.

Lemma bv_not_and_or: forall n a b, (size a) = n -> (size b) = n -> bv_not (bv_and a b) = bv_or (bv_not a) (bv_not b).
Proof. intros n a b H0 H1. unfold bv_and in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or, size, bits in *.
       do 2 rewrite <- not_list_length. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not, size, bits in *. 
       rewrite not_list_and_or. reflexivity.
Qed.

Lemma bv_not_or_and: forall n a b, (size a) = n -> (size b) = n -> bv_not (bv_or a b) = bv_and (bv_not a) (bv_not b).
Proof. intros n a b H0 H1. unfold bv_and, size, bits in *. 
       do 2 rewrite <- not_list_length.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold bv_or, size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl. 
       unfold bv_not, size, bits in *.
       rewrite not_list_or_and. reflexivity.
Qed.

(* list bitwise ADD properties*)

Lemma add_carry_ff: forall a, add_carry a false false = (a, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_f: forall a, add_carry a (negb a) false = (true, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_f_r: forall a, add_carry (negb a) a false = (true, false).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_neg_t: forall a, add_carry a (negb a) true = (false, true).
Proof. intros a.
       case a; simpl; auto.
Qed.

Lemma add_carry_tt: forall a, add_carry a true true = (a, true).
Proof. intro a. case a; auto. Qed.

Lemma add_list_empty_l: forall (a: list bool), (add_list [] a) = [].
Proof. intro a. induction a as [ | a xs IHxs].
         - unfold add_list. simpl. reflexivity.
         - apply IHxs.
Qed.

Lemma add_list_empty_r: forall (a: list bool), (add_list a []) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_l: forall (a: list bool) (c: bool), (add_list_ingr [] a c) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_ingr_r: forall (a: list bool) (c: bool), (add_list_ingr a [] c) = [].
Proof. intro a. induction a as [ | a xs IHxs]; unfold add_list; simpl; reflexivity. Qed.

Lemma add_list_carry_comm: forall (a b:  list bool) (c: bool), add_list_ingr a b c = add_list_ingr b a c.
Proof. intros a. induction a as [ | a' xs IHxs]; intros b c.
       - simpl. rewrite add_list_ingr_r. reflexivity.
       - case b as [ | b' ys].
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
Proof. intros a. induction a as [ | a' xs IHxs]; intros b c d1 d2 d3 d4.
       - simpl. reflexivity.
       - case b as [ | b' ys].
         + simpl. auto.
         + case c as [ | c' zs].
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

Lemma add_list_carry_length_eq: forall (a b: list bool) c, length a = length b -> length a = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. auto.
       intros [ | b ys].
       - simpl. intros. exact H.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity.
Qed.

Lemma add_list_carry_length_ge: forall (a b: list bool) c, (length a >= length b)%nat -> length b = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. intros b H0 H1. lia.
       intros [ | b ys].
       - simpl. intros. auto.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. lia.
Qed.

Lemma add_list_carry_length_le: forall (a b: list bool) c, (length b >= length a)%nat -> length a = length (add_list_ingr a b c).
Proof. induction a as [ | a' xs IHxs].
       simpl. intros b H0 H1. reflexivity.
       intros [ | b ys].
       - simpl. intros. contradict H. lia.
       - intros. simpl in *.
         case_eq (add_carry a' b c); intros r c0 Heq. simpl. apply f_equal.
         specialize (@IHxs ys). apply IHxs. lia.
Qed.

Lemma bv_neg_size: forall n a, (size a) = n -> size (bv_neg a) = n.
Proof. intros n a H. unfold bv_neg.
       unfold size, bits in *. unfold twos_complement.
       specialize (@add_list_carry_length_eq  (map negb a) (mk_list_false (length a)) true).
       intros. rewrite <- H0. now rewrite map_length.
       rewrite map_length.
       now rewrite length_mk_list_false.
Qed.


Lemma length_add_list_eq: forall (a b: list bool), length a = length b -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_eq a b false). exact H. Qed.



Lemma length_add_list_ge: forall (a b: list bool), (length a >= length b)%nat -> length b = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_ge a b false). exact H. Qed.

Lemma length_add_list_le: forall (a b: list bool), (length b >= length a)%nat -> length a = length (add_list a b).
Proof. intros a b H. unfold add_list. apply (@add_list_carry_length_le a b false). exact H. Qed.

Lemma add_list_assoc: forall (a b c: list bool), (add_list (add_list a b) c) = (add_list a (add_list b c)).
Proof. intros a b c. unfold add_list.
       apply (@add_list_carry_assoc a b c false false false false).
       simpl; reflexivity.
Qed.

Lemma add_list_carry_empty_neutral_n_l: forall (a: list bool) n, (n >= (length a))%nat -> (add_list_ingr (mk_list_false n) a false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro n. rewrite add_list_ingr_r. reflexivity.
       - intros [ | n]. 
         + simpl. intro H. contradict H. easy.
         + simpl. intro H.
           case a'; apply f_equal; apply IHxs; lia.
Qed.

Lemma add_list_carry_empty_neutral_n_r: forall (a: list bool) n, (n >= (length a))%nat -> (add_list_ingr a (mk_list_false n) false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro n. rewrite add_list_ingr_l. reflexivity.
       - intros [ | n]. 
         + simpl. intro H. contradict H. easy.
         + simpl. intro H.
           case a'; apply f_equal; apply IHxs; lia.
Qed.

Lemma add_list_carry_empty_neutral_l: forall (a: list bool), (add_list_ingr (mk_list_false (length a)) a false) = a.
Proof. intro a.
       rewrite add_list_carry_empty_neutral_n_l; auto.
Qed.

Lemma add_list_carry_empty_neutral_r: forall (a: list bool), (add_list_ingr a (mk_list_false (length a)) false) = a.
Proof. intro a.
       rewrite add_list_carry_empty_neutral_n_r; auto.
Qed.

Lemma add_list_empty_neutral_n_l: forall (a: list bool) n, (n >= (length a))%nat -> (add_list (mk_list_false n) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_n_l a).
Qed.

Lemma add_list_empty_neutral_n_r: forall (a: list bool) n, (n >= (length a))%nat -> (add_list a (mk_list_false n)) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_n_r a).
Qed.

Lemma add_list_empty_neutral_r: forall (a: list bool), (add_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_r a).
Qed.

Lemma add_list_empty_neutral_l: forall (a: list bool), (add_list (mk_list_false (length a)) a) = a.
Proof. intros a. unfold add_list.
       apply (@add_list_carry_empty_neutral_l a).
Qed.

Lemma add_list_carry_unit_t : forall a, add_list_ingr a (mk_list_true (length a)) true = a.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. case_eq (add_carry a true true). intros r0 c0 Heq0.
         rewrite add_carry_tt in Heq0. inversion Heq0.
         apply f_equal. exact IHxs.
Qed.

Lemma add_list_carry_twice: forall a c, add_list_ingr a a c = removelast (c :: a).
Proof. intro a. 
       induction a as [ | a xs IHxs].
       - intros c. simpl. reflexivity.
       - intros [ | ].
         + simpl. case a.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
         + simpl. case a.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
           * simpl. rewrite IHxs.
             case_eq xs. intro Heq0. simpl. reflexivity.
             reflexivity.
Qed.

Lemma add_list_twice: forall a, add_list a a = removelast (false :: a).
Proof. intro a. 
       unfold add_list. rewrite add_list_carry_twice. reflexivity.
Qed.

(*bitvector ADD properties*)

Lemma bv_add_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_add a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_add. rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold size, bits in *. rewrite <- (@length_add_list_eq a b). auto.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_add_comm: forall n a b, (size a) = n -> (size b) = n -> bv_add a b = bv_add b a.
Proof. intros n a b H0 H1.
       unfold bv_add, size, bits in *. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_comm. reflexivity.
Qed.

Lemma bv_add_assoc: forall n a b c, (size a) = n -> (size b) = n -> (size c) = n ->  
                                  (bv_add a (bv_add b c)) = (bv_add (bv_add a b) c).
Proof. intros n a b c H0 H1 H2.
       unfold bv_add, size, bits in *. rewrite H1, H2.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@length_add_list_eq b c). rewrite H0, H1.
       rewrite N.compare_refl. rewrite N.eqb_compare.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@length_add_list_eq a b). rewrite H0.
       rewrite N.compare_refl.
       rewrite add_list_assoc. reflexivity.
       now rewrite <- Nat2N.inj_iff, H0.
       now rewrite <- Nat2N.inj_iff, H1.
Qed.

Lemma bv_add_empty_neutral_l: forall a, (bv_add (mk_list_false (length (bits a))) a) = a.
Proof. intro a. unfold bv_add, size, bits. 
       rewrite N.eqb_compare. rewrite length_mk_list_false. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_l. reflexivity.
Qed.

Lemma bv_add_empty_neutral_r: forall a, (bv_add a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_add, size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false. rewrite N.compare_refl.
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.

Lemma bv_add_twice: forall a, bv_add a a = removelast (false :: a).
Proof. intro a. unfold bv_add, size, bits.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite add_list_twice. reflexivity.
Qed.

(* bitwise SUBST properties *)

Lemma subst_list_empty_empty_l: forall a, (subst_list [] a) = [].
Proof. intro a. unfold subst_list; auto. Qed.

Lemma subst_list_empty_empty_r: forall a, (subst_list a []) = [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - unfold subst_list; auto. 
Qed.

Lemma subst_list'_empty_empty_r: forall a, (subst_list' a []) = [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - auto.
       - unfold subst_list' in *. unfold twos_complement. simpl. reflexivity.
Qed.

Lemma subst_list_borrow_length: forall (a b: list bool) c, length a = length b -> length a = length (subst_list_borrow a b c). 
Proof. induction a as [ | a' xs IHxs]. 
       simpl. auto. 
       intros [ | b ys].
       - simpl. intros. exact H. 
       - intros. simpl in *. 
         case_eq (subst_borrow a' b c); intros r c0 Heq. simpl. apply f_equal. 
         specialize (@IHxs ys). apply IHxs. inversion H; reflexivity. 
Qed.

Lemma length_twos_complement: forall (a: list bool), length a = length (twos_complement a).
Proof. intro a.
      induction a as [ | a' xs IHxs].
      - auto.
      - unfold twos_complement. specialize (@add_list_carry_length_eq (map negb (a' :: xs)) (mk_list_false (length (a' :: xs))) true).        
        intro H. rewrite <- H. simpl. apply f_equal. rewrite <- not_list_length. reflexivity.
        rewrite length_mk_list_false. rewrite <- not_list_length. reflexivity.
Qed.

Lemma subst_list_length: forall (a b: list bool), length a = length b -> length a = length (subst_list a b). 
Proof. intros a b H. unfold subst_list. apply (@subst_list_borrow_length a b false). exact H. Qed.

Lemma subst_list'_length: forall (a b: list bool), length a = length b -> length a = length (subst_list' a b).
Proof. intros a b H. unfold subst_list'.
       rewrite <- (@length_add_list_eq a (twos_complement b)).
       - reflexivity.
       - rewrite <- (@length_twos_complement b). exact H.
Qed.

Lemma subst_list_borrow_empty_neutral: forall (a: list bool), (subst_list_borrow a (mk_list_false (length a)) false) = a.
Proof. intro a. induction a as [ | a' xs IHxs].
       - simpl. reflexivity.
       - simpl.
         cut(subst_borrow a' false false = (a', false)).
         + intro H. rewrite H. rewrite IHxs. reflexivity.
         + unfold subst_borrow. case a'; auto.
Qed.

Lemma subst_list_empty_neutral: forall (a: list bool), (subst_list a (mk_list_false (length a))) = a.
Proof. intros a. unfold subst_list.
       apply (@subst_list_borrow_empty_neutral a).
Qed.

Lemma twos_complement_cons_false: forall a, false :: twos_complement a = twos_complement (false :: a).
Proof. intro a.
       induction a as [ | a xs IHxs]; unfold twos_complement; simpl; reflexivity.
Qed.

Lemma twos_complement_false_false: forall n, twos_complement (mk_list_false n) = mk_list_false n.
Proof. intro n.
       induction n as [ | n IHn].
       - auto.
       - simpl. rewrite <- twos_complement_cons_false.
         apply f_equal. exact IHn.
Qed.

Lemma subst_list'_empty_neutral: forall (a: list bool), (subst_list' a (mk_list_false (length a))) = a.
Proof. intros a. unfold subst_list'.
       rewrite (@twos_complement_false_false (length a)).
       rewrite add_list_empty_neutral_r. reflexivity.
Qed.

(* some list ult and slt properties *)

Lemma ult_list_trans : forall x y z, ult_list x y = true -> ult_list y z = true -> ult_list x z = true.
Proof.
  intros x. induction x.
  simpl. easy.
  intros y z.
  case y.
  simpl. case x; easy.
  intros b l.
  intros.
  simpl in *. case x in *.
  case z in *. simpl in H0. case l in *; easy.
  case l in *.
  rewrite andb_true_iff in H.
  destruct H.
  apply negb_true_iff in H. subst.
  simpl. case z in *. easy.
  rewrite !orb_true_iff, !andb_true_iff in H0.
  destruct H0.
  destruct H.
  apply Bool.eqb_prop in H.
  subst.
  rewrite orb_true_iff. now right.
  destruct H. easy.
  rewrite !orb_true_iff, !andb_true_iff in H, H0.
  destruct H.
  simpl in H. easy.
  destruct H.
  apply negb_true_iff in H. subst.
  simpl.
  destruct H0.
  destruct H.
  apply Bool.eqb_prop in H.
  subst.
  case z; easy.
  destruct H. easy.
  case l in *.
  rewrite !orb_true_iff, !andb_true_iff in H.
  simpl in H. destruct H. destruct H. case x in H1; easy.
  destruct H.
  apply negb_true_iff in H. subst.
  simpl in H0.
  case z in *; try easy.
  case z in *; simpl in H0; try easy.
  case b in H0; simpl in H0; try easy.
  case z in *; try easy.
  rewrite !orb_true_iff, !andb_true_iff in *.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  apply Bool.eqb_prop in H.
  apply Bool.eqb_prop in H0.
  subst.
  left.
  split.
  apply Bool.eqb_reflx.
  now apply (IHx (b1 :: l) z H1 H2).
  right. apply Bool.eqb_prop in H. now subst.
  right. destruct H0, H0.
  apply Bool.eqb_prop in H0. now subst.
  easy.
Qed.  
  

Lemma rev_ult_list_trans : forall x y z,
    rev_ult_list x y = true -> rev_ult_list y z = true -> rev_ult_list x z = true.
Proof. unfold rev_ult_list. intros x y z. apply ult_list_trans.
Qed.


Lemma ult_list_not_eq : forall x y, ult_list x y = true -> x <> y.
Proof.
  intros x. induction x.
  simpl. easy.
  intros y.
  case y.
  simpl. case x; easy.
  intros b l.
  simpl.
  specialize (IHx l).
  case x in *.
  simpl.
  case l in *. case a; case b; simpl; easy.
  easy.
  rewrite !orb_true_iff, !andb_true_iff.
  intro.
  destruct H.
  destruct H.
  apply IHx in H0.
  apply Bool.eqb_prop in H.
  rewrite H in *.
  unfold not in *; intro.
  inversion H1; subst. now apply H0.
  destruct H.
  apply negb_true_iff in H. subst. easy.
Qed.  

Lemma rev_ult_list_not_eq : forall x y, rev_ult_list x y = true -> x <> y.
Proof. unfold rev_ult_list.
  unfold not. intros.
  apply ult_list_not_eq in H.
  subst. auto.
Qed.


(* bitvector SUBT properties *)

Lemma bv_subt_size: forall n a b, (size a) = n -> (size b) = n -> size (bv_subt a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_subt, size, bits in *. rewrite H0, H1. rewrite N.eqb_compare.
       rewrite N.compare_refl. rewrite <- subst_list_length. exact H0.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_subt_empty_neutral_r: forall a, (bv_subt a  (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_subt, size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite subst_list_empty_neutral. reflexivity.
Qed.

Lemma bv_subt'_size: forall n a b, (size a) = n -> (size b) = n -> size (bv_subt' a b) = n.
Proof. intros n a b H0 H1. unfold bv_subt', size, bits in *.
       rewrite H0, H1. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- subst_list'_length. exact H0.
       now rewrite <- Nat2N.inj_iff, H0.
Qed.

Lemma bv_subt'_empty_neutral_r: forall a, (bv_subt' a (mk_list_false (length (bits a)))) = a.
Proof. intro a. unfold bv_subt', size, bits.
       rewrite N.eqb_compare. rewrite length_mk_list_false.
       rewrite N.compare_refl.
       rewrite subst_list'_empty_neutral. reflexivity.
Qed.

(* bitwise ADD-NEG properties *)

Lemma add_neg_list_carry_false: forall a b c, add_list_ingr a (add_list_ingr b c true) false = add_list_ingr a (add_list_ingr b c false) true.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. auto.
       - case b as [ | b ys].
         + simpl. auto.
         + case c as [ | c zs].
           * simpl. auto.
           * simpl.
             case_eq (add_carry b c false); intros r0 c0 Heq0.
             case_eq (add_carry b c true); intros r1 c1 Heq1.
             case_eq (add_carry a r1 false); intros r2 c2 Heq2.
             case_eq (add_carry a r0 true); intros r3 c3 Heq3.
             case a, b, c; inversion Heq0; inversion Heq1; 
             inversion Heq2; inversion Heq3; rewrite <- H2 in H4; 
             rewrite <- H0 in H5; inversion H4; inversion H5; apply f_equal;
             try reflexivity; rewrite IHxs; reflexivity.
Qed.


Lemma add_neg_list_carry_neg_f: forall a, (add_list_ingr a (map negb a) false) = mk_list_true (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry a (negb a) false); intros r0 c0 Heq0.
         rewrite add_carry_neg_f in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry_neg_f_r: forall a, (add_list_ingr (map negb a) a false) = mk_list_true (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry (negb a) a false); intros r0 c0 Heq0.
         rewrite add_carry_neg_f_r in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry_neg_t: forall a, (add_list_ingr a (map negb a) true) = mk_list_false (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. 
         case_eq (add_carry a (negb a) true); intros r0 c0 Heq0.
         rewrite add_carry_neg_t in Heq0.
         inversion Heq0. rewrite IHxs. reflexivity.
Qed.

Lemma add_neg_list_carry: forall a, add_list_ingr a (twos_complement a) false = mk_list_false (length a).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - unfold twos_complement. rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
         rewrite add_list_carry_empty_neutral_r.
         rewrite add_neg_list_carry_neg_t. reflexivity.
Qed.

Lemma add_neg_list_absorb: forall a, add_list a (twos_complement a) = mk_list_false (length a).
Proof. intro a. unfold add_list. rewrite add_neg_list_carry. reflexivity. Qed.

(* bitvector ADD-NEG properties *)

Lemma bv_add_neg_unit: forall a, bv_add a (bv_not a) = mk_list_true (nat_of_N (size a)).
Proof. intro a. unfold bv_add, bv_not, size, bits. rewrite not_list_length.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold add_list. rewrite add_neg_list_carry_neg_f.
       rewrite Nat2N.id, not_list_length. reflexivity.
Qed. 


(* bitwise ADD-SUBST properties *)

Lemma add_subst_list_carry_opp: forall n a b, (length a) = n -> (length b) = n -> (add_list_ingr (subst_list' a b) b false) = a.
Proof. intros n a b H0 H1.
       unfold subst_list', twos_complement, add_list.
       rewrite add_neg_list_carry_false. rewrite not_list_length at 1.
       rewrite add_list_carry_empty_neutral_r.
       specialize (@add_list_carry_assoc a (map negb b) b true false false true).
       intro H2. rewrite H2; try auto. rewrite add_neg_list_carry_neg_f_r.
       rewrite H1. rewrite <- H0. rewrite add_list_carry_unit_t; reflexivity.
Qed.

Lemma add_subst_opp:  forall n a b, (length a) = n -> (length b) = n -> (add_list (subst_list' a b) b) = a.
Proof. intros n a b H0 H1. unfold add_list, size, bits.
       apply (@add_subst_list_carry_opp n a b); easy.
Qed.

(* bitvector ADD-SUBT properties *)

Lemma bv_add_subst_opp:  forall n a b, (size a) = n -> (size b) = n -> (bv_add (bv_subt' a b) b) = a.
Proof. intros n a b H0 H1. unfold bv_add, bv_subt', add_list, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite <- (@subst_list'_length a b). rewrite H0.
       rewrite N.compare_refl. rewrite (@add_subst_list_carry_opp (nat_of_N n) a b); auto;
       inversion H0; rewrite Nat2N.id; auto.
       symmetry. now rewrite <- Nat2N.inj_iff, H0.
        now rewrite <- Nat2N.inj_iff, H0.
Qed.

(* bitwise MULT properties *)

(*

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

Lemma mult_list_true: forall a n, ((length a) = n)%nat -> mult_list_carry [true] a n = a.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros n H. simpl in H. rewrite <- H.
         rewrite mult_list_carry_0. reflexivity.
       - intros [| n] H.
         + contradict H. easy.
         + rewrite <- (IHxs n) at 2; try auto. simpl.
           case a. unfold add_list. simpl. reflexivity.
           unfold add_list. simpl. reflexivity.
Qed.

Lemma mult_list_false_l: forall a n, mult_list_carry [false] a n = mk_list_false n.
Proof. intro a.
       induction a as [| a xs IHxs]; simpl; reflexivity.
Qed.

Lemma mult_list_carry_empty_l: forall (a: list bool) (c: nat), mult_list_carry [] a c = mk_list_false c.
Proof. intro a. induction a as [| a' xs IHxs]; auto. Qed.

Lemma strictly_positive_0_unique: forall n: nat, (0 >= n)%nat <-> (n = 0)%nat.
Proof. intro n. induction n as [| n IHn].
       split; try auto.
       split; intro H; contradict H; easy.
Qed.

Lemma mult_list_carry_length: forall (a b: list bool) n, ((length b) >= n)%nat -> n = length (mult_list_carry a b n).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H. rewrite mult_list_carry_empty_l, length_mk_list_false; reflexivity.
       - intros [| b ys] n H. simpl in H. rewrite strictly_positive_0_unique in H.
         rewrite H. rewrite mult_list_carry_0. easy.
         simpl. case a.
         + specialize (@length_add_list_ge (b :: ys) (mult_list_carry xs (false :: b :: ys) n)).
           intro H1. rewrite <- H1. 
           rewrite <- (IHxs (false :: b :: ys)). reflexivity. simpl in *. lia.
           specialize (@IHxs (false :: b :: ys)). rewrite <- IHxs. easy. simpl. simpl in H. lia.
         + specialize (@IHxs (false :: b :: ys)). apply IHxs. inversion H. simpl. lia. simpl in *. lia.
Qed.

Lemma mult_list_length: forall (a b: list bool), ((length b) >= (length a))%nat -> (length a) = length (mult_list a b).
Proof. intros a b H. unfold mult_list.
       rewrite <- (@mult_list_carry_length a b (length a)); auto.
Qed.

Lemma mult_list_length_eq: forall (a b: list bool), ((length a) = (length b))%nat -> (length a) = length (mult_list a b).
Proof. intros a b H. unfold mult_list.
       rewrite <- (@mult_list_carry_length a b (length a)); lia.
Qed.

Lemma mult_list_cons_false1: forall (a b: list bool) n, ((length a) >= n)%nat -> ((length b) >= n)%nat ->
                       mult_list_carry (false :: a) b n = mult_list_carry a (false :: b) n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0 H1. rewrite strictly_positive_0_unique in H0. rewrite H0.
         do 2 rewrite mult_list_carry_0. reflexivity.
       - intros [| b ys] n H0 H1.
         + rewrite strictly_positive_0_unique in H1. rewrite H1.
           do 2 rewrite mult_list_carry_0. reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false1': forall (a b: list bool) n, ((length (false :: b)) >= n)%nat ->
                       mult_list_carry (false :: a) b n = mult_list_carry a (false :: b) n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [| b ys] n H0.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false1'': forall (a b: list bool) n,
                       mult_list_carry (false :: a) b n = mult_list_carry a (false :: b) n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [| b ys] n.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false2: forall (a b: list bool) n, ((length a) >= n)%nat -> ((length b) >= n)%nat ->
                       mult_list_carry a (false :: b) n = mult_list_carry (false :: a) b n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0 H1. rewrite strictly_positive_0_unique in H0. rewrite H0.
         do 2 rewrite mult_list_carry_0. reflexivity.
       - intros [| b ys] n H0 H1.
         + rewrite strictly_positive_0_unique in H1. rewrite H1.
           do 2 rewrite mult_list_carry_0. reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false2': forall (a b: list bool) n, ((length (false :: b)) >= n)%nat ->
                       mult_list_carry a (false :: b) n = mult_list_carry (false :: a) b n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [| b ys] n H0.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false2'': forall (a b: list bool) n,
                       mult_list_carry a (false :: b) n = mult_list_carry (false :: a) b n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [| b ys] n.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma add_list_carry_rl0: forall (a b: list bool), 
add_list_ingr (add_list_ingr a a false) b false = add_list_ingr (removelast (false :: a)) b false.
Proof. intros a b. now rewrite add_list_carry_twice. Qed.

Lemma add_list_carry_rl1: forall (a b: list bool), 
add_list_ingr (removelast (false :: a)) b true = add_list_ingr (removelast (true :: a)) b false.
Proof. intros a b.
       simpl. case a.
       simpl. reflexivity.
       intros b0 l.
       simpl. reflexivity.
Qed.

Lemma add_list_carry_rl_t: forall  (a b: list bool), a <> [] ->
add_list_ingr (removelast (true :: a)) b false =
add_list_ingr a (add_list_ingr a b false) true.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b H0. now contradict H0.
       - intros [| b ys] H0.
         + reflexivity.
         + case a, b; 
           do 4 (rewrite <- (@add_list_carry_assoc _ _ _ false true); 
                 [rewrite add_list_carry_twice; rewrite  add_list_carry_rl1; reflexivity| auto]).
Qed.

Lemma add_list_carry_tf_t: forall (a b: list bool),
add_list (true :: a) (false :: b) = true :: add_list a b.
Proof. now simpl. Qed.

Lemma add_list_carry_ft_t: forall (a b: list bool),
add_list (false :: a) (true :: b) = true :: add_list a b.
Proof. now simpl. Qed.

Lemma add_list_carry_tf_tf_comm: forall (a b: list bool),
(add_list (true :: a) (false :: b)) = (add_list (true :: b) (false :: a)).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros [| b ys].
         + reflexivity.
         + simpl. now do 2 rewrite add_list_carry_tf_t.
       - intros [| b ys].
         + simpl. now do 2 rewrite add_list_carry_tf_t.
         + do 2 rewrite add_list_carry_tf_t. apply f_equal.
           case a, b; now rewrite add_list_comm.
Qed.

Lemma add_list_carry_ft_ft_comm: forall (a b: list bool),
(add_list (false :: a) (true :: b)) = (add_list (false :: b) (true :: a)).
Proof. intro a.
       induction a as [| a xs IHxs]; intros [| b ys]; try (now unfold add_list).
       unfold add_list. simpl. apply f_equal.
       case a, b; simpl; now rewrite add_list_carry_comm.
Qed.

Lemma add_list_carry_ff_f: forall (a b: list bool),
(add_list (false :: a) (false :: b)) = (false :: add_list a b).
Proof. intro a.
       induction a as [| a xs IHxs]; intros [| b ys]; now unfold add_list.
Qed.

Lemma mult_list_carry_f_f_1: forall (a b: list bool) n,
                       mult_list_carry (false :: a) b (S n) = false :: mult_list_carry a b n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [| b ys] n.
         + case a.
          * rewrite mult_list_cons_false1''. 
            simpl. rewrite mult_list_cons_false2''.
            rewrite IHxs.
            rewrite mult_list_cons_false2''.
            now rewrite <- add_list_carry_ff_f.
          * rewrite mult_list_cons_false1''. 
            simpl. rewrite mult_list_cons_false2''.
            rewrite IHxs.
            now rewrite mult_list_cons_false2''.
         + case a, b.
           * simpl. rewrite mult_list_cons_false2''. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite mult_list_cons_false2''. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite mult_list_cons_false2''.
             rewrite IHxs. reflexivity.
           * simpl. rewrite mult_list_cons_false2''.
             rewrite IHxs. reflexivity.
Qed.

Lemma mult_list_carry_f_f_2: forall (a b: list bool) n,
                       mult_list_carry a (false :: b) (S n) = false :: mult_list_carry a b n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [| b ys] n.
         + case a.
          * rewrite mult_list_cons_false2''. 
            simpl. rewrite IHxs.
            rewrite mult_list_cons_false2''.
            now rewrite <- add_list_carry_ff_f.
          * rewrite mult_list_cons_false1''.
            rewrite IHxs.
            now rewrite mult_list_cons_false2''.
         + case a, b.
           * simpl. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite IHxs. reflexivity.
           * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma mult_list_carry_ff_ff: forall (a b: list bool) n,
                       mult_list_carry (false :: a) (false :: b) (S (S n)) = false :: false :: mult_list_carry a b n.
Proof. intros a b n.
       rewrite mult_list_carry_f_f_1, mult_list_carry_f_f_2.
       reflexivity.
Qed.

Lemma mult_list_carry_1: forall (a: list bool), (mult_list_carry a [false; true] 1) = [false].
Proof. intro a.
       induction a as [| a xs IHxs].
       - simpl. reflexivity.
       - simpl. case a.
         + rewrite mult_list_cons_false2'.
           rewrite mult_list_carry_f_f_1. rewrite mult_list_carry_0. 
           now unfold add_list.
           simpl; lia.
         + rewrite mult_list_cons_false2'.
           rewrite mult_list_carry_f_f_1. now rewrite mult_list_carry_0.
           simpl; lia.
Qed.

Lemma nsubst_0: forall n, (n - 0)%nat = n.
Proof. intro n. 
       induction n as [| n IHn]; now simpl.
Qed.

Lemma nsubst_S: forall n, (n <> 0)%nat -> n = S (n - 1)%nat.
Proof. intro n.
       induction n as [| n IHn]; intro H.
       - now contradict H.
       - simpl. now rewrite nsubst_0.
Qed.


Lemma not_empty: forall (a: list bool) n, ((length a) > n)%nat -> a <> [].
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros n H. now contradict H.
       - intros [| n] H; easy.
Qed.

Lemma mult_list_carry_add_list_t_f: forall (a b: list bool) n, ((length a) > n)%nat ->
(mult_list_carry a (true :: b) (S n)) = (add_list a (false :: mult_list_carry a b n)).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0. simpl in H0.
         now contradict H0.
      - intros [| b ys] n H0.
         + case a.
           * simpl.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_tf_t.
             apply f_equal.
             now rewrite add_list_empty_r, add_list_empty_l.
           * rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f.
             apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_1.
               rewrite <- IHxs.
               reflexivity.
               simpl in *; lia.
         + case a, b.
           * simpl.
             rewrite mult_list_cons_false2''.
             rewrite mult_list_cons_false2''.
             rewrite add_list_carry_tf_tf_comm.
             symmetry; rewrite add_list_comm; symmetry.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_ft_t. apply f_equal.
             specialize (@IHxs (true :: ys)).
             rewrite <- add_list_assoc.
             cut ((add_list xs (true :: ys)) = (add_list (true :: ys) xs)).
             intro H3. rewrite H3.
             rewrite add_list_assoc.
             induction n.
               do 2 rewrite mult_list_carry_0. now do 3 rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             now rewrite add_list_comm.
           * simpl.
             rewrite mult_list_cons_false2''.
             rewrite mult_list_cons_false2''.
             rewrite add_list_carry_tf_tf_comm.
             symmetry; rewrite add_list_comm; symmetry.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_ft_t. apply f_equal.
             specialize (@IHxs (false :: ys)).
             rewrite <- add_list_assoc.
             cut ((add_list xs (false :: ys)) = (add_list (false :: ys) xs)).
             intro H3. rewrite H3.
             rewrite add_list_assoc.
             induction n.
               do 2 rewrite mult_list_carry_0. now do 3 rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             now rewrite add_list_comm.
           * rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f.
             apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
           * rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f.
             apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_t_tt_add_list_f_t_tt: forall (a b: list bool) n, ((length a) >= n)%nat ->
mult_list_carry (true :: a) (true :: true :: b) (S n) =
add_list (false :: a)
  (true :: mult_list_carry (true :: a) (true :: b) n).
Proof. intros. simpl.
        rewrite mult_list_cons_false2''.
        rewrite mult_list_cons_false2''.
        rewrite add_list_carry_ft_ft_comm.
        symmetry; rewrite add_list_comm; symmetry.
        rewrite mult_list_carry_f_f_1.
        induction n.
         do 2 rewrite mult_list_carry_0. rewrite add_list_empty_r.
          unfold add_list. simpl. now rewrite add_list_ingr_r.
        rewrite mult_list_carry_f_f_1.
        rewrite add_list_carry_tf_t.
        rewrite add_list_carry_tf_t. apply f_equal.
        rewrite add_list_carry_tf_tf_comm. simpl.
        rewrite mult_list_carry_add_list_t_f.
        rewrite add_list_carry_tf_tf_comm.
        rewrite <- add_list_assoc. rewrite <- add_list_assoc.
        cut (add_list (true :: b) a = add_list a (true :: b)).
        intro H3; now rewrite H3.
        now rewrite add_list_comm.
        simpl in *; lia.
Qed.

Lemma mult_list_carry_t_tf_add_list_f_t_tf: forall (a b: list bool) n, ((length a) >= n)%nat ->
mult_list_carry (true :: a) (true :: false :: b) (S n) =
add_list (false :: a) (true :: mult_list_carry (true :: a) (false :: b) n).
Proof. intros. simpl.
        rewrite mult_list_cons_false2''.
        rewrite mult_list_cons_false2''.
        rewrite add_list_carry_ft_ft_comm.
        symmetry; rewrite add_list_comm; symmetry.
        rewrite mult_list_carry_f_f_1.
        induction n.
         do 2 rewrite mult_list_carry_0. rewrite add_list_empty_r.
          unfold add_list. simpl. now rewrite add_list_ingr_r.
        rewrite mult_list_carry_f_f_1.
        rewrite add_list_carry_tf_t.
        rewrite add_list_carry_tf_t. apply f_equal.
        rewrite mult_list_carry_add_list_t_f.
        rewrite <- add_list_assoc.
        rewrite <- add_list_assoc.
        cut (add_list (false :: b) a = add_list a (false :: b)).
        intro H3; now rewrite H3.
        now rewrite add_list_comm.
        simpl in *; lia.
Qed.

Lemma mult_list_carry_tt_add_list_ft: forall (a b: list bool) n, ((length a) >= n)%nat ->
mult_list_carry a (true :: true :: b) n =
add_list a (mult_list_carry a (false :: true :: b) n).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0. rewrite strictly_positive_0_unique in H0. 
           rewrite H0. now do 2 rewrite mult_list_carry_0.
       - intros [| b ys] n H0.
         + case a.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_tf_t.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_tf_t. apply f_equal.
               rewrite IHxs.
               rewrite <- add_list_assoc.
               rewrite <- add_list_assoc.
               cut ((add_list [true] xs) = (add_list xs [true])). now (intro H1; rewrite H1).
               now rewrite add_list_comm.
               simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs. reflexivity.
               simpl in *; lia.
         + case a, b.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tt_add_list_f_t_tt.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tt_add_list_f_t_tt.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_tf_add_list_ff: forall (a b: list bool) n, ((length a) >= n)%nat  ->
mult_list_carry a (true :: false :: b) n =
add_list a (mult_list_carry (false :: a) (false :: b) n).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0. rewrite strictly_positive_0_unique in H0. 
           rewrite H0. now do 2 rewrite mult_list_carry_0.
       - intros [| b ys] n H0.
         + case a.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_tf_t.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_tf_t. apply f_equal.
               rewrite IHxs.
               rewrite <- add_list_assoc.
               rewrite <- add_list_assoc.
               cut ((add_list [false] xs) = (add_list xs [false])). now (intro H1; rewrite H1).
               now rewrite add_list_comm.
               simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs. reflexivity.
               simpl in *; lia.
         + case a, b.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tf_add_list_f_t_tf.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tf_add_list_f_t_tf.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_ft_add_list_f_ff: forall (a b: list bool) n, ((length a) >= n)%nat ->
(mult_list_carry a (false :: true :: b) n) =
(add_list (false :: a) ((mult_list_carry a (false :: false :: b) n))).
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0. rewrite strictly_positive_0_unique in H0. 
           rewrite H0. now do 2 rewrite mult_list_carry_0.
       - intros [| b ys] n H0.
         + case a.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs.
               rewrite <- add_list_assoc.
               rewrite <- add_list_assoc.
               cut ((add_list [true] (false :: xs)) = (add_list (true :: xs) [false])). now (intro H1; rewrite H1).
               now rewrite add_list_comm.
               simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs. reflexivity.
               simpl in *; lia.
         + case a, b.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_t_tt_add_list_f_t_tt.
               rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tf_add_list_f_t_tf.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_tt_add_list_ft. reflexivity.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_tf_add_list_ff. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_comm: forall (a b: list bool) n, ((length a) >= n)%nat -> ((length b) >= n)%nat ->
                            mult_list_carry a b n = mult_list_carry b a n.
Proof. intro a.
       induction a as [| a xs IHxs].
       - intros b n H0 H1. rewrite strictly_positive_0_unique in H0. rewrite H0.
         do 2 rewrite mult_list_carry_0. reflexivity.
       - intros [| b ys] n H0 H1.
         + rewrite strictly_positive_0_unique in H1. rewrite H1.
           do 2 rewrite mult_list_carry_0. reflexivity.
         + case a, b.
           * simpl.
             induction n.
             do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_tf_t. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. 
               now do 2 rewrite add_list_empty_r.
             rewrite mult_list_carry_add_list_t_f.
             rewrite mult_list_carry_add_list_t_f.
             rewrite IHxs.
             rewrite <- add_list_assoc.
             rewrite <- add_list_assoc.
             cut (add_list xs ys = add_list ys xs). now (intro H2 ;rewrite H2).
             now rewrite add_list_comm.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. 
               now rewrite add_list_empty_r.
             rewrite mult_list_carry_add_list_t_f.
             rewrite mult_list_carry_f_f_2.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. 
               now rewrite add_list_empty_r.
             rewrite mult_list_carry_add_list_t_f.
             rewrite mult_list_carry_f_f_2.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
           * simpl.
             induction n.
               now do 2 rewrite mult_list_carry_0.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2. apply f_equal.
             induction n.
               now do 2 rewrite mult_list_carry_0. 
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2. apply f_equal.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             simpl in *; lia.
Qed.

Lemma mult_list_comm: forall (a b: list bool) n, n = (length a) -> (n = length b) -> (mult_list a b) = (mult_list b a).
Proof. intros a b n H0 H1.
       unfold mult_list. 
       rewrite <- H0, H1.
       apply mult_list_carry_comm; lia.
Qed.
*)

(* (* bitvector MULT properties *) *)

Lemma prop_mult_bool_step_k_h_len: forall a b c k,
length (mult_bool_step_k_h a b c k) = length a.
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. simpl. easy.
       - intros.
         case b in *. simpl. rewrite IHa. simpl. omega.
         simpl. case (k - 1 <? 0)%Z; simpl; now rewrite IHa.
Qed. 


Lemma empty_list_length: forall {A: Type} (a: list A), (length a = 0)%nat <-> a = [].
Proof. intros A a.
       induction a; split; intros; auto; contradict H; easy.
Qed.

Lemma prop_mult_bool_step: forall k' a b res k, 
                       length (mult_bool_step a b res k k') = (length res)%nat.
Proof. intro k'.
       induction k'.
       - intros. simpl. rewrite prop_mult_bool_step_k_h_len. simpl. omega.
       - intros. simpl. rewrite IHk'. rewrite prop_mult_bool_step_k_h_len. simpl; omega.
Qed.

Lemma and_with_bool_len: forall a b, length (and_with_bool a (nth 0 b false)) = length a.
Proof. intro a.
       - induction a.
         intros. now simpl.
         intros. simpl. now rewrite IHa.
Qed.

Lemma bv_mult_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_mult a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold mult_list, bvmult_bool.
       case_eq (length a).
         intros.
         + rewrite empty_list_length in H. rewrite H in *. now simpl in *.
         + intros.
           case n0 in *. now rewrite and_with_bool_len.
           rewrite prop_mult_bool_step. now rewrite and_with_bool_len.
Qed.

       
(*
Lemma bv_mult_size a b: size (bv_mult a b) = size_bv_mult a b.
Proof. unfold size, bv_mult, bits, mult_list, size_bv_mult.
       case_eq (size a =? size b).
       - intros. unfold size in *. apply f_equal.         
         unfold bvmult_bool.
         case_eq (length a).
         intros.
         + rewrite empty_list_length in H0. rewrite H0. now simpl.
         + intros.
           case n in *. now rewrite and_with_bool_len.
           rewrite prop_mult_bool_step. now rewrite and_with_bool_len.
       - intros. easy.
Qed. 


(* bitvector MULT properties *)

Lemma bv_mult_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_mult a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       specialize (@mult_list_length_eq a b). intro H2.
       rewrite <- H2; lia.
Qed.


Lemma bv_mult_comm: forall n a b, (size a) = n -> (size b) = n -> bv_mult a b = bv_mult b a.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite (@mult_list_comm a b (nat_of_N n)). reflexivity.
       rewrite <- H0. now rewrite Nat2N.id.
       rewrite <- H1. now rewrite Nat2N.id.
Qed.
*)



End RAWBITVECTOR_LIST.

Module BITVECTOR_LIST <: BITVECTOR := RAW2BITVECTOR(RAWBITVECTOR_LIST).


(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

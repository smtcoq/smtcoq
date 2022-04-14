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


(* This example tests the tactics in "real" condition: a part of the
   proof of correctness of insertion sort. It requires propositional
   reasoning, uninterpreted functions, and a bit of integer arithmetic.

   Ideally, the proof of each lemma should consists only on
   induction/destruct followed by a call to [smt]. What we currently
   lack:
     - we have to provide all the needed lemmas and unfold all the
       definitions
     - it requires too much from uninterpreted functions even when it is
       not needed
     - it sometimes fails (may be realted to the previous item)
 *)


Require Import SMTCoq.SMTCoq.
Require Import ZArith List Bool.

Local Open Scope Z_scope.


(* This will improve when SMTCoq works with SSReflect! *)

Lemma impl_implb (a b:bool) : (a -> b) <-> (a ---> b).
Proof. auto using (reflect_iff _ _ (ReflectFacts.implyP a b)). Qed.


Lemma eq_false b : b = false <-> negb b.
Proof. case b; intuition. Qed.


Section InsertionSort.

  Fixpoint insert (x:Z) (l:list Z) : list Z :=
    match l with
    | nil => x::nil
    | y::ys => if (x <=? y)%Z then x::y::ys else y::(insert x ys)
    end.

  Fixpoint sort (l:list Z) : list Z :=
    match l with
    | nil => nil
    | x::xs => insert x (sort xs)
    end.


  Section Spec.

    Fixpoint is_sorted (l:list Z) : bool :=
      match l with
      | nil => true
      | x::xs =>
        match xs with
        | nil => true
        | y::_ => (x <=? y)%Z && (is_sorted xs)
        end
      end.

    Fixpoint smaller (x:Z) (l:list Z) : bool :=
      match l with
      | nil => true
      | y::ys => (x <=? y)%Z && (smaller x ys)
      end.


    Lemma is_sorted_smaller x y ys :
      (((x <=? y)%Z && is_sorted (y :: ys)) ---> is_sorted (x :: ys)).
    Proof.
      destruct ys as [ |z zs].
      - simpl. smt.
      - change (is_sorted (y :: z :: zs)) with ((y <=? z)%Z && (is_sorted (z::zs))).
        change (is_sorted (x :: z :: zs)) with ((x <=? z)%Z && (is_sorted (z::zs))).
        (* [smt] or [verit] fail? *)
        assert (H:forall b, (x <=? y)%Z && ((y <=? z) && b) ---> (x <=? z) && b) by smt.
        apply H.
    Qed.


    Lemma is_sorted_cons x xs :
      (is_sorted (x::xs)) <---> (is_sorted xs && smaller x xs).
    Proof.
      induction xs as [ |y ys IHys].
      - reflexivity.
      - change (is_sorted (x :: y :: ys)) with ((x <=? y)%Z && (is_sorted (y::ys))).
        change (smaller x (y :: ys)) with ((x <=? y)%Z && (smaller x ys)).
        generalize (is_sorted_smaller x y ys). revert IHys. rewrite !impl_implb.
        (* Idem *)
        assert (H:forall a b c d, (a <---> b && c) --->
                                  ((x <=? y) && d ---> a) --->
                                  ((x <=? y) && d <--->
                                  d && ((x <=? y) && c))) by smt.
        apply H.
    Qed.


    Lemma insert_keeps_smaller x y ys :
      smaller y ys ---> (y <=? x) ---> smaller y (insert x ys).
    Proof.
      induction ys as [ |z zs IHzs].
      - simpl. smt.
      - simpl. case (x <=? z).
        + simpl.
          (* [smt] or [verit] require [Compec (list Z)] but they should not *)
          assert (H:forall a, (y <=? z) && a ---> (y <=? x) ---> (y <=? x) && ((y <=? z) && a)) by smt.
          apply H.
        + simpl. revert IHzs. rewrite impl_implb.
          (* Idem *)
          assert (H:forall a b, (a ---> (y <=? x) ---> b) ---> (y <=? z) && a ---> (y <=? x) ---> (y <=? z) && b) by smt.
          apply H.
    Qed.


    Lemma insert_keeps_sorted x l : is_sorted l -> is_sorted (insert x l).
    Proof.
      induction l as [ |y ys IHys].
      - reflexivity.
      - intro H. simpl. case_eq (x <=? y); intro Heq.
        + change ((x <=? y)%Z && (is_sorted (y::ys))). rewrite Heq, H. reflexivity.
        + rewrite eq_false in Heq.
          rewrite (eqb_prop _ _ (is_sorted_cons _ _)) in H.
          rewrite (eqb_prop _ _ (is_sorted_cons _ _)).
          generalize (insert_keeps_smaller x y ys).
          revert IHys H Heq. rewrite !impl_implb.
          (* Idem *)
          assert (H: forall a b c d, (a ---> b) ---> a && c ---> negb (x <=? y) ---> (c ---> (y <=? x) ---> d) ---> b && d) by smt.
          apply H.
    Qed.


    Theorem sort_sorts l : is_sorted (sort l).
    Proof.
      induction l as [ |x xs IHxs].
      - reflexivity.
      - simpl. now apply insert_keeps_sorted.
    Qed.

  End Spec.

End InsertionSort.

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
   induction/destruct followed by a call to [smt].

   What we currently lack:
    - we have to provide all the needed lemmas and unfold all the definitions
    - it requires too much from uninterpreted functions even when it is not needed
    - it sometimes fails (may be realted to the previous item)
 *)


From SMTCoq Require Import SMTCoq.
From Stdlib Require Import Bool List ZArith.

Local Open Scope Z_scope.


Fixpoint insert (x: Z) (l: list Z) : list Z :=
  match l with
  | nil => x :: nil
  | y :: ys => if x <=? y then x :: y :: ys else y :: insert x ys
  end.

Fixpoint sort (l: list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs => insert x (sort xs)
  end.


Section Spec.

  (* This will improve when SMTCoq works with SSReflect! *)

  Lemma impl_implb (a b: bool) : (a -> b) <-> (a ---> b).
  Proof. apply reflect_iff, ReflectFacts.implyP. Qed.

  Lemma eq_false b : b = false <-> negb b.
  Proof. case b; intuition. Qed.


  Fixpoint is_sorted (l: list Z) : bool :=
    match l with
    | nil => true
    | x :: xs =>
      match xs with
      | nil => true
      | y :: _ => (x <=? y) && is_sorted xs
      end
    end.

  Fixpoint smaller (x: Z) (l: list Z) : bool :=
    match l with
    | nil => true
    | y :: ys => (x <=? y) && smaller x ys
    end.

  Lemma is_sorted_smaller x y ys :
    (x <=? y) && is_sorted (y :: ys) ---> is_sorted (x :: ys).
  Proof.
    destruct ys as [ | z zs]; simpl.
    { now apply impl_implb. }

    smt.
  Qed.

  Lemma is_sorted_cons x xs :
    (is_sorted (x::xs)) <---> (is_sorted xs && smaller x xs).
  Proof.
    induction xs as [ | y ys IHys].
    { reflexivity. }

    change (is_sorted (x :: y :: ys)) with ((x <=? y) && (is_sorted (y::ys))).
    change (smaller x (y :: ys)) with ((x <=? y) && (smaller x ys)).
    generalize (is_sorted_smaller x y ys).
    smt.
  Qed.

  Lemma insert_keeps_smaller x y ys :
    smaller y ys ---> (y <=? x) ---> smaller y (insert x ys).
  Proof.
    induction ys as [ | z zs IHzs]; simpl.
    { smt. }

    case (x <=? z); simpl.
    - smt.
    - smt.
  Qed.

  Lemma insert_keeps_sorted x l :
    is_sorted l -> is_sorted (insert x l).
  Proof.
    induction l as [ | y ys IHys].
    { reflexivity. }

    intro H; simpl.
    case_eq (x <=? y); intro Heq.
    - change ((x <=? y) && is_sorted (y :: ys)).
      smt.
    - rewrite eq_false in Heq.
      rewrite (eqb_prop _ _ (is_sorted_cons _ _)) in H.
      rewrite (eqb_prop _ _ (is_sorted_cons _ _)).
      generalize (insert_keeps_smaller x y ys).
      smt.
  Qed.

  Theorem sort_sorts l : is_sorted (sort l).
  Proof.
    induction l as [ | x xs IHxs].
    { reflexivity. }

    now apply insert_keeps_sorted.
  Qed.

End Spec.

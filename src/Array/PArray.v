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


(* Software implementation of arrays, based on finite maps using AVL
   trees *)

Declare Scope array_scope.

Require Export Int63 Psatz.
Require FMapAVL.
Require Import ZArith.

Local Open Scope int63_scope.

Import OrderedType.

Module IntOrderedType <: OrderedType.

  Definition t := int.

  Definition eq x y := (x == y) = true.

  Definition lt x y := (x < y) = true.

  Lemma eq_refl x : eq x x.
  Proof. unfold eq. rewrite eqb_spec. reflexivity. Qed.

  Lemma eq_sym x y : eq x y -> eq y x.
  Proof. unfold eq. rewrite !eqb_spec. intros ->. reflexivity. Qed.

  Lemma eq_trans x y z : eq x y -> eq y z -> eq x z.
  Proof. unfold eq. rewrite !eqb_spec. intros -> ->. reflexivity. Qed.

  Lemma lt_trans x y z : lt x y -> lt y z -> lt x z.
  Proof. unfold lt; rewrite !ltb_spec; apply Z.lt_trans. Qed.

  Lemma lt_not_eq x y : lt x y -> ~ eq x y.
  Proof. unfold lt, eq. rewrite ltb_spec, eqb_spec. intros H1 H2. rewrite H2 in H1. lia. Qed.

  Definition compare x y : Compare lt eq x y.
  Proof.
    case_eq (x < y); intro e.
      exact (LT e).
      case_eq (x == y); intro e2.
        exact (EQ e2).
        apply GT. unfold lt.
        rewrite <- Bool.not_false_iff_true, <- Bool.not_true_iff_false, ltb_spec, eqb_spec in *; intro e3.
        apply e2, to_Z_inj; lia.
  Defined.

  Definition eq_dec x y : { eq x y } + { ~ eq x y }.
  Proof.
    case_eq (x == y); intro e.
      left; exact e.
      right. intro H. rewrite H in e. discriminate.
  Defined.

End IntOrderedType.

Module Map := FMapAVL.Make(IntOrderedType).

(* An array is represented as a tuple of a finite map, the default
   element, and the length *)
Definition array (A:Type) : Type :=
  (Map.t A * A * int)%type.

Definition make {A:Type} (l:int) (d:A) : array A := (Map.empty A, d, l).

Definition get {A:Type} (t:array A) (i:int) : A :=
  let (td, l) := t in
  let (t, d) := td in
  if i < l then
    match Map.find i t with
      | Some x => x
      | None => d
    end
  else d.

Definition default {A:Type} (t:array A) : A :=
  let (td,_) := t in let (_,d) := td in d.

Definition set {A:Type} (t:array A) (i:int) (a:A) : array A :=
  let (td,l) := t in
  if l <= i then
    t
  else
    let (t,d) := td in
    (Map.add i a t, d, l).

Definition length {A:Type} (t:array A) : int :=
  let (_,l) := t in l.

Definition copy {A:Type} (t:array A) : array A := t.

Delimit Scope array_scope with array.
Notation "t '.[' i ']'" := (get t i) (at level 50) : array_scope.
Notation "t '.[' i '<-' a ']'" := (set t i a) (at level 50) : array_scope.

Local Open Scope array_scope.

Definition max_length := max_int.

(** Axioms *)
Require FSets.FMapFacts.
Module P := FSets.FMapFacts.WProperties_fun IntOrderedType Map.

Lemma get_outofbound : forall A (t:array A) i, (i < length t) = false -> t.[i] = default t.
intros A t i; unfold get.
destruct t as ((t, d), l).
unfold length; intro Hi; rewrite Hi; clear Hi.
reflexivity.
Qed.

Lemma get_set_same : forall A t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a.
intros A t i a.
destruct t as ((t, d), l).
unfold set, get, length.
intro Hi; generalize Hi.
rewrite ltb_spec.
rewrite Z.lt_nge.
rewrite <- leb_spec.
rewrite Bool.not_true_iff_false.
intro Hi'; rewrite Hi'; clear Hi'.
rewrite Hi; clear Hi.
rewrite P.F.add_eq_o.
reflexivity.
rewrite eqb_spec.
reflexivity.
Qed.

Lemma get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
intros A t i j a Hij.
destruct t as ((t, d), l).
unfold set, get, length.
case (l <= i).
reflexivity.
rewrite P.F.add_neq_o.
reflexivity.
intro H; apply Hij; clear Hij.
rewrite eqb_spec in H.
assumption.
Qed.

Lemma default_set : forall A t i (a:A), default (t.[i<-a]) = default t.
intros A t i a.
destruct t as ((t, d), l).
unfold default, set.
case (l <= i); reflexivity.
Qed.

Lemma get_make : forall A (a:A) size i, (make size a).[i] = a.
intros A a size i.
unfold make, get.
rewrite P.F.empty_o.
case (i < size); reflexivity.
Qed.

Lemma leb_length : forall A (t:array A), length t <= max_length = true.
intros A t.
generalize (length t); clear t.
intro i.
rewrite leb_spec.
apply Z.lt_succ_r.
change (Z.succ (to_Z max_length)) with wB.
apply to_Z_bounded.
Qed.

Lemma length_make : forall A size (a:A),
  length (make size a) = if size <= max_length then size else max_length.
intros A size a.
unfold length, make.
replace (size <= max_length) with true.
reflexivity.
symmetry.
rewrite leb_spec.
apply Z.lt_succ_r.
change (Z.succ (to_Z max_length)) with wB.
apply to_Z_bounded.
Qed.

Lemma length_set : forall A t i (a:A),
  length (t.[i<-a]) = length t.
intros A t i a.
destruct t as ((t, d), l).
unfold length, set.
case (l <= i); reflexivity.
Qed.

Lemma get_copy : forall A (t:array A) i, (copy t).[i] = t.[i].
intros A t i.
unfold copy; reflexivity.
Qed.

Lemma length_copy : forall A (t:array A), length (copy t) = length t.
intros A t.
unfold copy; reflexivity.
Qed.

(* Not true in this implementation (see #71, many thanks to Andres Erbsen) *)
(*
Axiom array_ext : forall A (t1 t2:array A),
  length t1 = length t2 ->
  (forall i, i < length t1 = true -> t1.[i] = t2.[i]) ->
  default t1 = default t2 ->
  t1 = t2.
*)

(* Lemmas *)

Lemma default_copy A (t:array A) : default (copy t) = default t.
unfold copy; reflexivity.
Qed.

Lemma default_make A (a : A) size : default (make size a) = a.
unfold default, make; reflexivity.
Qed.

Lemma get_set_same_default A (t : array A) (i : int) : t.[i <- default t].[i] = default t.
unfold default, get, set.
destruct t as ((t, d), l).
case_eq (i < l).
intro H; generalize H.
rewrite ltb_spec.
rewrite Z.lt_nge.
rewrite <- leb_spec.
rewrite Bool.not_true_iff_false.
intro H'; rewrite H'; clear H'.
rewrite H; clear H.
rewrite P.F.add_eq_o.
reflexivity.
rewrite eqb_spec.
reflexivity.
intro H; generalize H.
rewrite <- Bool.not_true_iff_false.
rewrite ltb_spec.
rewrite <- Z.le_ngt.
rewrite <- leb_spec.
intro H'; rewrite H'; clear H'.
rewrite H.
reflexivity.
Qed.

Lemma get_not_default_lt A (t:array A) x :
 t.[x] <> default t -> (x < length t) = true.
unfold get, default, length.
destruct t as ((t, d), l).
case (x < l); tauto.
Qed.

(* 
   Local Variables:
   coq-load-path: ((rec "../../.." "SMTCoq"))
   End: 
*)

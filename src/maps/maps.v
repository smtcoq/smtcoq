Require Export OrderedType.
Require Export OrderedTypeEx.
Require Export OrderedTypeAlt.
Require Export DecidableType.
Require Export DecidableTypeEx.
Require Export FSetInterface.
Require Export FSetBridge.
Require Export FSetFacts.
Require Export FSetDecide.
Require Export FSetProperties.
Require Export FSetEqProperties.
Require Export FSetWeakList.
Require Export FSetList.
Require Export FSetPositive.
Require Export FSetAVL.
Require Import FSetInterface.
Require Import FMapInterface.
Require Import Coq.FSets.FMapList.

Set Implicit Arguments.
Unset Strict Implicit.

(* using Finite map library *)

Module Raw (X:OrderedType).

Module E := X.
Module MX := OrderedTypeFacts X.
Module PX := KeyOrderedType X.
Import MX.
Import PX.

Definition key := X.t.
Definition t (elt:Set) := list (X.t * elt).

Section Elt.
Variable elt : Set.

Notation Sort := (sort ltk).
Notation Inf := (lelistA (ltk)).

Function find (k:key) (s: t elt) {struct s} : option elt :=
 match s with
  | nil => None
  | (k',x)::s' =>
     match X.compare k k' with
      | LT _ => None
      | EQ _ => Some x
      | GT _ => find k s'
     end
 end.

Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
Proof.
   intros m x. unfold PX.MapsTo.
   functional induction (find x m).
   - intros e H0. inversion H0.
   - intros e H0. inversion H0.
   - intros e H0. inversion H0. auto.
   - intros e H0. inversion H0. auto.
Qed.

Function add (k : key) (x : elt) (s : t elt) {struct s} : t elt :=
 match s with
  | nil => (k,x) :: nil
  | (k',y) :: l =>
     match X.compare k k' with
      | LT _ => (k,x)::s
      | EQ _ => (k,x)::l
      | GT _ => (k',y) :: add k x l
     end
 end.

Lemma add_1 : forall m x y e, X.eq x y -> MapsTo y e (add x e m).
Proof.
   intros m x y e.
   generalize y; clear y.
   unfold PX.MapsTo.
   functional induction (add x e m); simpl; auto.
Qed.

Lemma add_2 : forall m x y e e', ~ X.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Proof.
   intros m x y e e'.
   generalize y e; clear y e; unfold PX.MapsTo.
   functional induction (add x e' m) ;simpl;auto; clear e0.
   - intros y0 e H1; inversion_clear 1; destruct H0; simpl in *.
     order. auto. auto.
  - intros y0 e H1; inversion_clear 1; intuition.
Qed.

End Elt.

End Raw.



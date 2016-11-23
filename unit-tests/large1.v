Require Import SMTCoq Smt.

(* For Notations *)
Import Bool PArray Int63 List ZArith FArray BVList.BITVECTOR_LIST.
Import ListNotations.
Open Scope list_scope.
Open Scope farray_scope.
Open Scope bv_scope.

Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Notation "¬ x" := (negb x) (at level 30, right associativity): bool_scope.



Goal forall
    (a1 : (farray Z Z))
    ( e1 : Z)
    ( e10 : Z)
    ( e2 : Z)
    ( e3 : Z)
    ( e4 : Z)
    ( e5 : Z)
    ( e6 : Z)
    ( e7 : Z)
    ( e8 : Z)
    ( e9 : Z)
    ( i1 : Z)
    ( i10 : Z)
    ( i2 : Z)
    ( i3 : Z)
    ( i4 : Z)
    ( i5 : Z)
    ( i6 : Z)
    ( i7 : Z)
    ( i8 : Z)
    ( i9 : Z)
    (sk : (farray Z Z) -> (farray Z Z) -> Z),
    
    negb (i9 =? i10) &&
    negb (i8 =? i10) &&
    negb (i8 =? i9) &&
    negb (i7 =? i10) &&
    negb (i7 =? i9) &&
    negb (i7 =? i8) &&
    negb (i6 =? i10) &&
    negb (i6 =? i9) &&
    negb (i6 =? i8) &&
    negb (i6 =? i7) &&
    negb (i5 =? i10) &&
    negb (i5 =? i9) &&
    negb (i5 =? i8) &&
    negb (i5 =? i7) &&
    negb (i5 =? i6) &&
    negb (i4 =? i10) &&
    negb (i4 =? i9) &&
    negb (i4 =? i8) &&
    negb (i4 =? i7) &&
    negb (i4 =? i6) &&
    negb (i4 =? i5) &&
    negb (i3 =? i10) &&
    negb (i3 =? i9) &&
    negb (i3 =? i8) &&
    negb (i3 =? i7) &&
    negb (i3 =? i6) &&
    negb (i3 =? i5) &&
    negb (i3 =? i4) &&
    negb (i2 =? i10) &&
    negb (i2 =? i9) &&
    negb (i2 =? i8) &&
    negb (i2 =? i7) &&
    negb (i2 =? i6) &&
    negb (i2 =? i5) &&
    negb (i2 =? i4) &&
    negb (i2 =? i3) &&
    negb (i1 =? i10) &&
    negb (i1 =? i9) &&
    negb (i1 =? i8) &&
    negb (i1 =? i7) &&
    negb (i1 =? i6) &&
    negb (i1 =? i5) &&
    negb (i1 =? i4) &&
    negb (i1 =? i3) &&
    negb (i1 =? i2) -->

    ((select (store (store (store (store (store (store (store (store (store (store a1 i1 e1) i2 e2) i3 e3) i4 e4) i5 e5) i6 e6) i7 e7) i8 e8) i9 e9) i10 e10) (sk (store (store (store (store (store (store (store (store (store (store a1 i1 e1) i2 e2) i3 e3) i4 e4) i5 e5) i6 e6) i7 e7) i8 e8) i9 e9) i10 e10) (store (store (store (store (store (store (store (store (store (store a1 i9 e9) i3 e3) i5 e5) i4 e4) i6 e6) i1 e1) i10 e10) i2 e2) i8 e8) i7 e7))) =? (select (store (store (store (store (store (store (store (store (store (store a1 i9 e9) i3 e3) i5 e5) i4 e4) i6 e6) i1 e1) i10 e10) i2 e2) i8 e8) i7 e7) (sk (store (store (store (store (store (store (store (store (store (store a1 i1 e1) i2 e2) i3 e3) i4 e4) i5 e5) i6 e6) i7 e7) i8 e8) i9 e9) i10 e10) (store (store (store (store (store (store (store (store (store (store a1 i9 e9) i3 e3) i5 e5) i4 e4) i6 e6) i1 e1) i10 e10) i2 e2) i8 e8) i7 e7)))).
Proof.
  Time smt.
Qed.

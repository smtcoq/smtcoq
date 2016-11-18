(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     * Alain Mebsout                                                    *)
(*     * Burak Ekici                                                      *)
(*                                                                        *)
(*     * The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith BVList Logic Smt.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope int63_scope.
Local Open Scope Z_scope.
Local Open Scope bv_scope.

Import BVList.BITVECTOR_LIST. 
Require Import FArray.


Section BV.

  Import BVList.BITVECTOR_LIST.

  Local Open Scope bv_scope.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      #b|0|0|0|0| = bv1 /\
      #b|1|0|0|0| = bv2 /\
      #b|1|1|0|0| = bv3 ->
      #b|1|1|1|0| = bv4 ->
      bv_ultP bv1 bv2  \/ bv_ultP bv3 bv1 -> bv_ultP bv1 bv3 -> bv_ultP bv1 bv4 \/ bv_ultP bv4 bv1.
  Proof.
    smt.
  Qed.

  Goal forall (a: bitvector 32), a = a.
  Proof.
    smt.
  Qed.

  Goal forall (bv1 bv2: bitvector 4),
       bv1 = bv2 <-> bv2 = bv1.
  Proof.
     smt.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv1 = #b|0|0|0|0| /\
      bv2 = #b|1|0|0|0| /\
      bv3 = #b|1|1|0|0| ->
      bv4 = #b|1|1|1|0| ->
      bv_ultP bv1 bv2 \/ bv_ultP bv3 bv1 /\ bv_ultP bv3 bv4.
  Proof.
     smt.
  Qed.

  Goal forall (a b c: bitvector 4),
                                 (c = (bv_and a b)) ->
                                 ((bv_and (bv_and c a) b) = c).
  Proof.
     smt.
  Qed.


End BV.

Section Arrays.
  Import BVList.BITVECTOR_LIST.
  Import FArray.

  Local Open Scope farray_scope.
  Local Open Scope bv_scope.

  Goal forall (a:farray Z Z), a = a.
  Proof.
    smt.
  Qed.

  Goal forall (a b: farray Z Z), a = b <->  b = a.
  Proof. 
    smt.
  Qed.

  Goal forall (a b: farray (bitvector 8) (bitvector 8)), a = b <->  b = a.
  Proof. 
    smt.
  Qed.

  Goal forall (a b c d: farray Z Z),
      b[0 <- 4] = c ->
      d = b[0 <- 4][1 <- 4]  /\
      a = d[1 <- b[1]]  ->
      a = c.
  Proof.
    smt.
  Qed.

  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv1 = #b|0|0|0|0|  ->
      bv2 = #b|1|0|0|0|  ->
      c = b[bv1 <- 4]  ->
      d = b[bv1 <- 4][bv2 <- 4]  ->
      a = d[bv2 <- b[bv2]]  ->
      a = c.
  Proof.
    smt.
  Qed.

  Goal forall (a b: farray Z Z)
         (v w x y: Z)
         (g: farray Z Z -> Z)
         (f: Z -> Z),
         (a[x <- v] = b) /\ a[y <- w] = b  ->
         (f x) = (f y) \/  (g a) = (g b).
  Proof.
    smt.
  Qed.

  Goal forall (a b: farray Z Z) i,
      a[i <- 3][1 <- b[i <- 4][i]][2 <- 2][1] = 4.
  Proof.
    smt.
    rewrite read_over_other_write; [ | easy].
    rewrite read_over_write.
    rewrite read_over_write. red; auto.
Qed.

End Arrays.

Section UF.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         y = x -> (f x) = (f y).
  Proof.
    smt.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         (f x) = (f y) -> (f y) = (f x).
  Proof.
    smt.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         x + 1 = (y + 1) -> (f y) = (f x).
  Proof.
    smt.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         x = (y + 1) -> (f y) = (f (x - 1)).
  Proof.
    smt.
  Qed.

  Goal forall (f:Z -> Z -> Z) x y z, (x = y) -> (f z x) = (f z y).
  Proof.
    smt.
  Qed.

  Goal forall (t: Type) (p: CompDec t) (x y: t), (x = y) <-> (x = y).
  Proof.
    smt.
  Qed.

End UF.


Section LIA.

   Goal forall a b, a < b -> a < (b + 10).
   Proof. 
     smt.
   Qed.

  Goal forall (a b: Z), a = b <-> b = a.
  Proof.
    smt.
  Qed.

  Goal forall (a b: Z), a = a /\ b = b.
  Proof.
    smt.
  Qed.

  Goal forall (a b: Z), a < b -> a < (b + 1).
  Proof.
    smt.
  Qed.

  Goal forall (a b: Z), (a < b) -> (a + 2 < b + 3).
  Proof.
    smt.
  Qed.

End LIA.

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
Require Import Bool PArray Int63 List ZArith BVList Logic.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope int63_scope.
Local Open Scope Z_scope.
Local Open Scope bv_scope.


Infix "-->" := implb (at level 60, right associativity) : bool_scope.


Import BVList.BITVECTOR_LIST. 
Require Import FArray.

Section BV.

  Import BVList.BITVECTOR_LIST.

  Local Open Scope bv_scope.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 &&
      bv_eq #b|1|0|0|0| bv2 &&
      bv_eq #b|1|1|0|0| bv3 -->
      bv_eq #b|1|1|1|0| bv4 -->
      bv_ult bv1 bv2  || bv_ult bv3 bv1 --> bv_ult bv1 bv3 --> bv_ult bv1 bv4 || bv_ult bv4 bv1.
  Proof.
     smt.
  Qed.

  Goal forall (a: bitvector 32), bv_eq a a.
  Proof.
    smt.
  Qed.

  Goal forall (bv1 bv2: bitvector 4),
       (Bool.eqb (bv_eq bv1 bv2) (bv_eq bv2 bv1)).
  Proof.
     smt.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 &&
      bv_eq #b|1|0|0|0| bv2 &&
      bv_eq #b|1|1|0|0| bv3 -->
      bv_eq #b|1|1|1|0| bv4 -->
      bv_ult bv1 bv2 || bv_ult bv3 bv1 && bv_ult bv3 bv4.
  Proof.
     smt.
  Qed.

  Goal forall (a b c: bitvector 4),
                                 (bv_eq c (bv_and a b))  -->
                                 (bv_eq (bv_and (bv_and c a) b) c).
  Proof.
     smt.
  Qed.

End BV.

Section Arrays.
  Import BVList.BITVECTOR_LIST.
  Import FArray.

  Local Open Scope farray_scope.
  Local Open Scope bv_scope.

  Goal forall (a:farray Z Z), equal a a.
  Proof.
    smt.
  Qed.

  Goal forall (a b: farray Z Z), Bool.eqb (equal a b) (equal b a).
  Proof. 
    smt.
  Qed.

  Goal forall (a b: farray (bitvector 8) (bitvector 8)), Bool.eqb (equal a b) (equal b a).
  Proof. 
    smt.
  Qed.

  Goal forall (a b c d: farray Z Z),
      equal b[0 <- 4] c -->
      equal d b[0 <- 4][1 <- 4]  &&
      equal a d[1 <- b[1]]  -->
      equal a c.
  Proof.
    smt.
  Qed.

  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv_eq #b|0|0|0|0| bv1  -->
      bv_eq #b|1|0|0|0| bv2  -->
      equal c b[bv1 <- 4] -->
      equal d b[bv1 <- 4][bv2 <- 4] -->
      equal a d[bv2 <- b[bv2]] -->
      equal a c.
  Proof.
    smt.
  Qed.

  Goal forall (a b: farray Z Z)
         (v w x y: Z)
         (g: farray Z Z -> Z)
         (f: Z -> Z),
         (equal a[x <- v] b) && (equal a[y <- w] b) --> (Z.eqb (f x) (f y)) || (Z.eqb (g a) (g b)).
  Proof.
    smt.
  Qed.

Goal forall (a b: farray Z Z) i,
      Z.eqb (select (store (store (store a i 3%Z) 1%Z (select (store b i 4) i)) 2%Z 2%Z) 1%Z) 4.
Proof.
    smt.
    rewrite read_over_other_write; try easy.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
Qed.

End Arrays.

Section UF.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         Z.eqb y x --> Z.eqb (f x) (f y).
  Proof.
    smt.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         Z.eqb (f x) (f y) --> Z.eqb (f y) (f x).
  Proof.
    smt.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         Z.eqb (x + 1)  (y + 1) --> Z.eqb (f y) (f x).
  Proof.
    smt.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         Z.eqb x (y + 1) --> Z.eqb (f y) (f (x - 1)).
  Proof.
    smt.
  Qed.


Goal forall (f:Z -> Z -> Z) x y z, (Z.eqb x y) --> Z.eqb (f z x) (f z y).
Proof.
  smt.
Qed.

End UF.


Section LIA.

  Goal forall (a b: Z), Bool.eqb (Z.eqb a b)  (Z.eqb b a).
  Proof.
    smt.
  Qed.

  Goal forall (a b: Z), (Z.eqb a a) && (Z.eqb b b).
  Proof.
    smt.
  Qed.


End LIA.







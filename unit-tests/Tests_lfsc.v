(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Add Rec LoadPath "../src" as SMTCoq.

Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith Logic.


Infix "-->" := implb (at level 60, right associativity) : bool_scope.


Section BV.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

  Goal forall (a b c: bitvector 4),
                                 (c = (bv_and a b)) ->
                                 ((bv_and (bv_and c a) b) = c).
  Proof.
    smt.
  Qed.

  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
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

End BV.


Section Arrays.

  Import FArray.
  Local Open Scope farray_scope.


  Goal forall (a:farray Z Z) i j, i = j -> a[i] = a[j].
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


  (* TODO *)
  (* Goal forall (a b c d: farray Z Z), *)
  (*     b[0%Z <- 4] = c  -> *)
  (*     d = b[0%Z <- 4][1%Z <- 4]  -> *)
  (*     a = d[1%Z <- b[1%Z]]  -> *)
  (*     a = c. *)
  (* Proof. *)
  (*   smt. *)
  (* Qed. *)


(*
  Goal forall (a b: farray Z Z) i,
      (select (store (store (store a i 3%Z) 1%Z (select (store b i 4) i)) 2%Z 2%Z) 1%Z) =  4.
  Proof.
    smt.
    rewrite read_over_other_write; try easy.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
  Qed.
*)


End Arrays.


Section EUF.

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

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         x = (y + 1) -> (f (y + 1)) = (f x).
  Proof.
    smt.
  Qed.

End EUF.


Section LIA.


  Goal forall (a b: Z), a = b <-> b = a.
  Proof.
    smt.
  Qed.

  Goal forall (x y: Z), (x >= y) -> (y < x) \/ (x = y).
  Proof. 
    smt. 
  Qed.


  Goal forall (f : Z -> Z) (a:Z), ((f a) > 1) ->  ((f a) + 1) >= 2 \/((f a) = 30) .
  Proof.
   smt.
  Qed.
 
  Goal forall x: Z, (x = 0%Z) -> (8 >= 0).
  Proof.
    smt.
   Qed.

  Goal forall x: Z, ~ (x < 0%Z) -> (8 >= 0).
  Proof. 
    smt. 
  Qed.

  Goal forall (a b: Z), a < b -> a < (b + 1).
  Proof.
    smt.
  Qed.

  Goal forall (a b: Z), (a < b) -> (a + 2) < (b + 3).
  Proof.
    smt.
  Qed.


  Goal forall a b, a < b -> a < (b + 10).
  Proof. 
    smt.
  Qed.


End LIA.


Section PR.

 Local Open Scope int63_scope.

(* Simple connectors *)

Goal forall (a:bool), a || negb a.
  smt.
Qed.

Goal forall a, negb (a || negb a) = false.
  smt.
Qed.

Goal forall a, (a && negb a) = false.
  smt.
Qed.

Goal forall a, negb (a && negb a).
  smt.
Qed.

Goal forall a, a --> a.
  smt.
Qed.

Goal forall a, negb (a --> a) = false.
  smt.
Qed.


Goal forall a , (xorb a a) || negb (xorb a a).
  smt.
Qed.


Goal forall a, (a||negb a) || negb (a||negb a).
  smt.
Qed.

(* Polarities *)

Goal forall a b, andb (orb (negb (negb a)) b) (negb (orb a b)) = false.
Proof.
  smt.
Qed.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof.
  smt.
Qed.

(* Multiple negations *)

Goal forall a, orb a (negb (negb (negb a))) = true.
Proof.
  smt.
Qed.


Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  smt.
Qed.


Goal true.
  smt.
Qed.

Goal negb false.
  smt.
Qed.

 
Goal forall a, Bool.eqb a a.
Proof.
  smt.
Qed.

 
Goal forall (a:bool), a = a.
  smt.
Qed.

Goal (false || true) && false = false.
Proof.
  smt.
Qed.


Goal negb true = false.
Proof.
  smt.
Qed.


Goal false = false.
Proof.
  smt.
Qed.

Goal forall x y, Bool.eqb (xorb x y) ((x && (negb y)) || ((negb x) && y)).
Proof.
  smt.
Qed.


Goal forall x y, Bool.eqb (x --> y) ((x && y) || (negb x)).
Proof.
  smt.
Qed.


Goal forall x y z, Bool.eqb (ifb x y z) ((x && y) || ((negb x) && z)).
Proof.
  smt.
Qed.


Goal forall a b c, (((a && b) || (b && c)) && (negb b)) = false.
Proof.
  smt.
Qed.

Goal forall a, ((a || a) && (negb a)) = false.
Proof.
  smt.
Qed.


Goal forall a, (negb (a || (negb a))) = false.
Proof.
  smt.
Qed.


Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  smt.
Qed.


(** The same goal above with a, b and c are concrete terms *)
Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  smt.
Qed.


Goal forall a b c d, ((a && b) && (c || d) && (negb (c || (a && b && d)))) = false.
Proof.
  smt.
Qed.


Goal forall a b c d, (a && b && c && ((negb a) || (negb b) || d) && ((negb d) || (negb c))) = false.
Proof.
  smt.
Qed.


(* Pigeon hole: 4 holes, 5 pigeons *)
Goal forall x11 x12 x13 x14 x15 x21 x22 x23 x24 x25 x31 x32 x33 x34 x35 x41 x42 x43 x44 x45, (
  (orb (negb x11) (negb x21)) &&
  (orb (negb x11) (negb x31)) &&
  (orb (negb x11) (negb x41)) &&
  (orb (negb x21) (negb x31)) &&
  (orb (negb x21) (negb x41)) &&
  (orb (negb x31) (negb x41)) &&

  (orb (negb x12) (negb x22)) &&
  (orb (negb x12) (negb x32)) &&
  (orb (negb x12) (negb x42)) &&
  (orb (negb x22) (negb x32)) &&
  (orb (negb x22) (negb x42)) &&
  (orb (negb x32) (negb x42)) &&

  (orb (negb x13) (negb x23)) &&
  (orb (negb x13) (negb x33)) &&
  (orb (negb x13) (negb x43)) &&
  (orb (negb x23) (negb x33)) &&
  (orb (negb x23) (negb x43)) &&
  (orb (negb x33) (negb x43)) &&

  (orb (negb x14) (negb x24)) &&
  (orb (negb x14) (negb x34)) &&
  (orb (negb x14) (negb x44)) &&
  (orb (negb x24) (negb x34)) &&
  (orb (negb x24) (negb x44)) &&
  (orb (negb x34) (negb x44)) &&

  (orb (negb x15) (negb x25)) &&
  (orb (negb x15) (negb x35)) &&
  (orb (negb x15) (negb x45)) &&
  (orb (negb x25) (negb x35)) &&
  (orb (negb x25) (negb x45)) &&
  (orb (negb x35) (negb x45)) &&


  (orb (negb x11) (negb x12)) &&
  (orb (negb x11) (negb x13)) &&
  (orb (negb x11) (negb x14)) &&
  (orb (negb x11) (negb x15)) &&
  (orb (negb x12) (negb x13)) &&
  (orb (negb x12) (negb x14)) &&
  (orb (negb x12) (negb x15)) &&
  (orb (negb x13) (negb x14)) &&
  (orb (negb x13) (negb x15)) &&
  (orb (negb x14) (negb x15)) &&

  (orb (negb x21) (negb x22)) &&
  (orb (negb x21) (negb x23)) &&
  (orb (negb x21) (negb x24)) &&
  (orb (negb x21) (negb x25)) &&
  (orb (negb x22) (negb x23)) &&
  (orb (negb x22) (negb x24)) &&
  (orb (negb x22) (negb x25)) &&
  (orb (negb x23) (negb x24)) &&
  (orb (negb x23) (negb x25)) &&
  (orb (negb x24) (negb x25)) &&

  (orb (negb x31) (negb x32)) &&
  (orb (negb x31) (negb x33)) &&
  (orb (negb x31) (negb x34)) &&
  (orb (negb x31) (negb x35)) &&
  (orb (negb x32) (negb x33)) &&
  (orb (negb x32) (negb x34)) &&
  (orb (negb x32) (negb x35)) &&
  (orb (negb x33) (negb x34)) &&
  (orb (negb x33) (negb x35)) &&
  (orb (negb x34) (negb x35)) &&

  (orb (negb x41) (negb x42)) &&
  (orb (negb x41) (negb x43)) &&
  (orb (negb x41) (negb x44)) &&
  (orb (negb x41) (negb x45)) &&
  (orb (negb x42) (negb x43)) &&
  (orb (negb x42) (negb x44)) &&
  (orb (negb x42) (negb x45)) &&
  (orb (negb x43) (negb x44)) &&
  (orb (negb x43) (negb x45)) &&
  (orb (negb x44) (negb x45)) &&


  (orb (orb (orb x11 x21) x31) x41) &&
  (orb (orb (orb x12 x22) x32) x42) &&
  (orb (orb (orb x13 x23) x33) x43) &&
  (orb (orb (orb x14 x24) x34) x44) &&
  (orb (orb (orb x15 x25) x35) x45)) = false.
Proof.
  smt.
Qed.


Goal forall a b c f p, ((Z.eqb a c) && (Z.eqb b c) && ((negb (Z.eqb (f a) (f b))) || ((p a) && (negb (p b))))) = false.
Proof.
  smt.
Qed.


Goal forall a b c (p : Z -> bool), ((((p a) && (p b)) || ((p b) && (p c))) && (negb (p b))) = false.
Proof.
  smt.
Qed.


Goal forall x y z f, ((Z.eqb x y) && (Z.eqb y z) && (negb (Z.eqb (f x) (f z)))) = false.
Proof.
  smt.
Qed.

Goal forall x y z f, ((negb (Z.eqb (f x) (f y))) && (Z.eqb y z) && (Z.eqb (f x) (f (f z))) && (Z.eqb x y)) = false.
Proof.
  smt.
Qed.

Goal forall a b c d e f, ((Z.eqb a b) && (Z.eqb b c) && (Z.eqb c d) && (Z.eqb c e) && (Z.eqb e f) && (negb (Z.eqb a f))) = false.
Proof.
  smt.
Qed.



Goal forall x y z, ((x <=? 3) && ((y <=? 7) || (z <=? 9))) -->
  ((x + y <=? 10) || (x + z <=? 12)) = true.
Proof.
  smt.
Qed.

Goal forall x, (Z.eqb (x - 3) 7)  -->  (x >=? 10) = true.
Proof.
  smt.
Qed.


Goal forall x y, (x >? y) --> (y + 1 <=? x) = true.
Proof.
  smt.
Qed.


Goal forall x y, Bool.eqb (x <? y) (x <=? y - 1) = true.
Proof.
  smt.
Qed.

Goal forall x y, ((x + y <=? - (3)) && (y >=? 0) 
        || (x <=? - (3))) && (x >=? 0) = false. 
 Proof. 
   smt.
 Qed. 

Goal forall x, (andb ((x - 3) <=? 7) (7 <=? (x - 3))) --> (x >=? 10) = true.
Proof.
  smt.
Qed.

Goal forall x, (Z.eqb (x - 3) 7) --> (10 <=? x) = true.
Proof.
  smt.
Qed.


(* More general examples *)
Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  smt.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  smt.
Qed.


Goal forall b1 b2 x1 x2,
  (ifb b1
    (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
    (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2)))) -->
  ((b1 --> b2) && (b2 --> b1) && (Z.eqb x1 x2)).
Proof.
  smt.
Qed.


(* With let ... in ... *)
Goal forall b,
  let a := b in
  a && (negb a) = false.
Proof.
  smt.
Qed.

Goal forall b,
  let a := b in
  a || (negb a) = true.
Proof.
  smt.
Qed.

(* With concrete terms *)
Goal forall i j,
  let a := i == j in
  a && (negb a) = false.
Proof.
  smt.
Qed.

Goal forall i j,
  let a := i == j in
  a || (negb a) = true.
Proof.
  smt.
Qed.


(* Congruence in which some premises are REFL *)
Goal forall (f:Z -> Z -> Z) x y z,
  (Z.eqb x y) --> (Z.eqb (f z x) (f z y)).
Proof.
  smt.
Qed.

Goal forall (f:Z -> Z -> Z) x y z,
  (x = y) -> (f z x) = (f z y).
Proof.
  smt.
Qed.

Goal forall (P:Z -> Z -> bool) x y z,
  (Z.eqb x y) --> ((P z x) --> (P z y)).
Proof.
  smt.
Qed.


End PR.


Section A_BV_EUF_LIA_PR.
  Import BVList.BITVECTOR_LIST FArray.

  Local Open Scope farray_scope.
  Local Open Scope bv_scope. 

  (* TODO *)
  (* Goal forall (bv1 bv2 : bitvector 4) *)
  (*        (a b c d : farray (bitvector 4) Z), *)
  (*     bv1 = #b|0|0|0|0|  -> *)
  (*     bv2 = #b|1|0|0|0|  -> *)
  (*     c = b[bv1 <- 4]  -> *)
  (*     d = b[bv1 <- 4][bv2 <- 4]  -> *)
  (*     a = d[bv2 <- b[bv2]]  -> *)
  (*     a = c. *)
  (* Proof. *)
  (*   smt. *)
  (* Qed. *)

  (* TODO *)
  (* Goal forall (bv1 bv2 : bitvector 4) *)
  (*        (a b c d : farray (bitvector 4) Z), *)
  (*     bv1 = #b|0|0|0|0|  /\ *)
  (*     bv2 = #b|1|0|0|0|  /\ *)
  (*     c = b[bv1 <- 4]  /\ *)
  (*     d = b[bv1 <- 4][bv2 <- 4]  /\ *)
  (*     a = d[bv2 <- b[bv2]]  -> *)
  (*     a = c. *)
  (* Proof. *)
  (*   smt. *)
  (* Qed. *)

  (** the example in the CAV paper *)
  Goal forall (a b: farray Z Z) (v w x y: Z)
              (r s: bitvector 4)
              (f: Z -> Z)
              (g: farray Z Z -> Z)
              (h: bitvector 4 -> Z),
              a[x <- v] = b /\ a[y <- w] = b ->
              r = s /\ h r = v /\ h s = y ->
              v < x + 1 /\ v > x - 1 ->
              f (h r) = f (h s) \/ g a = g b.
  Proof.
    smt. (** "cvc4. verit." also solves the goal *)
  Qed.

  (** the example in the FroCoS paper *)
  Goal forall (a b: farray Z Z) (v w x y z t: Z)
              (r s: bitvector 4)
              (f: Z -> Z)
              (g: farray Z Z -> Z)
              (h: bitvector 4 -> Z),
              a[x <- v] = b /\ a[y <- w] = b ->
              a[z <- w] = b /\ a[t <- v] = b ->
              r = s -> v < x + 10 /\ v > x - 5 ->
              ~ (g a = g b) \/ f (h r) = f (h s).
  Proof.
    smt. (** "cvc4. verit." also solves the goal *)
  Qed.


  Goal forall (a b: farray (bitvector 4) Z)
         (x y: bitvector 4)
         (v: Z),
      b[bv_add y x <- v] = a /\
      b = a[bv_add x y <- v]  ->
      a = b.
  Proof.
    smt.
    (* CVC4 preprocessing hole on BV *)
    replace (bv_add x y) with (bv_add y x)
      by apply bv_eq_reflect, bv_add_comm.
    verit.
  Qed.

  Goal forall (a:farray Z Z), a = a.
  Proof.
    smt.
  Qed.

  Goal forall (a b: farray Z Z), a = b <->  b = a.
  Proof.
    smt.
  Qed.

End A_BV_EUF_LIA_PR.


(*
   Local Variables:
   coq-load-path: ((rec "../src" "SMTCoq"))
   End:
*)

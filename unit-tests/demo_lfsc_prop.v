Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith BVList Logic.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope int63_scope.
Local Open Scope Z_scope.
Local Open Scope bv_scope.

Import BVList.BITVECTOR_LIST. 
Require Import FArray.

Ltac cvc4' :=
  repeat match goal with
          | [ |- forall _ : bitvector _, _]                => intro
          | [ |- forall _ : farray _ _, _]                 => intro
          | [ |- forall _ : _ -> _, _]                     => intro
          | [ |- forall _ : Z, _]                          => intro
          | [ |- forall _ : Type, _]                       => intro
          | [ p: (CompDec ?t) 
             |-  context[ forall _ : ?t, _ ] ]             => intro

          | [ |- forall t : Type, CompDec t -> _  ]        => intro
          | [ |- CompDec _ -> _  ]                         => intro
          | [ |- context[ bv_ultP _ _ ] ]                  => rewrite <- bv_ult_B2P
          | [ |- context[ bv_sltP _ _ ] ]                  => rewrite <- bv_slt_B2P
          | [ |- context[ Z.lt _ _ ] ]                     => rewrite <- lt_Z_B2P'; rewrite <- lt_Z_B2P
          | [ |- context[ Z.gt _ _ ] ]                     => rewrite <- gt_Z_B2P'; rewrite <- gt_Z_B2P
          | [ |- context[ Z.le _ _ ] ]                     => rewrite <- le_Z_B2P'; rewrite <- le_Z_B2P
          | [ |- context[ Z.ge _ _ ] ]                     => rewrite <- ge_Z_B2P'; rewrite <- ge_Z_B2P

          | [ p: (CompDec ?t)
              |- context[ @Logic.eq ?t _ _ ] ]             => pose proof p as p0; rewrite <- !(leibniz_lcompdec _ p); 
                                                              rewrite <- !(@lcompdec _ p); destruct p

          | [ Eqb : (EqbType ?ty)  |- _ ]                  => destruct Eqb; simpl

          | [ |- context[ @Logic.eq (bitvector _) _ _ ] ]  => rewrite <- leibniz_bv_eq_B2P; rewrite <- bv_eq_B2P
          | [ |- context[ @Logic.eq (farray _ _) _ _ ] ]   => rewrite <- leibniz_equal_B2P; rewrite <- equal_B2P
          | [ |- context[ @Logic.eq Z _ _ ] ]              => rewrite <- leibniz_eq_Z_B2P; rewrite <- eq_Z_B2P


          | [ |- context[?G0 = true \/ ?G1 = true ] ]      => rewrite (@reflect_iff (G0 = true \/ G1 = true) (orb G0 G1));
                                                              try apply orP
          | [ |- context[?G0 = true -> ?G1 = true ] ]      => rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1)); 
                                                              try apply implyP
          | [ |- context[?G0 = true /\ ?G1 = true ] ]      => rewrite (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1)); 
                                                              try apply andP
          | [ |- context[?G0 = true <-> ?G1 = true ] ]     => rewrite (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1)); 
                                                              try apply iffP 
          | [ |- _ : bool]                                 => verit
          | [ |- _ : bool]                                 => try (cvc4; verit)
          | [ |- _ : (CompDec _ )]                         => try easy

         end.


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
     cvc4'.
  Qed.

  Goal forall (a: bitvector 32), a = a.
  Proof.
    cvc4'.
  Qed.

  Goal forall (bv1 bv2: bitvector 4),
       bv1 = bv2 <-> bv2 = bv1.
  Proof.
     cvc4'.
  Qed.

  Goal forall (bv1 bv2: bitvector 4),
      bv1 = bv2 <-> bv2 = bv1.
  Proof.
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv1 = #b|0|0|0|0| /\
      bv2 = #b|1|0|0|0| /\
      bv3 = #b|1|1|0|0| ->
      bv4 = #b|1|1|1|0| ->
      bv_ultP bv1 bv2 \/ bv_ult bv3 bv1 = true /\ bv_ultP bv3 bv4.
  Proof.
     cvc4'.
  Qed.

  Goal forall (a b c: bitvector 4),
                                 (c = (bv_and a b)) ->
                                 ((bv_and (bv_and c a) b) = c).
  Proof.
     cvc4'.
  Qed.

  Goal forall (a b c: bitvector 4),
                                 (bv_eq c (bv_and a b)) = true ->
                                 (bv_eq (bv_and (bv_and c a) b) c) = true.
  Proof.
     cvc4'.
  Qed.

End BV.

Section Arrays.
  Import BVList.BITVECTOR_LIST.
  Import FArray.

  Local Open Scope farray_scope.
  Local Open Scope bv_scope.

  Goal forall (a:farray Z Z), a = a.
  Proof.
    cvc4'. Grab Existential Variables. 
    apply Z_comp.
    apply Z_comp.
  Qed.

  Goal forall (a b: farray Z Z), a = b <->  b = a.
  Proof. 
    cvc4'. Grab Existential Variables. 
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
  Qed.

  Goal forall (a b: farray (bitvector 8) (bitvector 8)), a = b <->  b = a.
  Proof. 
    cvc4'. Grab Existential Variables. 
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
  Qed.

  Goal forall (a b c d: farray Z Z),
      b[0 <- 4] = c ->
      d = b[0 <- 4][1 <- 4]  /\
      a = d[1 <- b[1]]  ->
      a = c.
  Proof.
    cvc4'. Grab Existential Variables. 
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
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
    cvc4'. Grab Existential Variables.
    apply Z_comp.
    apply BV_comp.
    apply Z_comp.
    apply BV_comp.
    apply Z_comp.
    apply BV_comp.
    apply Z_comp.
    apply BV_comp.
  Qed.

  Goal forall (a b: farray Z Z)
         (v w x y: Z)
         (g: farray Z Z -> Z)
         (f: Z -> Z),
         (a[x <- v] = b) /\ a[y <- w] = b  ->
         (f x) = (f y) \/  (g a) = (g b).
  Proof.
    cvc4'. Grab Existential Variables.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
  Qed.

Goal forall (a b: farray Z Z) i,
      (select (store (store (store a i 3%Z) 1%Z (select (store b i 4) i)) 2%Z 2%Z) 1%Z) =  4.
Proof.
    cvc4'.
    rewrite read_over_other_write; try easy.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
Qed.

End Arrays.

Section UF.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         y = x -> (f x) = (f y).
  Proof.
    cvc4'.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         (f x) = (f y) -> (f y) = (f x).
  Proof.
    cvc4'.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         x + 1 = (y + 1) -> (f y) = (f x).
  Proof.
    cvc4'.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         x = (y + 1) -> (f y) = (f (x - 1)).
  Proof.
    cvc4'.
  Qed.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         x = (y + 1) -> (f (y + 1)) = (f x).
  Proof.
    cvc4'.
  Qed.

  Goal forall (f : Z -> Z) (a:Z), ((f a) > 1) ->  ((f a) + 1) >= 2 \/ ((f a) = 30) .
  Proof.
    cvc4'.
  Qed.

Goal forall (f:Z -> Z -> Z) x y z, (x = y) -> (f z x) = (f z y).
Proof.
  cvc4'.
Qed.

Goal forall (t: Type) (p: CompDec t) (x y: t), (x = y) <-> (x = y).
Proof. cvc4'. Qed.

End UF.


Section LIA.

  Goal forall a b, a < b -> a < (b + 10).
  Proof. 
    cvc4'.
  Qed.

  Goal forall (a b: Z), a = b <-> b = a.
  Proof.
    cvc4'.
  Qed.

  Goal forall (a b: Z), a = a /\ b = b.
  Proof.
    cvc4'.
  Qed.

  Goal forall (a b: Z), a < b -> a < (b + 1).
  Proof.
    cvc4'.
  Qed.

  Goal forall (a b: Z), (a < b) -> (a + 2) < (b + 3).
  Proof. 
    cvc4'.
  Qed.

End LIA.







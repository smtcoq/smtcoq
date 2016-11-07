Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith BVList Logic.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope int63_scope.
Local Open Scope Z_scope.
Local Open Scope bv_scope.

Import BVList.BITVECTOR_LIST. 
Require Import FArray.

Infix "-->" := implb (at level 60, right associativity) : bool_scope.

Ltac cvc4' :=
  repeat match goal with
          | [ |- forall _ : bitvector _, _]                => intro
          | [ |- forall _ : farray _ _, _]                 => intro
          | [ |- forall _ : _ -> _, _]                     => intro
          | [ |- forall _ : Z, _]                          => intro
          | [ |- context[ bv_ultP _ _ ] ]                  => rewrite <- bv_ult_B2P
          | [ |- context[ bv_sltP _ _ ] ]                  => rewrite <- bv_slt_B2P
          | [ |- context[ Z.lt _ _ ] ]                     => rewrite <- lt_Z_B2P'; rewrite <- lt_Z_B2P

          | [ |- context[ @Logic.eq (bitvector _) _ _ ] ]  => rewrite <- leibniz_bv_eq_B2P; rewrite <- bv_eq_B2P
          | [ |- context[ @Logic.eq (farray _ _) _ _ ] ]   => rewrite <- leibniz_equal_B2P; rewrite <- equal_B2P
          | [ |- context[ @Logic.eq Z _ _ ] ]              => rewrite <- leibniz_eq_Z_B2P; rewrite <- eq_Z_B2P

          | [ |- context[?G0 = true \/ ?G1 = true ] ]      => rewrite (@reflect_iff (G0 = true \/ G1 = true) (orb G0 G1));
                                                              try apply orP
          | [ |- context[?G0 = true -> ?G1 = true ] ]      => rewrite (@reflect_iff (G0 = true -> G1 = true) (G0 --> G1)); 
                                                              try apply implyP
          | [ |- context[?G0 = true /\ ?G1 = true ] ]      => rewrite (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1)); 
                                                              try apply andP
          | [ |- context[?G0 = true <-> ?G1 = true ] ]     => rewrite (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1)); 
                                                              try apply iffP 
          | [ |- _ : bool]                                 => verit
          | [ |- _ : bool]                                 => (cvc4; verit)

         end.

Goal forall (f : Z -> Z) (a:Z), ((f a) = 1) ->  ((f a) + 1) = 2.
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

  Goal forall (a b: Z), a = b -> a < (b + 1).
  Proof.
    cvc4'.
  Qed.

Goal forall (a b: farray Z Z) i,
      (select (store (store (store a i 3%Z) 1%Z (select (store b i 4) i)) 2%Z 2%Z) 1%Z) =  4.
Proof.
    cvc4'.
    rewrite read_over_other_write; try easy.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
Qed.

Section BV.

  Import BVList.BITVECTOR_LIST.

  Check bv_eqP.
  Local Open Scope bv_scope.

  Goal forall (bv1 bv2 bv3: bitvector 4),
      Logic.eq #b|0|0|0|0| bv1 /\
      Logic.eq #b|1|0|0|0| bv2  /\
      Logic.eq #b|1|1|0|0| bv3  ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true -> bv_ultP bv1 bv3.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true /\
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv_eq #b|1|1|0|0| bv3 = true  ->
      bv_eq #b|1|1|1|0| bv4 = true  ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true -> bv_ultP bv1 bv3 \/ bv_ultP bv1 bv4.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true /\
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv_eq #b|1|1|0|0| bv3 = true  ->
      bv_eq #b|1|1|1|0| bv4 = true  ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true -> bv_ultP bv1 bv3 /\ bv_ultP bv1 bv4.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true /\
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv_eq #b|1|1|0|0| bv3 = true  ->
      bv_eq #b|1|1|1|0| bv4 = true  ->
      bv_ult bv1 bv2 = true \/ bv_ultP bv3 bv1 -> bv_ultP bv1 bv3 /\ bv_ultP bv1 bv4.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      Logic.eq #b|0|0|0|0| bv1 /\
      Logic.eq #b|1|0|0|0| bv2  /\
      Logic.eq #b|1|1|0|0| bv3  ->
      Logic.eq #b|1|1|1|0| bv4  ->
      bv_ultP bv1 bv2 \/ bv_ultP bv3 bv1 -> bv_ultP bv1 bv3 /\ bv_ultP bv1 bv4.
  Proof. 
     Time cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true /\
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv_eq #b|1|1|0|0| bv3 = true  ->
      bv_eq #b|1|1|1|0| bv4 = true  ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true -> bv_ultP bv1 bv3 -> bv_ultP bv1 bv4 \/ bv_ultP bv4 bv1.
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
      bv_eq bv1 bv2 = true <-> bv_eq bv2 bv1 = true.
  Proof.
     cvc4'.
  Qed.


  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true  ->
      bv_eq #b|1|0|0|0| bv2 = true /\
      bv_eq #b|1|1|0|0| bv3 = true ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true \/ bv_ult bv2 bv1 = true.
  Proof. 
     cvc4'.
  Qed.


  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv_ultP bv1 bv2 \/ bv_ultP bv3 bv1.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true  /\
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv_eq #b|1|1|0|0| bv3 = true ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true  /\
      bv_eq #b|1|0|0|0| bv2 = true /\
      bv_eq #b|1|1|0|0| bv3 = true ->
      bv_ult bv1 bv2 = true \/ bv_ult bv3 bv1 = true.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv1 = #b|0|0|0|0|  ->
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv4 = #b|1|1|1|0|  ->
      (bv_ult bv1 bv2 = true \/ bv_ultP bv3 bv1) /\ bv_ultP bv3 bv4 \/ bv_ult bv1 bv4 = true /\ bv_ultP bv2 bv4.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true  ->
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv_eq #b|1|1|0|0| bv3 = true ->
      bv_eq #b|1|1|1|0| bv4 = true ->
      bv_ultP bv1 bv2 \/ bv_ult bv3 bv1 = true /\ bv_ult bv3 bv4 = true.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv_eq #b|1|0|0|0| bv2 = true  /\
      bv3 = #b|1|1|0|0|  ->
      bv4 = #b|1|1|1|0|  ->
      bv_ultP bv1 bv2 \/ bv_ultP bv3 bv1 /\ bv_ultP bv3 bv4 /\ bv_ult bv1 bv4 = true.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true  /\
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv4 = #b|1|1|1|0|  ->
      bv_ultP bv1 bv2 \/ bv_ultP bv3 bv1 /\ bv_ultP bv3 bv4.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3 bv4: bitvector 4),
      bv_eq #b|0|0|0|0| bv1 = true  /\
      bv2 = #b|1|0|0|0|  /\
      bv_eq #b|1|1|0|0| bv3 = true  ->
      bv4 = #b|1|1|1|0| ->
      bv_ultP bv1 bv2 \/ bv_ult bv3 bv1 = true /\ bv_ultP bv3 bv4.
  Proof. 
     cvc4'.
  Qed.


  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2 bv3: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
      bv3 = #b|1|1|0|0|  ->
      bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3 /\ bv_ultP bv1 bv3.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (bv1 bv2: bitvector 4),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  ->
      bv_ultP bv1 bv2.
  Proof. 
     cvc4'.
  Qed.

  Goal forall (a b c: bitvector 4),
                                 (c = (bv_and a b)) ->
                                 ((bv_and (bv_and c a) b) = c).
  Proof.
    cvc4'.
  Qed.

  Goal forall (bv1 bv2: bitvector 4),
      bv1 = #b|0|0|0|0|  ->
      bv2 = #b|1|0|0|0|  ->
      bv_ultP bv1 bv2.
  Proof. 
     cvc4'.
  Qed.


  Goal forall (a b c: bitvector 4),
                                 (bv_eqP c (bv_and a b)) ->
                                 (bv_eqP (bv_and (bv_and c a) b) c).
  Proof.
    intros a b c H.
    apply bv_eq_B2P. apply bv_eq_B2P in H.
    revert H. 
    apply
     (reflect_iff (bv_eq (n:=4) c (bv_and (n:=4) a b) = true ->
                   bv_eq (n:=4) (bv_and (n:=4) (bv_and (n:=4) c a) b) c = true) 
                   (bv_eq (n:=4) c (bv_and (n:=4) a b) -->
                   bv_eq (n:=4) (bv_and (n:=4) (bv_and (n:=4) c a) b) c) ).
    apply implyP. 
    cvc4.
  Qed.

  Goal forall (a b c: bitvector 4),
                                 (bv_eq c (bv_and a b)) = true ->
                                 (bv_eq (bv_and (bv_and c a) b) c) = true.
  Proof.
    intros a b c. 
    apply
     (reflect_iff (bv_eq (n:=4) c (bv_and (n:=4) a b) = true ->
                   bv_eq (n:=4) (bv_and (n:=4) (bv_and (n:=4) c a) b) c = true)
                   (bv_eq (n:=4) c (bv_and (n:=4) a b) -->
                   bv_eq (n:=4) (bv_and (n:=4) (bv_and (n:=4) c a) b) c) ).
     apply implyP. 
     cvc4.
  Qed.

  Goal forall (bv1 bv2 : bitvector 4),
      bv_eqP #b|0|0|0|0| bv1  ->
      bv_eqP #b|1|0|0|0| bv2  ->
      bv_ultP bv1 bv2.
  Proof.
     intros a b H0 H1.
     apply bv_eq_B2P in H0. apply bv_eq_B2P in H1. apply bv_ult_B2P.
     revert H1.

     apply 
       (reflect_iff
            (bv_eq (n:=N.of_nat (Datatypes.length (b|1|0|0|0))) #b|1|0|0|0| b = true -> 
             bv_ult (n:=4) a b = true)
            (bv_eq (n:=N.of_nat (Datatypes.length (b|1|0|0|0))) #b|1|0|0|0| b --> 
             bv_ult (n:=4) a b)
            ).
     apply implyP.
  
     revert H0.
     apply 
       (reflect_iff
            (bv_eq (n:=N.of_nat (Datatypes.length (b|0|0|0|0))) #b|0|0|0|0| a = true ->
             bv_eq (n:=N.of_nat (Datatypes.length (b|1|0|0|0))) #b|1|0|0|0| b --> 
             bv_ult (n:=4) a b = true)
            (bv_eq (n:=N.of_nat (Datatypes.length (b|0|0|0|0))) #b|0|0|0|0| a -->
             bv_eq (n:=N.of_nat (Datatypes.length (b|1|0|0|0))) #b|1|0|0|0| b -->
             bv_ult (n:=4) a b)
            ).

      apply implyP.

     cvc4.
  Qed.

  Goal forall (bv1 bv2 : bitvector 4),
      bv_eqP #b|0|0|0|0| bv1  ->
      bv_eqP #b|1|0|0|0| bv2  ->
      bv_ultP bv1 bv2.
  Proof.  
     intros a b H0 H1.
     apply bv_eq_B2P in H0. apply bv_eq_B2P in H1. apply bv_ult_B2P.
     revert H0 H1.

     apply 
       (reflect_iff
            (bv_eq (n:=N.of_nat (Datatypes.length (b|0|0|0|0))) #b|0|0|0|0| a = true ->
             bv_eq (n:=N.of_nat (Datatypes.length (b|1|0|0|0))) #b|1|0|0|0| b = true -> 
             bv_ult (n:=4) a b = true)
            (bv_eq (n:=N.of_nat (Datatypes.length (b|0|0|0|0))) #b|0|0|0|0| a -->
             bv_eq (n:=N.of_nat (Datatypes.length (b|1|0|0|0))) #b|1|0|0|0| b --> 
             bv_ult (n:=4) a b)
            ).
     apply implyP2.

     cvc4.
  Qed.

End BV.


Section Arrays.
  Import BVList.BITVECTOR_LIST.
  Import FArray.

  Local Open Scope farray_scope.
  Local Open Scope bv_scope.

  Goal forall (a:farray Z Z), equalP a a.
  Proof.
    intro a.
    apply equal_B2P.
    cvc4; verit.
  Qed.

  Goal forall (a b: farray Z Z), equalP a b -> equalP b a.
  Proof.
    intros a b H.
    apply equal_B2P. apply equal_B2P in H.
    revert H.
    apply 
      (reflect_iff 
         (equal a b = true -> equal b a = true)
         (equal a b --> equal b a)  ).
    apply implyP.

    cvc4; verit.
  Qed.

  Goal forall (a b: farray Z Z)
         (v w x y: Z)
         (g: farray Z Z -> Z)
         (f: Z -> Z),
         equal a[x <- v] b && equal a[y <- w] b  -->
         Z.eqb (f x) (f y) || Z.eqb (g a) (g b).
  Proof.
    cvc4'.
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

  Goal forall (a:bitvector 4), (bv_add a a) = (bv_add a a).
  Proof.
    cvc4'.
  Qed.

  Goal forall (a b c d: farray Z Z),
      b[0%Z <- 4] = c  ->
      d = b[0%Z <- 4][1%Z <- 4]  ->
      a = d[1%Z <- b[1%Z]]  ->
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

  Goal forall (a b c d: farray Z Z),
      b[0%Z <- 4%Z] = c  ->
      d = b[0%Z <- 4%Z][1%Z <- 4%Z]  /\
      a = d[1%Z <- b[1%Z]]  ->
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

  Goal forall (a b c d: farray Z Z),
      b[0 <- 4] = c  /\
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

  Goal forall (a b c d: farray Z Z),
      equal b[0 <- 4] c  -->
      equal d b[0 <- 4][1 <- 4]  -->
      equal a d[1 <- b[1]]  -->
      equal a c.
  Proof.
    cvc4'.
  Qed.


  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv_eq #b|0|0|0|0| bv1  -->
      bv_eq #b|1|0|0|0| bv2  -->
      equal c b[bv1 <- 4]  -->
      equal d b[bv1 <- 4][bv2 <- 4]  -->
      equal a d[bv2 <- b[bv2]]  -->
      equal a c.
  Proof.
    cvc4'.
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

  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv1 = #b|0|0|0|0|  ->
      bv2 = #b|1|0|0|0|  /\
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

  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
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

  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv1 = #b|0|0|0|0|  /\
      bv2 = #b|1|0|0|0|  /\
      c = b[bv1 <- 4]  /\
      d = b[bv1 <- 4][bv2 <- 4]  /\
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

  Goal forall (bv1 bv2 : bitvector 4)
         (a b c d : farray (bitvector 4) Z),
      bv1 = #b|0|0|0|0| /\
      bv2 = #b|1|0|0|0|  /\
      c = b[bv1 <- 4]  /\
      d = b[bv1 <- 4][bv2 <- 4]  /\
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

  Goal forall (bv1 bv2 : bitvector 4) (x: bitvector 4)
         (a b c d : farray (bitvector 4) (bitvector 4)),
      bv_eq #b|0|0|0|0| bv1  -->
      bv_eq #b|1|0|0|0| bv2  -->
      equal c b[bv1 <- x]  -->
      equal d b[bv1 <- x][bv2 <- x]  -->
      equal a d[bv2 <- b[bv2]]  -->
      equal a c.
  Proof.
    Time cvc4. verit.
  Time Qed.

  Goal forall (bv1 bv2 : bitvector 4) (x: bitvector 4)
         (a b c d : farray (bitvector 4) (bitvector 4)),
      bv_eq #b|0|0|0|0| bv1  -->
      bv_eq #b|1|0|0|0| bv2  -->
      equal c b[bv1 <- x]  -->
      equal d b[bv1 <- x][bv2 <- x]  -->
      equal a d[bv2 <- b[bv2]]  -->
      equal a c.
  Proof.
    Time cvc4'.
  Time Qed.

  Goal forall (bv1 bv2 : bitvector 4) (x: bitvector 4)
         (a b c d : farray (bitvector 4) (bitvector 4)),
      bv1 = #b|0|0|0|0|  ->
      bv2 = #b|1|0|0|0|  ->
      c = b[bv1 <- x]  ->
      d = b[bv1 <- x][bv2 <- x]  ->
      a = d[bv2 <- b[bv2]]  ->
      a = c.
  Proof.
    Time cvc4'. Grab Existential Variables.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
    apply BV_comp.
  Time Qed.

  Goal forall (a:bool), a || negb a.
    cvc4'.
  Qed.

  Goal forall (bv1 bv2 : bitvector 4) (x: Z)
         (a b c d : farray (bitvector 4) Z),
      bv_eq #b|0|0|0|0| bv1  -->
      bv_eq #b|1|0|0|0| bv2  -->
      equal c b[bv1 <- x]  -->
      equal d b[bv1 <- x][bv2 <- x]  -->
      equal a d[bv2 <- b[bv2]]  -->
      equal a c.
  Proof.
    cvc4'.
  Qed.

  Goal forall (bv1 bv2 : bitvector 4) (x: Z)
         (a b c d : farray (bitvector 4) Z),
      bv1 = #b|0|0|0|0| ->
      bv2 = #b|1|0|0|0| ->
      c = b[bv1 <- x]  ->
      d = b[bv1 <- x][bv2 <- x]  ->
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

  Goal forall (a:farray Z Z), equal a a.
  Proof.
    verit.
  Qed.

  Goal forall (a b: farray Z Z), a = b <->  b = a.
  Proof. 
    cvc4'. Grab Existential Variables. 
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
    apply Z_comp.
  Qed.

  Goal forall (a:farray Z Z), a = a.
  Proof.
    cvc4'. Grab Existential Variables. 
    apply Z_comp.
    apply Z_comp.
  Qed.

  Goal forall (a b:bitvector 4), bv_eq a b  -->  bv_eq b a.
  Proof.
    verit.
  Qed.

  Goal forall (a b:bitvector 4), a = b  ->  b = a.
  Proof.
    cvc4'.
  Qed.


  Definition lenb := @length bool.
    
  Goal forall (l r: list bool), Nat.eqb (lenb l) (lenb r)  -->  Nat.eqb (lenb l) (lenb r).
  Proof.
    verit. apply Nat_compdec. admit.
  Admitted.
  
  Goal forall (a:farray Z Z) i, Z.eqb (select a i) (select a i).
  Proof.
    verit.
  Qed.

  Goal forall (a:farray Z Z) i, (select a i) = (select a i).
  Proof.
    cvc4'.
  Qed.
  
  Goal forall (a:farray Z Z) i, Z.eqb (select (store a i 1) i) (select (store a i 1) i).
  Proof.
    verit.
  Qed.
  
  Goal forall (a:farray Z Z) i, (select (store a i 1) i) = (select (store a i 1) i).
  Proof.
    cvc4'.
  Qed.

  Goal forall (a:bitvector 4), bv_eq (bv_add a a) (bv_add a a).
  Proof.
    verit.
  Qed.

  Goal forall (a:bitvector 4), (bv_add a a) = (bv_add a a).
  Proof.
    cvc4'.
  Qed.


End Arrays.

Section LIA.

  (** !!! cvc4 tactic crashes !!! => solved by verit *)
  Goal forall a b, a < b -> a < (b + 10).
  Proof. 
    cvc4'.
  Qed.

  Goal forall (a b: Z), a = b -> b = a.
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

  Goal forall (a b: Z), a = a /\ b = b.
  Proof.
    cvc4'.
  Qed.

End LIA.


Local Open Scope int63_scope.


  
(* CVC4 tactic *)

(* Simple connectors *)

Goal forall (a:bool), a || negb a.
  cvc4'.
Qed.

Goal forall a, negb (a || negb a) = false.
  cvc4'.
Qed.

Goal forall a, (a && negb a) = false.
  cvc4'.
Qed.

Goal forall a, negb (a && negb a).
  cvc4'.
Qed.

Goal forall a, implb a a.
  cvc4'.
Qed.

Goal forall a, negb (implb a a) = false.
  cvc4'.
Qed.


Goal forall a , (xorb a a) || negb (xorb a a).
  cvc4'.
Qed.
                                    
Goal forall a, (a||negb a) || negb (a||negb a).
  cvc4'.
Qed.



(* Polarities *)

Goal forall a b, andb (orb (negb (negb a)) b) (negb (orb a b)) = false.
Proof.
  cvc4'.
Qed.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof.
  cvc4'.
Qed.

(* Multiple negations *)

Goal forall a, orb a (negb (negb (negb a))) = true.
Proof.
  cvc4'.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  cvc4'.
Qed.

Goal forall (a b: farray Z Z) i,
      (select (store (store (store a i 3%Z) 1%Z (select (store b i 4) i)) 2%Z 2%Z) 1%Z) =  4.
Proof.
    cvc4'.
    rewrite read_over_other_write; try easy.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
    rewrite read_over_same_write; try easy; try apply Z_compdec.
Qed.

Goal true.
  cvc4'.
Qed.

                                    
Goal negb false.
  cvc4'.
Qed.

 
Goal forall a, Bool.eqb a a.
Proof.
  cvc4'.
Qed.

 
Goal forall (a:bool), a = a.
  cvc4'.
Qed.


(* (* Other connectors *) *)

Goal (false || true) && false = false.
Proof.
  cvc4'.
Qed.


Goal negb true = false.
Proof.
  cvc4'.
Qed.


Goal false = false.
Proof.
  cvc4'.
Qed.


Goal forall x y, Bool.eqb (xorb x y) ((x && (negb y)) || ((negb x) && y)).
Proof.
  cvc4'.
Qed.


Goal forall x y, Bool.eqb (implb x y) ((x && y) || (negb x)).
Proof.
  cvc4'.
Qed.


Goal forall x y z, Bool.eqb (ifb x y z) ((x && y) || ((negb x) && z)).
Proof.
  cvc4'.
Qed.


(* sat2.smt *)
(* ((a ∧ b) ∨ (b ∧ c)) ∧ ¬b = ⊥ *)

Goal forall a b c, (((a && b) || (b && c)) && (negb b)) = false.
Proof.
  cvc4'.
Qed.


(* sat3.smt *)
(* (a ∨ a) ∧ ¬a = ⊥ *)

Goal forall a, ((a || a) && (negb a)) = false.
Proof.
  cvc4'.
Qed.


(* sat4.smt *)
(* ¬(a ∨ ¬a) = ⊥ *)

Goal forall a, (negb (a || (negb a))) = false.
Proof.
  cvc4'.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  cvc4'.
Qed.


(* Le même, mais où a, b et c sont des termes concrets *)

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  cvc4'.
Qed.


(* sat6.smt *)
(* (a ∧ b) ∧ (c ∨ d) ∧ ¬(c ∨ (a ∧ b ∧ d)) = ⊥ *)

Goal forall a b c d, ((a && b) && (c || d) && (negb (c || (a && b && d)))) = false.
Proof.
  cvc4'.
Qed.


(* sat7.smt *)
(* a ∧ b ∧ c ∧ (¬a ∨ ¬b ∨ d) ∧ (¬d ∨ ¬c) = ⊥ *)

Goal forall a b c d, (a && b && c && ((negb a) || (negb b) || d) && ((negb d) || (negb c))) = false.
Proof.
  cvc4'.
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
  cvc4'.
Qed.


(* uf1.smt *)

Goal forall a b c f p, ((Z.eqb a c) && (Z.eqb b c) && ((negb (Z.eqb (f a) (f b))) || ((p a) && (negb (p b))))) = false.
Proof.
  cvc4'.
Qed.


(* uf2.smt *)

Goal forall a b c (p : Z -> bool), ((((p a) && (p b)) || ((p b) && (p c))) && (negb (p b))) = false.
Proof.
  cvc4'.
Qed.


(* uf3.smt *)

Goal forall x y z f, ((Z.eqb x y) && (Z.eqb y z) && (negb (Z.eqb (f x) (f z)))) = false.
Proof.
  cvc4'.
Qed.

(* uf4.smt *)

Goal forall x y z f, ((negb (Z.eqb (f x) (f y))) && (Z.eqb y z) && (Z.eqb (f x) (f (f z))) && (Z.eqb x y)) = false.
Proof.
  cvc4'.
Qed.


(* uf5.smt *)

Goal forall a b c d e f, ((Z.eqb a b) && (Z.eqb b c) && (Z.eqb c d) && (Z.eqb c e) && (Z.eqb e f) && (negb (Z.eqb a f))) = false.
Proof.
  cvc4'.
Qed.


(* lia1.smt *)


(* lia1.smt *)

Theorem lia1: forall x y z, implb ((x <=? 3) && ((y <=? 7) || (z <=? 9)))
  ((x + y <=? 10) || (x + z <=? 12)) = true.
Proof.
  cvc4'.
Qed.

(* lia2.smt *)

Theorem lia2: forall x, implb (Z.eqb (x - 3) 7) (x >=? 10) = true.
Proof.
  cvc4'.
Qed.


(* lia3.smt *)

Theorem lia3: forall x y, implb (x >? y) (y + 1 <=? x) = true.
Proof.
  cvc4'.
Qed.


(* lia4.smt *)

Theorem lia4: forall x y, Bool.eqb (x <? y) (x <=? y - 1) = true.
Proof.
  cvc4'.
Qed.


(* lia5.smt *)
(* cvc4 crashes *)
(* Theorem lia5: forall x y, ((x + y <=? - (3)) && (y >=? 0) *)
(*         || (x <=? - (3))) && (x >=? 0) = false. *)
(* Proof. *)
(*   cvc4. *)
(* Admitted. *)

(* Print Assumptions lia5. *)


(* lia6.smt *)

Theorem lia6: forall x, implb (andb ((x - 3) <=? 7) (7 <=? (x - 3))) (x >=? 10) = true.
Proof.
  cvc4'.
Qed.

(* lia7.smt *)

Theorem lia7: forall x, implb (Z.eqb (x - 3) 7) (10 <=? x) = true.
Proof.
  cvc4'.
Qed.


(* More general examples *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  cvc4'.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  cvc4'.
Qed.


Theorem lia8: forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
    (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  cvc4'.
Qed.


(* With let ... in ... *)

Goal forall b,
  let a := b in
  a && (negb a) = false.
Proof.
  cvc4'.
Qed.

Goal forall b,
  let a := b in
  a || (negb a) = true.
Proof.
  cvc4'.
Qed.

(* Does not work since the [is_true] coercion includes [let in] 
Goal forall b,
  let a := b in
  a || (negb a).
Proof.
  cvc4.
Qed.
*)

(* With concrete terms *)

Goal forall i j,
  let a := i == j in
  a && (negb a) = false.
Proof.
  cvc4'.
Qed.

Goal forall i j,
  let a := i == j in
  a || (negb a) = true.
Proof.
  cvc4'.
Qed.


Section Concret.
  Theorem c1: forall i j,
    (i + j == j) && (negb (i + j == j)) = false.
  Proof. intros.
    cvc4.
    exact int63_compdec.
  Qed.  

End Concret.

Section Concret2.
  Lemma concret : forall i j, (i == j) || (negb (i == j)).
  Proof.
    cvc4.
    exact int63_compdec.
  Qed.

  Check concret.
End Concret2.
Check concret.


(* Congruence in which some premices are REFL *)

Goal forall (f:Z -> Z -> Z) x y z,
  implb (Z.eqb x y) (Z.eqb (f z x) (f z y)).
Proof.
  cvc4'.
Qed.


Goal forall (f:Z -> Z -> Z) x y z,
  (x = y) -> (f z x) = (f z y).
Proof.
  cvc4'.
Qed.

Goal forall (P:Z -> Z -> bool) x y z,
  implb (Z.eqb x y) (implb (P z x) (P z y)).
Proof.
  cvc4'.
Qed.




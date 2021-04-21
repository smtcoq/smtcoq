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


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.11, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

(* Examples that check ZChaff certificates *)

Local Open Scope int63_scope.

Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".
Check sat.

Zchaff_Checker "hole4.cnf" "hole4.log".


(* Example that checks a VeriT certificate, for logic QF_UFLIA *)

Section Verit.
  Verit_Checker "lia.smt2" "lia.vtlog".
End Verit.


(* Example that checks a LFSC certificate, for logic QF_UFLIA *)

Section Lfsc.
  Lfsc_Checker "lia.smt2" "lia.lfsc".
End Lfsc.


(* Examples of the zchaff tactic (requires zchaff in your PATH
   environment variable):
   - with booleans
   - with concrete terms *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

Goal forall (i j k : Z),
    let a := Z.eqb i j in
    let b := Z.eqb j k in
    let c := Z.eqb k i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.


(* Examples of the verit tactics (requires verit in your PATH environment
   variable), which handle
   - propositional logic
   - theory of equality
   - linear integer arithmetic
   - universally quantified hypotheses *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit_bool.
Qed.

Local Open Scope Z_scope.

Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Z.eqb (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit_bool.
Qed.

Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  verit_bool.
Qed.

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
Proof.
  verit.
Qed.


(* Some examples of using verit with lemmas. Use <verit H1 .. Hn> to
   temporarily add the lemmas H1 .. Hn to the verit environment.
 *)

Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, f a =? f b) ->
    forall x, f x =? f 0.
Proof.
  intros f Hf.
  verit Hf.
Qed.

Section With_lemmas.
  Variable f : Z -> Z.
  Variable k : Z.
  Hypothesis f_k_linear : forall x, f (x + 1) =? f x + k.

  Lemma fSS2:
    forall x, f (x + 2) =? f x + 2 * k.
  Proof. verit_no_check f_k_linear. Qed.
End With_lemmas.

(* Instantiating a lemma with multiple quantifiers *)

Section NonLinear.
  Lemma distr_right_inst a b (mult : Z -> Z -> Z) :
    (forall x y z, mult (x + y)  z =? mult x z + mult y z) ->
    (mult (3 + a) b =? mult 3 b + mult a b).
  Proof.
    intro H.
    verit H.
  Qed.
End NonLinear.

(* You can use <Add_lemmas H1 .. Hn> to permanently add the lemmas H1 .. Hn to
   the environment. If you did so in a section then, at the end of the section,
   you should use <Clear_lemmas> to empty the globally added lemmas because
   those lemmas won't be available outside of the section. *)

Section mult3.
  Variable mult3 : Z -> Z.
  Hypothesis mult3_0 : mult3 0 =? 0.
  Hypothesis mult3_Sn : forall n, mult3 (n+1) =? mult3 n + 3.
  Add_lemmas mult3_0 mult3_Sn.

  Lemma mult_3_4_12 : mult3 4 =? 12.
  Proof. verit. Qed.

  Clear_lemmas.
End mult3.


(* Examples of the smt tactic (requires verit and cvc4 in your PATH environment
   variable):
   - propositional logic
   - theory of equality
   - linear integer arithmetic
   - theory of fixed-sized bit-vectors
   - theory of arrays *)

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
    implb
      (ifb b1
           (ifb b2 (Z.eqb (2*x1+1) (2*x2+1)) (Z.eqb (2*x1+1) (2*x2)))
           (ifb b2 (Z.eqb (2*x1) (2*x2+1)) (Z.eqb (2*x1) (2*x2))))
      ((implb b1 b2) && (implb b2 b1) && (Z.eqb x1 x2)).
Proof.
  smt.
Qed.

Goal forall
    (x y: Z)
    (f: Z -> Z),
    x = y + 1 -> f y = f (x - 1).
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
  smt.
Qed.


(* All tactics have a "no_check" variant that is faster but, in case of
   failure, it will only fail at Qed *)

Goal forall (bv1 bv2 bv3: bitvector 4),
    bv1 = #b|0|0|0|0|  /\
    bv2 = #b|1|0|0|0|  /\
    bv3 = #b|1|1|0|0|  ->
    bv_ultP bv1 bv2 /\ bv_ultP bv2 bv3.
Proof.
  smt_no_check.
Qed.

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
  smt_no_check.
Qed.


(** SMTCoq also provides conversion tactics, to inject various integer
    types into the type Z supported by SMTCoq. They can be called before
    the standard SMTCoq tactics. **)

Local Open Scope positive_scope.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof.
  pos_convert.
  verit.
Qed.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((3 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof.
  pos_convert.
  verit.
Qed.

Local Close Scope positive_scope.

Local Open Scope N_scope.

Goal forall (f : N -> N) (x y : N),
    implb ((x + 3) =? y)
          ((f (x + 3)) <=? (f y))
    = true.
Proof.
  N_convert.
  verit.
Qed.

Goal forall (f : N -> N) (x y : N),
    implb ((x + 3) =? y)
          ((2 <? y) && ((f (x + 3)) <=? (f y)))
    = true.
Proof.
  N_convert.
  verit.
Qed.

Local Close Scope N_scope.

Require Import NPeano.
Local Open Scope nat_scope.

Goal forall (f : nat -> nat) (x y : nat),
    implb (Nat.eqb (x + 3) y)
          ((f (x + 3)) <=? (f y))
    = true.
Proof.
  nat_convert.
  verit.
Qed.

Goal forall (f : nat -> nat) (x y : nat),
    implb (Nat.eqb (x + 3) y)
          ((2 <? y) && ((f (x + 3)) <=? (f y)))
    = true.
Proof.
  nat_convert.
  verit.
Qed.

Local Close Scope nat_scope.

(* An example with all 3 types and a binary function *)
Goal forall f : positive -> nat -> N, forall (x : positive) (y : nat),
  implb (x =? 3)%positive
    (implb (Nat.eqb y 7)
      (implb (f 3%positive 7%nat =? 12)%N
        (f x y =? 12)%N)) = true.
  pos_convert.
  nat_convert.
  N_convert.
  verit.
Qed.

Open Scope Z_scope.


(** Now more insightful examples. The first one automatically proves
    properties in group theory. **)

Section Group.
  Variable G : Type.
  (* We suppose that G has a decidable equality *)
  Variable HG : CompDec G.
  Variable op : G -> G -> G.
  Variable inv : G -> G.
  Variable e : G.

  Local Notation "a ==? b" := (@eqb_of_compdec G HG a b) (at level 60).

  (* We can prove automatically that we have a group if we only have the
     "left" versions of the axioms of a group *)
  Hypothesis associative :
    forall a b c : G, op a (op b c) ==? op (op a b) c.
  Hypothesis inverse :
    forall a : G, op (inv a) a ==? e.
  Hypothesis identity :
    forall a : G, op e a ==? a.
  Add_lemmas associative inverse identity.

  (* The "right" version of inverse *)
  Lemma inverse' :
    forall a : G, op a (inv a) ==? e.
  Proof. smt. Qed.

  (* The "right" version of identity *)
  Lemma identity' :
    forall a : G, op a e ==? a.
  Proof. smt inverse'. Qed.

  (* Some other interesting facts about groups *)
  Lemma unique_identity e':
    (forall z, op e' z ==? z) -> e' ==? e.
  Proof. intros pe'; smt pe'. Qed.

  Lemma simplification_right x1 x2 y:
      op x1 y ==? op x2 y -> x1 ==? x2.
  Proof. intro H. smt_no_check (H, inverse'). Qed.

  Lemma simplification_left x1 x2 y:
      op y x1 ==? op y x2 -> x1 ==? x2.
  Proof. intro H. smt_no_check (H, inverse'). Qed.

  Clear_lemmas.
End Group.


(* A full example coming from CompCert, slightly revisited.
   See: https://hal.inria.fr/inria-00289542
        https://xavierleroy.org/memory-model/doc/Memory.html (Section 3)
 *)
Section CompCert.

  Variable block : Set.
  Hypothesis eq_block : CompDec block.

  Variable mem: Set.
  Hypothesis dec_mem : CompDec mem.
  Variable alloc_block: mem -> Z -> Z -> block.
  Variable alloc_mem: mem -> Z -> Z -> mem.
  Variable valid_block: mem -> block -> bool.

  Hypothesis alloc_valid_block_1:
    forall m lo hi b,
      valid_block (alloc_mem m lo hi) b -> ((b = (alloc_block m lo hi)) \/ valid_block m b).

  Hypothesis alloc_valid_block_2:
    forall m lo hi b,
      ((b = (alloc_block m lo hi)) \/ valid_block m b) -> (valid_block (alloc_mem m lo hi) b).

  Hypothesis alloc_not_valid_block:
    forall m lo hi,
       negb (valid_block m (alloc_block m lo hi)).

  Lemma alloc_valid_block_inv m lo hi b :
    valid_block m b -> valid_block (alloc_mem m lo hi) b.
  Proof.
    intro H. verit (alloc_valid_block_2, H).
  Qed.

  Lemma alloc_not_valid_block_2 m lo hi b' :
    valid_block m b' -> b' <> (alloc_block m lo hi).
  Proof.
    intro H. verit (alloc_not_valid_block, H).
  Qed.

End CompCert.

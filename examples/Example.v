(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.6, replace it with:
     Require Import SMTCoq.
   *)

Require Import SMTCoq.SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

(* Examples that check ZChaff certificates *)

Zchaff_Checker "sat.cnf" "sat.log".
Zchaff_Theorem sat "sat.cnf" "sat.log".
Check sat.

Zchaff_Checker "hole4.cnf" "hole4.log".

(* Example that checks a VeriT certificate, for logic QF_UF *)

Section Verit.
  Verit_Checker "euf.smt2" "euf.log".
End Verit.

(* Examples of the zchaff tactic (requires zchaff in your PATH
   environment variable):
   - with booleans
   - with concrete terms *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.

(* Examples of the verit tactic (requires verit in your PATH environment
   variable):
   - with booleans
   - in logics QF_UF and QF_LIA *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  negb (f a =? b) || negb (P (f a)) || (P b).
Proof.
  verit.
Qed.

Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (2*x1+1 =? 2*x2+1) (2*x1+1 =? 2*x2))
    (ifb b2 (2*x1 =? 2*x2+1) (2*x1 =? 2*x2)))
  ((implb b1 b2) && (implb b2 b1) && (x1 =? x2)).
Proof.
  verit.
Qed.

(* Examples of using the conversion tactics *)

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

(* Some examples of using verit with lemmas. Use <verit_base H1 .. Hn; vauto>
   to temporarily add the lemmas H1 .. Hn to the verit environment. *)
Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, f a =? f b) ->
    forall x, f x =? f 0.
Proof.
  intros f Hf.
  verit_base Hf; vauto.
Qed.

Section Without_lemmas.
  Lemma fSS:
    forall (f : Z -> Z) (k : Z) (x : Z),
      implb (f (x+1) =? f x + k)
     (implb (f (x+2) =? f (x+1) + k)
            (f (x+2) =? f x + 2 * k)).
  Proof. verit. Qed.
End Without_lemmas.

Section With_lemmas.
  Variable f : Z -> Z.
  Variable k : Z.
  Hypothesis f_k_linear : forall x, f (x + 1) =? f x + k.

  Lemma fSS2:
    forall x, f (x + 2) =? f x + 2 * k.
  Proof. verit_base f_k_linear; vauto. Qed.
End With_lemmas.

(* You can use <Add_lemmas H1 .. Hn> to permanently add the lemmas H1 .. Hn to
   the environment. If you did so in a section then, at the end of the section,
   you should use <Clear_lemmas> to empty the globally added lemmas because
   those lemmas won't be available outside of the section. *)
Section mult3.
  Variable mult3 : Z -> Z.
  Hypothesis mult3_0 : mult3 0 =? 0.
  Hypothesis mult3_Sn : forall n, mult3 (n+1) =? mult3 n + 3.
  Add_lemmas mult3_0 mult3_Sn.

  Lemma mult3_21 : mult3 7 =? 21.
  Proof. verit. Qed.

  Clear_lemmas.
End mult3.

Section NonLinear.
  Lemma distr_right_inst a b (mult : Z -> Z -> Z) :
    (forall x y z, mult (x + y)  z =? mult x z + mult y z) ->
    (mult (3 + a) b =? mult 3 b + mult a b).
  Proof.
    intro H.
    verit_base H; vauto.
  Qed.
End NonLinear.

Section group.
  Variable op : Z -> Z -> Z.
  Variable inv : Z -> Z.
  Variable e : Z.

  Hypothesis associative :
    forall a b c : Z, op a (op b c) =? op (op a b) c.
  Hypothesis identity :
    forall a : Z, (op e a =? a) && (op a e =? a).
  Hypothesis inverse :
    forall a : Z, (op a (inv a) =? e) && (op (inv a) a =? e).
  Add_lemmas associative identity inverse.

  Lemma unique_identity e':
    (forall z, op e' z =? z) -> e' =? e.
  Proof. intros pe'. verit_base pe'; vauto. Qed.

  Lemma simplification_right x1 x2 y:
      op x1 y =? op x2 y -> x1 =? x2.
  Proof. intro H. verit_base H; vauto. Qed.

  Lemma simplification_left x1 x2 y:
      op y x1 =? op y x2 -> x1 =? x2.
  Proof. intro H. verit_base H; vauto. Qed.

  Clear_lemmas.
End group.

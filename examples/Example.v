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
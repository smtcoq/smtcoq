Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof.
  cvc4.
Qed.


Goal forall a b, andb (andb (orb a b) (negb a)) (negb b) = false.
Proof.
  cvc4.
Qed.


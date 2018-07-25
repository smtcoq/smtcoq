Require Import SMTCoq.

Parameter g : Z -> Z.

Axiom g_2_linear : forall x, Zeq_bool (g (x + 1)) ((g x) + 2).

Lemma apply_lemma_multiple :
  forall x y, Zeq_bool (g (x + y)) ((g x) + y * 2).

Proof.
  verit g_2_linear.
  
Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Parameter m : Z -> Z.
Axiom m_0 : m 0 =? 5.

Lemma cinq_m_0 :
  m 0 =? 5.
Proof. verit_base m_0; vauto. Qed.

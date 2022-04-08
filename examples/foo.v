Add Rec LoadPath "../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import ZArith.

Section test_timeout.

Variable P : Z -> bool.
Variable H0 : P 0.
Variable HInd : forall n, implb (P n) (P (n + 1)).

Goal P 3.
verit.
Qed.

Tactic Notation "verit_timeout2"           :=
  prop2bool;
  [ .. | get_hyps ltac:(fun Hs =>
                          lazymatch Hs with
                          | Some ?Hs => idtac 1 ;
                            prop2bool_hyps Hs; idtac 2 ;
                            [ .. | idtac 3 ; verit_bool_base_auto_timeout (Some Hs) ]
                          | None => idtac 4 ; verit_bool_base_auto_timeout (@None nat)
                          end)
  ].

Goal true -> P 1000000000.
intro H.
verit_timeout2. constructor.
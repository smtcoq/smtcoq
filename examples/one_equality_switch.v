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


Require Import SMTCoq.
Require Import Bool.
Local Open Scope int63_scope.

Parameter f : Z -> Z.

Lemma sym_zeq_bool x y :
  Zeq_bool x y = Zeq_bool y x.

Proof.
  case_eq (Zeq_bool x y).
  rewrite <- Zeq_is_eq_bool. intro H. symmetry. now rewrite <- Zeq_is_eq_bool.
  symmetry. apply not_true_is_false.
  intro H1. rewrite <- Zeq_is_eq_bool in H1.
  symmetry in H1. rewrite Zeq_is_eq_bool in H1.
  rewrite H in H1. discriminate H1.
Qed.

Axiom f_spec : forall x, (f (x+1) =? f x + 1) && (f 0 =? 0).

Lemma f_1 : f 1 =? 1.

Proof.
  verit_base f_spec; vauto; rewrite Z.eqb_sym; auto.
Qed.

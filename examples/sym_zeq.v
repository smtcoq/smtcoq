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

Open Scope Z_scope.

Parameter h : Z -> Z -> Z.
Axiom h_Sm_n : forall x y, h (x+1) y =? h x y.

Lemma h_1_0 :
  h 1 0 =? h 0 0.
Proof. verit_base h_Sm_n; vauto. Qed.

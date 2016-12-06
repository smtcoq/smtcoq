(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Burak Ekici                                                        *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     The University of Iowa                                             *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import
        Bool ZArith BVList Logic BVList FArray
        SMT_classes SMT_classes_instances SMT_terms.
Import BVList.BITVECTOR_LIST. 

Local Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Local Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.

Ltac prop2bool :=
  repeat
    match goal with
    | [ |- forall _ : bitvector _, _] => intro
    | [ |- forall _ : farray _ _, _] => intro
    | [ |- forall _ : _ -> _, _] => intro
    | [ |- forall _ : Z, _] => intro
    | [ |- forall _ : Type, _] => intro
    | [ p: (CompDec ?t) |-  context[ forall _ : ?t, _ ] ] => intro

    | [ |- forall t : Type, CompDec t -> _  ] => intro
    | [ |- CompDec _ -> _  ] => intro
    | [ |- context[ bv_ultP _ _ ] ] => rewrite <- bv_ult_B2P
    | [ |- context[ bv_sltP _ _ ] ] => rewrite <- bv_slt_B2P
    | [ |- context[ Z.lt _ _ ] ] => rewrite <- Z.ltb_lt
    | [ |- context[ Z.gt _ _ ] ] => rewrite Z.gt_lt_iff; rewrite <- Z.ltb_lt
    | [ |- context[ Z.le _ _ ] ] => rewrite <- Z.leb_le
    | [ |- context[ Z.ge _ _ ] ] => rewrite Z.ge_le_iff; rewrite <- Z.leb_le

    | [ p: (CompDec ?t) |- context[ @Logic.eq ?t _ _ ] ] =>
      pose proof p as p0;
      rewrite (@compdec_eq_eqb _ p0);
      destruct p0;
      try exact p

    | [ Eqb : (EqbType ?ty)  |- _ ] => destruct Eqb; simpl

    | [ |- context[ @Logic.eq (bitvector _) _ _ ] ] =>
      rewrite <- bv_eq_reflect

    | [ |- context[ @Logic.eq (farray _ _) _ _ ] ] =>
      rewrite <- equal_iff_eq

    | [ |- context[ @Logic.eq Z _ _ ] ] =>
      rewrite <- Z.eqb_eq

    | [ |- context[?G0 = true \/ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true \/ G1 = true) (orb G0 G1));
      try apply orP

    | [ |- context[?G0 = true -> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1)); 
      try apply implyP

    | [ |- context[?G0 = true /\ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1));
      try apply andP

    | [ |- context[?G0 = true <-> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1));
      try apply iffP

    | [ |- context[?G0 <> true] ] =>
      rewrite (@reflect_iff (G0 <> true) (negb G0));
      try apply negP

    | [ |- context[ True ] ] => rewrite <- TrueB

    | [ |- context[ False ] ] => rewrite <- FalseB

    (* | [ |- _ : (CompDec _ )] => try easy *)
    end.


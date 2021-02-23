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


Require Import
        Bool ZArith BVList Logic BVList FArray
        SMT_classes SMT_classes_instances ReflectFacts.
Import BVList.BITVECTOR_LIST. 

Ltac prop2bool :=
  repeat
    match goal with
    | [ |- forall _ : ?t, _ ] =>
      lazymatch type of t with
      | Prop => fail
      | _ => intro
      end

    | [ |- context[ bv_ultP _ _ ] ] => rewrite <- bv_ult_B2P
    | [ |- context[ bv_sltP _ _ ] ] => rewrite <- bv_slt_B2P
    | [ |- context[ Z.lt _ _ ] ] => rewrite <- Z.ltb_lt
    | [ |- context[ Z.gt _ _ ] ] => rewrite Z.gt_lt_iff; rewrite <- Z.ltb_lt
    | [ |- context[ Z.le _ _ ] ] => rewrite <- Z.leb_le
    | [ |- context[ Z.ge _ _ ] ] => rewrite Z.ge_le_iff; rewrite <- Z.leb_le
    | [ |- context[ Z.eq _ _ ] ] => rewrite <- Z.eqb_eq

    | [ |- context[ @Logic.eq ?t _ _ ] ] =>
      lazymatch t with
      | bitvector _ => rewrite <- bv_eq_reflect
      | farray _ _ => rewrite <- equal_iff_eq
      | Z => rewrite <- Z.eqb_eq
      | bool => fail
      | _ =>
        lazymatch goal with
        | [ p: (CompDec t) |- _ ] =>
          rewrite (@compdec_eq_eqb _ p)
        | _ =>
          let p := fresh "p" in
          assert (p:CompDec t);
          [ auto with typeclass_instances
          | rewrite (@compdec_eq_eqb _ p)
          ]
        end
      end

    | [ |- context[?G0 = true \/ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true \/ G1 = true) (orb G0 G1));
      [ | apply orP]

    | [ |- context[?G0 = true -> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1)); 
      [ | apply implyP]

    | [ |- context[?G0 = true /\ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1));
      [ | apply andP]

    | [ |- context[?G0 = true <-> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1));
      [ | apply iffP]
          
    | [ |- context[ ~ ?G = true ] ] =>
      rewrite (@reflect_iff (~ G = true) (negb G));
      [ | apply negP]

    | [ |- context[ is_true ?G ] ] =>
      unfold is_true

    | [ |- context[ True ] ] => rewrite <- TrueB

    | [ |- context[ False ] ] => rewrite <- FalseB

    (* | [ |- _ : (CompDec _ )] => try easy *)
    end.


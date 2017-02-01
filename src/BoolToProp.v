(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     * Alain Mebsout                                                    *)
(*     * Burak Ekici                                                      *)
(*                                                                        *)
(*     * The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import
        Bool ZArith BVList Logic BVList FArray
        SMT_classes SMT_classes_instances ReflectFacts.
Import BVList.BITVECTOR_LIST. 

Local Coercion is_true : bool >-> Sortclass.

Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.

Ltac bool2prop :=
  repeat
    match goal with
    | [ |- forall _ : bitvector _, _] => intro
    | [ |- forall _ : farray _ _, _] => intro
    | [ |- forall _ : _ -> _, _] => intro
    | [ |- forall _ : Z, _] => intro
    | [ |- forall _ : bool, _] => intro
    | [ |- forall _ : Type, _] => intro
    | [ p: Type |-  context[ forall _ : ?t, _ ] ] => intro

    | [ |- forall t : Type, CompDec t -> _  ] => intro
    | [ |- CompDec _ -> _  ] => intro

    | [ |- context[ bv_ult _ _ ] ] => unfold is_true; rewrite bv_ult_B2P
    | [ |- context[ bv_slt _ _ ] ] => unfold is_true; rewrite bv_slt_B2P
    | [ |- context[ bv_eq _ _ ] ]  => unfold is_true; rewrite bv_eq_reflect
    | [ |- context[ equal _ _ ] ]  => unfold is_true; rewrite equal_iff_eq
    | [ |- context[ Z.ltb _ _ ] ]  => unfold is_true; rewrite Z.ltb_lt
    | [ |- context[ Z.gtb _ _ ] ]  => unfold is_true; rewrite Z.gtb_lt
    | [ |- context[ Z.leb _ _ ] ]  => unfold is_true; rewrite Z.leb_le
    | [ |- context[ Z.geb _ _ ] ]  => unfold is_true; rewrite Z.geb_le
    | [ |- context[ Z.eqb _ _ ] ]  => unfold is_true; rewrite Z.eqb_eq

    | [ |- context[?G0 --> ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true -> G1 = true)  (G0 --> G1)); 
      [ | apply implyP]

    | [ |- context[?G0 || ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true \/ G1 = true) (G0 || G1)); 
      [ | apply orP]

    | [ |- context[?G0 && ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true /\ G1 = true) (G0 && G1)); 
      [ | apply andP]

    | [ |- context[?G0 <--> ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 = true <-> G1 = true) (G0 <--> G1)); 
      [ | apply iffP]

    | [ |- context[ negb ?G ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G <> true) (negb G)); 
      [ | apply negP]

    | [R : CompDec ?t |- context[ CompDec ?t  ] ] => exact R

    | [R : EqbType ?t |- context[ EqbType ?t  ] ] => exact R

    | [ |- context[ false = true ] ] => rewrite FalseB
                                              
    | [ |- context[ true = true ] ] => rewrite TrueB

    end.

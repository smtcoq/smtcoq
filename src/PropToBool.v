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


Section ReflectFacts.

  Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
  Proof.
    intros; destruct H; easy.
  Qed.

  Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
  Proof.
    intros.
    destr_bool; constructor; try now apply H.
    unfold not. intros. apply H in H0. destruct H. easy.
  Qed.

  Lemma reflect_dec : forall P b, reflect P b -> {P} + {~P}.
  Proof. intros; destruct H; [now left | now right]. Qed.

  Lemma implyP : forall (b1 b2: bool), reflect (b1 = true -> b2 = true) (b1 --> b2).
  Proof. intros; apply iff_reflect; split;
      case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
  Qed.

  Lemma iffP : forall (b1 b2: bool), reflect (b1 = true <-> b2 = true) (eqb b1 b2).
  Proof. intros; apply iff_reflect; split;
      case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
  Qed.

  Lemma implyP2 : forall (b1 b2 b3: bool),
      reflect (b1 = true -> b2 = true -> b3 = true) (b1 --> b2 --> b3).
  Proof. intros; apply iff_reflect; split;
      case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
  Qed.

  Lemma andP : forall (b1 b2: bool), reflect (b1 = true /\ b2 = true) (b1 && b2).
  Proof. intros; apply iff_reflect; split;
      case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
  Qed.

  Lemma orP : forall (b1 b2: bool), reflect (b1 = true \/ b2 = true) (b1 || b2).
  Proof. intros; apply iff_reflect; split;
      case_eq b1; case_eq b2; intros; try easy; try compute in *.
    destruct H1 as [H1a | H1b ]; easy. left. easy. left. easy.
    right. easy.
  Qed.

  Lemma negP : forall (b: bool), reflect (~ b = true) (negb b).
  Proof. intros; apply iff_reflect; split;
      case_eq b; intros; try easy; try compute in *.
    contradict H0. easy.
  Qed.

  Lemma FalseB : (false = true) <-> False.
  Proof. split; auto. discriminate. Qed.

  Lemma TrueB : (true = true) <-> True.
  Proof. split; auto. Qed.

End ReflectFacts.


Ltac prop2bool :=
  repeat
    match goal with
    | [ |- forall _ : bitvector _, _] => intro
    | [ |- forall _ : farray _ _, _] => intro
    | [ |- forall _ : _ -> _, _] => intro
    | [ |- forall _ : Z, _] => intro
    | [ |- forall _ : bool, _] => intro
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
      [ | apply orP]
          
    | [ |- context[?G0 = true -> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1)); 
      [ | apply implyP]
          
    | [ |- context[?G0 = true /\ ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1));
      [ | apply andP]
          
    | [ |- context[?G0 = true <-> ?G1 = true ] ] =>
      rewrite (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1));      try apply iffP

    | [ |- context[?G0 <> true] ] =>
      rewrite (@reflect_iff (G0 <> true) (negb G0));
      try apply negP
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

<<<<<<< HEAD

=======
Coercion is_true : bool >-> Sortclass.

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
      unfold is_true; rewrite <- (@reflect_iff (G0 -> G1)  (G0 --> G1)); 
      [ | apply implyP]

    | [ |- context[?G0 || ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 \/ G1) (G0 || G1)); 
      [ | apply orP]

    | [ |- context[?G0 && ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 /\ G1) (G0 && G1)); 
      [ | apply andP]

    | [ |- context[?G0 <--> ?G1 ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (G0 <-> G1) (G0 <--> G1)); 
      [ | apply iffP]

    | [ |- context[ negb ?G ] ] =>
      unfold is_true; rewrite <- (@reflect_iff (~ G) (negb G)); 
      [ | apply negP]

    | [R : CompDec ?t |- context[ CompDec ?t  ] ] => exact R

    | [Eqb : EqbType ?t |- context[ _: bool ] ] =>
      destruct Eqb as (K, L); simpl; rewrite !L

    | [ |- context[ false = true ] ] => rewrite FalseB
                                   
    | [ |- context[ true = true ] ] => rewrite TrueB

    end.

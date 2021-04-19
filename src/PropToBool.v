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


Lemma geb_ge (n m : Z) : (n >=? m)%Z = true <-> (n >= m)%Z.
Proof.
  now rewrite Z.geb_le, Z.ge_le_iff.
Qed.

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
    | [ |- context[ Z.gt _ _ ] ] => rewrite Zgt_is_gt_bool
    | [ |- context[ Z.le _ _ ] ] => rewrite <- Z.leb_le
    | [ |- context[ Z.ge _ _ ] ] => rewrite <- geb_ge
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
    end.


Ltac bool2prop_true :=
  repeat
    match goal with
    | [ |- forall _ : ?t, _ ] => intro

    | [ |- context[ bv_ult _ _ = true ] ] => rewrite bv_ult_B2P
    | [ |- context[ bv_slt _ _ = true ] ] => rewrite bv_slt_B2P
    | [ |- context[ Z.ltb _ _ = true ] ] => rewrite Z.ltb_lt
    | [ |- context[ Z.gtb _ _ ] ] => rewrite <- Zgt_is_gt_bool
    | [ |- context[ Z.leb _ _ = true ] ] => rewrite Z.leb_le
    | [ |- context[ Z.geb _ _ ] ] => rewrite geb_ge
    | [ |- context[ Z.eqb _ _ = true ] ] => rewrite Z.eqb_eq

    | [ |- context[ eqb_of_compdec ?p _ _ = true ] ] => rewrite <- (@compdec_eq_eqb _ p)

    | [ |- context[ ?G0 || ?G1 = true ] ] =>
      rewrite <- (@reflect_iff (G0 = true \/ G1 = true) (orb G0 G1));
      [ | apply orP]

    | [ |- context[ implb ?G0 ?G1 = true ] ] =>
      rewrite <- (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1));
      [ | apply implyP]

    | [ |- context[?G0 && ?G1 = true ] ] =>
      rewrite <- (@reflect_iff (G0 = true /\ G1 = true) (andb G0 G1));
      [ | apply andP]

    | [ |- context[Bool.eqb ?G0 ?G1 = true ] ] =>
      rewrite <- (@reflect_iff (G0 = true <-> G1 = true) (Bool.eqb G0 G1));
      [ | apply iffP]

    | [ |- context[ negb ?G = true ] ] =>
      rewrite <- (@reflect_iff (~ G = true) (negb G));
      [ | apply negP]

    | [ |- context[ true = true ] ] => rewrite TrueB

    | [ |- context[ false = true ] ] => rewrite FalseB
    end.

Ltac bool2prop := unfold is_true; bool2prop_true.


Ltac prop2bool_hyp H :=
  let TH := type of H in
  let t := fresh "t" in epose (t := ?[t] : Type);
  let comp := fresh "comp" in epose (comp := ?[comp] : bool);
  let H' := fresh in
  assert (H':False -> TH);
  [ let HFalse := fresh "HFalse" in intro HFalse;
    repeat match goal with
           | [ |- forall _ : _, _ ] => intro
           | [ |- @eq ?A _ _ ] => instantiate (t := A); instantiate (comp := true)
           | _ => instantiate (t := nat); instantiate (comp := false)
           end;
    destruct HFalse
  | ];
  clear H';
  match (eval compute in comp) with
  | true =>
    let Hcompdec := fresh "Hcompdec" in
    assert (Hcompdec: CompDec t); subst t;
    [ auto with typeclass_instances | ]
  | false => clear t
  end;
  clear comp;
  [ .. |
    let Hbool := fresh "Hbool" in epose (Hbool := ?[Hbool] : Prop);
    assert (H':False -> TH);
    [ let HFalse := fresh "HFalse" in intro HFalse;
      let rec tac_rec :=
          match goal with
          | [ |- forall _ : _, _ ] =>
            let H := fresh in
            intro H; tac_rec; revert H
          | _ => prop2bool
          end in
      tac_rec;
      match goal with
      | [ |- ?g ] => only [Hbool]: refine g
      end;
      destruct HFalse
    | ];
    clear H';
    assert (H':Hbool); subst Hbool;
    [ bool2prop; apply H | ];
    clear H; assert (H:=H'); clear H'
  ].





Section Toto.
  Variable A : Type.

  Hypothesis toto : forall (l1 l2:list A), length (l1++l2) = length l1 + length l2.
  Hypothesis tutu : forall (z1 z2:Z), (z1 < z2)%Z.
  Hypothesis tata : forall (a:A), a = a.

  Goal True.
  Proof.
    prop2bool_hyp toto.
    prop2bool_hyp tutu.
    prop2bool_hyp tata.
  Abort.
End Toto.





Infix "--->" := implb (at level 60, right associativity) : bool_scope.
Infix "<--->" := Bool.eqb (at level 60, right associativity) : bool_scope.



(* See if it fails with 8.13 *)

Goal True.
  evar (t:Type).
  assert (H:True).
  - instantiate (t:=nat). exact I.
  - exact I.
Qed.

Goal True.
  evar (t:option Set).
  assert (H:True).
  - instantiate (t:=Some nat). exact I.
  - exact I.
Qed.

Goal True.
  evar (t:option Type).
  assert (H:True).
  - Fail instantiate (t:=Some nat). exact I.
  - exact I.
Abort.

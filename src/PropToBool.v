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
      | Prop =>
        match t with
        | forall _ : _, _ => intro
        | _ => fail
        end
      | _ => intro
      end

    | [ |- context[ bv_ultP _ _ ] ] => rewrite <- bv_ult_B2P
    | [ |- context[ bv_sltP _ _ ] ] => rewrite <- bv_slt_B2P
    | [ |- context[ Z.lt _ _ ] ] => rewrite <- Z.ltb_lt
    | [ |- context[ Z.gt _ _ ] ] => rewrite Zgt_is_gt_bool
    | [ |- context[ Z.le _ _ ] ] => rewrite <- Z.leb_le
    | [ |- context[ Z.ge _ _ ] ] => rewrite <- geb_ge
    | [ |- context[ Z.eq _ _ ] ] => rewrite <- Z.eqb_eq

    | [ |- context[ @Logic.eq ?t ?x ?y ] ] =>
      lazymatch t with
      | bitvector _ => rewrite <- bv_eq_reflect
      | farray _ _ => rewrite <- equal_iff_eq
      | Z => rewrite <- Z.eqb_eq
      | bool =>
        lazymatch y with
        | true => fail
        | _ => rewrite <- eqb_true_iff
        end
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
    | [ |- forall _ : ?t, _ ] =>
      lazymatch type of t with
      | Prop => fail
      | _ => intro
      end

    | [ |- context[ bv_ult _ _ = true ] ] => rewrite bv_ult_B2P
    | [ |- context[ bv_slt _ _ = true ] ] => rewrite bv_slt_B2P
    | [ |- context[ Z.ltb _ _ = true ] ] => rewrite Z.ltb_lt
    | [ |- context[ Z.gtb _ _ ] ] => rewrite <- Zgt_is_gt_bool
    | [ |- context[ Z.leb _ _ = true ] ] => rewrite Z.leb_le
    | [ |- context[ Z.geb _ _ ] ] => rewrite geb_ge
    | [ |- context[ Z.eqb _ _ = true ] ] => rewrite Z.eqb_eq

    |  [ |- context[ Bool.eqb _ _ = true ] ] => rewrite eqb_true_iff

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

  (* Add a CompDec hypothesis if needed *)
  let prop2bool_t := fresh "prop2bool_t" in epose (prop2bool_t := ?[prop2bool_t_evar] : Type);
  let prop2bool_comp := fresh "prop2bool_comp" in epose (prop2bool_comp := ?[prop2bool_comp_evar] : bool);
  let H' := fresh in
  assert (H':False -> TH);
  [ let HFalse := fresh "HFalse" in intro HFalse;
    repeat match goal with
           | [ |- forall _ : ?t, _ ] =>
             lazymatch type of t with
             | Prop => fail
             | _ => intro
             end
           | [ |- context[@Logic.eq ?A _ _] ] => instantiate (prop2bool_t_evar := A); instantiate (prop2bool_comp_evar := true)
           | _ => instantiate (prop2bool_t_evar := nat); instantiate (prop2bool_comp_evar := false)
           end;
    destruct HFalse
  | ];
  clear H';
  match (eval compute in prop2bool_comp) with
  | true =>
    let A := eval cbv in prop2bool_t in
    match goal with
    | [ _ : CompDec A |- _ ] => idtac
    | _ =>
      let Hcompdec := fresh "Hcompdec" in
      assert (Hcompdec: CompDec A);
      [ auto with typeclass_instances | ]
    end
  | false => idtac
  end;
  clear prop2bool_t; clear prop2bool_comp;

  (* Compute the bool version of the lemma *)
  [ .. |
    let prop2bool_Hbool := fresh "prop2bool_Hbool" in epose (prop2bool_Hbool := ?[prop2bool_Hbool_evar] : Prop);
    assert (H':False -> TH);
    [ let HFalse := fresh "HFalse" in intro HFalse;
      let rec tac_rec :=
          match goal with
          | [ |- forall _ : ?t, _ ] =>
            lazymatch type of t with
            | Prop => fail
            | _ =>
              let H := fresh in
              intro H; tac_rec; revert H
            end
          | _ => prop2bool
          end in
      tac_rec;
      match goal with
      | [ |- ?g ] => only [prop2bool_Hbool_evar]: refine g
      end;
      destruct HFalse
    | ];
    clear H';

    (* Assert and prove the bool version of the lemma *)
    assert (H':prop2bool_Hbool); subst prop2bool_Hbool;
    [ bool2prop; apply H | ];

    (* Replace the Prop version with the bool version *)
    try clear H; let H := fresh H in assert (H:=H'); clear H'
  ].

Ltac prop2bool_hyps Hs :=
  match Hs with
  | (?Hs, ?H) => try prop2bool_hyp H; [ .. | prop2bool_hyps Hs]
  | ?H => try prop2bool_hyp H
  end.



Section Test.
  Variable A : Type.

  Hypothesis basic : forall (l1 l2:list A), length (l1++l2) = (length l1 + length l2)%nat.
  Hypothesis no_eq : forall (z1 z2:Z), (z1 < z2)%Z.
  Hypothesis uninterpreted_type : forall (a:A), a = a.
  Hypothesis bool_eq : forall (b:bool), negb (negb b) = b.

  Goal True.
  Proof.
    prop2bool_hyp basic.
    prop2bool_hyp no_eq.
    prop2bool_hyp uninterpreted_type.
    admit.
    prop2bool_hyp bool_eq.
    prop2bool_hyp plus_n_O.
  Abort.

  Goal True.
  Proof.
    prop2bool_hyps (basic, plus_n_O, no_eq, uninterpreted_type, bool_eq, plus_O_n).
    admit.
  Abort.
End Test.

Section Group.

  Variable G : Type.
  Variable HG : CompDec G.
  Variable op : G -> G -> G.
  Variable inv : G -> G.
  Variable e : G.

  Hypothesis associative :
    forall a b c : G, op a (op b c) = op (op a b) c.
  Hypothesis identity :
    forall a : G, (op e a = a) /\ (op a e = a).
  Hypothesis inverse :
    forall a : G, (op a (inv a) = e) /\ (op (inv a) a = e).

  Variable e' : G.
  Hypothesis other_id : forall e' z, op e' z = z.

  Goal True.
  Proof.
    prop2bool_hyp associative.
    prop2bool_hyp identity.
    prop2bool_hyp inverse.
    prop2bool_hyp other_id.
    exact I.
  Qed.

  Goal True.
  Proof.
    prop2bool_hyps (associative, identity, inverse, other_id).
    exact I.
  Qed.

End Group.


Section MultipleCompDec.

  Variables A B : Type.
  Hypothesis multiple : forall (a1 a2:A) (b1 b2:B), a1 = a2 -> b1 = b2.

  Goal True.
  Proof.
    Fail prop2bool_hyp multiple.
  Abort.

End MultipleCompDec.


(* We can assume that we deal only with monomorphic hypotheses, since
   polymorphism will be removed before *)
Section Poly.
  Hypothesis basic : forall (A:Type) (l1 l2:list A),
    length (l1++l2) = (length l1 + length l2)%nat.
  Hypothesis uninterpreted_type : forall (A:Type) (a:A), a = a.

  Goal True.
  Proof.
    prop2bool_hyp basic.
    Fail prop2bool_hyp uninterpreted_type.
  Abort.

End Poly.





Infix "--->" := implb (at level 60, right associativity) : bool_scope.
Infix "<--->" := Bool.eqb (at level 60, right associativity) : bool_scope.



(* Does not fail since 8.10 *)

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

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Int63 numbers defines Z/(2^63)Z, and can hence be equipped
      with a ring structure and a ring tactic *)

Require Import Int63Lib Cyclic63 CyclicAxioms.

Local Open Scope int63_scope.

(** Detection of constants *)

Local Open Scope list_scope.

Ltac isInt63cst_lst l :=
 match l with
 | nil => constr:true
 | ?t::?l => match t with
               | D1 => isInt63cst_lst l
               | D0 => isInt63cst_lst l
               | _ => constr:false
             end
 | _ => constr:false
 end.

Ltac isInt63cst t :=
 match t with
 | I63 ?i0 ?i1 ?i2 ?i3 ?i4 ?i5 ?i6 ?i7 ?i8 ?i9 ?i10
       ?i11 ?i12 ?i13 ?i14 ?i15 ?i16 ?i17 ?i18 ?i19 ?i20
       ?i21 ?i22 ?i23 ?i24 ?i25 ?i26 ?i27 ?i28 ?i29 ?i30
       ?i31 ?i32 ?i33 ?i34 ?i35 ?i36 ?i37 ?i38 ?i39 ?i40
       ?i41 ?i42 ?i43 ?i44 ?i45 ?i46 ?i47 ?i48 ?i49 ?i50
       ?i51 ?i52 ?i53 ?i54 ?i55 ?i56 ?i57 ?i58 ?i59 ?i60
       ?i61 ?i62 =>
    let l :=
      constr:(i0::i1::i2::i3::i4::i5::i6::i7::i8::i9::i10
      ::i11::i12::i13::i14::i15::i16::i17::i18::i19::i20
      ::i21::i22::i23::i24::i25::i26::i27::i28::i29::i30
      ::i31::i32::i33::i34::i35::i36::i37::i38::i39::i40
      ::i41::i42::i43::i44::i45::i46::i47::i48::i49::i50
      ::i51::i52::i53::i54::i55::i56::i57::i58::i59::i60
      ::i61::i62::nil)
    in isInt63cst_lst l
 | Int63Lib.On => constr:true
 | Int63Lib.In => constr:true
 | Int63Lib.Tn => constr:true
 | Int63Lib.Twon => constr:true
 | _ => constr:false
 end.

Ltac Int63cst t :=
 match isInt63cst t with
 | true => constr:t
 | false => constr:NotConstant
 end.

(** The generic ring structure inferred from the Cyclic structure *)

Module Int63ring := CyclicRing Int63Cyclic.

(** Unlike in the generic [CyclicRing], we can use Leibniz here. *)

Lemma Int63_canonic : forall x y, phi x = phi y -> x = y.
Proof.
 intros x y EQ.
 now rewrite <- (phi_inv_phi x), <- (phi_inv_phi y), EQ.
Qed.

Lemma ring_theory_switch_eq :
 forall A (R R':A->A->Prop) zero one add mul sub opp,
  (forall x y : A, R x y -> R' x y) ->
  ring_theory zero one add mul sub opp R ->
  ring_theory zero one add mul sub opp R'.
Proof.
intros A R R' zero one add mul sub opp Impl Ring.
constructor; intros; apply Impl; apply Ring.
Qed.

Lemma Int63Ring : ring_theory 0 1 add63 mul63 sub63 opp63 Logic.eq.
Proof.
exact (ring_theory_switch_eq _ _ _ _ _ _ _ _ _ Int63_canonic Int63ring.CyclicRing).
Qed.

Lemma eqb63_eq : forall x y, eqb63 x y = true <-> x=y.
Proof.
unfold eqb63. intros x y.
rewrite Cyclic63.spec_compare. case Z.compare_spec.
intuition. apply Int63_canonic; auto.
intuition; subst; auto with zarith; try discriminate.
intuition; subst; auto with zarith; try discriminate.
Qed.

Lemma eqb63_correct : forall x y, eqb63 x y = true -> x=y.
Proof. now apply eqb63_eq. Qed.

Add Ring Int63Ring : Int63Ring
 (decidable eqb63_correct,
  constants [Int63cst]).

Section TestRing.
Let test : forall x y, 1 + x*y + x*x + 1 = 1*1 + 1 + y*x + 1*x*x.
intros. ring.
Qed.

Let test2 : forall x, (x - 1) + 1 = x.
intros. ring.
Qed.
End TestRing.


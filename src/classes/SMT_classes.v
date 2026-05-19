(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


From Stdlib Require Import Bool OrderedType.

(** This file defines a number of typeclasses which are useful to build the
    terms of SMT (in particular arrays indexed by instances of these
    classes). *)


(** Boolean equality to decidable equality *)
Definition eqb_to_eq_dec :
  forall T (eqb : T -> T -> bool) (eqb_spec : forall x y, eqb x y = true <-> x = y) (x y : T),
    { x = y } + { x <> y }.
  intros.
  case_eq (eqb x y); intro.
  left. apply eqb_spec; auto.
  right. red. intro. apply eqb_spec in H0. rewrite H in H0. now contradict H0.
  Defined.


(** Types with a Boolean equality that reflects Leibniz equality *)
Class EqbType T := {
 eqb : T -> T -> bool;
 eqb_spec : forall x y, eqb x y = true <-> x = y
}.


(** Types with a decidable equality *)
Class DecType T := {
 eq_dec : forall x y : T, { x = y } + { x <> y }
}.


(** Types equipped with Boolean equality are decidable *)
Section EqbToDecType.
  Generalizable Variable T.
  Context `{ET : EqbType T}.

  Instance EqbToDecType : DecType T.
  Proof.
    destruct ET as [eqb0 Heqb0]. split.
    apply (eqb_to_eq_dec _ eqb0); auto.
  Defined.
End EqbToDecType.


(** Basic properties on types with Boolean equality *)
Section EqbTypeProp.
  Generalizable Variable T.
  Context `{ET : EqbType T}.

  Lemma eqb_refl x : eqb x x = true.
  Proof. now rewrite eqb_spec. Qed.

  Lemma eqb_sym x y : eqb x y = true -> eqb y x = true.
  Proof. rewrite !eqb_spec. now intros ->. Qed.

  Lemma eqb_trans x y z : eqb x y = true -> eqb y z = true -> eqb x z = true.
  Proof. rewrite !eqb_spec. now intros ->. Qed.

  Lemma eqb_spec_false x y : eqb x y = false <-> x <> y.
  Proof.
    split.
    - intros H1 H2. subst y. rewrite eqb_refl in H1. inversion H1.
    - intro H. case_eq (eqb x y); auto. intro H1. elim H. now rewrite <- eqb_spec.
  Qed.

  Lemma reflect_eqb x y : reflect (x = y) (eqb x y).
  Proof.
    case_eq (eqb x y); intro H; constructor.
    - now rewrite eqb_spec in H.
    - now rewrite eqb_spec_false in H.
  Qed.

  Lemma eqb_sym2 x y : eqb x y = eqb y x.
  Proof.
    case_eq (eqb y x); intro H.
    - now apply eqb_sym.
    - rewrite eqb_spec_false in *. auto.
  Qed.
End EqbTypeProp.


(** Class of inhabited types *)
Class Inhabited T := {
  default_value : T
}.

(** * CompDec: EqbType with inhabitant *)

Class CompDec T := {
  ty := T;                      (* This is redundant for performance reasons *)
  Eqb :: EqbType ty;
  Inh :: Inhabited ty
}.


Global Instance eqbtype_of_compdec {t} `{c: CompDec t} : (EqbType t) :=
  let (_, eqb, _) := c in eqb.

Global Instance inh_of_compdec {t} `{c: CompDec t} : (Inhabited t) :=
  let (_, _, inh) := c in inh.


Definition type_compdec {ty:Type} (cd : CompDec ty) := ty.

Definition eqb_of_compdec {t} (c : CompDec t) : t -> t -> bool :=
  match eqbtype_of_compdec (t:=t) with
  | {| eqb := eqb |} => eqb
  end.


Lemma compdec_eq_eqb {T:Type} {c : CompDec T} : forall x y : T,
    x = y <-> eqb_of_compdec c x y = true.
Proof.
  intros x y. destruct c as [TY [E HE] O C I]. unfold eqb_of_compdec. simpl. now rewrite HE.
Qed.


Record typ_compdec : Type := Typ_compdec {
  te_carrier : Type;
  te_compdec : CompDec te_carrier
}.


Section CompDec_from.

  Variable T : Type.

  Variable eqb' : T -> T -> bool.
  Variable eqb'_spec : forall x y, eqb' x y = true <-> x = y.

  Variable d : T.

  Program Instance CompDec_from : (CompDec T) := {|
    Eqb := {| eqb := eqb'; eqb_spec := eqb'_spec |};
    Inh := {| default_value := d |}
  |}.

  Definition typ_compdec_from : typ_compdec :=
    Typ_compdec T CompDec_from.

End CompDec_from.


(* Register constants for OCaml access *)
Register typ_compdec as SMTCoq.classes.SMT_classes.typ_compdec.
Register Typ_compdec as SMTCoq.classes.SMT_classes.Typ_compdec.
Register te_carrier as SMTCoq.classes.SMT_classes.te_carrier.
Register te_compdec as SMTCoq.classes.SMT_classes.te_compdec.
Register eqb_of_compdec as SMTCoq.classes.SMT_classes.eqb_of_compdec.
Register CompDec as SMTCoq.classes.SMT_classes.CompDec.

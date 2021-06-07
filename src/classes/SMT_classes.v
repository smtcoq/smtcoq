(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool OrderedType.

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


(** Class of types with a partial order *)
Class OrdType T := {
  lt: T -> T -> Prop;
  lt_trans : forall x y z : T, lt x y -> lt y z -> lt x z;
  lt_not_eq : forall x y : T, lt x y -> x <> y
}.

#[export] Hint Resolve lt_not_eq lt_trans : typeclass_ordtype.


Global Instance StrictOrder_OrdType T `(OrdType T) :
  StrictOrder (lt : T -> T -> Prop).
Proof.
  split.
  unfold Irreflexive, Reflexive, complement.
  intros. apply lt_not_eq in H0; auto.
  unfold Transitive. intros x y z. apply lt_trans.
Qed.

(** Augment class of partial order with a compare function to obtain a total
    order *)
Class Comparable T {ot:OrdType T} := {
  compare : forall x y : T, Compare lt eq x y
}.


(* A Comparable type is also an EqbType *)
Section Comparable2EqbType.
  Generalizable Variable T.
  Context `{OTT : OrdType T}.
  Context `{CT : Comparable T}.

  Definition compare2eqb (x y:T) : bool :=
    match compare x y with
    | EQ _ => true
    | _ => false
    end.

  Lemma compare2eqb_spec x y : compare2eqb x y = true <-> x = y.
  Proof.
    unfold compare2eqb.
    case_eq (compare x y); simpl; intros e He; split; try discriminate;
      try (intros ->; elim (lt_not_eq _ _ e (eq_refl _))); auto.
  Qed.

  Instance Comparable2EqbType : EqbType T := Build_EqbType _ _ compare2eqb_spec.
End Comparable2EqbType.


(** Class of inhabited types *)
Class Inhabited T := {
  default_value : T
}.

(** * CompDec: Merging all previous classes *)

Class CompDec T := {
  ty := T;                      (* This is redundant for performance reasons *)
  Eqb :> EqbType ty;             (* This is redundant since implied by Comp, but it actually allows us to choose a specific equality function *)
  Ordered :> OrdType ty;
  Comp :> @Comparable ty Ordered;
  Inh :> Inhabited ty
}.


Instance eqbtype_of_compdec t `{c: CompDec t} : (EqbType t) :=
  let (_, eqb, _, _, _) := c in eqb.

Instance ord_of_compdec t `{c: CompDec t} : (OrdType t) :=
  let (_, _, ord, _, _) := c in ord.

Instance inh_of_compdec t `{c: CompDec t} : (Inhabited t) :=
  let (_, _, _, _, inh) := c in inh.

Instance comp_of_compdec t `{c: CompDec t} : @Comparable t (ord_of_compdec t).
  destruct c; trivial.
Defined.


Definition type_compdec {ty:Type} (cd : CompDec ty) := ty.

Definition eqb_of_compdec {t} (c : CompDec t) : t -> t -> bool :=
  match eqbtype_of_compdec t with
  | {| eqb := eqb |} => eqb
  end.


Lemma compdec_eq_eqb {T:Type} {c : CompDec T} : forall x y : T,
    x = y <-> eqb_of_compdec c x y = true.
Proof.
  intros x y. destruct c as [TY [E HE] O C I]. unfold eqb_of_compdec. simpl. now rewrite HE.
Qed.

#[export] Hint Resolve
     ord_of_compdec
     inh_of_compdec
     comp_of_compdec
     eqbtype_of_compdec : typeclass_instances.


Record typ_compdec : Type := Typ_compdec {
  te_carrier : Type;
  te_compdec : CompDec te_carrier
}.


Section CompDec_from.

  Variable T : Type.

  Variable eqb' : T -> T -> bool.
  Variable eqb'_spec : forall x y, eqb' x y = true <-> x = y.

  Variable lt' : T -> T -> Prop.
  Hypothesis lt'_trans : forall x y z : T, lt' x y -> lt' y z -> lt' x z.
  Hypothesis lt'_neq : forall x y : T, lt' x y -> x <> y.

  Variable compare': forall x y : T, Compare lt' eq x y.

  Variable d : T.

  Program Instance CompDec_from : (CompDec T) := {|
    Eqb := {| eqb := eqb'; eqb_spec := eqb'_spec |};
    Ordered := {| lt := lt'; lt_trans := lt'_trans |};
    Comp := {| compare := compare' |};
    Inh := {| default_value := d |}
  |}.

  Definition typ_compdec_from : typ_compdec :=
    Typ_compdec T CompDec_from.

End CompDec_from.

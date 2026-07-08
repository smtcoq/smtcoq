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


(** Types with a Boolean equality that reflects Leibniz equality *)
Class EqbType T := {
 eqb : T -> T -> bool;
 eqb_spec : forall x y, eqb x y = true <-> x = y
}.


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

Create HintDb typeclass_ordtype discriminated.
Hint Constants Transparent : typeclass_ordtype.
Hint Projections Opaque : typeclass_ordtype.
Hint Variables Opaque : typeclass_ordtype.
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
  Eqb :: EqbType ty;             (* This is redundant since implied by Comp, but it actually allows us to choose a specific equality function *)
  Ordered :: OrdType ty;
  Comp :: @Comparable ty Ordered;
  Inh :: Inhabited ty
}.


Global Instance eqbtype_of_compdec {t} `{c: CompDec t} : (EqbType t) :=
  let (_, eqb, _, _, _) := c in eqb.

Global Instance ord_of_compdec {t} `{c: CompDec t} : (OrdType t) :=
  let (_, _, ord, _, _) := c in ord.

Global Instance inh_of_compdec {t} `{c: CompDec t} : (Inhabited t) :=
  let (_, _, _, _, inh) := c in inh.

Global Instance comp_of_compdec {t} `{c: CompDec t} : @Comparable t (ord_of_compdec (t:=t)).
  destruct c; trivial.
Defined.


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


(* Register constants for OCaml access *)
Register typ_compdec as SMTCoq.utils.CompDec.typ_compdec.
Register Typ_compdec as SMTCoq.utils.CompDec.Typ_compdec.
Register te_carrier as SMTCoq.utils.CompDec.te_carrier.
Register te_compdec as SMTCoq.utils.CompDec.te_compdec.
Register eqb_of_compdec as SMTCoq.utils.CompDec.eqb_of_compdec.
Register CompDec as SMTCoq.utils.CompDec.CompDec.


(* Compatibility of CompDec with standard type constructions *)

Section list_EqbType.

  Generalizable Variable A.
  Context `{HA : EqbType A}.

 Fixpoint eqb_list (xs ys:list A) : bool :=
    match xs, ys with
    | nil, nil => true
    | x::xs, y::ys => eqb x y && eqb_list xs ys
    | _, _ => false
    end.

  Lemma eqb_list_spec xs : forall ys, eqb_list xs ys = true <-> xs = ys.
  Proof.
    induction xs as [ |x xs IHxs]; intros [ |y ys]; split; simpl; intro H; auto; try discriminate.
    - rewrite andb_true_iff in H. destruct H as [H1 H2].
      rewrite eqb_spec in H1; subst.
      now rewrite (IHxs ys) in H2; subst.
    - injection H. intros -> ->. rewrite andb_true_iff; split.
      + now rewrite eqb_spec.
      + now rewrite IHxs.
  Qed.

  Global Instance list_eqbtype : EqbType (list A) :=
    {| eqb := eqb_list;
       eqb_spec := eqb_list_spec |}.

End list_EqbType.


Section list.

  Generalizable Variable A.
  Context `{HA : CompDec A}.


  Fixpoint list_lt (xs ys : list A) : Prop :=
    match xs, ys with
    | nil, nil => False
    | nil, _::_ => True
    | _::_, nil => False
    | x::xs, y::ys => (lt x y) \/ (eqb x y = true /\ list_lt xs ys)
    end.


  Definition list_compare : forall (x y : list A), Compare list_lt Logic.eq x y.
  Proof.
    induction x as [ |x xs IHxs]; intros [ |y ys]; simpl.
    - now apply EQ.
    - now apply LT.
    - now apply GT.
    - case_eq (compare x y); intros l H.
      + apply LT. simpl. now left.
      + case_eq (IHxs ys); intros l1 H1.
        * apply LT. simpl. right. split; auto. now apply eqb_spec.
        * apply EQ. now rewrite l, l1.
        * apply GT. simpl. right. split; auto. now apply eqb_spec.
      + apply GT. simpl. now left.
  Defined.


  Lemma list_lt_trans : forall (x y z : list A),
      list_lt x y -> list_lt y z -> list_lt x z.
  Proof.
    induction x as [ |x xs IHxs]; intros [ |y ys] [ |z zs]; simpl; auto.
    - inversion 1.
    - intros [H1|[H1a H1b]] [H2|[H2a H2b]].
      + left; eapply lt_trans; eauto.
      + left. unfold is_true in H2a. rewrite eqb_spec in H2a. now subst z.
      + left. unfold is_true in H1a. rewrite eqb_spec in H1a. now subst y.
      + right. split.
        * unfold is_true in H1a. rewrite eqb_spec in H1a. now subst y.
        * eapply IHxs; eauto.
  Qed.


  Lemma list_lt_not_eq : forall (x y : list A), list_lt x y -> x <> y.
  Proof.
    induction x as [ |x xs IHxs]; intros [ |y ys]; simpl; auto.
    - discriminate.
    - intros [H1|[H1 H2]]; intros H; inversion H; subst.
      + now apply (lt_not_eq _ _ H1).
      + now apply (IHxs _ H2).
  Qed.


  Global Instance list_ord : OrdType (list A) :=
    Build_OrdType _ _ list_lt_trans list_lt_not_eq.


  Global Instance list_comp : Comparable (list A) := Build_Comparable _ _ list_compare.


  Global Instance list_inh : Inhabited (list A) := Build_Inhabited _ nil.


  Global Instance list_compdec : CompDec (list A) := {|
    Ordered := list_ord;
    Comp := list_comp;
    Inh := list_inh
  |}.

End list.


Section prod_EqbType.

  Generalizable Variables A B.
  Context `{HA : EqbType A} `{HB : EqbType B}.

  Definition eqb_prod (x y:A * B) : bool :=
    let (xa, xb) := x in
    let (ya, yb) := y in
    eqb xa ya && eqb xb yb.

  Lemma eqb_prod_spec : forall x y, eqb_prod x y = true <-> x = y.
  Proof.
    intros [xa xb] [ya yb]; simpl; split; rewrite andb_true_iff.
    - rewrite !eqb_spec. now intros [-> ->].
    - intro H. rewrite !eqb_spec. now inversion H.
  Qed.

  Global Instance prod_eqbtype : EqbType (prod A B) :=
    {| eqb := eqb_prod;
       eqb_spec := eqb_prod_spec |}.

End prod_EqbType.


Section prod_OrdType.

  Generalizable Variables A B.
  Context `{HA : OrdType A} `{HB : OrdType B}.


  Definition prod_lt (x y:A*B) : Prop :=
    let (a1, b1) := x in
    let (a2, b2) := y in
    (lt a1 a2) \/ ((a1 = a2) /\ (lt b1 b2)).


  Lemma prod_lt_trans : forall (x y z:A*B),
      prod_lt x y -> prod_lt y z -> prod_lt x z.
  Proof.
    intros [a1 b1] [a2 b2] [a3 b3]; simpl.
    intros [H1|[H1 H4]] [H2|[H2 H3]].
    - left. eapply lt_trans; eauto.
    - subst a3. now left.
    - subst a2. now left.
    - subst a2 a3. right. split; auto. eapply lt_trans; eauto.
  Qed.


  Lemma prod_lt_not_eq : forall (x y:A*B), prod_lt x y -> x <> y.
  Proof.
    intros [a1 b1] [a2 b2]; simpl.
    intros [H1|[_ H1]] H3; inversion H3 as [[H4 H5]]; clear H3; subst a2 b2;
      now apply (lt_not_eq _ _ H1).
  Qed.


  Global Instance prod_ord : OrdType (prod A B) :=
    Build_OrdType _ _ prod_lt_trans prod_lt_not_eq.

End prod_OrdType.


Section prod.

  Generalizable Variables A B.
  Context `{HA : CompDec A} `{HB : CompDec B}.


  Definition prod_compare : forall (x y:A*B), Compare lt Logic.eq x y.
  Proof.
    intros [a1 b1] [a2 b2].
    case_eq (compare a1 a2); intros l H.
    - apply LT. simpl. now left.
    - case_eq (compare b1 b2); intros l1 H1.
      + apply LT. simpl. now right.
      + apply EQ. now subst.
      + apply GT. simpl. now right.
    - apply GT. simpl. now left.
  Defined.


  Global Instance prod_comp : Comparable (prod A B) := Build_Comparable _ _ prod_compare.


  Global Instance prod_inh : Inhabited (prod A B) :=
    Build_Inhabited _ (default_value, default_value).


  Global Instance prod_compdec : CompDec (prod A B) := {|
    Ordered := prod_ord;
    Comp := prod_comp;
    Inh := prod_inh
  |}.

End prod.


Section option.

  Generalizable Variable A.
  Context `{HA : CompDec A}.


  Definition option_lt (x y : option A) : Prop :=
    match x, y with
    | Some a, Some b => lt a b
    | Some _, None => True
    | None, Some _ => False
    | None, None => False
    end.


  Lemma option_lt_trans : forall (x y z : option A),
      option_lt x y -> option_lt y z -> option_lt x z.
  Proof.
    intros [a| ] [b| ] [c| ]; simpl; auto.
    - apply lt_trans.
    - intros _ [].
  Qed.


  Lemma option_lt_not_eq : forall (x y : option A), option_lt x y -> x <> y.
  Proof.
    intros [a| ] [b| ]; simpl; auto.
    - intros H1 H2. inversion H2 as [H3]. revert H3. now apply lt_not_eq.
    - discriminate.
  Qed.


  Global Instance option_ord : OrdType (option A) :=
    Build_OrdType _ _ option_lt_trans option_lt_not_eq.


  Definition option_compare : forall (x y : option A), Compare option_lt Logic.eq x y.
  Proof.
    intros [a| ] [b| ]; simpl.
    - case_eq (compare a b); intros l H.
      + now apply LT.
      + apply EQ. now subst b.
      + now apply GT.
    - now apply LT.
    - now apply GT.
    - now apply EQ.
  Defined.

  Global Instance option_comp : Comparable (option A) := Build_Comparable _ _ option_compare.

  Global Instance option_eqbtype : EqbType (option A) := Comparable2EqbType.


  Global Instance option_inh : Inhabited (option A) := Build_Inhabited _ None.


  Global Instance option_compdec : CompDec (option A) := {|
    Ordered := option_ord;
    Comp := option_comp;
    Inh := option_inh
  |}.

End option.

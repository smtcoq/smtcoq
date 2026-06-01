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


(* Compatibility of CompDec with standard type constructions *)

Section list.

  Generalizable Variable A.
  Context `{HA : CompDec A}.


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

  Global Instance list_inh : Inhabited (list A) := Build_Inhabited _ nil.

  Global Instance list_compdec : CompDec (list A) := {|
    Eqb := list_eqbtype;
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


Section prod.

  Generalizable Variables A B.
  Context `{HA : CompDec A} `{HB : CompDec B}.

  Global Instance prod_inh : Inhabited (prod A B) :=
    Build_Inhabited _ (default_value, default_value).

  Global Instance prod_compdec : CompDec (prod A B) := {|
    Eqb := prod_eqbtype;
    Inh := prod_inh
  |}.

End prod.


Section option.

  Generalizable Variable A.
  Context `{HA : CompDec A}.

  Definition eqb_option (x y:option A) : bool :=
    match x, y with
    | Some a, Some b => eqb a b
    | None, None => true
    | _, _ => false
    end.

  Lemma eqb_option_spec : forall x y, eqb_option x y = true <-> x = y.
  Proof.
    intros [a| ] [b| ]; simpl; split; try discriminate; try reflexivity; rewrite eqb_spec.
    - now intros ->.
    - intro H; now inversion H.
  Qed.

  Global Instance option_eqbtype : EqbType (option A) :=
    {| eqb := eqb_option;
       eqb_spec := eqb_option_spec |}.

  Global Instance option_inh : Inhabited (option A) := Build_Inhabited _ None.

  Global Instance option_compdec : CompDec (option A) := {|
    Eqb := option_eqbtype;
    Inh := option_inh
  |}.

End option.

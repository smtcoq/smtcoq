(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*     Burak Ekici                                                        *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*     The University of Iowa                                             *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Bool OrderedType.

(** This file defines a number of typeclasses which are useful to builds the
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


(** Types with a Boolean equality that reflects in Leibniz equality *)
Class EqbType T := {
 eqb : T -> T -> bool;
 eqb_spec : forall x y, eqb x y = true <-> x = y
}.


(** Types with a decidable equality *)
Class DecType T := {
 eq_refl : forall x : T, x = x;
 eq_sym : forall x y : T, x = y -> y = x;
 eq_trans : forall x y z : T, x = y -> y = z -> x = z;
 eq_dec : forall x y : T, { x = y } + { x <> y }
}.


Hint Immediate eq_sym.
Hint Resolve eq_refl eq_trans.

(** Types equipped with Boolean equality are decidable *)
Instance EqbToDecType T `(EqbType T) : DecType T.
Proof.
  destruct H.
  split; auto.
  intros; subst; auto.
  apply (eqb_to_eq_dec _ eqb0); auto.
Defined.


(** Class of types with a partial order *)
Class OrdType T := {
  lt: T -> T -> Prop;
  lt_trans : forall x y z : T, lt x y -> lt y z -> lt x z;
  lt_not_eq : forall x y : T, lt x y -> ~ eq x y
  (* compare : forall x y : T, Compare lt eq x y *)
}.

Hint Resolve lt_not_eq lt_trans.


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


(** Class of inhabited types *)
Class Inhabited T := {
  default_value : T
}.

(** * CompDec: Merging all previous classes *)

Class CompDec T := {
  ty := T;
  Eqb :> EqbType ty;
  Decidable := EqbToDecType ty Eqb;
  Ordered :> OrdType ty;       
  Comp :> @Comparable ty Ordered;
  Inh :> Inhabited ty
}.


Instance ord_of_compdec t `{c: CompDec t} : (OrdType t) := 
  let (_, _, _, ord, _, _) := c in ord.

Instance inh_of_compdec t `{c: CompDec t} : (Inhabited t) := 
  let (_, _, _, _, _, inh) := c in inh.

Instance comp_of_compdec t `{c: CompDec t} : @Comparable t (ord_of_compdec t).
destruct c; trivial.
Defined.

Instance eqbtype_of_compdec t `{c: CompDec t} : EqbType t :=
  let (_, eqbtype, _, _, _, inh) := c in eqbtype.

Instance dec_of_compdec t `{c: CompDec t} : DecType t :=
  let (_, _, dec, _, _, inh) := c in dec.


Definition type_compdec {ty:Type} (cd : CompDec ty) := ty.

Definition eqb_of_compdec {t} (c : CompDec t) : t -> t -> bool :=
  match c with
  | {| ty := ty; Eqb := {| eqb := eqb |} |} => eqb
  end.

Definition eqP_t {t: Type} (p: CompDec t) (x y: t) := if (eqb_of_compdec p x y) then True else False.

Theorem lcompdec: forall (t: Type) (p: CompDec t) (x y: t),
 eqb_of_compdec p x y = true <-> eqP_t p x y.
Proof. intros. split. intros.
       unfold eqP_t. now rewrite H.
       intros. unfold eqP_t in H.
       case_eq (eqb_of_compdec p x y); intros.
       easy. rewrite H0 in H. now contradict H.
Qed.

Theorem leibniz_lcompdec: forall (t: Type) (p: CompDec t) (x y: t),
 eqP_t p x y <-> x = y.
Proof. intros. split. intros.
       unfold eqP_t in H. destruct p.
       destruct Eqb0. apply eqb_spec0. simpl in H.
       case_eq (eqb0 x y); intros. easy. now rewrite H0 in H.
       intros. unfold eqP_t. destruct p. destruct Eqb0. simpl.
       apply eqb_spec0 in H. now rewrite H.
Qed.

Hint Resolve
     ord_of_compdec
     inh_of_compdec
     comp_of_compdec
     eqbtype_of_compdec
     dec_of_compdec : typeclass_instances.


Record typ_compdec : Type := Typ_compdec {
  te_carrier : Type;
  te_compdec : CompDec te_carrier
}.

Section CompDec_from.

  Variable T : Type.
  Variable eqb' : T -> T -> bool.
  Variable lt' : T -> T -> Prop.
  Variable d : T.

  Hypothesis eqb_spec' : forall x y : T, eqb' x y = true <-> x = y.
  Hypothesis lt_trans': forall x y z : T, lt' x y -> lt' y z -> lt' x z.
  Hypothesis lt_neq': forall x y : T, lt' x y -> x <> y.
  
  Variable compare': forall x y : T, Compare lt' eq x y.
  
  Program Instance CompDec_from : (CompDec T) := {|
    Eqb := {| eqb := eqb' |};
    Ordered := {| lt := lt'; lt_trans := lt_trans' |};
    Comp := {| compare := compare' |};
    Inh := {| default_value := d |}
  |}.

  
  Definition typ_compdec_from : typ_compdec :=
    Typ_compdec T CompDec_from.
  
End CompDec_from.
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
 (* eq_refl : forall x : T, x = x; *)
 (* eq_sym : forall x y : T, x = y -> y = x; *)
 (* eq_trans : forall x y z : T, x = y -> y = z -> x = z; *)
 eq_dec : forall x y : T, { x = y } + { x <> y }
}.


(* Hint Immediate eq_sym. *)
(* Hint Resolve eq_refl eq_trans. *)

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


(** Class of types with a partial order *)
Class OrdType T := {
  lt: T -> T -> Prop;
  lt_trans : forall x y z : T, lt x y -> lt y z -> lt x z;
  lt_not_eq : forall x y : T, lt x y -> x <> y
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
  (* ty := T; *)
  (* Eqb :> EqbType T; *)
  (* Decidable := EqbToDecType ty Eqb; *)
  Ordered :> OrdType T;
  Comp :> @Comparable T Ordered;
  Inh :> Inhabited T
}.


Instance ord_of_compdec t `{c: CompDec t} : (OrdType t) := 
  let (ord, _, _) := c in ord.
  (* let (_, _, _, ord, _, _) := c in ord. *)

Instance inh_of_compdec t `{c: CompDec t} : (Inhabited t) :=
  let (_, _, inh) := c in inh.

Instance comp_of_compdec t `{c: CompDec t} : @Comparable t (ord_of_compdec t).
  destruct c; trivial.
Defined.

Instance eqbtype_of_compdec t `{c: CompDec t} : EqbType t := Comparable2EqbType.
  (* let (_, eqbtype, _, _, _, inh) := c in eqbtype. *)

(* Instance dec_of_compdec t `{c: CompDec t} : DecType t := *)
(*   let (_, _, dec, _, _, inh) := c in dec. *)


(* Definition type_compdec {ty:Type} (cd : CompDec ty) := ty. *)

Definition eqb_of_compdec {t} (c : CompDec t) : t -> t -> bool :=
  match eqbtype_of_compdec t with
  | {| eqb := eqb |} => eqb
  end.


Lemma compdec_eq_eqb {T:Type} {c : CompDec T} : forall x y : T,
    x = y <-> eqb_of_compdec c x y = true.
Proof.
  intros x y. unfold eqb_of_compdec, eqbtype_of_compdec, Comparable2EqbType.
  now rewrite compare2eqb_spec.
Qed.

Hint Resolve
     ord_of_compdec
     inh_of_compdec
     comp_of_compdec
     eqbtype_of_compdec
     (* dec_of_compdec *) : typeclass_instances.


Record typ_compdec : Type := Typ_compdec {
  te_carrier : Type;
  te_compdec : CompDec te_carrier
}.

(* Section CompDec_from. *)

(*   Variable T : Type. *)
(*   Variable eqb' : T -> T -> bool. *)
(*   Variable lt' : T -> T -> Prop. *)
(*   (* Variable d : T. *) *)

(*   Hypothesis eqb_spec' : forall x y : T, eqb' x y = true <-> x = y. *)
(*   Hypothesis lt_trans': forall x y z : T, lt' x y -> lt' y z -> lt' x z. *)
(*   Hypothesis lt_neq': forall x y : T, lt' x y -> x <> y. *)
  
(*   Variable compare': forall x y : T, Compare lt' eq x y. *)
  
(*   Program Instance CompDec_from : (CompDec T) := {| *)
(*     Eqb := {| eqb := eqb' |}; *)
(*     Ordered := {| lt := lt'; lt_trans := lt_trans' |}; *)
(*     Comp := {| compare := compare' |} *)
(*     (* Inh := {| default_value := d |} *) *)
(*   |}. *)

  
(*   Definition typ_compdec_from : typ_compdec := *)
(*     Typ_compdec T CompDec_from. *)
  
(* End CompDec_from. *)

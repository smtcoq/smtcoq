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


From Stdlib Require Import Bool OrderedType BinPos ZArith OrderedTypeEx.
From Stdlib Require Import Uint63.
Require Import State BVList FArray.
Require Export SMT_classes.


Section Unit.
  Let eqb : unit -> unit -> bool := fun _ _ => true.

  Global Instance unit_eqbtype : EqbType unit.
  Proof.
    exists eqb. intros. destruct x, y. unfold eqb. split; trivial.
  Defined.

  Global Instance unit_inh : Inhabited unit := {| default_value := tt |}.

  Global Instance unit_compdec : CompDec unit := {|
    Eqb := unit_eqbtype;
    Inh := unit_inh
  |}.

  Definition unit_typ_compdec := Typ_compdec unit unit_compdec.

End Unit.


Section Bool.

  Global Instance bool_eqbtype : EqbType bool :=
    {| eqb := Bool.eqb; eqb_spec := eqb_true_iff |}.

  Global Instance bool_inh : Inhabited bool := {| default_value := false|}.

  Global Instance bool_compdec : CompDec bool := {|
    Eqb := bool_eqbtype;
    Inh := bool_inh
  |}.

End Bool.


Section Z.

  Global Instance Z_eqbtype : EqbType Z :=
    {| eqb := Z.eqb; eqb_spec := Z.eqb_eq |}.

  Global Instance Z_inh : Inhabited Z := {| default_value := 0%Z |}.

  Global Instance Z_compdec : CompDec Z := {|
    Eqb := Z_eqbtype;
    Inh := Z_inh
  |}.

  (** lt and eq predicates in Prop and their equivalences with the ones in bool *)
  Definition eqP_Z x y := if Z.eqb x y then True else False.

  Lemma eq_Z_B2P: forall x y, Z.eqb x y = true <-> eqP_Z x y.
  Proof. intros x y; split; intro H.
         unfold eqP_Z; now rewrite H.
         unfold eqP_Z in H.
         case_eq ((x =? y)%Z ); intros; try now subst.
         rewrite H0 in H. now contradict H.
  Qed.

  Lemma leibniz_eq_Z_B2P: forall x y, eqP_Z x y <-> Logic.eq x y.
  Proof. intros x y; split; intro H.
         unfold eqP_Z in H. case_eq ((x =? y)%Z); intros.
         now apply Z.eqb_eq in H0. rewrite H0 in H. now contradict H.
         rewrite H. unfold eqP_Z. now rewrite Z.eqb_refl.
  Qed.

End Z.


Section Nat.

  Global Instance Nat_eqbtype : EqbType nat :=
    {| eqb := Nat.eqb; eqb_spec := Nat.eqb_eq |}.

  Global Instance Nat_inh : Inhabited nat := {| default_value := O%nat |}.

  Global Instance Nat_compdec : CompDec nat := {|
    Eqb := Nat_eqbtype;
    Inh := Nat_inh
  |}.

End Nat.


Section Positive.

  Global Instance Positive_eqbtype : EqbType positive :=
    {| eqb := Pos.eqb; eqb_spec := Pos.eqb_eq |}.

  Global Instance Positive_inh : Inhabited positive := {| default_value := 1%positive |}.

  Global Instance Positive_compdec : CompDec positive := {|
    Eqb := Positive_eqbtype;
    Inh := Positive_inh
  |}.

End Positive.


Section N.

  Global Instance N_eqbtype : EqbType N :=
    {| eqb := N.eqb; eqb_spec := N.eqb_eq |}.

  Global Instance N_inh : Inhabited N := {| default_value := 0%N |}.

  Global Instance N_compdec : CompDec N := {|
    Eqb := N_eqbtype;
    Inh := N_inh
  |}.

End N.


Section BV.

  Import BITVECTOR_LIST.

  Global Instance BV_eqbtype n : EqbType (bitvector n) :=
    {| eqb := @bv_eq n;
       eqb_spec := @bv_eq_reflect n |}.

  Global Instance BV_inh n : Inhabited (bitvector n) :=
    {| default_value := zeros n |}.

  Global Instance BV_compdec n: CompDec (bitvector n) := {|
    Eqb := BV_eqbtype n;
    Inh := BV_inh n
  |}.

End BV.


Section Uint63.

  Local Open Scope uint63_scope.

  Global Instance int63_eqbtype : EqbType int :=
    {| eqb := Uint63.eqb; eqb_spec := Uint63.eqb_spec |}.

  Global Instance int63_inh : Inhabited int := {| default_value := 0 |}.

  Global Instance int63_compdec : CompDec int := {|
    Eqb := int63_eqbtype;
    Inh := int63_inh
  |}.

End Uint63.


From Stdlib Require Import ProofIrrelevance. (* TODO: remove *)

Section FArray.

  Generalizable Variables key elt.
  Context `{Hk : CompDec key}.
  Context `{He : CompDec elt}.

  (* Since EqbType requires a decidable equality that reflects Leibniz
     equality, we define one for the moment - this is of course weaker
     than using [equal].

     TODO: Modify EqbType such that it requires a decidable equivalence
     relation *)

  Definition eqb_farray (a1 a2:farray key elt) : bool :=
    let (l1, _, _) := a1 in
    let (l2, _, _) := a2 in
    eqb_list l1 l2.

  Lemma eqb_farray_spec : forall a1 a2, eqb_farray a1 a2 = true <-> a1 = a2.
  Proof.
    intros [athis aNoDup anodefault] [bthis bNoDup bnodefault]; simpl.
    rewrite eqb_list_spec. split.
    - intros ->. rewrite (proof_irrelevance _ aNoDup bNoDup).
      now rewrite (proof_irrelevance _ anodefault bnodefault).
    - intro H; now inversion H.
  Qed.

  Global Instance FArray_eqbtype : EqbType (farray key elt) :=
    {| eqb := eqb_farray;
       eqb_spec := eqb_farray_spec |}.

  Global Instance FArray_inh : Inhabited (farray key elt) :=
    {| default_value := @FArray.empty key elt _ |}.


  Global Instance FArray_compdec : CompDec (farray key elt) :=
    {|
      Eqb := FArray_eqbtype;
      Inh := FArray_inh
    |}.

End FArray.


(* Register constants for OCaml access *)
Register unit_typ_compdec as SMTCoq.classes.SMT_classes_instances.unit_typ_compdec.
Register bool_compdec as SMTCoq.classes.SMT_classes_instances.bool_compdec.
Register Z_compdec as SMTCoq.classes.SMT_classes_instances.Z_compdec.
Register Positive_compdec as SMTCoq.classes.SMT_classes_instances.Positive_compdec.
Register N_compdec as SMTCoq.classes.SMT_classes_instances.N_compdec.
Register BV_compdec as SMTCoq.classes.SMT_classes_instances.BV_compdec.
Register FArray_compdec as SMTCoq.classes.SMT_classes_instances.FArray_compdec.

Register eqb_farray as SMTCoq.array.FArray.eqb_farray.

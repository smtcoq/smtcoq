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


Require Import Bool OrderedType BinPos ZArith.
Require Import Int63.
Require Import State BVList.
Require Structures.
Require Export SMT_classes.


Section Unit.

  Let eqb : unit -> unit -> bool := fun _ _ => true.

  Let lt : unit -> unit -> Prop := fun _ _ => False.
  
  Instance unit_ord : OrdType unit.
  Proof. exists lt; unfold lt; trivial.
    intros; contradict H; trivial.
  Defined.

  Instance unit_eqbtype : EqbType unit.
  Proof.
    exists eqb. intros. destruct x, y. unfold eqb. split; trivial.
  Defined.

  Instance unit_comp : @Comparable unit unit_ord.
  Proof.
    split. intros. destruct x, y.
    apply OrderedType.EQ; trivial.
  Defined.

  Instance unit_inh : Inhabited unit := {| default_value := tt |}.
  
  Instance unit_compdec : CompDec unit := {|
    Eqb := unit_eqbtype;
    Ordered := unit_ord;
    Comp := unit_comp;
    Inh := unit_inh
  |}.


  
  Definition unit_typ_compdec := Typ_compdec unit unit_compdec.


  Lemma eqb_eq_unit : forall x y, eqb x y <-> x = y.
  Proof. intros. split; case x; case y; unfold eqb; intros; now auto.
  Qed.
  
End Unit.


Section Bool.

  Definition ltb_bool x y := negb x && y.

  Definition lt_bool x y := ltb_bool x y = true.
  
  Instance bool_ord : OrdType bool.
  Proof.
    exists lt_bool.
    intros x y z.
    case x; case y; case z; intros; simpl; subst; auto. 
    intros x y.
    case x; case y; intros; simpl in H; easy. 
  Defined.

  Instance bool_eqbtype : EqbType bool :=
    {| eqb := Bool.eqb; eqb_spec := eqb_true_iff |}.
  
  Instance bool_dec : DecType bool :=
    EqbToDecType _ bool_eqbtype.

  Instance bool_comp: Comparable bool.
  Proof.
    constructor.
    intros x y.
    case_eq (ltb_bool x y).
    intros.
    apply OrderedType.LT.
    unfold lt, bool_ord, lt_bool. auto.
    case_eq (Bool.eqb x y).
    intros.
    apply OrderedType.EQ.
    apply Bool.eqb_prop. auto.
    intros.
    apply OrderedType.GT.
    unfold lt, bool_ord, lt_bool. auto.
    case x in *; case y in *; auto.
  Defined.

  Instance bool_inh : Inhabited bool := {| default_value := false|}.

  Instance bool_compdec : CompDec bool := {|
    Eqb := bool_eqbtype;                                    
    Ordered := bool_ord;                                    
    Comp := bool_comp;
    Inh := bool_inh
  |}.


  Lemma ltb_bool_iff_lt: forall x y, ltb_bool x y = true <-> lt_bool x y.
  Proof. intros x y; split; intro H;
         case_eq x; case_eq y; intros; subst; compute in *; easy.
  Qed.

End Bool.


Section Z.

  Require Import OrderedTypeEx.

  Instance Z_ord : OrdType Z.
  Proof.
    exists Z_as_OT.lt.
    exact Z_as_OT.lt_trans.
    exact Z_as_OT.lt_not_eq.
  Defined.

  Instance Z_eqbtype : EqbType Z :=
    {| eqb := Z.eqb; eqb_spec := Z.eqb_eq |}.

  (* Instance Z_eqbtype : EqbType Z := *)
  (*   {| eqb := Zeq_bool; eqb_spec := fun x y => symmetry (Zeq_is_eq_bool x y) |}. *)
  
  Instance Z_dec : DecType Z :=
    EqbToDecType _ Z_eqbtype.

  
  Instance Z_comp: Comparable Z.
  Proof.
    constructor.
    apply Z_as_OT.compare.
  Defined.


  Instance Z_inh : Inhabited Z := {| default_value := 0%Z |}.

    
  Instance Z_compdec : CompDec Z := {|
    Eqb := Z_eqbtype;                                    
    Ordered := Z_ord;                                    
    Comp := Z_comp;
    Inh := Z_inh
  |}.

  (** lt and eq predicates in Prop and their equivalences with the ones in bool *)
  Definition eqP_Z x y := if Z.eqb x y then True else False.
  Definition ltP_Z x y := if Z.ltb x y then True else False.
  Definition leP_Z x y := if Z.leb x y then True else False.
  Definition gtP_Z x y := if Z.gtb x y then True else False.
  Definition geP_Z x y := if Z.geb x y then True else False.

  Lemma eq_Z_B2P: forall x y, Z.eqb x y = true <-> eqP_Z x y.
  Proof. intros x y; split; intro H.
         unfold eqP_Z; now rewrite H.
         unfold eqP_Z in H.
         case_eq ((x =? y)%Z ); intros; try now subst.
         rewrite H0 in H. now contradict H.
  Qed.

  Lemma lt_Z_B2P: forall x y, Z.ltb x y = true <-> ltP_Z x y.
  Proof. intros x y; split; intro H.
         unfold ltP_Z; now rewrite H.
         unfold ltP_Z in H.
         case_eq ((x <? y)%Z ); intros; try now subst.
         rewrite H0 in H. now contradict H.
  Qed.

  Lemma le_Z_B2P: forall x y, Z.leb x y = true <-> leP_Z x y.
  Proof. intros x y; split; intro H.
         unfold leP_Z; now rewrite H.
         unfold leP_Z in H.
         case_eq ((x <=? y)%Z ); intros; try now subst.
         rewrite H0 in H. now contradict H.
  Qed.

  Lemma gt_Z_B2P: forall x y, Z.gtb x y = true <-> gtP_Z x y.
  Proof. intros x y; split; intro H.
         unfold gtP_Z; now rewrite H.
         unfold gtP_Z in H.
         case_eq ((x >? y)%Z ); intros; try now subst.
         rewrite H0 in H. now contradict H.
  Qed.

  Lemma ge_Z_B2P: forall x y, Z.geb x y = true <-> geP_Z x y.
  Proof. intros x y; split; intro H.
         unfold geP_Z; now rewrite H.
         unfold geP_Z in H.
         case_eq ((x >=? y)%Z ); intros; try now subst.
         rewrite H0 in H. now contradict H.
  Qed.

  Lemma lt_Z_B2P': forall x y, ltP_Z x y <-> Z.lt x y.
  Proof. intros x y; split; intro H.
         unfold ltP_Z in H. 
         case_eq ((x <? y)%Z ); intros; rewrite H0 in H; try easy.
         now apply Z.ltb_lt in H0.
         apply lt_Z_B2P.
         now apply Z.ltb_lt.
  Qed.

  Lemma le_Z_B2P': forall x y, leP_Z x y <-> Z.le x y.
  Proof. intros x y; split; intro H.
         unfold leP_Z in H. 
         case_eq ((x <=? y)%Z ); intros; rewrite H0 in H; try easy.
         now apply Z.leb_le in H0.
         apply le_Z_B2P.
         now apply Z.leb_le.
  Qed.

  Lemma gt_Z_B2P': forall x y, gtP_Z x y <-> Z.gt x y.
  Proof. intros x y; split; intro H.
         unfold gtP_Z in H. 
         case_eq ((x >? y)%Z ); intros; rewrite H0 in H; try easy.
         now apply Zgt_is_gt_bool in H0.
         apply gt_Z_B2P.
         now apply Zgt_is_gt_bool.
  Qed.

  Lemma ge_Z_B2P': forall x y, geP_Z x y <-> Z.ge x y.
  Proof. intros x y; split; intro H.
         unfold geP_Z in H. 
         case_eq ((x >=? y)%Z ); intros; rewrite H0 in H; try easy.
         rewrite Z.geb_leb in H0. rewrite le_Z_B2P in H0.
         apply le_Z_B2P' in H0. now apply Z.ge_le_iff.
         apply ge_Z_B2P.
         rewrite Z.geb_leb. rewrite le_Z_B2P.
         apply le_Z_B2P'. now apply Z.ge_le_iff.
  Qed.

  Lemma leibniz_eq_Z_B2P: forall x y, eqP_Z x y <-> Logic.eq x y.
  Proof. intros x y; split; intro H.
         unfold eqP_Z in H. case_eq ((x =? y)%Z); intros.
         now apply Z.eqb_eq in H0. rewrite H0 in H. now contradict H.
         rewrite H. unfold eqP_Z. now rewrite Z.eqb_refl.
  Qed.

End Z.


Section Nat.

  Require Import OrderedTypeEx.

  Instance Nat_ord : OrdType nat.
  Proof.
    
    exists Nat_as_OT.lt.
    exact Nat_as_OT.lt_trans.
    exact Nat_as_OT.lt_not_eq.
  Defined.

  Instance Nat_eqbtype : EqbType nat :=
    {| eqb := Structures.nat_eqb; eqb_spec := Structures.nat_eqb_eq |}.
  
  Instance Nat_dec : DecType nat :=
    EqbToDecType _ Nat_eqbtype.

  
  Instance Nat_comp: Comparable nat.
  Proof.
    constructor.
    apply Nat_as_OT.compare.
  Defined.


  Instance Nat_inh : Inhabited nat := {| default_value := O%nat |}.

    
  Instance Nat_compdec : CompDec nat := {|
    Eqb := Nat_eqbtype;                                    
    Ordered := Nat_ord;                                    
    Comp := Nat_comp;
    Inh := Nat_inh
  |}.

End Nat.


Section Positive.

  
  Require Import OrderedTypeEx.

  Instance Positive_ord : OrdType positive.
  Proof.
    exists Positive_as_OT.lt.
    exact Positive_as_OT.lt_trans.
    exact Positive_as_OT.lt_not_eq.
  Defined.

  Instance Positive_eqbtype : EqbType positive :=
    {| eqb := Pos.eqb; eqb_spec := Pos.eqb_eq |}.
  
  Instance Positive_dec : DecType positive :=
    EqbToDecType _ Positive_eqbtype.

  Instance Positive_comp: Comparable positive.
  Proof.
    constructor.
    apply Positive_as_OT.compare.
  Defined.

  Instance Positive_inh : Inhabited positive := {| default_value := 1%positive |}.

  Instance Positive_compdec : CompDec positive := {|
    Eqb := Positive_eqbtype;                                    
    Ordered := Positive_ord;                                    
    Comp := Positive_comp;
    Inh := Positive_inh
  |}.


End Positive.


Section BV.

  Import BITVECTOR_LIST.

  
  Instance BV_ord n : OrdType (bitvector n).
  Proof.
    exists (fun a b => (bv_ult a b)).
    unfold bv_ult, RAWBITVECTOR_LIST.bv_ult.
    intros x y z; destruct x, y, z.
    simpl. rewrite wf0, wf1, wf2. rewrite N.eqb_refl. simpl.
    apply RAWBITVECTOR_LIST.ult_list_trans.
    intros x y; destruct x, y.
    simpl.
    intros. unfold not.
    intros. rewrite H0 in H.
    unfold bv_ult, bv in *.
    unfold RAWBITVECTOR_LIST.bv_ult, RAWBITVECTOR_LIST.size in H.
    rewrite N.eqb_refl in H.
    apply RAWBITVECTOR_LIST.ult_list_not_eq in H.
    apply H. easy.
  Defined.

  Instance BV_eqbtype n : EqbType (bitvector n) :=
    {| eqb := @bv_eq n;
       eqb_spec := @bv_eq_reflect n |}.

  Instance BV_dec n : DecType (bitvector n) :=
    EqbToDecType _ (BV_eqbtype n).

  
  Instance BV_comp n: Comparable (bitvector n).
  Proof.
    constructor.
    intros x y.
    case_eq (bv_ult x y).
    intros.
    apply OrderedType.LT.
    unfold lt, BV_ord. auto.
    case_eq (bv_eq x y).
    intros.
    apply OrderedType.EQ.
    apply bv_eq_reflect. auto.
    intros.
    apply OrderedType.GT.
    unfold lt, BV_ord. auto.
    destruct (BV_ord n).
    unfold bv_ult.
    unfold bv_eq, RAWBITVECTOR_LIST.bv_eq,
    RAWBITVECTOR_LIST.bits in H.
    unfold bv_ult, RAWBITVECTOR_LIST.bv_ult in H0.
    unfold is_true.

    unfold RAWBITVECTOR_LIST.bv_ult, RAWBITVECTOR_LIST.size.
    destruct x, y. simpl in *.
    unfold RAWBITVECTOR_LIST.size in *.
    rewrite wf0, wf1 in *.
    rewrite N.eqb_refl in *.

    apply RAWBITVECTOR_LIST.nlt_be_neq_gt.
    rewrite !List.rev_length.
    apply (f_equal (N.to_nat)) in wf0.
    apply (f_equal (N.to_nat)) in wf1.
    rewrite Nnat.Nat2N.id in wf0, wf1.
    now rewrite wf0, wf1.
    unfold RAWBITVECTOR_LIST.ult_list in H0. easy.
    now apply RAWBITVECTOR_LIST.rev_neq in H.
  Defined.

  Instance BV_inh n : Inhabited (bitvector n) :=
    {| default_value := zeros n |}.


  Instance BV_compdec n: CompDec (bitvector n) := {|
    Eqb := BV_eqbtype n;                                    
    Ordered := BV_ord n;                                    
    Comp := BV_comp n;
    Inh := BV_inh n
  |}.

End BV.



Section FArray.

  Require Import FArray.
  
  Instance FArray_ord key elt
           `{key_ord: OrdType key}
           `{elt_ord: OrdType elt}
           `{elt_dec: DecType elt}
           `{elt_inh: Inhabited elt}
           `{key_comp: @Comparable key key_ord} : OrdType (farray key elt).
  Proof.
    exists (@lt_farray key elt key_ord key_comp elt_ord elt_inh).
    apply lt_farray_trans.
    unfold not.
    intros.
    apply lt_farray_not_eq in H.
    apply H.
    rewrite H0.
    apply eqfarray_refl. auto.
  Defined.

  Instance FArray_eqbtype key elt
           `{key_ord: OrdType key}
           `{elt_ord: OrdType elt}
           `{elt_eqbtype: EqbType elt}
           `{key_comp: @Comparable key key_ord}
           `{elt_comp: @Comparable elt elt_ord}
           `{elt_inh: Inhabited elt}
    : EqbType (farray key elt).
  Proof.
    exists FArray.equal.
    intros.
    split.
    apply FArray.equal_eq.
    intros. subst. apply eq_equal. apply eqfarray_refl.
    apply EqbToDecType. auto.
  Defined.

  
  Instance FArray_dec key elt
           `{key_ord: OrdType key}
           `{elt_ord: OrdType elt}
           `{elt_eqbtype: EqbType elt}
           `{key_comp: @Comparable key key_ord}
           `{elt_comp: @Comparable elt elt_ord}
           `{elt_inh: Inhabited elt}
    : DecType (farray key elt) :=
    EqbToDecType _ (FArray_eqbtype key elt).

  
  Instance FArray_comp key elt
           `{key_ord: OrdType key}
           `{elt_ord: OrdType elt}
           `{elt_eqbtype: EqbType elt}
           `{key_comp: @Comparable key key_ord}
           `{elt_inh: Inhabited elt}
           `{elt_comp: @Comparable elt elt_ord} : Comparable (farray key elt).
  Proof.
    constructor.
    intros.
    destruct (compare_farray key_comp (EqbToDecType _ elt_eqbtype) elt_comp x y).
    - apply OrderedType.LT. auto.
    - apply OrderedType.EQ.
      specialize (@eq_equal key elt key_ord key_comp elt_ord elt_comp elt_inh x y).
      intros.
      apply H in e.
      now apply equal_eq in e.
    - apply OrderedType.GT. auto.
  Defined.

  Instance FArray_inh key elt
           `{key_ord: OrdType key}
           `{elt_inh: Inhabited elt} : Inhabited (farray key elt) :=
    {| default_value := FArray.empty key_ord elt_inh |}.


  Program Instance FArray_compdec key elt
          `{key_compdec: CompDec key}
          `{elt_compdec: CompDec elt} :
    CompDec (farray key elt) :=
    {|
      Eqb := FArray_eqbtype key elt;
      Ordered := FArray_ord key elt;
      (*  Comp := FArray_comp key elt ; *)
      Inh := FArray_inh key elt
    |}.
  
  Next Obligation.
    constructor.
    destruct key_compdec, elt_compdec.
    simpl in *.
    unfold lt_farray.
    intros. simpl.
    unfold EqbToDecType. simpl.
    case_eq (compare x y); intros.
    apply OrderedType.LT.
    destruct (compare x y); try discriminate H; auto.
    apply OrderedType.EQ.
    destruct (compare x y); try discriminate H; auto.
    apply OrderedType.GT.
    destruct (compare y x); try discriminate H; auto; clear H.
  Defined.

End FArray.


Section Int63.
  
  Local Open Scope int63_scope.

  Let int_lt x y :=
    if Int63Native.ltb x y then True else False.
  
  Instance int63_ord : OrdType int.
  Proof.
    exists int_lt; unfold int_lt.
    - intros x y z. 
      case_eq (x < y); intro;
        case_eq (y < z); intro;
          case_eq (x < z); intro;
            simpl; try easy.
      contradict H1.
      rewrite not_false_iff_true.
      rewrite Int63Axioms.ltb_spec in *.
      exact (Z.lt_trans _ _ _ H H0).
    - intros x y.
      case_eq (x < y); intro; simpl; try easy.
      intros.
      rewrite Int63Axioms.ltb_spec in *.
      rewrite <- Int63Properties.to_Z_eq.
      exact (Z.lt_neq _ _ H).
  Defined.
  
  Instance int63_eqbtype : EqbType int :=
    {| eqb := Int63Native.eqb; eqb_spec := Int63Properties.eqb_spec |}.

  Instance int63_dec : DecType int :=
    EqbToDecType _ int63_eqbtype.


  Instance int63_comp: Comparable int.
  Proof.
    constructor.
    intros x y.
    case_eq (x < y); intro;
      case_eq (x == y); intro; unfold lt in *; simpl.
    - rewrite Int63Properties.eqb_spec in H0.
      contradict H0.
      assert (int_lt x y). unfold int_lt.
      rewrite H; trivial.
      remember lt_not_eq. unfold lt in *. simpl in n.
      exact (n _ _ H0).
    - apply LT. unfold int_lt. rewrite H; trivial.
    - apply EQ. rewrite Int63Properties.eqb_spec in H0; trivial.
    - apply GT. unfold int_lt.
      case_eq (y < x); intro; simpl; try easy.
      specialize (leb_ltb_eqb x y); intro.
      contradict H2.
      rewrite leb_negb_gtb. rewrite H1. simpl.
      red. intro. symmetry in H2.
      rewrite orb_true_iff in H2. destruct H2; contradict H2.
      rewrite H. auto.
      rewrite H0. auto.
  Defined.


  Instance int63_inh : Inhabited int := {| default_value := 0 |}.
    
  Instance int63_compdec : CompDec int := {|
    Eqb := int63_eqbtype;                                    
    Ordered := int63_ord;                                    
    Comp := int63_comp;
    Inh := int63_inh
  |}.
         

End Int63.


Hint Resolve unit_ord bool_ord Z_ord Positive_ord BV_ord FArray_ord : typeclass_instances.
Hint Resolve unit_eqbtype bool_eqbtype Z_eqbtype Positive_eqbtype BV_eqbtype FArray_eqbtype : typeclass_instances.
Hint Resolve bool_dec Z_dec Positive_dec BV_dec FArray_dec : typeclass_instances.
Hint Resolve unit_comp bool_comp Z_comp Positive_comp BV_comp FArray_comp : typeclass_instances.
Hint Resolve unit_inh bool_inh Z_inh Positive_inh BV_inh FArray_inh : typeclass_instances.
Hint Resolve unit_compdec bool_compdec Z_compdec Positive_compdec BV_compdec FArray_compdec : typeclass_instances.

Hint Resolve int63_ord int63_inh int63_eqbtype int63_dec int63_comp int63_compdec
  : typeclass_instances.

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

Require Import Bool Int63 State OrderedType BinPos ZArith BVList.
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
  
End Z.


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

  Let int63_lt x y :=
    if Int63Native.ltb x y == true then True else False.
  
  Instance int63_ord : OrdType int.
  Proof.
    exists int63_lt; unfold int63_lt.
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
      assert (int63_lt x y). unfold int63_lt. rewrite H; simpl; trivial.
      remember lt_not_eq. unfold lt in *. simpl in n.
      exact (n _ _ H0).
    - apply LT. unfold int63_lt. rewrite H; simpl; trivial.
    - apply EQ. rewrite Int63Properties.eqb_spec in H0; trivial.
    - apply GT. unfold int63_lt.
      case_eq (y < x); intro; simpl; try easy.
      (* contradict H1. *)
      (* rewrite not_false_iff_true. *)
      (* rewrite ltb_negb_geb. *)
      specialize (leb_ltb_eqb x y); intro.
      contradict H2.
      rewrite leb_negb_gtb. rewrite H1. simpl.
      red. intro. symmetry in H2.
      rewrite orb_true_iff in H2. destruct H2; contradict H2.
      rewrite H. auto.
      rewrite H0. auto.
  Defined.


  Instance int63_inh : Inhabited int := {| default_value := 0%int |}.
    
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


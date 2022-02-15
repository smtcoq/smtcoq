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


Require Import Bool OrderedType SMT_classes.
Require Import ProofIrrelevance.


(** This file formalizes functional arrays with extensionality as specified in
    SMT-LIB 2. It gives realization to axioms that define the SMT-LIB theory of
    arrays. For this, it uses a formalization of maps with the same approach as
    FMaplist excepted that constraints on keys and elements are expressed
    through the use of typeclasses instead of functors. *)

Set Implicit Arguments.

(** Raw maps (see FMaplist) *)
Module Raw.

  Section Array.

  Variable key : Type.
  Variable elt : Type.
  Variable key_dec : DecType key.
  Variable key_ord : OrdType key.
  Variable key_comp : Comparable key.
  Variable elt_dec : DecType elt.
  Variable elt_ord : OrdType elt.

  Definition eqb_key (x y : key) : bool := if eq_dec x y then true else false.
  Definition eqb_elt (x y : elt) : bool := if eq_dec x y then true else false.

  Lemma eqb_key_eq x y : eqb_key x y = true <-> x = y.
  Proof. unfold eqb_key. case (eq_dec x y); split; easy. Qed.

  Lemma eqb_elt_eq x y : eqb_elt x y = true <-> x = y.
  Proof. unfold eqb_elt. case (eq_dec x y); split; easy. Qed.

  Hint Immediate eqb_key_eq eqb_elt_eq : smtcoq_array.

  Definition farray := list (key * elt).

  Definition eqk (a b : (key * elt)) := fst a = fst b.
  Definition eqe (a b : (key * elt)) := snd a = snd b.
  Definition eqke (a b : (key * elt)) := fst a = fst b /\ snd a = snd b.

  Definition ltk (a b : (key * elt)) := lt (fst a) (fst b).

  Hint Unfold ltk eqk eqke : smtcoq_array.
  Hint Extern 2 (eqke ?a ?b) => split : smtcoq_array.

  Global Instance lt_key_strorder : StrictOrder (lt : key -> key -> Prop).
  Proof. apply StrictOrder_OrdType. Qed.

  Global Instance lt_elt_strorder : StrictOrder (lt : elt -> elt -> Prop).
  Proof. apply StrictOrder_OrdType. Qed.

  Global Instance ke_dec : DecType (key * elt).
  Proof.
    split; auto.
    intros; destruct x, y.
    destruct (eq_dec k k0).
    destruct (eq_dec e e0).
    left; rewrite e1, e2; auto.
    right; unfold not in *. intro; inversion H. exact (n H2).
    right; unfold not in *. intro; inversion H. exact (n H1).
  Qed.

  Global Instance ke_ord: OrdType (key * elt).
  Proof.
    exists ltk; unfold ltk; intros.
    apply (lt_trans _ (fst y)); auto.
    destruct x, y. simpl in H.
    unfold not. intro. inversion H0.
    apply (lt_not_eq k k0); auto.
  Defined.

  (* ltk ignore the second components *)

   Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
   Proof. auto. Qed.

   Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
   Proof. auto. Qed.
   Hint Immediate ltk_right_r ltk_right_l : smtcoq_array.

  Notation Sort := (sort ltk).
  Notation Inf := (lelistA (ltk)).

  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.

  Notation NoDupA := (NoDupA eqk).

  Hint Unfold MapsTo In : smtcoq_array.

   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
   Proof.
     unfold eqk, eqke; intuition.
   Qed.

  (* eqk, eqke are equalities *)

  Lemma eqk_refl : forall e, eqk e e.
  Proof. auto with smtcoq_array. Qed.

  Lemma eqke_refl : forall e, eqke e e.
  Proof. auto with smtcoq_array. Qed.

  Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
  Proof. auto with smtcoq_array. Qed.

  Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
  Proof. unfold eqke; intuition. Qed.

  Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
  Proof. unfold eqk; now intros e1 e2 e3 ->. Qed.

  Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
  Proof.
    unfold eqke; intros [k1 e1] [k2 e2] [k3 e3]; simpl; now intros [-> ->].
  Qed.

  Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
  Proof. unfold ltk; eauto with typeclass_ordtype. Qed.

  Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
  Proof. unfold ltk, eqk. intros. apply lt_not_eq; auto with smtcoq_array. Qed.

  Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
  Proof.
    unfold eqke, ltk; intuition; simpl in *; subst.
    apply lt_not_eq in H. auto with smtcoq_array.
  Qed.

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : smtcoq_array.
  Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke : smtcoq_array.
  Hint Immediate eqk_sym eqke_sym : smtcoq_array.

  Global Instance eqk_equiv : Equivalence eqk.
  Proof. split; eauto with smtcoq_array. Qed.

  Global Instance eqke_equiv : Equivalence eqke.
  Proof. split; eauto with smtcoq_array. Qed.

  Global Instance ltk_strorder : StrictOrder ltk.
  Proof.
    split.
    unfold Irreflexive, Reflexive, complement.
    intros. apply lt_not_eq in H; auto with smtcoq_array.
    unfold Transitive. intros x y z. apply lt_trans.
  Qed.

  Global Instance eq_equiv : @Equivalence (key * elt) eq.
  Proof.
    split; auto with smtcoq_array.
    unfold Transitive. apply eq_trans.
  Qed.

  Global Instance ltk_compat : Proper (eq ==> eq ==> iff) ltk.
  Proof.
    split; rewrite H, H0; trivial.
  Qed.

  Global Instance ltk_compatk : Proper (eqk==>eqk==>iff) ltk.
  Proof.
  intros (x,e) (x',e') Hxx' (y,f) (y',f') Hyy'; compute.
   compute in Hxx'; compute in Hyy'. rewrite Hxx', Hyy'; auto with smtcoq_array.
  Qed.

  Global Instance ltk_compat' : Proper (eqke==>eqke==>iff) ltk.
  Proof.
  intros (x,e) (x',e') (Hxx',_) (y,f) (y',f') (Hyy',_); compute.
   compute in Hxx'; compute in Hyy'. rewrite Hxx', Hyy'; auto with smtcoq_array.
  Qed.

  Global Instance ltk_asym : Asymmetric ltk.
  Proof. apply (StrictOrder_Asymmetric ltk_strorder). Qed.

  (* Additional facts *)

  Lemma eqk_not_ltk : forall x x', eqk x x' -> ~ltk x x'.
  Proof.
    unfold eqk, ltk.
    unfold not. intros x x' H.
    destruct x, x'. simpl in *.
    intro.
    symmetry in H.
    apply lt_not_eq in H. auto with smtcoq_array.
    subst. auto with smtcoq_array.
  Qed.

  Lemma ltk_eqk : forall e e' e'', ltk e e' -> eqk e' e'' -> ltk e e''.
  Proof. unfold ltk, eqk. destruct e, e', e''. simpl.
    intros; subst; trivial.
  Qed.

  Lemma eqk_ltk : forall e e' e'', eqk e e' -> ltk e' e'' -> ltk e e''.
  Proof.
    intros (k,e) (k',e') (k'',e'').
    unfold ltk, eqk; simpl; intros; subst; trivial.
  Qed.
  Hint Resolve eqk_not_ltk : smtcoq_array.
  Hint Immediate ltk_eqk eqk_ltk : smtcoq_array.
  
  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition.
  Qed.

  Hint Resolve InA_eqke_eqk : smtcoq_array.

  Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
  Proof.
  firstorder.
  exists x; auto with smtcoq_array.
  induction H.
  destruct y.
  exists e; auto with smtcoq_array.
  destruct IHInA as [e H0].
  exists e; auto with smtcoq_array.
  Qed.

  Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
  Proof.
  intros; unfold MapsTo in *; apply InA_eqA with (x,e); eauto with *.
  Qed.

  Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
  Proof.
  destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto with smtcoq_array.
  Qed.

  Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
  Proof. exact (InfA_eqA eqk_equiv ltk_compatk). Qed.

  Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
  Proof. exact (InfA_ltA ltk_strorder). Qed.

  Hint Immediate Inf_eq : smtcoq_array.
  Hint Resolve Inf_lt : smtcoq_array.

  Lemma Sort_Inf_In :
    forall l p q, Sort l -> Inf q l -> InA eqk p l -> ltk q p.
  Proof.
    exact (SortA_InfA_InA eqk_equiv ltk_strorder ltk_compatk).
  Qed.

  Lemma Sort_Inf_NotIn :
    forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
  Proof.
    intros; red; intros.
    destruct H1 as [e' H2].
    elim (@ltk_not_eqk (k,e) (k,e')).
    eapply Sort_Inf_In; eauto with smtcoq_array.
    red; simpl; auto with smtcoq_array.
  Qed.

  Hint Resolve Sort_Inf_NotIn : smtcoq_array.

  Lemma Sort_NoDupA: forall l, Sort l -> NoDupA l.
  Proof.
    exact (SortA_NoDupA eqk_equiv ltk_strorder ltk_compatk).
  Qed.

  Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
  Proof.
    inversion 1; intros; eapply Sort_Inf_In; eauto with smtcoq_array.
  Qed.

  Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
                                   ltk e e' \/ eqk e e'.
  Proof.
    inversion_clear 2; auto with smtcoq_array.
    left; apply Sort_In_cons_1 with l; auto with smtcoq_array.
  Qed.

  Lemma Sort_In_cons_3 :
    forall x l k e, Sort ((k,e)::l) -> In x l -> ~eq x k.
  Proof.
    inversion_clear 1; red; intros.
    destruct (Sort_Inf_NotIn H0 H1 (In_eq H2 H)).
  Qed.

  Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
  Proof.
    inversion 1.
    inversion_clear H0; eauto with smtcoq_array.
    destruct H1; simpl in *; intuition.
  Qed.

  Lemma In_inv_2 : forall k k' e e' l,
      InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
  Proof.
    inversion_clear 1; compute in H0; intuition.
  Qed.

  Lemma In_inv_3 : forall x x' l,
      InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
  Proof.
    inversion_clear 1; compute in H0; intuition.
  Qed.

  Hint Resolve In_inv_2 In_inv_3 : smtcoq_array.

  (** * FMAPLIST interface implementaion  *)

  (** * [empty] *)

  Definition empty : farray := nil.

  Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

  Lemma empty_1 : Empty empty.
  Proof.
    unfold Empty,empty.
    intros a e.
    intro abs.
    inversion abs.
  Qed.
  Hint Resolve empty_1 : smtcoq_array.

  Lemma empty_sorted : Sort empty.
  Proof.
    unfold empty; auto with smtcoq_array.
  Qed.

  Lemma MapsTo_inj : forall x e e' l (Hl:Sort l),
      MapsTo x e l -> MapsTo x e' l -> e = e'.
    induction l.
    - intros. apply empty_1 in H. contradiction.
    - intros.
      destruct a as (y, v).
      pose proof H as HH.
      pose proof H0 as HH0.
      unfold MapsTo in H.
      apply InA_eqke_eqk in H.
      apply InA_eqke_eqk in H0.
      apply (Sort_In_cons_2 Hl) in H.
      apply (Sort_In_cons_2 Hl) in H0.
      destruct H, H0.
      + apply ltk_not_eqk in H.
        apply ltk_not_eqk in H0.
        assert (~ eqk (x, e) (y, v)). unfold not in *. intros. apply H. now apply eqk_sym.
        assert (~ eqk (x, e') (y, v)). unfold not in *. intros. apply H. now apply eqk_sym.
        specialize (In_inv_3 HH0 H2).
        specialize (In_inv_3 HH H1).
        inversion_clear Hl.
        apply (IHl H3).
      + apply ltk_not_eqk in H.
        unfold eqk in H, H0; simpl in H, H0. contradiction.
      + apply ltk_not_eqk in H0.
        unfold eqk in H, H0; simpl in H, H0. contradiction.
      + unfold eqk in H, H0. simpl in *. subst.
        inversion_clear HH.
        inversion_clear HH0.
        unfold eqke in *. simpl in *. destruct H, H1; subst; auto with smtcoq_array.
        apply InA_eqke_eqk in H1.
        inversion_clear Hl.
        specialize (Sort_Inf_In H2 H3 H1).
        unfold ltk. simpl. intro. apply lt_not_eq in H4. contradiction.
        apply InA_eqke_eqk in H.
        inversion_clear Hl.
        specialize (Sort_Inf_In H1 H2 H).
        unfold ltk. simpl. intro. apply lt_not_eq in H3. contradiction.
  Qed.

  (** * [is_empty] *)

  Definition is_empty (l : farray) : bool := if l then true else false.

  Lemma is_empty_1 :forall m, Empty m -> is_empty m = true.
  Proof.
    unfold Empty, MapsTo.
    intros m.
    case m;auto with smtcoq_array.
    intros (k,e) l inlist.
    absurd (InA eqke (k, e) ((k, e) :: l));auto with smtcoq_array.
  Qed.

  Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
  Proof.
    intros m.
    case m;auto with smtcoq_array.
    intros p l abs.
    inversion abs.
  Qed.

  (** * [mem] *)

  Fixpoint mem (k : key) (s : farray) {struct s} : bool :=
    match s with
    | nil => false
    | (k',_) :: l =>
      match compare k k' with
      | LT _ => false
      | EQ _ => true
      | GT _ => mem k l
      end
    end.

  Lemma mem_1 : forall m (Hm:Sort m) x, In x m -> mem x m = true.
  Proof.
    intros m Hm x; generalize Hm; clear Hm.
    induction m as [ |[k' _x] l IHb]; intros sorted belong1.
    - inversion belong1. inversion H.
    - simpl. case_eq (compare x k'); trivial.
      + intros _x0 e0.
        absurd (In x ((k', _x) :: l));try assumption.
        apply Sort_Inf_NotIn with _x;auto with smtcoq_array.
      + intros _x0 e0.
        apply IHb.
        elim (sort_inv sorted);auto with smtcoq_array.
        elim (In_inv belong1);auto with smtcoq_array.
        intro abs.
        absurd (eq x k'); auto with smtcoq_array.
        symmetry in abs.
        apply lt_not_eq in abs; auto with smtcoq_array.
  Qed.

  Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m.
  Proof.
    intros m Hm x; generalize Hm; clear Hm; unfold In,MapsTo.
    induction m as [ |[k' _x] l IHb]; intros sorted hyp;try ((inversion hyp);fail).
    revert hyp. simpl. case_eq (compare x k'); intros _x0 e0 hyp;try ((inversion hyp);fail).
    - exists _x; auto with smtcoq_array.
    - induction IHb; auto with smtcoq_array.
      + exists x0; auto with smtcoq_array.
      + inversion_clear sorted; auto with smtcoq_array.
  Qed.

  Lemma mem_3 : forall m (Hm:Sort m) x, mem x m = false -> ~ In x m.
    intros.
    rewrite <- not_true_iff_false in H.
    unfold not in *. intros; apply H.
    now apply mem_1.
  Qed.

  (** * [find] *)

  Fixpoint find (k:key) (s: farray) {struct s} : option elt :=
    match s with
    | nil => None
    | (k',x)::s' =>
      match compare k k' with
      | LT _ => None
      | EQ _ => Some x
      | GT _ => find k s'
      end
    end.

  Lemma find_2 :  forall m x e, find x m = Some e -> MapsTo x e m.
  Proof.
    intros m x. unfold MapsTo.
    induction m as [ |[k' _x] l IHb];simpl; intro e';try now (intro eqfind; inversion eqfind; auto with smtcoq_array).
    case_eq (compare x k'); intros _x0 e0 eqfind; inversion eqfind; auto with smtcoq_array.
  Qed.

  Lemma find_1 :  forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e.
  Proof.
    intros m Hm x e; generalize Hm; clear Hm; unfold MapsTo.
    induction m as [ |[k' _x] l IHb];simpl; subst; try clear H_eq_1.
    - inversion 2.
    - case_eq (compare x k'); intros _x0 e1; subst.
      + inversion_clear 2.
        * clear e1;compute in H0; destruct H0.
          apply lt_not_eq in H; auto with smtcoq_array. now contradict H.
        * clear e1;generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute.
          (* order. *)
          intros.
          apply (lt_trans k') in _x0; auto with smtcoq_array.
          apply lt_not_eq in _x0.
          now contradict _x0.
      + clear e1;inversion_clear 2.
        * compute in H0; destruct H0; intuition congruence.
        * generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute.
          (* order. *)
          intros.
          apply lt_not_eq in H. now contradict H.
      + clear e1; do 2 inversion_clear 1; auto with smtcoq_array.
        compute in H2; destruct H2.
        (* order. *)
        subst. apply lt_not_eq in _x0. now contradict _x0.
  Qed.

  (** * [add] *)

  Fixpoint add (k : key) (x : elt) (s : farray) {struct s} : farray :=
    match s with
    | nil => (k,x) :: nil
    | (k',y) :: l =>
      match compare k k' with
      | LT _ => (k,x)::s
      | EQ _ => (k,x)::l
      | GT _ => (k',y) :: add k x l
      end
    end.

  Lemma add_1 : forall m x y e, eq x y -> MapsTo y e (add x e m).
  Proof.
    intros m x y e; generalize y; clear y.
    unfold MapsTo.
    induction m as [ |[k' _x] l IHb]; simpl; [ |case_eq (compare x k'); intros _x0 e1]; simpl; auto with smtcoq_array.
  Qed.

  Lemma add_2 : forall m x y e e',
      ~ eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros m x  y e e'.
    generalize y e; clear y e; unfold MapsTo.
    induction m as [ |[k' _x] l IHb]; simpl; [ |case_eq (compare x k'); intros _x0 e0];simpl;auto with smtcoq_array;  clear e0.
    subst;auto with smtcoq_array.

    intros y' e'' eqky';  inversion_clear 1;  destruct H0; simpl in *.
    (* order. *)
    subst. now contradict eqky'.
    auto with smtcoq_array.
    auto with smtcoq_array.
    intros y' e'' eqky'; inversion_clear 1; intuition.
  Qed.

  Lemma add_3 : forall m x y e e',
      ~ eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    intros m x y e e'. generalize y e; clear y e; unfold MapsTo.
    induction m as [ |[k' _x] l IHb]; simpl; [ |case_eq (compare x k'); intros _x0 e1];simpl; intros.
    apply (In_inv_3 H0); compute; auto with smtcoq_array.
    apply (In_inv_3 H0); compute; auto with smtcoq_array.
    constructor 2; apply (In_inv_3 H0); compute; auto with smtcoq_array.
    inversion_clear H0; auto with smtcoq_array.
  Qed.

  Lemma add_Inf : forall (m:farray)(x x':key)(e e':elt),
      Inf (x',e') m -> ltk (x',e') (x,e) -> Inf (x',e') (add x e m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x'',e'').
    inversion_clear H.
    compute in H0,H1.
    simpl; case (compare x x''); intuition.
  Qed.
  Hint Resolve add_Inf : smtcoq_array.

  Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; case (compare x x'); intuition; inversion_clear Hm; auto with smtcoq_array.
    constructor; auto with smtcoq_array.
    apply Inf_eq with (x',e'); auto with smtcoq_array.
  Qed.

  (** * [remove] *)

  Fixpoint remove (k : key) (s : farray) {struct s} : farray :=
    match s with
    | nil => nil
    | (k',x) :: l =>
      match compare k k' with
      | LT _ => s
      | EQ _ => l
      | GT _ => (k',x) :: remove k l
      end
    end.

  Lemma remove_1 : forall m (Hm:Sort m) x y, eq x y -> ~ In y (remove x m).
  Proof.
    intros m Hm x y; generalize Hm; clear Hm.
    induction m as [ |[k' x0] l IHb]; simpl;intros; [ |case_eq (compare x k'); intros _x e0];simpl;intros;subst.

    red; inversion 1; inversion H0.

    apply Sort_Inf_NotIn with x0; auto with smtcoq_array.

    clear e0. inversion Hm. subst.
    apply Sort_Inf_NotIn with x0; auto with smtcoq_array.

    clear e0;inversion_clear Hm.
    assert (notin:~ In y (remove y l)) by auto with smtcoq_array.
    intros (x1,abs).
    inversion_clear abs.
    compute in H1; destruct H1.
    subst. apply lt_not_eq in _x; now contradict _x.
    apply notin; exists x1; auto with smtcoq_array.
  Qed.


  Lemma remove_2 : forall m (Hm:Sort m) x y e,
      ~ eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    induction m as [ |[k' _x] l IHb]; simpl; [ |case_eq (compare x k'); intros _x0 e1];subst;auto with smtcoq_array;
      match goal with
      | [H: compare _ _ = _ |- _ ] => clear H
      | _ => idtac
      end.

    inversion_clear 3; auto with smtcoq_array.
    compute in H1; destruct H1.
    subst; now contradict H.
    inversion_clear 1; inversion_clear 2; auto with smtcoq_array.
  Qed.

  Lemma remove_3 : forall m (Hm:Sort m) x y e,
      MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    induction m as [ |[k' _x] l IHb]; simpl; [ |case_eq (compare x k'); intros _x0 e1];subst;auto with smtcoq_array.
    inversion_clear 1; inversion_clear 1; auto with smtcoq_array.
  Qed.

  Lemma remove_4_aux : forall m (Hm:Sort m) x y,
      ~ eq x y -> In y m -> In y (remove x m).
  Proof.
    intros m Hm x y; generalize Hm; clear Hm.
    induction m as [ |[k' x0] l IHf]; simpl; [ |case_eq (compare x k'); intros _x e1];subst;auto with smtcoq_array;
      match goal with
      | [H: compare _ _ = _ |- _ ] => clear H
      | _ => idtac
      end.
    rewrite In_alt.
    inversion_clear 3; auto with smtcoq_array.
    inversion H2.
    unfold eqk in H3. simpl in H3. subst. now contradict H0.
    apply In_alt.
    exists x. auto with smtcoq_array.
    apply lt_not_eq in _x.
    intros.
    inversion_clear Hm.
    inversion_clear H0.
    unfold MapsTo in H3.
    apply InA_eqke_eqk in H3.
    unfold In.
    destruct (eq_dec k' y).
    exists x0.
    apply InA_cons_hd.
    split; simpl; auto with smtcoq_array.
    inversion H3.
    unfold eqk in H4. simpl in H4; subst. now contradict n.
    assert ((exists e : elt, MapsTo y e (remove x l)) -> (exists e : elt, MapsTo y e ((k', x0) :: remove x l))).
    intros.
    destruct H6. exists x2.
    apply InA_cons_tl. auto with smtcoq_array.
    apply H6.
    apply IHf; auto with smtcoq_array.
    apply In_alt.
    exists x1. auto with smtcoq_array.
  Qed.

  Lemma remove_4 : forall m (Hm:Sort m) x y,
      ~ eq x y -> In y m <-> In y (remove x m).
  Proof.
    split.
    apply remove_4_aux; auto with smtcoq_array.
    revert H.
    generalize Hm; clear Hm.
    induction m as [ |[k' _x] l IHb]; simpl; [ |case_eq (compare x k'); intros _x0 e1];subst;auto with smtcoq_array;
      match goal with
      | [H: compare _ _ = _ |- _ ] => clear H
      | _ => idtac
      end.
    intros.
    destruct H0 as (e, H0).
    exists e.
    apply InA_cons_tl. auto with smtcoq_array.
    intros.
    apply lt_not_eq in _x0.
    inversion_clear Hm.
    apply In_inv in H0.
    destruct H0.
    exists _x.
    apply InA_cons_hd. split; simpl; auto with smtcoq_array.
    specialize (IHb H1 H H0).
    inversion IHb.
    exists x0.
    apply InA_cons_tl. auto with smtcoq_array.
  Qed.

  Lemma remove_Inf : forall (m:farray)(Hm : Sort m)(x x':key)(e':elt),
      Inf (x',e') m -> Inf (x',e') (remove x m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x'',e'').
    inversion_clear H.
    compute in H0.
    simpl; case (compare x x''); intuition.
    inversion_clear Hm.
    apply Inf_lt with (x'',e''); auto with smtcoq_array.
  Qed.
  Hint Resolve remove_Inf : smtcoq_array.

  Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; case (compare x x'); intuition; inversion_clear Hm; auto with smtcoq_array.
  Qed.

  (** * [elements] *)

  Definition elements (m: farray) := m.

  Lemma elements_1 : forall m x e,
      MapsTo x e m -> InA eqke (x,e) (elements m).
  Proof.
    auto with smtcoq_array.
  Qed.

  Lemma elements_2 : forall m x e,
      InA eqke (x,e) (elements m) -> MapsTo x e m.
  Proof.
    auto with smtcoq_array.
  Qed.

  Lemma elements_3 : forall m (Hm:Sort m), sort ltk (elements m).
  Proof.
    auto with smtcoq_array.
  Qed.

  Lemma elements_3w : forall m (Hm:Sort m), NoDupA (elements m).
  Proof.
    intros.
    apply Sort_NoDupA.
    apply elements_3; auto with smtcoq_array.
  Qed.

  (** * [fold] *)

  Fixpoint fold (A:Type)(f:key->elt->A->A)(m:farray) (acc:A) {struct m} :  A :=
    match m with
    | nil => acc
    | (k,e)::m' => fold f m' (f k e acc)
    end.

  Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros; revert i; induction m as [ |[k e]]; simpl; auto with smtcoq_array.
  Qed.

  (** * [equal] *)

  Fixpoint equal (cmp:elt->elt->bool)(m m' : farray) {struct m} : bool :=
    match m, m' with
    | nil, nil => true
    | (x,e)::l, (x',e')::l' =>
      match compare x x' with
      | EQ _ => cmp e e' && equal cmp l l'
      | _    => false
      end
    | _, _ => false
    end.

  Definition Equivb cmp m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

  Lemma equal_1 : forall m (Hm:Sort m) m' (Hm': Sort m') cmp,
      Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
    intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
    revert m'; induction m as [ |[x e] l IHl]; intros [ |[x' e'] l']; simpl; auto with smtcoq_array; unfold Equivb; intuition; subst.
    - destruct (H0 x') as [_ H3].
      assert (H2: In x' nil).
      {
        apply H3. exists e'. now constructor.
      }
      elim H2. intros x Hx. inversion Hx.
    - destruct (H0 x) as [H3 _].
      assert (H2: In x nil).
      {
        apply H3. exists e. now constructor.
      }
      elim H2. intros x0 Hx0. inversion Hx0.
    - case_eq (compare x x'); simpl; subst;auto with smtcoq_array; unfold Equivb;
      intuition; subst.
      + destruct (H0 x).
        assert (In x ((x',e')::l')).
        apply H2; auto with smtcoq_array.
        exists e; auto with smtcoq_array.
        destruct (In_inv H4).
        (* order. *)
        clear H. apply lt_not_eq in l0; now contradict l0.
        inversion_clear Hm'.
        assert (Inf (x,e) l').
        apply Inf_lt with (x',e'); auto with smtcoq_array.
        elim (Sort_Inf_NotIn H6 H8 H5).
      + match goal with H: compare _ _ = _ |- _ => clear H end.
        assert (cmp_e_e':cmp e e' = true).
        apply H1 with x'; auto with smtcoq_array.
        rewrite cmp_e_e'; simpl.
        apply IHl; auto with smtcoq_array.
        inversion_clear Hm; auto with smtcoq_array.
        inversion_clear Hm'; auto with smtcoq_array.
        unfold Equivb; intuition.
        destruct (H0 k).
        assert (In k ((x',e) ::l)).
        destruct H as (e'', hyp); exists e''; auto with smtcoq_array.
        destruct (In_inv (H2 H4)); auto with smtcoq_array.
        inversion_clear Hm.
        elim (Sort_Inf_NotIn H6 H7).
        destruct H as (e'', hyp); exists e''; auto with smtcoq_array.
        apply MapsTo_eq with k; auto with smtcoq_array.
        destruct (H0 k).
        assert (In k ((x',e') ::l')).
        destruct H as (e'', hyp); exists e''; auto with smtcoq_array.
        destruct (In_inv (H3 H4)); auto with smtcoq_array.
        subst.
        inversion_clear Hm'.
        now elim (Sort_Inf_NotIn H5 H6).
        apply H1 with k; destruct (eq_dec x' k); auto with smtcoq_array.
      + destruct (H0 x').
        assert (In x' ((x,e)::l)).
        apply H3; auto with smtcoq_array.
        exists e'; auto with smtcoq_array.
        destruct (In_inv H4).
        (* order. *)
        clear H; subst; apply lt_not_eq in l0; now contradict l0.
        inversion_clear Hm.
        assert (Inf (x',e') l).
        apply Inf_lt with (x,e); auto with smtcoq_array.
        elim (Sort_Inf_NotIn H6 H8 H5).
  Qed.

  Lemma equal_2 : forall m (Hm:Sort m) m' (Hm:Sort m') cmp,
      equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
    revert m'; induction m as [ |[x e] l IHl]; intros [ |[x' e'] l']; simpl; subst;auto with smtcoq_array; unfold Equivb;
      intuition; try discriminate; subst;
        try match goal with H: compare _ _ = _ |- _ => clear H end.
    - inversion H0.
    - revert H; case_eq (compare x x'); intros _x _ H; try inversion H.
      inversion_clear Hm;inversion_clear Hm'.
      destruct (andb_prop _ _ H); clear H.
      destruct (IHl _ H1 H4 H7).
      destruct (In_inv H0).
      exists e'; constructor; split; trivial; apply eq_trans with x; auto with smtcoq_array.
      destruct (H k).
      destruct (H10 H9) as (e'',hyp).
      exists e''; auto with smtcoq_array.
    - revert H; case_eq (compare x x'); intros _x _ H; try inversion H.
      inversion_clear Hm;inversion_clear Hm'.
      destruct (andb_prop _ _ H); clear H.
      destruct (IHl _ H1 H4 H7).
      destruct (In_inv H0).
      exists e; constructor; split; trivial; apply eq_trans with x'; auto with smtcoq_array.
      destruct (H k).
      destruct (H11 H9) as (e'',hyp).
      exists e''; auto with smtcoq_array.
    - revert H; case_eq (compare x x'); intros _x _ H; [inversion H| |inversion H].
      inversion_clear Hm;inversion_clear Hm'.
      destruct (andb_prop _ _ H); clear H.
      destruct (IHl _ H2 H4 H7).
      inversion_clear H0.
      + destruct H9; simpl in *; subst.
        inversion_clear H1.
        * destruct H0; simpl in *; subst; auto with smtcoq_array.
        * elim (Sort_Inf_NotIn H4 H5).
          exists e'0; apply MapsTo_eq with x'; auto with smtcoq_array.
      (* order. *)
      + inversion_clear H1.
        * destruct H0; simpl in *; subst; auto with smtcoq_array.
          elim (Sort_Inf_NotIn H2 H3).
          exists e0; apply MapsTo_eq with x'; auto with smtcoq_array.
        (* order. *)
        * apply H8 with k; auto with smtcoq_array.
  Qed.

  (** This lemma isn't part of the spec of [Equivb], but is used in [FMapAVL] *)

  Lemma equal_cons : forall cmp l1 l2 x y, Sort (x::l1) -> Sort (y::l2) ->
    eqk x y -> cmp (snd x) (snd y) = true ->
    (Equivb cmp l1 l2 <-> Equivb cmp (x :: l1) (y :: l2)).
  Proof.
    intros.
    inversion H; subst.
    inversion H0; subst.
    destruct x; destruct y; compute in H1, H2.
    split; intros.
    apply equal_2; auto with smtcoq_array.
    simpl.
    case (compare k k0);
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH).
    rewrite H2; simpl.
    apply equal_1; auto with smtcoq_array.
    apply equal_2; auto with smtcoq_array.
    generalize (equal_1 H H0 H3).
    simpl.
    case (compare k k0);
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH).
    rewrite H2; simpl; auto with smtcoq_array.
  Qed.

End Array.

End Raw.


(** * Functional Arrays *)

Section FArray.

  Variable key : Type.
  Variable elt : Type.
  Variable key_dec : DecType key.
  Variable key_ord : OrdType key.
  Variable key_comp : Comparable key.
  Variable elt_dec : DecType elt.
  Variable elt_ord : OrdType elt.
  Variable elt_comp : Comparable elt.
  Variable key_inh :  Inhabited key.
  Variable elt_inh :  Inhabited elt.

  Set Implicit Arguments.

  Definition NoDefault l := forall k:key, ~ Raw.MapsTo k default_value l.

  Record farray :=
    {this :> Raw.farray key elt;
     sorted : sort (Raw.ltk key_ord) this;
     nodefault : NoDefault this
    }.

  Lemma empty_nodefault : NoDefault (Raw.empty key elt).
    unfold NoDefault.
    intros.
    apply Raw.empty_1.
  Qed.

  (** Boolean comparison over elements *)
  Definition cmp := @compare2eqb _ _ elt_comp.

  Lemma cmp_refl : forall e, cmp e e = true.
  Proof. intro e. unfold cmp. now rewrite compare2eqb_spec. Qed.


  Lemma remove_nodefault : forall l (Hd:NoDefault l) (Hs:Sorted (Raw.ltk key_ord) l) x ,
      NoDefault (Raw.remove key_comp x l).
  Proof.
    intros.
    unfold NoDefault. intros.
    unfold not. intro.
    apply Raw.remove_3 in H; auto.
    now apply Hd in H.
  Qed.

  Definition raw_add_nodefault (k:key) (x:elt) (l:Raw.farray key elt) :=
    if cmp x default_value then
      if Raw.mem key_comp k l then Raw.remove key_comp k l
      else l
    else Raw.add key_comp k x l.


  Lemma add_sorted : forall l (Hs:Sorted (Raw.ltk key_ord) l) x e,
      Sorted (Raw.ltk key_ord) (raw_add_nodefault x e l).
  Proof.
    intros.
    unfold raw_add_nodefault.
    case (cmp e default_value); auto.
    case (Raw.mem key_comp x l); auto.
    apply Raw.remove_sorted; auto.
    apply Raw.add_sorted; auto.
  Qed.

  Lemma add_nodefault : forall l (Hd:NoDefault l) (Hs:Sorted (Raw.ltk key_ord) l) x e,
      NoDefault (raw_add_nodefault x e l).
  Proof.
    intros l Hd Hs x e.
    unfold raw_add_nodefault.
    case_eq (cmp e default_value); intro H; auto.
    - case_eq (Raw.mem key_comp x l); intro H0; auto.
      apply remove_nodefault; auto.
    - unfold NoDefault; intros k.
      assert (H0: e <> default_value).
      { intro H1. subst e. rewrite cmp_refl in H. discriminate. }
      destruct (eq_dec k x) as [e0|n].
      + symmetry in e0.
        apply (Raw.add_1 key_comp l e) in e0.
        unfold not; intro.
        specialize (Raw.add_sorted key_comp Hs x e).
        intro Hsadd.
        specialize (Raw.MapsTo_inj Hsadd e0 H1).
        intro. contradiction.
      + unfold not; intro.
        assert (x <> k). unfold not in *. intro. apply n. symmetry; auto.
        specialize (Raw.add_3 key_comp l e H2 H1).
        intro. now apply Hd in H3.
  Qed.

  Definition empty : farray :=
    Build_farray (Raw.empty_sorted elt key_ord) empty_nodefault.

  Definition is_empty m : bool := Raw.is_empty m.(this).

  Definition add x e m : farray :=
    Build_farray (add_sorted m.(sorted) x e)
                (add_nodefault m.(nodefault) m.(sorted) x e).

  Definition find x m : option elt := Raw.find key_comp x m.(this).

  Definition remove x m : farray :=
    Build_farray (Raw.remove_sorted key_comp m.(sorted) x) (remove_nodefault m.(nodefault) m.(sorted) x).

  Definition mem x m : bool := Raw.mem key_comp x m.(this).
  Definition elements m : list (key*elt) := Raw.elements m.(this).
  Definition cardinal m := length m.(this).
  Definition fold (A:Type)(f:key->elt->A->A) m (i:A) : A :=
    Raw.fold f m.(this) i.
  Definition equal m m' : bool := Raw.equal key_comp cmp m.(this) m'.(this).

  Definition MapsTo x e m : Prop := Raw.MapsTo x e m.(this).
  Definition In x m : Prop := Raw.In x m.(this).
  Definition Empty m : Prop := Raw.Empty m.(this).

  Definition Equal m m' := forall y, find y m = find y m'.
  Definition Equiv m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> e = e').
  Definition Equivb m m' : Prop := Raw.Equivb cmp m.(this) m'.(this).

  Definition eq_key : (key*elt) -> (key*elt) -> Prop := @Raw.eqk key elt.
  Definition eq_key_elt : (key*elt) -> (key*elt) -> Prop:= @Raw.eqke key elt.
  Definition lt_key : (key*elt) -> (key*elt) -> Prop := @Raw.ltk key elt key_ord.

  Lemma MapsTo_1 : forall m x y e, eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros m. apply Raw.MapsTo_eq. Qed.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof. intros m; apply (Raw.mem_1); auto. apply m.(sorted). Qed.
  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof. intros m; apply (Raw.mem_2); auto. apply m.(sorted). Qed.

  Lemma empty_1 : Empty empty.
  Proof. apply Raw.empty_1. Qed.

  Lemma is_empty_1 : forall m, Empty m -> is_empty m = true.
  Proof. intros m; apply Raw.is_empty_1. Qed.
  Lemma is_empty_2 :  forall m, is_empty m = true -> Empty m.
  Proof. intros m; apply Raw.is_empty_2. Qed.

  Lemma add_1 : forall m x y e, e <> default_value -> eq x y -> MapsTo y e (add x e m).
  Proof.
    intros m x y e H H0.
    unfold add, raw_add_nodefault.
    unfold MapsTo. simpl.
    case_eq (cmp e default_value); intro H1; auto.
    - elim H. unfold cmp in H1. now rewrite compare2eqb_spec in H1.
    - apply Raw.add_1; auto.
  Qed.

  Lemma add_2 : forall m x y e e', ~ eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros.
    unfold add, raw_add_nodefault, MapsTo. simpl.
    case_eq (cmp e' default_value); intro; auto.
    case_eq (Raw.mem key_comp x m); intro; auto.
    apply (Raw.remove_2 _ m.(sorted)); auto.
    apply Raw.add_2; auto.
  Qed.

  Lemma add_3 : forall m x y e e', ~ eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    unfold add, raw_add_nodefault, MapsTo. simpl.
    intros m x y e e'.
    case_eq (cmp e' default_value); intro; auto.
    case_eq (Raw.mem key_comp x m); intro; auto.
    intro. apply (Raw.remove_3 _ m.(sorted)); auto.
    apply Raw.add_3; auto.
  Qed.

  Lemma remove_1 : forall m x y, eq x y -> ~ In y (remove x m).
  Proof. intros m; apply Raw.remove_1; auto. apply m.(sorted). Qed.

  Lemma remove_2 : forall m x y e, ~ eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof. intros m; apply Raw.remove_2; auto. apply m.(sorted). Qed.

  Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
  Proof. intros m; apply Raw.remove_3; auto. apply m.(sorted). Qed.

  Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
  Proof. intros m; apply Raw.find_1; auto. apply m.(sorted). Qed.

  Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
  Proof. intros m; apply Raw.find_2; auto. Qed.

  Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof. intros m; apply Raw.elements_1. Qed.

  Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof. intros m; apply Raw.elements_2. Qed.

  Lemma elements_3 : forall m, sort lt_key (elements m).
  Proof. intros m; apply Raw.elements_3; auto. apply m.(sorted). Qed.

  Lemma elements_3w : forall m, NoDupA eq_key (elements m).
  Proof. intros m; apply (Raw.elements_3w m.(sorted)). Qed.

  Lemma cardinal_1 : forall m, cardinal m = length (elements m).
  Proof. intros; reflexivity. Qed.

  Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof. intros m; apply Raw.fold_1. Qed.

  Lemma equal_1 : forall m m', Equivb m m' -> equal m m' = true.
  Proof. intros m m'; apply Raw.equal_1; auto. apply m.(sorted). apply  m'.(sorted). Qed.

  Lemma equal_2 : forall m m', equal m m' = true -> Equivb m m'.
  Proof. intros m m'; apply Raw.equal_2; auto. apply m.(sorted). apply  m'.(sorted). Qed.

  Fixpoint eq_list (m m' : list (key * elt)) : Prop :=
    match m, m' with
    | nil, nil => True
    | (x,e)::l, (x',e')::l' =>
      match compare x x' with
      | EQ _ => eq e e' /\ eq_list l l'
      | _       => False
      end
    | _, _ => False
    end.

  Definition eq m m' := eq_list m.(this) m'.(this).

  Lemma nodefault_tail : forall x m, NoDefault (x :: m) -> NoDefault m.
    unfold NoDefault. unfold not in *. intros.
    apply (H k). unfold Raw.MapsTo. apply InA_cons_tl. apply H0.
  Qed.

  Lemma raw_equal_eq :
    forall a (Ha: Sorted (Raw.ltk key_ord) a) b (Hb: Sorted (Raw.ltk key_ord) b),
      Raw.equal key_comp cmp a b = true -> a = b.
  Proof.
    induction a as [ |a a0 IHa]; intros Ha b Hb H.
    - simpl in H.
      case b in *; auto.
      now contradict H.
    - destruct a as (xa, ea).
      simpl in H.
      case b in *.
      + now contradict H.
      + destruct p as (xb, eb).
        destruct (compare xa xb); auto; try (now contradict H).
        rewrite andb_true_iff in H. destruct H as [H H0].
        unfold cmp in H. rewrite compare2eqb_spec in H.
        subst. apply f_equal.
        apply IHa; auto.
        * now inversion Ha.
        * now inversion Hb.
  Qed.

  Lemma eq_equal : forall m m', eq m m' <-> equal m m' = true.
  Proof.
    intros (l,Hl,Hd); induction l as [ |a l IHl].
    - intros (l',Hl',Hd'); unfold eq; simpl.
      destruct l'; unfold equal; simpl; intuition.
    - intros (l',Hl',Hd'); unfold eq.
      destruct l' as [ |p l'].
      + destruct a; unfold equal; simpl; intuition.
      + destruct a as (x,e).
        destruct p as (x',e').
        unfold equal; simpl.
        destruct (compare x x') as [Hlt|Heq|Hlt]; simpl; [intuition| |intuition].
        split.
        * intros [H0 H1].
          unfold cmp, compare2eqb at 1.
          case (compare e e');
            subst; intro HH; try (apply lt_not_eq in HH; now contradict HH);
              clear HH; simpl.
          inversion_clear Hl.
          inversion_clear Hl'.
          apply nodefault_tail in Hd.
          apply nodefault_tail in Hd'.
          destruct (IHl H Hd (Build_farray H2 Hd')).
          unfold equal, eq in H5; simpl in H5; auto.
        * { intro H. destruct (andb_prop _ _ H) as [H0 H1]; clear H. split.
            - generalize H0; unfold cmp, compare2eqb.
              case (compare e e');
                subst; intro HH; try (apply lt_not_eq in HH; now contradict HH);
                  auto; intro; discriminate.
            - inversion_clear Hl.
              inversion_clear Hl'.
              apply nodefault_tail in Hd.
              apply nodefault_tail in Hd'.
              destruct (IHl H Hd (Build_farray H3 Hd')).
              unfold equal, eq in H6; simpl in H6; auto.
          }
  Qed.

  Lemma eq_1 : forall m m', Equivb m m' -> eq m m'.
  Proof.
    intros.
    generalize (@equal_1 m m').
    generalize (@eq_equal m m').
    intuition.
  Qed.

  Lemma eq_2 : forall m m', eq m m' -> Equivb m m'.
  Proof.
    intros.
    generalize (@equal_2 m m').
    generalize (@eq_equal m m').
    intuition.
  Qed.

  Lemma eqfarray_refl : forall m : farray, eq m m.
  Proof.
    intros (m,Hm,Hd); induction m; unfold eq; simpl; auto.
    destruct a.
    destruct (compare k k) as [Hlt|Heq|Hlt]; auto.
    apply lt_not_eq in Hlt. auto.
    split.
    apply eq_refl.
    inversion_clear Hm.
    apply nodefault_tail in Hd.
    apply (IHm H Hd).
    apply lt_not_eq in Hlt. auto.
  Qed.

  Lemma eqfarray_sym : forall m1 m2 : farray, eq m1 m2 -> eq m2 m1.
  Proof.
    intros (m,Hm,Hd); induction m;
      intros (m',Hm',Hd'); destruct m'; unfold eq; simpl;
        try destruct a as (x,e); try destruct p as (x',e'); auto.
    destruct (compare x x')  as [Hlt|Heq|Hlt]; try easy.
    inversion_clear Hm; inversion_clear Hm'.
    apply nodefault_tail in Hd. apply nodefault_tail in Hd'.
    intro. destruct H3.
    subst.
    case (compare x' x');
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH).
    split; auto.
    apply (IHm H Hd (Build_farray H1 Hd')); auto.
  Qed.

  Lemma eqfarray_trans : forall m1 m2 m3 : farray, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Proof.
    intros (m1,Hm1,Hd1); induction m1;
      intros (m2,Hm2,Hd2); destruct m2;
        intros (m3,Hm3,Hd3); destruct m3; unfold eq; simpl;
          try destruct a as (x,e);
          try destruct p as (x',e');
          try destruct p0 as (x'',e''); try contradiction; auto.
    destruct (compare x x') as [Hlt|Heq|Hlt];
      destruct (compare x' x'') as [Hlt'|Heq'|Hlt']; try easy.
    intros; destruct H, H0;  subst.
    case (compare x'' x'');
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH).
    split; auto.
    inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
    apply nodefault_tail in Hd1.
    apply nodefault_tail in Hd2.
    apply nodefault_tail in Hd3.
    apply (IHm1 H Hd1 (Build_farray H3 Hd2) (Build_farray H5 Hd3)); intuition.
  Qed.

  Fixpoint lt_list (m m' : list (key * elt)) : Prop :=
    match m, m' with
    | nil, nil => False
    | nil, _  => True
    | _, nil  => False
    | (x,e)::l, (x',e')::l' =>
      match compare x x' with
      | LT _ => True
      | GT _ => False
      | EQ _ => lt e e' \/ (e = e' /\ lt_list l l')
      end
    end.

  Definition lt_farray m m' := lt_list m.(this) m'.(this).

  Lemma lt_farray_trans : forall m1 m2 m3 : farray,
      lt_farray m1 m2 -> lt_farray m2 m3 -> lt_farray m1 m3.
  Proof.
    intros (m1,Hm1,Hd1); induction m1;
      intros (m2,Hm2,Hd2); destruct m2;
        intros (m3,Hm3,Hd3); destruct m3; unfold lt_farray; simpl;
          try destruct a as (x,e);
          try destruct p as (x',e');
          try destruct p0 as (x'',e''); try contradiction; auto.
    destruct (compare x x') as [Hlt|Heq|Hlt];
      destruct (compare x' x'') as [Hlt'|Heq'|Hlt'];
      destruct (compare x x'') as [Hlt''|Heq''|Hlt'']; intros; subst; auto; try easy.
    apply (lt_trans x') in Hlt; apply lt_not_eq in Hlt.
    now contradict Hlt. auto.
    apply (lt_trans x') in Hlt; apply lt_not_eq in Hlt.
    now contradict Hlt.
    apply (lt_trans _ x'') ; auto.
    apply lt_not_eq in Hlt. now contradict Hlt.
    apply (lt_trans x'') in Hlt; apply lt_not_eq in Hlt.
    now contradict Hlt. auto.
    subst.
    apply lt_not_eq in Hlt'. now contradict Hlt'.
    apply (lt_trans x'') in Hlt'; apply lt_not_eq in Hlt'.
    now contradict Hlt'. auto.
    destruct H, H0.
    left; apply lt_trans with e'; auto.
    left. destruct H0. subst; auto.
    left. destruct H. subst; auto.
    right. destruct H, H0. subst; split; auto.
    inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3.
    apply nodefault_tail in Hd1.
    apply nodefault_tail in Hd2.
    apply nodefault_tail in Hd3.
    apply (IHm1 H Hd1 (Build_farray H3 Hd2) (Build_farray H5 Hd3)); intuition.
    apply lt_not_eq in Hlt''. now contradict Hlt''.
  Qed.

  Lemma lt_farray_not_eq : forall m1 m2 : farray, lt_farray m1 m2 -> ~ eq m1 m2.
  Proof.
    intros (m1,Hm1,Hd1); induction m1;
      intros (m2,Hm2,Hd2); destruct m2; unfold eq, lt; simpl;
        try destruct a as (x,e);
        try destruct p as (x',e'); try contradiction; auto.
    destruct (compare x x') as [Hlt|Heq|Hlt]; auto.
    intuition.
    inversion_clear Hm1; inversion_clear Hm2.
    specialize (nodefault_tail Hd2).
    specialize (nodefault_tail Hd1). intros.
    subst.
    apply (IHm1 H0 H6 (Build_farray H4 H7)); intuition.
    unfold lt_farray in *.
    simpl in H.
    case (compare x' x') in *.
    apply lt_not_eq in l. now contradict l.
    destruct H.
    apply lt_not_eq in H. now contradict H.
    destruct H.
    auto.
    apply lt_not_eq in l. now contradict l.
  Qed.

  Definition compare_farray : forall m1 m2, Compare lt_farray eq m1 m2.
  Proof.
    intros (m1,Hm1,Hd1); induction m1;
      intros (m2,Hm2,Hd2); destruct m2;
        [ apply EQ | apply LT | apply GT | ]; auto.
    (* cmp_solve. *)
    unfold eq. simpl; auto.
    unfold lt_farray. simpl; auto.
    unfold lt_farray. simpl; auto.
    destruct a as (x,e); destruct p as (x',e').
    destruct (compare x x');
      [ apply LT | | apply GT ].
    unfold lt_farray. simpl.
    destruct (compare x x'); auto.
    subst. apply lt_not_eq in l; now contradict l.
    apply (lt_trans x') in l; auto. subst. apply lt_not_eq in l; now contradict l.
    (* subst. *)
    destruct (compare e e');
      [ apply LT | | apply GT ].
    unfold lt_farray. simpl.
    destruct (compare x x'); auto; try (subst; apply lt_not_eq in l0; now contradict l0).
    assert (Hm11 : sort (Raw.ltk key_ord) m1).
    inversion_clear Hm1; auto.
    assert (Hm22 : sort (Raw.ltk key_ord) m2).
    inversion_clear Hm2; auto.
    specialize (nodefault_tail Hd2). specialize (nodefault_tail Hd1).
    intros Hd11 Hd22.
    destruct (IHm1 Hm11 Hd11 (Build_farray Hm22 Hd22));
      [ apply LT | apply EQ | apply GT ].
    unfold lt_farray in *. simpl.
    destruct (compare x x'); auto; try (subst; apply lt_not_eq in l0; now contradict l0).
    unfold eq in *. simpl.
    destruct (compare x x'); auto; try (subst; apply lt_not_eq in l; now contradict l).
    unfold lt_farray in *. simpl.
    destruct (compare x' x); auto; try (subst; apply lt_not_eq in l0; now contradict l0).
    unfold lt_farray in *. simpl.
    destruct (compare x' x); auto; try (subst; apply lt_not_eq in l0; now contradict l0).
    unfold lt_farray in *. simpl.
    destruct (compare x' x); auto; try (subst; apply lt_not_eq in l; now contradict l).
    apply (lt_trans x) in l; auto. subst. apply lt_not_eq in l; now contradict l.
  Qed.

  Lemma eq_option_alt : forall (elt:Type)(o o':option elt),
      o=o' <-> (forall e, o=Some e <-> o'=Some e).
  Proof.
    split; intros.
    subst; split; auto.
    destruct o; destruct o'; try rewrite H; auto.
    symmetry; rewrite <- H; auto.
  Qed.

  Lemma find_mapsto_iff : forall m x e, MapsTo x e m <-> find x m = Some e.
  Proof.
    split; [apply find_1|apply find_2].
  Qed.

  Lemma add_neq_mapsto_iff : forall m x y e e',
      x <> y -> (MapsTo y e' (add x e m)  <-> MapsTo y e' m).
  Proof.
    split; [apply add_3|apply add_2]; auto.
  Qed.


  Lemma add_eq_o : forall m x y e,
      x = y -> e <> default_value -> find y (add x e m) = Some e.
  Proof. intros.
    apply find_1.
    apply add_1; auto.
  Qed.

  Lemma raw_add_d_rem : forall m (Hm: Sorted (Raw.ltk key_ord) m) x,
      raw_add_nodefault x default_value m = Raw.remove key_comp x m.
  Proof.
    intros m Hm x.
    unfold raw_add_nodefault.
    rewrite cmp_refl.
    case_eq (Raw.mem key_comp x m); intro H; auto.
    apply Raw.mem_3 in H; auto.
    apply raw_equal_eq; auto.
    - apply Raw.remove_sorted; auto.
    - apply Raw.equal_1; auto.
      + apply Raw.remove_sorted; auto.
      + unfold Raw.Equivb.
        split.
        * { intros k.
            destruct (eq_dec x k) as [e|n].
            - subst.
              split.
              + intro. contradiction.
              + intro. contradict H0.
                apply Raw.remove_1; auto.
            - apply Raw.remove_4; auto.
          }
        * { intros k e e' H0 H1.
            destruct (eq_dec x k) as [e0|n].
            - assert (H2:exists e, InA (Raw.eqk (elt:=elt)) (k, e) (Raw.remove key_comp x m)).
              { exists e'. apply Raw.InA_eqke_eqk; auto. }
              rewrite <- Raw.In_alt in H2; auto.
              + contradict H2.
                apply Raw.remove_1; auto.
              + apply key_comp.
            - apply (Raw.remove_2 key_comp Hm n) in H0.
              specialize (Raw.remove_sorted key_comp Hm x). intros H2.
              specialize (Raw.MapsTo_inj H2 H0 H1).
              intro H3. subst. apply cmp_refl.
          }
  Qed.

  Lemma add_d_rem : forall m x, add x default_value m = remove x m.
    intros.
    unfold add, remove.
    specialize (raw_add_d_rem m.(sorted) x). intro.
    generalize (add_sorted m.(sorted) x default_value).
    generalize (add_nodefault (nodefault m) (sorted m) x default_value).
    generalize (Raw.remove_sorted key_comp (sorted m) x).
    generalize (remove_nodefault (nodefault m) (sorted m) x).
    rewrite H.
    intros H4 H3 H2 H1.
    rewrite (proof_irrelevance _ H1 H3), (proof_irrelevance _ H2 H4).
    reflexivity.
  Qed.

  Lemma add_eq_d : forall m x y,
      x = y -> find y (add x default_value m) = None.
  Proof.
    intros m x y h.
    rewrite add_d_rem.
    case_eq (find y (remove x m)); auto.
    intros e H0.
    apply find_2 in H0.
    unfold MapsTo, Raw.MapsTo in H0.
    assert (H1:exists e, InA (Raw.eqk (elt:=elt)) (y, e) (remove x m).(this)).
    { exists e. apply Raw.InA_eqke_eqk in H0. auto. }
    rewrite <- Raw.In_alt in H1; auto.
    - contradict H1.
      apply remove_1; auto.
    - apply key_comp.
  Qed.

  Lemma add_neq_o : forall m x y e,
      ~ x = y -> find y (add x e m) = find y m.
  Proof.
    intros. rewrite eq_option_alt. intro e'. rewrite <- 2 find_mapsto_iff.
    apply add_neq_mapsto_iff; auto.
  Qed.
  Hint Resolve add_neq_o : smtcoq_array.

  Lemma MapsTo_fun : forall m x (e e':elt),
      MapsTo x e m -> MapsTo x e' m -> e=e'.
  Proof.
    intros.
    generalize (find_1 H) (find_1 H0); clear H H0.
    intros; rewrite H in H0; injection H0; auto.
  Qed.

  (** Another characterisation of [Equal] *)

  Lemma Equal_mapsto_iff : forall m1 m2 : farray,
      Equal m1 m2 <-> (forall k e, MapsTo k e m1 <-> MapsTo k e m2).
  Proof.
    intros m1 m2. split; [intros Heq k e|intros Hiff].
    rewrite 2 find_mapsto_iff, Heq. split; auto.
    intro k. rewrite eq_option_alt. intro e.
    rewrite <- 2 find_mapsto_iff; auto.
  Qed.

  (** * Relations between [Equal], [Equiv] and [Equivb]. *)

  (** First, [Equal] is [Equiv] with Leibniz on elements. *)

  Lemma Equal_Equiv : forall (m m' : farray),
      Equal m m' <-> Equiv m m'.
  Proof.
    intros. rewrite Equal_mapsto_iff. split; intros.
    split.
    split; intros (e,Hin); exists e; unfold MapsTo in H; [rewrite <- H|rewrite H]; auto.
    intros; apply MapsTo_fun with m k; auto; rewrite H; auto.
    split; intros H'.
    destruct H.
    assert (Hin : In k m') by (rewrite <- H; exists e; auto).
    destruct Hin as (e',He').
    rewrite (H0 k e e'); auto.
    destruct H.
    assert (Hin : In k m) by (rewrite H; exists e; auto).
    destruct Hin as (e',He').
    rewrite <- (H0 k e' e); auto.
  Qed.

  Lemma Equiv_Equivb : forall m m', Equiv m m' <-> Equivb m m'.
  Proof.
    unfold Equiv, Equivb, Raw.Equivb, cmp; intuition; specialize (H1 k e e' H H2).
    - unfold compare2eqb; destruct (compare e e'); auto; apply lt_not_eq in l; auto.
    - unfold compare2eqb in *; destruct (compare e e'); auto; inversion H1.
  Qed.

  (** Composition of the two last results: relation between [Equal]
    and [Equivb]. *)

  Lemma Equal_Equivb : forall (m m':farray), Equal m m' <-> Equivb m m'.
  Proof.
    intros; rewrite Equal_Equiv.
    apply Equiv_Equivb; auto.
  Qed.

  (** * Functional arrays with default value *)

  Definition select (a: farray) (i: key) : elt :=
    match find i a with
    | Some v => v
    | None => default_value
    end.

  Definition store (a: farray) (i: key) (v: elt) : farray := add i v a.

  Lemma read_over_same_write : forall a i j v, i = j -> select (store a i v) j = v.
  Proof.
    intros a i j v Heq.
    unfold select, store.
    case_eq (cmp v default_value); intro H; auto.
    - unfold cmp, compare2eqb in H.
      case (compare v default_value) as [ | |e] in H; auto; try now contradict H.
      rewrite e.
      rewrite add_eq_d; auto.
    - assert (H0: v <> default_value).
      { unfold cmp, compare2eqb in H.
        case (compare v default_value) as [l|e|l] in H; auto; try now contradict H.
        - apply lt_not_eq in l. auto.
        - apply lt_not_eq in l. auto. }
      rewrite (add_eq_o a Heq H0). auto.
  Qed.

  Lemma read_over_write : forall a i v, select (store a i v) i = v.
  Proof.
    intros; apply read_over_same_write; auto.
  Qed.

  Lemma read_over_other_write : forall a i j v,
      i <> j -> select (store a i v) j = select a j.
  Proof.
    intros a i j v Hneq.
    unfold select, store.
    apply (add_neq_o a v) in Hneq.
    rewrite Hneq. auto.
  Qed.

  Lemma find_ext_dec:
    (forall m1 m2: farray, Equal m1 m2 -> (equal m1 m2) = true).
  Proof. intros.
    apply Equal_Equivb in H.
    apply equal_1.
    exact H.
  Qed.

  Lemma extensionality_eqb : forall a b,
      (forall i, select a i = select b i) -> equal a b = true.
  Proof.
    intros.
    unfold select in H.
    assert (forall i, find i a = find i b).
    - intro i. specialize (H i).
      case_eq (find i a);
        case_eq (find i b);
        intros; rewrite H0 in *; rewrite H1 in *; subst; auto.
      + apply find_2 in H1.
        contradict H1.
        unfold MapsTo.
        apply a.(nodefault).
      + apply find_2 in H0.
        contradict H0.
        unfold MapsTo.
        apply b.(nodefault).
    - apply find_ext_dec in H0.
      exact H0.
  Qed.

  Lemma equal_eq : forall a b, equal a b = true -> a = b.
  Proof. intros. apply eq_equal in H.
    destruct a as (a, asort, anodef), b as (b, bsort, bnodef).
    unfold eq in H.
    revert b bsort bnodef H.
    induction a; intros; destruct b.
    rewrite (proof_irrelevance _ asort bsort).
    rewrite (proof_irrelevance _ anodef bnodef).
    auto.
    simpl in H. now contradict H.
    simpl in H. destruct a; now contradict H.
    simpl in H. destruct a, p.
    destruct (compare k k0); auto; try (now contradict H).
    destruct H.
    subst.
    inversion_clear asort.
    inversion_clear bsort.
    specialize (nodefault_tail bnodef).
    specialize (nodefault_tail anodef). intros.
    specialize (IHa H H4 b H2 H5 H0).
    inversion IHa. subst.
    rewrite (proof_irrelevance _ asort bsort).
    rewrite (proof_irrelevance _ anodef bnodef).
    reflexivity.
 Qed.

  Lemma notequal_neq : forall a b, equal a b = false -> a <> b.
    intros.
    red. intros.
    apply not_true_iff_false in H.
    unfold not in *. intros.
    apply H. rewrite H0.
    apply eq_equal. apply eqfarray_refl.
  Qed.

  Lemma extensionality : forall a b, (forall i, select a i = select b i) -> a = b.
  Proof.
    intros; apply equal_eq; apply extensionality_eqb; auto.
  Qed.


  Lemma eq_list_refl: forall a, eq_list a a.
  Proof.
    intro a.
    induction a; intros.
    - now simpl.
    - simpl. destruct a as (k, e).
      case_eq (compare k k); intros.
      + revert H. generalize l.
        apply lt_not_eq in l. now contradict l.
      + split; easy.
      + revert H. generalize l.
        apply lt_not_eq in l. now contradict l.
  Qed.

  Lemma equal_refl: forall a, equal a a = true.
  Proof. intros; apply eq_equal; apply eq_list_refl. Qed.

  Lemma equal_iff_eq : forall a b, equal a b = true <-> a = b.
  Proof.
    intros a b.
    split.
    - apply equal_eq.
    - intro; subst. apply equal_refl.
  Qed.

  Section Classical_extensionality.

    Lemma lt_select_default i xs xsS xsD : (forall xe, HdRel lt (i, xe) xs) ->
      select {| this := xs; sorted := xsS; nodefault := xsD |} i = default_value.
    Proof.
      intro H1. unfold select, find. simpl.
      destruct xs as [ |[xk xe] xs]; auto.
      simpl. assert (H2:=H1 xe). inversion H2 as [ |b l H0 H]; subst.
      case_eq (compare i xk); auto.
      - intros e He. subst i. now elim (lt_not_eq _ _ H0).
      - intros l _. simpl in H0. unfold Raw.ltk in H0. simpl in H0.
        now elim (lt_not_eq _ _ (lt_trans _ _ _ H0 l)).
    Qed.

    Lemma HdRelElt (xk:key) (ye:elt) ys : HdRel lt (xk, ye) ys -> forall ye', HdRel lt (xk, ye') ys.
    Proof.
      induction ys as [ |[yk yee] ys IHys]; auto.
      simpl. intros H ye'. inversion H as [ |b l H1 H0]; subst.
      now constructor.
    Qed.

    Lemma diff_index_p : forall a b, a <> b -> {i | select a i <> select b i}.
    Proof.
      intros a b.
      assert (Hcomp:forall (k:key), exists e, compare k k = EQ e).
      {
        intro k.
        case_eq (compare k k); try (intro H; now elim (lt_not_eq _ _ H)).
        intros e He. now exists e.
      }
      assert (HInd: forall x y (xS:Sorted _ x) (yS:Sorted _ y) (xD:NoDefault x) (yD:NoDefault y),
                 let a := Build_farray xS xD in
                 let b := Build_farray yS yD in
                 a <> b -> {i : key | select a i <> select b i}).
      {
        clear a b. intros x y.
        case_eq (list_eq_dec (@eq_dec _ (Raw.ke_dec key_dec elt_dec)) x y).
        - intros e He. subst x. intros xS yS xD yD a b. subst a b.
          rewrite (proof_irrelevance _ xS yS),  (proof_irrelevance _ xD yD).
          intro H. elim H. reflexivity.
        - intros n _ xS yS xD yD a b _. subst a b.
          revert x y n xS yS xD yD.
          {
            induction x as [ |[xk xe] xs IHxs]; intros [ |[yk ye] ys].
            - intro H; now elim H.
            - intros _ xS yS xD yD. exists yk.
              unfold select, find. simpl. destruct (Hcomp yk) as [e ->].
              unfold NoDefault in yD. intro H. subst ye. elim (yD yk). unfold Raw.MapsTo.
              constructor. apply Raw.eqke_refl.
            - intros _ xS yS xD yD. exists xk.
              unfold select, find. simpl. destruct (Hcomp xk) as [e ->].
              unfold NoDefault in xD. intro H. subst xe. elim (xD xk). unfold Raw.MapsTo.
              constructor. apply Raw.eqke_refl.
            - intros H xS yS xD yD. case_eq (compare xk yk).
              + intros l Hl. exists xk. unfold select, find. simpl.
                destruct (Hcomp xk) as [e ->]. rewrite Hl.
                unfold NoDefault in xD. intro H1; subst xe.
                apply (xD xk). unfold Raw.MapsTo. constructor. apply Raw.eqke_refl.
              + intros e _. subst xk. case_eq (eq_dec xe ye).
                * intros e _. subst ye. assert (H1:xs <> ys)
                    by (intro H1; rewrite H1 in H; now apply H).
                  assert (xsS : Sorted (Raw.ltk key_ord) xs) by now inversion xS.
                  assert (ysS : Sorted (Raw.ltk key_ord) ys) by now inversion yS.
                  assert (xsD:NoDefault xs) by exact (nodefault_tail xD).
                  assert (ysD:NoDefault ys) by exact (nodefault_tail yD).
                  destruct (IHxs _ H1 xsS ysS xsD ysD) as [i Hi].
                  {
                    case_eq (compare i yk).
                    - intros l Hl.
                      rewrite (lt_select_default xsS xsD) in Hi.
                      + rewrite (lt_select_default ysS ysD) in Hi.
                        * now elim Hi.
                        *
                          {
                            intro xe0.
                            apply (InfA_ltA _ (y:=(yk, xe))).
                            - simpl. unfold Raw.ltk. simpl. auto.
                            - now inversion yS.
                          }
                      + intro xe0.
                        apply (InfA_ltA _ (y:=(yk, xe))).
                        * simpl. unfold Raw.ltk. simpl. auto.
                        * now inversion xS.
                    - intros l Hl.
                      rewrite (lt_select_default xsS xsD) in Hi.
                      + rewrite (lt_select_default ysS ysD) in Hi.
                        * now elim Hi.
                        * intro xe0.
                          inversion yS as [ |a l0 H3 H4 H0]; subst.
                          apply (HdRelElt H4).
                      + intro xe0.
                        inversion xS as [ |a l0 H3 H4 H0]; subst.
                        apply (HdRelElt H4).
                    - intros l Hl. exists i. unfold select, find. simpl. now rewrite Hl.
                  }
                * intros n Hn. exists yk. unfold select, find. simpl.
                  now destruct (Hcomp yk) as [e ->].
              + intros l Hl. exists yk. unfold select, find. simpl.
                destruct (Hcomp yk) as [e ->].
                case_eq (compare yk xk).
                * intros m Hm. unfold NoDefault in yD. intro H1; subst ye.
                  apply (yD yk). unfold Raw.MapsTo. constructor. apply Raw.eqke_refl.
                * intros f _. subst yk. now elim (lt_not_eq _ _ l).
                * intros f _. now elim (lt_not_eq _ _ (lt_trans _ _ _ l f)).
          }
      }
      intro H.
      apply (HInd (this a) (this b) (sorted a) (sorted b) (nodefault a) (nodefault b)).
      destruct a as [aL aS aD]. simpl.
      destruct b as [bL bS bD]. simpl. auto.
    Qed.

    Lemma extensionality2 : forall a b, a <> b -> exists i, select a i <> select b i.
    Proof.
      intros a b Hab. destruct (diff_index_p Hab) as [i Hi]. now exists i.
    Qed.

    Definition diff_index : forall a b, a <> b -> key :=
      (fun a b u => proj1_sig (diff_index_p u)).


    Example d : forall a b (u:a <> b), let i := diff_index u in select a i <> select b i.
      unfold diff_index.
      intros.
      destruct (diff_index_p u). simpl. auto.
    Qed.

    Definition diff (a b: farray) : key.
    Proof.
      case_eq (equal a b); intro H.
      - apply default_value.
      - apply (diff_index (notequal_neq H)).
    Defined.

   Lemma select_at_diff: forall a b, a <> b ->
            select a (diff a b) <> select b (diff a b).
   Proof.
     intros a b H. unfold diff.
     assert (equal a b = false).
     apply not_true_iff_false.
     red. intro. apply equal_eq in H0. subst. auto.
     generalize (@notequal_neq a b).
     rewrite H0.
     intro.
     unfold diff_index.
     destruct (diff_index_p (n Logic.eq_refl)). simpl; auto.
   Qed.

  End Classical_extensionality.

End FArray.

Arguments farray _ _ {_} {_}.
Arguments select {_} {_} {_} {_} {_} _ _.
Arguments store {_} {_} {_} {_} {_} {_} {_} {_} _ _ _.
Arguments diff {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _.
Arguments equal {_} {_} {_} {_} {_} {_} {_}  _ _.
Arguments equal_iff_eq {_} {_} {_} {_} {_} {_} {_} _ _.
Arguments read_over_same_write {_} {_} {_} {_} {_} {_} {_} _ _ _ _ _.
Arguments read_over_write {_} {_} {_} {_} {_} {_} {_} _ _ _.
Arguments read_over_other_write {_} {_} {_} {_} {_} {_} _ _ _ _ _.
Arguments extensionality {_} {_} {_} {_} {_} {_} {_} _ _ _.
Arguments extensionality2 {_} {_} {_} {_} {_} {_} {_} {_} {_} _.
Arguments select_at_diff {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _ _.


Declare Scope farray_scope.

Notation "a '[' i ']'" := (select a i) (at level 1, format "a [ i ]") : farray_scope.
Notation "a '[' i '<-' v ']'" := (store a i v)
   (at level 1, format "a [ i  <-  v ]") : farray_scope.


(* Register constants for OCaml access *)
Register FArray.farray as SMTCoq.array.FArray.farray.
Register select as SMTCoq.array.FArray.select.
Register store as SMTCoq.array.FArray.store.
Register diff as SMTCoq.array.FArray.diff.
Register FArray.equal as SMTCoq.array.FArray.equal.



(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

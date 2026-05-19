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


From Stdlib Require Import Bool RelationClasses SetoidList.
Require Import SMT_classes.
From Stdlib Require Import ProofIrrelevance.

(* TODO: remove ProofIrrelevance *)


(** This file formalizes functional arrays with extensionality as specified in
    SMT-LIB 2. It gives realization to axioms that define the SMT-LIB theory of
    arrays. For this, it uses a formalization of maps with the same approach as
    FMapWeakList excepted that constraints on keys and elements are expressed
    through the use of typeclasses instead of functors. *)

Set Implicit Arguments.

(** Raw maps (see FMapWeakList) *)
Module Raw.

  Section Array.

  Variable key : Type.
  Variable elt : Type.
  Variable key_dec : DecType key.
  Variable elt_dec : DecType elt.

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

  Hint Unfold eqk eqke : smtcoq_array.
  Hint Extern 2 (eqke ?a ?b) => split : smtcoq_array.

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

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : smtcoq_array.
  Hint Immediate eqk_sym eqke_sym : smtcoq_array.

  Global Instance eqk_equiv : Equivalence eqk.
  Proof. split; eauto with smtcoq_array. Qed.

  Global Instance eqke_equiv : Equivalence eqke.
  Proof. split; eauto with smtcoq_array. Qed.

  Global Instance eq_equiv : @Equivalence (key * elt) eq.
  Proof.
    split; auto with smtcoq_array.
    unfold Transitive. apply eq_trans.
  Qed.

  (* Additional facts *)

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

  (** * FMAPLIST interface implementation  *)

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

  Lemma empty_NoDup : NoDupA empty.
  Proof.
    unfold empty; auto.
  Qed.

  Lemma MapsTo_inj : forall x e e' l (Hl:NoDupA l),
      MapsTo x e l -> MapsTo x e' l -> e = e'.
    induction l.
    - intros. apply empty_1 in H. contradiction.
    - intros H H0 H10.
      destruct a as (y, v).
      inversion H as [ |[a b] l0 H3 H4 H1]; subst; clear H.
      unfold MapsTo in H0.
      inversion H0 as [y0 l0 H1 H|y0 l0 H H1]; subst; clear H0.
      + inversion H10 as [y10 l10 H11 H12|y10 l10 H12 H11]; subst; clear H10.
        * unfold eqke in H1, H11; simpl in H1, H11; destruct H1; destruct H11; subst; auto.
        * unfold eqke in H1; simpl in H1; destruct H1; subst. elim H3. apply InA_eqke_eqk in H12.
          assert (H100 : eqk (y, e') (y, v)) by reflexivity.
          apply (InA_eqA _ H100 H12).
      + inversion H10 as [y10 l10 H11 H12|y10 l10 H12 H11]; subst; clear H10.
        * unfold eqke in H11; simpl in H11; destruct H11; subst. elim H3. apply InA_eqke_eqk in H.
          assert (H100 : eqk (y, e) (y, v)) by reflexivity.
          apply (InA_eqA _ H100 H).
        * now apply IHl.
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
    | (k',_) :: l => if eq_dec k k' then true else mem k l
    end.

  Lemma mem_1 : forall m (Hm:NoDupA m) x, In x m -> mem x m = true.
  Proof.
    intros m Hm x; generalize Hm; clear Hm.
    induction m; simpl; intros NoDup belong1.
    - inversion belong1. inversion H.
    - destruct a; destruct eq_dec; [reflexivity|]; apply IHm.
      + inversion_clear NoDup; assumption.
      + inversion_clear belong1; inversion_clear H; [elim n; apply H0|exists x0; auto].
  Qed.

  Lemma mem_2 : forall m (Hm:NoDupA m) x, mem x m = true -> In x m.
  Proof.
    intros m Hm x; generalize Hm; clear Hm; unfold In,MapsTo.
    induction m; intros NoDup hyp; try discriminate; simpl in *.
    destruct a, eq_dec.
    + exists e; constructor; split; [assumption|reflexivity].
    + destruct IHm as [e' He'].
    - inversion_clear NoDup; assumption.
    - assumption.
    - exists e'; auto.
  Qed.

  Lemma mem_3 : forall m (Hm:NoDupA m) x, mem x m = false -> ~ In x m.
    intros.
    rewrite <- not_true_iff_false in H.
    unfold not in *. intros; apply H.
    now apply mem_1.
  Qed.

  (** * [find] *)

  Fixpoint find (k:key) (s: farray) {struct s} : option elt :=
    match s with
    | nil => None
    | (k',x)::s' => if eq_dec k k' then Some x else find k s'
    end.

  Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
  Proof.
    intros m x. unfold MapsTo.
    induction m; simpl;intros e' eqfind; inversion eqfind; auto.
    destruct a, eq_dec.
    + constructor; split; simpl; congruence.
    + constructor 2; apply IHm; assumption.
  Qed.

  Lemma find_1 : forall m (Hm:NoDupA m) x e,
      MapsTo x e m -> find x m = Some e.
  Proof.
    intros m; induction m as [|[a e]]; simpl; intros Hdup x e' Hm.
    - inversion Hm.
    - inversion_clear Hdup.
      inversion_clear Hm; destruct eq_dec.
      + destruct H1; simpl in *; congruence.
      + elim n; apply H1.
      + elim H. apply InA_eqA with (x,e'); auto using eqk_equiv, InA_eqke_eqk.
      + apply IHm; auto.
  Qed.

  (* Not part of the exported specifications, used later for [combine]. *)

  Lemma find_eq : forall m (Hm:NoDupA m) x x',
      eq x x' -> find x m = find x' m.
  Proof.
    induction m; simpl; auto; destruct a; intros.
    inversion_clear Hm.
    rewrite (IHm H1 x x'); auto.
    destruct (eq_dec x k) as [|Hneq]; destruct (eq_dec x' k) as [|?Hneq'];
      trivial.
    - elim Hneq'; apply eq_trans with x; auto.
    - elim Hneq; apply eq_trans with x'; auto.
  Qed.

  (** * [add] *)

  Fixpoint add (k : key) (x : elt) (s : farray) {struct s} : farray :=
    match s with
    | nil => (k,x) :: nil
    | (k',y) :: l => if eq_dec k k' then (k,x)::l else (k',y)::add k x l
    end.

  Lemma add_1 : forall m x y e, eq x y -> MapsTo y e (add x e m).
  Proof.
    induction m as [|[a m]]; intros x y e He; simpl in *; auto with smtcoq_array.
    destruct eq_dec; [now auto with smtcoq_array|].
    apply InA_cons_tl, IHm, He.
  Qed.

  Lemma add_2 : forall m x y e e',
      ~ eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    induction m as [|[a m]]; intros x y e e' H Hm; simpl in *.
    - inversion_clear Hm.
    - inversion_clear Hm; destruct eq_dec.
      + elim H; apply eq_trans with a; [auto|apply eq_sym; apply H0].
      + apply InA_cons_hd; apply H0.
      + apply InA_cons_tl; assumption.
      + apply InA_cons_tl; apply IHm; auto.
  Qed.

  Lemma add_3 : forall m x y e e',
      ~ eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    induction m as [|[a m]]; intros x y e e' H Hm.
    - exfalso; inversion_clear Hm.
      + elim H; apply eq_sym; apply H0.
      + inversion_clear H0.
    - simpl in Hm; destruct eq_dec.
      + apply InA_cons_tl; apply InA_cons in Hm; destruct Hm; [|now auto].
        elim H; apply eq_sym; apply H0.
      + apply InA_cons in Hm; destruct Hm.
        * apply InA_cons_hd; auto.
        * apply InA_cons_tl; eapply IHm; eauto.
  Qed.

  Lemma add_3' : forall m x y e e',
      ~ eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m.
  Proof.
    induction m as [|[a m]]; intros x y e e' H Hm; simpl in *.
    - inversion_clear Hm; [|now auto].
      compute in H0; elim H; auto.
    - destruct eq_dec; simpl in *.
      + apply InA_cons in Hm; destruct Hm; [elim H; apply eq_sym; apply H0|].
        apply InA_cons_tl; auto.
      + apply InA_cons in Hm; destruct Hm; [apply InA_cons_hd; auto|].
        apply InA_cons_tl; eapply IHm; eauto.
  Qed.

  Lemma add_NoDup : forall m (Hm:NoDupA m) x e, NoDupA (add x e m).
  Proof.
    induction m.
    - simpl; constructor; auto; red; inversion 1.
    - intros.
      destruct a as (x',e').
      simpl; case (eq_dec x x'); inversion_clear Hm; auto.
      + constructor; auto.
        contradict H.
        apply InA_eqA with (x,e); auto using eqk_equiv.
      + constructor; auto.
        contradict H; apply add_3' with x e; auto.
  Qed.

  (* Not part of the exported specifications, used later for [combine]. *)

  Lemma add_eq : forall m (Hm:NoDupA m) x a e,
      eq x a -> find x (add a e m) = Some e.
  Proof.
    intros.
    apply find_1; auto.
    - apply add_NoDup; auto.
    - apply add_1; auto.
  Qed.

  Lemma add_not_eq : forall m (Hm:NoDupA m) x a e,
      ~eq x a -> find x (add a e m) = find x m.
  Proof.
    intros.
    case_eq (find x m); intros.
    - apply find_1; auto.
      + apply add_NoDup; auto.
      + apply add_2; auto.
        apply find_2; auto.
    - case_eq (find x (add a e m)); intros; auto.
      rewrite <- H0; symmetry.
      apply find_1; auto.
      apply add_3 with a e; auto.
      apply find_2; auto.
  Qed.

  (** * [remove] *)

  Fixpoint remove (k : key) (s : farray) {struct s} : farray :=
    match s with
    | nil => nil
    | (k',x) :: l => if eq_dec k k' then l else (k',x) :: remove k l
    end.

  Lemma remove_1 : forall m (Hm:NoDupA m) x y, eq x y -> ~ In y (remove x m).
  Proof.
    induction m as [|[a m]]; intros Hm x y H; simpl in *.

    - inversion 1; inversion H1.

    - inversion_clear Hm.
      destruct eq_dec.
      + intros [e' ?]; elim H0.
        apply InA_eqA with (y, e').
        * exact eqk_equiv.
        * apply eq_trans with x; [|auto].
          apply eq_sym; auto.
        * apply InA_eqke_eqk; auto.
      + intros [e' H2]; apply InA_cons in H2; destruct H2.
        * elim n; apply eq_trans with y; [auto|apply H2].
        * elim IHm with x y; auto.
          exists e'; auto.
  Qed.

  Lemma remove_2 : forall m (Hm:NoDupA m) x y e,
      ~ eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    induction m as [|[a m]]; intros Hm x y e H He; simpl in *.
    + inversion_clear He.
    + apply InA_cons in He; destruct He, eq_dec.
    - elim H; apply eq_trans with a; [auto|]; apply eq_sym; apply H0.
    - inversion_clear Hm; apply InA_cons_hd; assumption.
    - apply H0.
    - inversion_clear Hm.
      apply InA_cons; destruct (eq_dec y a).
      * elim H1; apply InA_eqA with (y, e); [exact eqk_equiv|assumption|]; apply InA_eqke_eqk; auto.
      * right; apply IHm; auto.
  Qed.

  Lemma remove_3 : forall m (Hm:NoDupA m) x y e,
      MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    induction m as [|[a m]]; intros Hm x y e H; unfold MapsTo; simpl in *; auto.
    destruct eq_dec.
    - apply InA_cons_tl; apply H.
    - inversion_clear Hm; apply InA_cons in H; destruct H; [apply InA_cons_hd; auto|].
      apply InA_cons_tl; apply IHm with x; auto.
  Qed.

  Lemma remove_3' : forall m (Hm:NoDupA m) x y e,
      InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
  Proof.
    induction m as [|[a m]]; intros Hm x y e H; unfold MapsTo; simpl in *.
    - inversion_clear H.
    - destruct eq_dec.
      + apply InA_cons_tl; auto.
      + apply InA_cons in H; destruct H; [apply InA_cons_hd; auto|].
        inversion_clear Hm; apply InA_cons_tl; apply IHm with x; auto.
  Qed.

  Lemma remove_NoDup : forall m (Hm:NoDupA m) x, NoDupA (remove x m).
  Proof.
    induction m.
    - simpl; intuition.
    - intros.
      inversion_clear Hm.
      destruct a as (x',e').
      simpl; case (eq_dec x x'); auto.
      constructor; auto.
      contradict H; apply remove_3' with x; auto.
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

  Lemma elements_3w : forall m (Hm:NoDupA m), NoDupA (elements m).
  Proof.
    auto with smtcoq_array.
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

  Definition check (cmp : elt -> elt -> bool)(k:key)(e:elt)(m': farray) :=
    match find k m' with
    | None => false
    | Some e' => cmp e e'
    end.

  Definition submap (cmp : elt -> elt -> bool)(m m' : farray) : bool :=
    fold (fun k e b => andb (check cmp k e m') b) m true.

  Definition equal (cmp : elt -> elt -> bool)(m m' : farray) : bool :=
    andb (submap cmp m m') (submap (fun e' e => cmp e e') m' m).

  Definition Submap cmp m m' :=
    (forall k, In k m -> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

  Definition Equivb cmp m m' :=
    (forall k, In k m <-> In k m') /\
      (forall k e e', MapsTo k e m -> MapsTo k e' m' -> cmp e e' = true).

  Lemma submap_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
      Submap cmp m m' -> submap cmp m m' = true.
  Proof.
    unfold Submap, submap.
    induction m.
    - simpl; auto.
    - destruct a; simpl; intros.
      destruct H.
      inversion_clear Hm.
      assert (H3 : In k m').
      + apply H; exists e; auto with smtcoq_array.
      + destruct H3 as (e', H3).
        unfold check at 2; rewrite (find_1 Hm' H3).
        rewrite (H0 k); simpl; auto with smtcoq_array.
        eapply IHm; auto.
        split; intuition.
        * apply H.
          destruct H5 as (e'',H5); exists e''; auto with smtcoq_array.
        * apply H0 with k0; auto with smtcoq_array.
  Qed.

  Lemma submap_2 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
      submap cmp m m' = true -> Submap cmp m m'.
  Proof.
    unfold Submap, submap.
    induction m.
    - simpl; auto.
      intuition.
      + destruct H0; inversion H0.
      + inversion H0.

    - destruct a; simpl; intros.
      inversion_clear Hm.
      rewrite andb_b_true in H.
      assert (check cmp k e m' = true).
      + clear H1 H0 Hm' IHm.
        set (b:=check cmp k e m') in *.
        generalize H; clear H; generalize b; clear b.
        induction m; simpl; auto; intros.
        destruct a; simpl in *.
        destruct (andb_prop _ _ (IHm _ H)); auto.
      + rewrite H2 in H.
        destruct (IHm H1 m' Hm' cmp H); auto.
        unfold check in H2.
        case_eq (find k m'); [intros e' H5 | intros H5];
          rewrite H5 in H2; try discriminate.
        split; intros.
        * destruct H6 as (e0,H6); inversion_clear H6.
          -- compute in H7; destruct H7; subst.
             exists e'.
             apply MapsTo_eq with k; auto.
             apply find_2; auto.
          -- apply H3.
             exists e0; auto.
        * inversion_clear H6.
          -- compute in H8; destruct H8; subst.
             rewrite (find_1 Hm' (MapsTo_eq eq_refl H7)) in H5; congruence.
          -- apply H4 with k0; auto.
  Qed.

  (** Specification of [equal] *)

  Lemma equal_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m') cmp,
      Equivb cmp m m' -> equal cmp m m' = true.
  Proof.
    unfold Equivb, equal.
    intuition.
    apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
  Qed.

  Lemma equal_2 : forall m (Hm:NoDupA m) m' (Hm':NoDupA m') cmp,
      equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    unfold Equivb, equal.
    intros.
    destruct (andb_prop _ _ H); clear H.
    generalize (submap_2 Hm Hm' _ H0).
    generalize (submap_2 Hm' Hm _ H1).
    firstorder.
  Qed.

  (* TODO ? map and mapi *)

  End Array.

End Raw.


(** * Functional Arrays *)

Section FArray.

  Variable key : Type.
  Variable elt : Type.
  Variable key_dec : DecType key.
  Variable elt_dec : DecType elt.
  Variable key_inh : Inhabited key. (* TODO: seems useless *)
  Variable elt_inh : Inhabited elt.

  Set Implicit Arguments.

  Definition NoDefault l := forall k:key, ~ Raw.MapsTo k default_value l.

  Record farray :=
    {this :> Raw.farray key elt;
     NoDup : NoDupA (@Raw.eqk _ _) this;
     nodefault : NoDefault this
    }.

  Lemma empty_nodefault : NoDefault (Raw.empty key elt).
    unfold NoDefault.
    intros.
    apply Raw.empty_1.
  Qed.


  (** Boolean comparison over elements *)
  Definition cmp (x y:elt) := if eq_dec x y then true else false.

  Lemma cmp_refl : forall e, cmp e e = true.
  Proof. intro e. unfold cmp. now case (eq_dec e e). Qed.


  Lemma remove_nodefault : forall l (Hd:NoDefault l) (Hs:NoDupA (@Raw.eqk _ _) l) x ,
      NoDefault (Raw.remove key_dec x l).
  Proof.
    intros.
    unfold NoDefault. intros.
    unfold not. intro.
    apply Raw.remove_3 in H; auto.
    now apply Hd in H.
  Qed.

  Definition raw_add_nodefault (k:key) (x:elt) (l:Raw.farray key elt) :=
    if cmp x default_value then
      if Raw.mem key_dec k l then Raw.remove key_dec k l
      else l
    else Raw.add key_dec k x l.

  Lemma add_NoDup : forall l (Hs:NoDupA (@Raw.eqk _ _) l) x e,
      NoDupA (@Raw.eqk _ _) (raw_add_nodefault x e l).
  Proof.
    intros.
    unfold raw_add_nodefault.
    case (cmp e default_value); auto.
    case (Raw.mem key_dec x l); auto.
    apply Raw.remove_NoDup; auto.
    apply Raw.add_NoDup; auto.
  Qed.

  Lemma add_nodefault : forall l (Hd:NoDefault l) (Hs:NoDupA (@Raw.eqk _ _) l) x e,
      NoDefault (raw_add_nodefault x e l).
  Proof.
    intros l Hd Hs x e.
    unfold raw_add_nodefault.
    case_eq (cmp e default_value); intro H; auto.
    - case_eq (Raw.mem key_dec x l); intro H0; auto.
      apply remove_nodefault; auto.
    - unfold NoDefault; intros k.
      assert (H0: e <> default_value).
      { intro H1. subst e. rewrite cmp_refl in H. discriminate. }
      destruct (eq_dec k x) as [e0|n].
      + symmetry in e0.
        apply (Raw.add_1 key_dec l e) in e0.
        unfold not; intro.
        specialize (Raw.add_NoDup key_dec Hs x e).
        intro Hsadd.
        specialize (Raw.MapsTo_inj Hsadd e0 H1).
        intro. contradiction.
      + unfold not; intro.
        assert (x <> k). unfold not in *. intro. apply n. symmetry; auto.
        specialize (Raw.add_3 key_dec l e H2 H1).
        intro. now apply Hd in H3.
  Qed.

  Definition empty : farray :=
    Build_farray (Raw.empty_NoDup key elt) empty_nodefault.

  Definition is_empty m : bool := Raw.is_empty m.(this).

  Definition add x e m : farray :=
    Build_farray (add_NoDup m.(NoDup) x e)
                (add_nodefault m.(nodefault) m.(NoDup) x e).

  Definition find x m : option elt := Raw.find key_dec x m.(this).

  Definition remove x m : farray :=
    Build_farray (Raw.remove_NoDup key_dec m.(NoDup) x) (remove_nodefault m.(nodefault) m.(NoDup) x).

  Definition mem x m : bool := Raw.mem key_dec x m.(this).
  Definition elements m : list (key*elt) := Raw.elements m.(this).
  Definition cardinal m := length m.(this).
  Definition fold (A:Type)(f:key->elt->A->A) m (i:A) : A :=
    Raw.fold f m.(this) i.
  Definition equal m m' : bool := Raw.equal key_dec cmp m.(this) m'.(this).

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

  Lemma MapsTo_1 : forall m x y e, eq x y -> MapsTo x e m -> MapsTo y e m.
  Proof. intros m. apply Raw.MapsTo_eq. Qed.

  Lemma mem_1 : forall m x, In x m -> mem x m = true.
  Proof. intros m; apply (Raw.mem_1); auto. apply m.(NoDup). Qed.
  Lemma mem_2 : forall m x, mem x m = true -> In x m.
  Proof. intros m; apply (Raw.mem_2); auto. apply m.(NoDup). Qed.

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
    - elim H. unfold cmp in H1.
      case_eq (eq_dec e default_value); auto.
      intros H2 H3. rewrite H3 in H1. discriminate.
    - apply Raw.add_1; auto.
  Qed.

  Lemma add_2 : forall m x y e e', ~ eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros.
    unfold add, raw_add_nodefault, MapsTo. simpl.
    case_eq (cmp e' default_value); intro; auto.
    case_eq (Raw.mem key_dec x m); intro; auto.
    apply (Raw.remove_2 _ m.(NoDup)); auto.
    apply Raw.add_2; auto.
  Qed.

  Lemma add_3 : forall m x y e e', ~ eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    unfold add, raw_add_nodefault, MapsTo. simpl.
    intros m x y e e'.
    case_eq (cmp e' default_value); intro; auto.
    case_eq (Raw.mem key_dec x m); intro; auto.
    intro. apply (Raw.remove_3 _ m.(NoDup)); auto.
    apply Raw.add_3; auto.
  Qed.

  Lemma remove_1 : forall m x y, eq x y -> ~ In y (remove x m).
  Proof. intros m; apply Raw.remove_1; auto. apply m.(NoDup). Qed.

  Lemma remove_2 : forall m x y e, ~ eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof. intros m; apply Raw.remove_2; auto. apply m.(NoDup). Qed.

  Lemma remove_3 : forall m x y e, MapsTo y e (remove x m) -> MapsTo y e m.
  Proof. intros m; apply Raw.remove_3; auto. apply m.(NoDup). Qed.

  Lemma find_1 : forall m x e, MapsTo x e m -> find x m = Some e.
  Proof. intros m; apply Raw.find_1; auto. apply m.(NoDup). Qed.

  Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
  Proof. intros m; apply Raw.find_2; auto. Qed.

  Lemma elements_1 : forall m x e, MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
  Proof. intros m; apply Raw.elements_1. Qed.

  Lemma elements_2 : forall m x e, InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.
  Proof. intros m; apply Raw.elements_2. Qed.

  Lemma elements_3w : forall m, NoDupA eq_key (elements m).
  Proof. intros m; apply (Raw.elements_3w m.(NoDup)). Qed.

  Lemma cardinal_1 : forall m, cardinal m = length (elements m).
  Proof. intros; reflexivity. Qed.

  Lemma fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof. intros m; apply Raw.fold_1. Qed.

  Lemma equal_1 : forall m m', Equivb m m' -> equal m m' = true.
  Proof. intros m m'; apply Raw.equal_1; auto. apply m.(NoDup). apply m'.(NoDup). Qed.

  Lemma equal_2 : forall m m', equal m m' = true -> Equivb m m'.
  Proof. intros m m'; apply Raw.equal_2; auto. apply m.(NoDup). apply m'.(NoDup). Qed.

  (* Lemma nodefault_tail : forall x m, NoDefault (x :: m) -> NoDefault m. *)
  (*   unfold NoDefault. unfold not in *. intros. *)
  (*   apply (H k). unfold Raw.MapsTo. apply InA_cons_tl. apply H0. *)
  (* Qed. *)

  (* (* Lemma raw_equal_eq : *) *)
  (* (*   forall a (Ha: NoDupA (@Raw.eqk _ _) a) b (Hb: NoDupA (@Raw.eqk _ _) b), *) *)
  (* (*     Raw.equal key_dec cmp a b = true -> a = b. *) *)
  (* (* Proof. *) *)
  (* (*   induction a as [ |a a0 IHa]; intros Ha b Hb H. *) *)
  (* (*   - simpl in H. *) *)
  (* (*     case b in *; auto. *) *)
  (* (*     apply (Raw.equal_2 _ elt_dec Ha Hb) in H. *) *)
  (* (*     destruct p as [p1 p2]. *) *)
  (* (*     unfold Raw.Equivb in H. destruct H as [H _]. destruct (H p1) as [_ H2]. *) *)
  (* (*     assert (H1:Raw.In p1 ((p1, p2) :: b)) by (exists p2; constructor; split; reflexivity). *) *)
  (* (*     assert (H3 := H2 H1). destruct H3 as [e H3]. inversion H3. *) *)
  (* (*   - destruct a as (xa, ea). *) *)
  (* (*     simpl in H. *) *)
  (* (*     case b in *. *) *)
  (* (*     + apply (Raw.equal_2 _ elt_dec Ha Hb) in H. *) *)
  (* (*       unfold Raw.Equivb in H. destruct H as [H _]. destruct (H xa) as [H2 _]. *) *)
  (* (*       assert (H1:Raw.In xa ((xa, ea) :: a0)) by (exists ea; constructor; split; reflexivity). *) *)
  (* (*       assert (H3 := H2 H1). destruct H3 as [e H3]. inversion H3. *) *)
  (* (*     + destruct p as (xb, eb). *) *)
  (* (*       destruct (eq_dec xa xb); auto; try (now contradict H). *) *)
  (* (*       rewrite andb_true_iff in H. destruct H as [H H0]. *) *)
  (* (*       unfold cmp in H. rewrite compare2eqb_spec in H. *) *)
  (* (*       subst. apply f_equal. *) *)
  (* (*       apply IHa; auto. *) *)
  (* (*       * now inversion Ha. *) *)
  (* (*       * now inversion Hb. *) *)
  (* (* Qed. *) *)

  (* (* Lemma eq_equal : forall m m', eq m m' <-> equal m m' = true. *) *)
  (* (* Proof. *) *)
  (* (*   intros (l,Hl,Hd); induction l as [ |a l IHl]. *) *)
  (* (*   - intros (l',Hl',Hd'); unfold eq; simpl. *) *)
  (* (*     destruct l'; unfold equal; simpl; intuition auto with *. *) *)
  (* (*   - intros (l',Hl',Hd'); unfold eq. *) *)
  (* (*     destruct l' as [ |p l']. *) *)
  (* (*     + destruct a; unfold equal; simpl; intuition auto with *. *) *)
  (* (*     + destruct a as (x,e). *) *)
  (* (*       destruct p as (x',e'). *) *)
  (* (*       unfold equal; simpl. *) *)
  (* (*       destruct (compare x x') as [Hlt|Heq|Hlt]; simpl; [intuition auto with *| |intuition auto with *]. *) *)
  (* (*       split. *) *)
  (* (*       * intros [H0 H1]. *) *)
  (* (*         unfold cmp, compare2eqb at 1. *) *)
  (* (*         case (compare e e'); *) *)
  (* (*           subst; intro HH; try (apply lt_not_eq in HH; now contradict HH); *) *)
  (* (*             clear HH; simpl. *) *)
  (* (*         inversion_clear Hl. *) *)
  (* (*         inversion_clear Hl'. *) *)
  (* (*         apply nodefault_tail in Hd. *) *)
  (* (*         apply nodefault_tail in Hd'. *) *)
  (* (*         destruct (IHl H Hd (Build_farray H2 Hd')). *) *)
  (* (*         unfold equal, eq in H5; simpl in H5; auto. *) *)
  (* (*       * { intro H. destruct (andb_prop _ _ H) as [H0 H1]; clear H. split. *) *)
  (* (*           - generalize H0; unfold cmp, compare2eqb. *) *)
  (* (*             case (compare e e'); *) *)
  (* (*               subst; intro HH; try (apply lt_not_eq in HH; now contradict HH); *) *)
  (* (*                 auto; intro; discriminate. *) *)
  (* (*           - inversion_clear Hl. *) *)
  (* (*             inversion_clear Hl'. *) *)
  (* (*             apply nodefault_tail in Hd. *) *)
  (* (*             apply nodefault_tail in Hd'. *) *)
  (* (*             destruct (IHl H Hd (Build_farray H3 Hd')). *) *)
  (* (*             unfold equal, eq in H6; simpl in H6; auto. *) *)
  (* (*         } *) *)
  (* (* Qed. *) *)

  (* Lemma eq_1 : forall m m', Equivb m m' -> eq m m'. *)
  (* Proof. *)
  (*   intros. *)
  (*   generalize (@equal_1 m m'). *)
  (*   generalize (@eq_equal m m'). *)
  (*   intuition. *)
  (* Qed. *)

  (* Lemma eq_2 : forall m m', eq m m' -> Equivb m m'. *)
  (* Proof. *)
  (*   intros. *)
  (*   generalize (@equal_2 m m'). *)
  (*   generalize (@eq_equal m m'). *)
  (*   intuition. *)
  (* Qed. *)

  (* Lemma eqfarray_refl : forall m : farray, eq m m. *)
  (* Proof. *)
  (*   intros (m,Hm,Hd); induction m; unfold eq; simpl; auto. *)
  (*   destruct a. *)
  (*   destruct (compare k k) as [Hlt|Heq|Hlt]; auto. *)
  (*   apply lt_not_eq in Hlt. auto. *)
  (*   split. *)
  (*   apply eq_refl. *)
  (*   inversion_clear Hm. *)
  (*   apply nodefault_tail in Hd. *)
  (*   apply (IHm H Hd). *)
  (*   apply lt_not_eq in Hlt. auto. *)
  (* Qed. *)

  (* Lemma eqfarray_sym : forall m1 m2 : farray, eq m1 m2 -> eq m2 m1. *)
  (* Proof. *)
  (*   intros (m,Hm,Hd); induction m; *)
  (*     intros (m',Hm',Hd'); destruct m'; unfold eq; simpl; *)
  (*       try destruct a as (x,e); try destruct p as (x',e'); auto. *)
  (*   destruct (compare x x')  as [Hlt|Heq|Hlt]; try easy. *)
  (*   inversion_clear Hm; inversion_clear Hm'. *)
  (*   apply nodefault_tail in Hd. apply nodefault_tail in Hd'. *)
  (*   intro. destruct H3. *)
  (*   subst. *)
  (*   case (compare x' x'); *)
  (*   subst; intro HH; try (apply lt_not_eq in HH; now contradict HH). *)
  (*   split; auto. *)
  (*   apply (IHm H Hd (Build_farray H1 Hd')); auto. *)
  (* Qed. *)

  (* Lemma eqfarray_trans : forall m1 m2 m3 : farray, eq m1 m2 -> eq m2 m3 -> eq m1 m3. *)
  (* Proof. *)
  (*   intros (m1,Hm1,Hd1); induction m1; *)
  (*     intros (m2,Hm2,Hd2); destruct m2; *)
  (*       intros (m3,Hm3,Hd3); destruct m3; unfold eq; simpl; *)
  (*         try destruct a as (x,e); *)
  (*         try destruct p as (x',e'); *)
  (*         try destruct p0 as (x'',e''); try contradiction; auto. *)
  (*   destruct (compare x x') as [Hlt|Heq|Hlt]; *)
  (*     destruct (compare x' x'') as [Hlt'|Heq'|Hlt']; try easy. *)
  (*   intros; destruct H, H0;  subst. *)
  (*   case (compare x'' x''); *)
  (*   subst; intro HH; try (apply lt_not_eq in HH; now contradict HH). *)
  (*   split; auto. *)
  (*   inversion_clear Hm1; inversion_clear Hm2; inversion_clear Hm3. *)
  (*   apply nodefault_tail in Hd1. *)
  (*   apply nodefault_tail in Hd2. *)
  (*   apply nodefault_tail in Hd3. *)
  (*   apply (IHm1 H Hd1 (Build_farray H3 Hd2) (Build_farray H5 Hd3)); intuition. *)
  (* Qed. *)

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

  Lemma raw_remove_no_mem m :
    NoDupA (Raw.eqk (elt:=elt)) m ->
    forall x, Raw.mem key_dec x m = false ->
              m = Raw.remove key_dec x m.
  Proof.
    induction m as [ |[k v] m IHm]; try reflexivity.
    intros H1. inversion H1 as [ |x l H2 H3 H]; subst; clear H1.
    intro x. simpl. case (eq_dec x k); try discriminate.
    intros H4 H5. now rewrite <- (IHm H3 x H5).
  Qed.


  Lemma raw_add_d_rem : forall m (Hm: NoDupA (@Raw.eqk _ _) m) x,
      raw_add_nodefault x default_value m = Raw.remove key_dec x m.
  Proof.
    intros m Hm x.
    unfold raw_add_nodefault.
    rewrite cmp_refl.
    case_eq (Raw.mem key_dec x m); intro H; auto.
    now apply raw_remove_no_mem.
  Qed.

  Lemma add_d_rem : forall m x, add x default_value m = remove x m.
    intros.
    unfold add, remove.
    specialize (raw_add_d_rem m.(NoDup) x). intro.
    generalize (add_NoDup m.(NoDup) x default_value).
    generalize (add_nodefault (nodefault m) (NoDup m) x default_value).
    generalize (Raw.remove_NoDup key_dec (NoDup m) x).
    generalize (remove_nodefault (nodefault m) (NoDup m) x).
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
    contradict H1.
    apply remove_1; auto.
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
    - subst. now case (eq_dec e' e').
    - now revert H1; case (eq_dec e e'); try discriminate.
  Qed.

  (* (** Composition of the last two results: relation between [Equal] *)
  (*   and [Equivb]. *) *)

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
    intros a i j v ->.
    unfold select, store.
    case_eq (cmp v default_value); intro H; auto.
    - unfold cmp in H.
      case (eq_dec v default_value) as [->| ]; [clear H|discriminate H].
      rewrite add_eq_d; auto.
    - assert (H0: v <> default_value).
      { unfold cmp in H.
        case (eq_dec v default_value) as [->|H1]; [discriminate H|auto]. }
      rewrite (add_eq_o a (eq_refl _) H0). auto.
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

 (*  Lemma equal_eq : forall a b, equal a b = true -> a = b. *)
 (*  Proof. intros. apply eq_equal in H. *)
 (*    destruct a as (a, asort, anodef), b as (b, bsort, bnodef). *)
 (*    unfold eq in H. *)
 (*    revert b bsort bnodef H. *)
 (*    induction a; intros; destruct b. *)
 (*    rewrite (proof_irrelevance _ asort bsort). *)
 (*    rewrite (proof_irrelevance _ anodef bnodef). *)
 (*    auto. *)
 (*    simpl in H. now contradict H. *)
 (*    simpl in H. destruct a; now contradict H. *)
 (*    simpl in H. destruct a, p. *)
 (*    destruct (compare k k0); auto; try (now contradict H). *)
 (*    destruct H. *)
 (*    subst. *)
 (*    inversion_clear asort. *)
 (*    inversion_clear bsort. *)
 (*    specialize (nodefault_tail bnodef). *)
 (*    specialize (nodefault_tail anodef). intros. *)
 (*    specialize (IHa H H4 b H2 H5 H0). *)
 (*    inversion IHa. subst. *)
 (*    rewrite (proof_irrelevance _ asort bsort). *)
 (*    rewrite (proof_irrelevance _ anodef bnodef). *)
 (*    reflexivity. *)
 (* Qed. *)

  (* Lemma notequal_neq : forall a b, equal a b = false -> a <> b. *)
  (*   intros. *)
  (*   red. intros. *)
  (*   apply not_true_iff_false in H. *)
  (*   unfold not in *. intros. *)
  (*   apply H. rewrite H0. *)
  (*   apply eq_equal. apply eqfarray_refl. *)
  (* Qed. *)

  (* Lemma extensionality : forall a b, (forall i, select a i = select b i) -> a = b. *)
  (* Proof. *)
  (*   intros; apply equal_eq; apply extensionality_eqb; auto. *)
  (* Qed. *)

  (* Lemma equal_refl: forall a, equal a a = true. *)
  (* Proof. intros; apply eq_equal; apply eq_list_refl. Qed. *)

  (* Lemma equal_iff_eq : forall a b, equal a b = true <-> a = b. *)
  (* Proof. *)
  (*   intros a b. *)
  (*   split. *)
  (*   - apply equal_eq. *)
  (*   - intro; subst. apply equal_refl. *)
  (* Qed. *)

  (* Section Classical_extensionality. *)

  (*   Lemma lt_select_default i xs xsS xsD : (forall xe, HdRel lt (i, xe) xs) -> *)
  (*     select {| this := xs; sorted := xsS; nodefault := xsD |} i = default_value. *)
  (*   Proof. *)
  (*     intro H1. unfold select, find. simpl. *)
  (*     destruct xs as [ |[xk xe] xs]; auto. *)
  (*     simpl. assert (H2:=H1 xe). inversion H2 as [ |b l H0 H]; subst. *)
  (*     case_eq (compare i xk); auto. *)
  (*     - intros e He. subst i. now elim (lt_not_eq _ _ H0). *)
  (*     - intros l _. simpl in H0. unfold Raw.ltk in H0. simpl in H0. *)
  (*       now elim (lt_not_eq _ _ (lt_trans _ _ _ H0 l)). *)
  (*   Qed. *)

  (*   Lemma HdRelElt (xk:key) (ye:elt) ys : HdRel lt (xk, ye) ys -> forall ye', HdRel lt (xk, ye') ys. *)
  (*   Proof. *)
  (*     induction ys as [ |[yk yee] ys IHys]; auto. *)
  (*     simpl. intros H ye'. inversion H as [ |b l H1 H0]; subst. *)
  (*     now constructor. *)
  (*   Qed. *)

  (*   Lemma diff_index_p : forall a b, a <> b -> {i | select a i <> select b i}. *)
  (*   Proof. *)
  (*     intros a b. *)
  (*     assert (Hcomp:forall (k:key), exists e, compare k k = EQ e). *)
  (*     { *)
  (*       intro k. *)
  (*       case_eq (compare k k); try (intro H; now elim (lt_not_eq _ _ H)). *)
  (*       intros e He. now exists e. *)
  (*     } *)
  (*     assert (HInd: forall x y (xS:Sorted _ x) (yS:Sorted _ y) (xD:NoDefault x) (yD:NoDefault y), *)
  (*                let a := Build_farray xS xD in *)
  (*                let b := Build_farray yS yD in *)
  (*                a <> b -> {i : key | select a i <> select b i}). *)
  (*     { *)
  (*       clear a b. intros x y. *)
  (*       case_eq (list_eq_dec (@eq_dec _ (Raw.ke_dec key_dec elt_dec)) x y). *)
  (*       - intros e He. subst x. intros xS yS xD yD a b. subst a b. *)
  (*         rewrite (proof_irrelevance _ xS yS),  (proof_irrelevance _ xD yD). *)
  (*         intro H. elim H. reflexivity. *)
  (*       - intros n _ xS yS xD yD a b _. subst a b. *)
  (*         revert x y n xS yS xD yD. *)
  (*         { *)
  (*           induction x as [ |[xk xe] xs IHxs]; intros [ |[yk ye] ys]. *)
  (*           - intro H; now elim H. *)
  (*           - intros _ xS yS xD yD. exists yk. *)
  (*             unfold select, find. simpl. destruct (Hcomp yk) as [e ->]. *)
  (*             unfold NoDefault in yD. intro H. subst ye. elim (yD yk). unfold Raw.MapsTo. *)
  (*             constructor. apply Raw.eqke_refl. *)
  (*           - intros _ xS yS xD yD. exists xk. *)
  (*             unfold select, find. simpl. destruct (Hcomp xk) as [e ->]. *)
  (*             unfold NoDefault in xD. intro H. subst xe. elim (xD xk). unfold Raw.MapsTo. *)
  (*             constructor. apply Raw.eqke_refl. *)
  (*           - intros H xS yS xD yD. case_eq (compare xk yk). *)
  (*             + intros l Hl. exists xk. unfold select, find. simpl. *)
  (*               destruct (Hcomp xk) as [e ->]. rewrite Hl. *)
  (*               unfold NoDefault in xD. intro H1; subst xe. *)
  (*               apply (xD xk). unfold Raw.MapsTo. constructor. apply Raw.eqke_refl. *)
  (*             + intros e _. subst xk. case_eq (eq_dec xe ye). *)
  (*               * intros e _. subst ye. assert (H1:xs <> ys) *)
  (*                   by (intro H1; rewrite H1 in H; now apply H). *)
  (*                 assert (xsS : Sorted (Raw.ltk key_ord) xs) by now inversion xS. *)
  (*                 assert (ysS : Sorted (Raw.ltk key_ord) ys) by now inversion yS. *)
  (*                 assert (xsD:NoDefault xs) by exact (nodefault_tail xD). *)
  (*                 assert (ysD:NoDefault ys) by exact (nodefault_tail yD). *)
  (*                 destruct (IHxs _ H1 xsS ysS xsD ysD) as [i Hi]. *)
  (*                 { *)
  (*                   case_eq (compare i yk). *)
  (*                   - intros l Hl. *)
  (*                     rewrite (lt_select_default xsS xsD) in Hi. *)
  (*                     + rewrite (lt_select_default ysS ysD) in Hi. *)
  (*                       * now elim Hi. *)
  (*                       * *)
  (*                         { *)
  (*                           intro xe0. *)
  (*                           apply (InfA_ltA _ (y:=(yk, xe))). *)
  (*                           - simpl. unfold Raw.ltk. simpl. auto. *)
  (*                           - now inversion yS. *)
  (*                         } *)
  (*                     + intro xe0. *)
  (*                       apply (InfA_ltA _ (y:=(yk, xe))). *)
  (*                       * simpl. unfold Raw.ltk. simpl. auto. *)
  (*                       * now inversion xS. *)
  (*                   - intros l Hl. *)
  (*                     rewrite (lt_select_default xsS xsD) in Hi. *)
  (*                     + rewrite (lt_select_default ysS ysD) in Hi. *)
  (*                       * now elim Hi. *)
  (*                       * intro xe0. *)
  (*                         inversion yS as [ |a l0 H3 H4 H0]; subst. *)
  (*                         apply (HdRelElt H4). *)
  (*                     + intro xe0. *)
  (*                       inversion xS as [ |a l0 H3 H4 H0]; subst. *)
  (*                       apply (HdRelElt H4). *)
  (*                   - intros l Hl. exists i. unfold select, find. simpl. now rewrite Hl. *)
  (*                 } *)
  (*               * intros n Hn. exists yk. unfold select, find. simpl. *)
  (*                 now destruct (Hcomp yk) as [e ->]. *)
  (*             + intros l Hl. exists yk. unfold select, find. simpl. *)
  (*               destruct (Hcomp yk) as [e ->]. *)
  (*               case_eq (compare yk xk). *)
  (*               * intros m Hm. unfold NoDefault in yD. intro H1; subst ye. *)
  (*                 apply (yD yk). unfold Raw.MapsTo. constructor. apply Raw.eqke_refl. *)
  (*               * intros f _. subst yk. now elim (lt_not_eq _ _ l). *)
  (*               * intros f _. now elim (lt_not_eq _ _ (lt_trans _ _ _ l f)). *)
  (*         } *)
  (*     } *)
  (*     intro H. *)
  (*     apply (HInd (this a) (this b) (sorted a) (sorted b) (nodefault a) (nodefault b)). *)
  (*     destruct a as [aL aS aD]. simpl. *)
  (*     destruct b as [bL bS bD]. simpl. auto. *)
  (*   Qed. *)

  (*   Lemma extensionality2 : forall a b, a <> b -> exists i, select a i <> select b i. *)
  (*   Proof. *)
  (*     intros a b Hab. destruct (diff_index_p Hab) as [i Hi]. now exists i. *)
  (*   Qed. *)

  (*   Definition diff_index : forall a b, a <> b -> key := *)
  (*     (fun a b u => proj1_sig (diff_index_p u)). *)


  (*   Example d : forall a b (u:a <> b), let i := diff_index u in select a i <> select b i. *)
  (*     unfold diff_index. *)
  (*     intros. *)
  (*     destruct (diff_index_p u). simpl. auto. *)
  (*   Qed. *)

  (*   Definition diff (a b: farray) : key. *)
  (*   Proof. *)
  (*     case_eq (equal a b); intro H. *)
  (*     - apply default_value. *)
  (*     - apply (diff_index (notequal_neq H)). *)
  (*   Defined. *)

  (*  Lemma select_at_diff: forall a b, a <> b -> *)
  (*           select a (diff a b) <> select b (diff a b). *)
  (*  Proof. *)
  (*    intros a b H. unfold diff. *)
  (*    assert (equal a b = false). *)
  (*    apply not_true_iff_false. *)
  (*    red. intro. apply equal_eq in H0. subst. auto. *)
  (*    generalize (@notequal_neq a b). *)
  (*    rewrite H0. *)
  (*    intro. *)
  (*    unfold diff_index. *)
  (*    destruct (diff_index_p (n Logic.eq_refl)). simpl; auto. *)
  (*  Qed. *)

  (* End Classical_extensionality. *)

End FArray.

Arguments farray _ _ {_}.
Arguments select {_} {_} {_} {_} _ _.
Arguments store {_} {_} {_} {_} {_} _ _ _.
(* Arguments diff {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _. *)
Arguments equal {_} {_} {_} {_} {_}  _ _.
(* Arguments equal_iff_eq {_} {_} {_} {_} {_} {_} {_} _ _. *)
Arguments read_over_same_write {_} {_} {_} {_} {_} _ _ _ _ _.
Arguments read_over_write {_} {_} {_} {_} {_} _ _ _.
Arguments read_over_other_write {_} {_} {_} {_} {_} _ _ _ _ _.
(* Arguments extensionality {_} {_} {_} {_} {_} {_} {_} _ _ _. *)
(* Arguments extensionality2 {_} {_} {_} {_} {_} {_} {_} {_} {_} _. *)
(* Arguments select_at_diff {_} {_} {_} {_} {_} {_} {_} {_} {_} _ _ _. *)


Declare Scope farray_scope.

Notation "a '[' i ']'" := (select a i) (at level 1, format "a [ i ]") : farray_scope.
Notation "a '[' i '<-' v ']'" := (store a i v)
   (at level 1, format "a [ i  <-  v ]") : farray_scope.


(* Register constants for OCaml access *)
Register FArray.farray as SMTCoq.array.FArray.farray.
Register select as SMTCoq.array.FArray.select.
Register store as SMTCoq.array.FArray.store.
(* Register diff as SMTCoq.array.FArray.diff. *)
Register FArray.equal as SMTCoq.array.FArray.equal.

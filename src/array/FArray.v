Require Import SetoidList Bool.
(* Require Import List Bool NArith Psatz Int63. *)

Section Array.

  Class DecType T := {
    eq_refl : forall x : T, x = x;
    eq_sym : forall x y : T, x = y -> y = x;
    eq_trans : forall x y z : T, x = y -> y = z -> x = z;
    eq_dec : forall x y : T, { x = y } + { x <> y }
  }.
  
  Hint Immediate eq_sym.
  Hint Resolve eq_refl eq_trans.
    
  Variable key : Type.
  Variable elt : Type.
  Variable key_dec : DecType key.
  Variable elt_dec : DecType elt.

  Set Implicit Arguments.


  Definition eqb_key (x y : key) : bool := if eq_dec x y then true else false.
  Definition eqb_elt (x y : elt) : bool := if eq_dec x y then true else false.

  Lemma eqb_key_eq x y : eqb_key x y = true <-> x = y.
  Proof. unfold eqb_key. case (eq_dec x y); easy. Qed.

  Lemma eqb_elt_eq x y : eqb_elt x y = true <-> x = y.
  Proof. unfold eqb_elt. case (eq_dec x y); easy. Qed.

  Hint Immediate eqb_key_eq eqb_elt_eq.
  
  Definition farray := list (key * elt).

  Definition eqk (a b : (key * elt)) := fst a = fst b.
  Definition eqe (a b : (key * elt)) := snd a = snd b.
  Definition eqke (a b : (key * elt)) := fst a = fst b /\ snd a = snd b.

  Hint Unfold eqk eqke.
  Hint Extern 2 (eqke ?a ?b) => split.

  
   (* eqke is stricter than eqk *)

   Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
   Proof.
     unfold eqk, eqke; intuition.
   Qed.

  (* eqk, eqke are equalities *)

  Lemma eqk_refl : forall e, eqk e e.
  Proof. auto. Qed.

  Lemma eqke_refl : forall e, eqke e e.
  Proof. auto. Qed.

  Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
  Proof. auto. Qed.

  Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
  Proof. unfold eqke; intuition. Qed.

  Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
  Proof. eauto. Qed.

  Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
  Proof.
    unfold eqke; intuition; [ eauto | congruence ].
  Qed.

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
  Hint Immediate eqk_sym eqke_sym.

  Global Instance eqk_equiv : Equivalence eqk.
  Proof. split; eauto. Qed.

  Global Instance eqke_equiv : Equivalence eqke.
  Proof. split; eauto. Qed.

  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition.
  Qed.

  Hint Resolve InA_eqke_eqk.

  Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m.
  Proof.
   intros; apply InA_eqA with p; auto with *.
  Qed.


  
  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.
  Notation NoDupA := (NoDupA eqk).

  Hint Unfold MapsTo In.

  (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

  Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
  Proof.
  firstorder.
  exists x; auto.
  induction H.
  destruct y.
  exists e; auto.
  destruct IHInA as [e H0].
  exists e; auto.
  Qed.

  Lemma MapsTo_eq : forall l x y e, x = y -> MapsTo x e l -> MapsTo y e l.
  Proof.
  intros; unfold MapsTo in *; apply InA_eqA with (x,e); eauto with *.
  Qed.

  Lemma In_eq : forall l x y, x = y -> In x l -> In y l.
  Proof.
  destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
  Qed.

  Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> k = k' \/ In k l.
  Proof.
    inversion 1.
    inversion_clear H0; eauto.
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


  Hint Resolve In_inv_2 In_inv_3.


  Definition empty : farray := nil.

  Definition Empty m := forall (a : key)(e:elt), ~ MapsTo a e m.

  Lemma empty_1 : Empty empty.
  Proof.
    unfold Empty,empty.
    intros a e.
    intro abs.
    inversion abs.
  Qed.

  Hint Resolve empty_1.

  Lemma empty_NoDup : NoDupA empty.
  Proof.
    unfold empty; auto.
  Qed.

  
  (** * [is_empty] *)

  Definition is_empty (l : farray) : bool := if l then true else false.

  Lemma is_empty_1 :forall m, Empty m -> is_empty m = true.
  Proof.
    unfold Empty, MapsTo.
    intros m.
    case m;auto.
    intros p l inlist.
    destruct p.
    absurd (InA eqke (k, e) ((k, e) :: l)); auto.
  Qed.

  Lemma is_empty_2 : forall m, is_empty m = true -> Empty m.
  Proof.
    intros m.
    case m;auto.
    intros p l abs.
    inversion abs.
  Qed.

  (** * [mem] *)

  Function mem (k : key) (s : farray) {struct s} : bool :=
    match s with
    | nil => false
    | (k',_) :: l => if eq_dec k k' then true else mem k l
    end.

  Lemma mem_1 : forall m (Hm:NoDupA m) x, In x m -> mem x m = true.
  Proof.
    intros m Hm x; generalize Hm; clear Hm.
    functional induction (mem x m);intros NoDup belong1;trivial.
    inversion belong1. inversion H.
    inversion_clear NoDup.
    inversion_clear belong1.
    inversion_clear H1.
    compute in H2; destruct H2.
    contradiction.
    apply IHb; auto.
    exists x0; auto.
  Qed.

  Lemma mem_2 : forall m (Hm:NoDupA m) x, mem x m = true -> In x m.
  Proof.
    intros m Hm x; generalize Hm; clear Hm; unfold In,MapsTo.
    functional induction (mem x m); intros NoDup hyp; try discriminate.
    exists _x; auto.
    inversion_clear NoDup.
    destruct IHb; auto.
    exists x0; auto.
  Qed.

  (** * [find] *)

  Function find (k:key) (s: farray) {struct s} : option elt :=
    match s with
    | nil => None
    | (k',x)::s' => if eq_dec k k' then Some x else find k s'
    end.

  Lemma find_2 : forall m x e, find x m = Some e -> MapsTo x e m.
  Proof.
    intros m x. unfold MapsTo.
    functional induction (find x m);simpl;intros e' eqfind; inversion eqfind; auto.
  Qed.

  Lemma find_1 : forall m (Hm:NoDupA m) x e,
      MapsTo x e m -> find x m = Some e.
  Proof.
    intros m Hm x e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (find x m);simpl; subst; try clear H_eq_1.

    inversion 2.

    do 2 inversion_clear 1.
    compute in H2; destruct H2; subst; trivial.
    elim H; apply InA_eqk with (x,e); auto.

    do 2 inversion_clear 1; auto.
    compute in H2; destruct H2; elim _x; auto.
  Qed.

  (* Not part of the exported specifications, used later for [combine]. *)

  Lemma find_eq : forall m (Hm:NoDupA m) x x',
      eq x x' -> find x m = find x' m.
  Proof.
    induction m; simpl; auto; destruct a; intros.
    inversion_clear Hm.
    rewrite (IHm H1 x x'); auto.
    destruct (eq_dec x k); destruct (eq_dec x' k); trivial.
    elim n; apply eq_trans with x; auto.
    elim n; apply eq_trans with x'; auto.
  Qed.

  (** * [add] *)

  Function add (k : key) (x : elt) (s : farray) {struct s} : farray :=
    match s with
    | nil => (k,x) :: nil
    | (k',y) :: l => if eq_dec k k' then (k,x)::l else (k',y)::add k x l
    end.

  Lemma add_1 : forall m x y e, eq x y -> MapsTo y e (add x e m).
  Proof.
    intros m x y e; generalize y; clear y; unfold MapsTo.
    functional induction (add x e m);simpl;auto.
  Qed.

  Lemma add_2 : forall m x y e e',
      ~ eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros m x  y e e'; generalize y e; clear y e; unfold MapsTo.
    functional induction (add x e' m);simpl;auto.
    intros y' e'' eqky';  inversion_clear 1.
    destruct H0; simpl in *.
    elim eqky'; auto.
    auto.
    intros y' e'' eqky'; inversion_clear 1; intuition.
  Qed.

  Lemma add_3 : forall m x y e e',
      ~ eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    intros m x y e e'. generalize y e; clear y e; unfold MapsTo.
    functional induction (add x e' m);simpl;auto.
    intros; eauto.
    constructor 2; eauto.
    inversion_clear 2; auto.
  Qed.

  Lemma add_3' : forall m x y e e',
      ~ eq x y -> InA eqk (y,e) (add x e' m) -> InA eqk (y,e) m.
  Proof.
    intros m x y e e'. generalize y e; clear y e.
    functional induction (add x e' m);simpl;auto.
    inversion_clear 2.
    compute in H1; elim H; auto.
    inversion H1.
    constructor 2; inversion_clear H0; auto.
    compute in H1; elim H; auto.
    inversion_clear 2; auto.
  Qed.

  Lemma add_NoDup : forall m (Hm:NoDupA m) x e, NoDupA (add x e m).
  Proof.
    induction m.
    simpl; constructor; auto; red; inversion 1.
    intros.
    destruct a as (x',e').
    simpl; case (eq_dec x x'); inversion_clear Hm; auto.
    constructor; auto.
    contradict H.
    apply InA_eqk with (x,e); auto.
    constructor; auto.
    contradict H; apply add_3' with x e; auto.
  Qed.

  (* Not part of the exported specifications, used later for [combine]. *)

  Lemma add_eq : forall m (Hm:NoDupA m) x a e,
      eq x a -> find x (add a e m) = Some e.
  Proof.
    intros.
    apply find_1; auto.
    apply add_NoDup; auto.
    apply add_1; auto.
  Qed.

  Lemma add_not_eq : forall m (Hm:NoDupA m) x a e,
      ~eq x a -> find x (add a e m) = find x m.
  Proof.
    intros.
    case_eq (find x m); intros.
    apply find_1; auto.
    apply add_NoDup; auto.
    apply add_2; auto.
    apply find_2; auto.
    case_eq (find x (add a e m)); intros; auto.
    rewrite <- H0; symmetry.
    apply find_1; auto.
    apply add_3 with a e; auto.
    apply find_2; auto.
  Qed.



  (** * [remove] *)

  Function remove (k : key) (s : farray) {struct s} : farray :=
    match s with
    | nil => nil
    | (k',x) :: l => if eq_dec k k' then l else (k',x) :: remove k l
    end.

  Lemma remove_1 : forall m (Hm:NoDupA m) x y, x = y -> ~ In y (remove x m).
  Proof.
    intros m Hm x y; generalize Hm; clear Hm.
    functional induction (remove x m);simpl;intros;auto.

    red; inversion 1; inversion H1.

    inversion_clear Hm.
    subst.
    contradict H0.
    destruct H0 as (e,H2); unfold MapsTo in H2.
    apply InA_eqk with (y,e); auto.
    compute; auto.

    intro H2.
    destruct H2 as (e,H2); inversion_clear H2.
    compute in H0; destruct H0.
    elim _x; apply eq_trans with y; auto.
    inversion_clear Hm.
    elim (IHf H2 H).
    exists e; auto.
  Qed.

  Lemma remove_2 : forall m (Hm:NoDupA m) x y e,
      x <> y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (remove x m);auto.
    inversion_clear 3; auto.
    compute in H1; destruct H1.
    elim H; auto.

    inversion_clear 1; inversion_clear 2; auto.
  Qed.

  Lemma remove_3 : forall m (Hm:NoDupA m) x y e,
      MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (remove x m);auto.
    do 2 inversion_clear 1; auto.
  Qed.

  Lemma remove_3' : forall m (Hm:NoDupA m) x y e,
      InA eqk (y,e) (remove x m) -> InA eqk (y,e) m.
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (remove x m);auto.
    do 2 inversion_clear 1; auto.
  Qed.

  Lemma remove_NoDup : forall m (Hm:NoDupA m) x, NoDupA (remove x m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    inversion_clear Hm.
    destruct a as (x',e').
    simpl; case (eq_dec x x'); auto.
    constructor; auto.
    contradict H; apply remove_3' with x; auto.
  Qed.

  
  (** * [elements] *)

  Definition elements (m: farray) := m.

  Lemma elements_1 : forall m x e, MapsTo x e m -> InA eqke (x,e) (elements m).
  Proof.
    auto.
  Qed.

  Lemma elements_2 : forall m x e, InA eqke (x,e) (elements m) -> MapsTo x e m.
  Proof.
    auto.
  Qed.

  Lemma elements_3w : forall m (Hm:NoDupA m), NoDupA (elements m).
  Proof.
    auto.
  Qed.

  
  (** * [fold] *)

  Function fold {A:Type} (f:key->elt->A->A) (m:farray) (acc : A) {struct m} :  A :=
    match m with
    | nil => acc
    | (k,e)::m' => fold f m' (f k e acc)
    end.

  Lemma fold_1 : forall m (A:Type) (i:A) (f:key->elt->A->A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros; functional induction (@fold A f m i); auto.
  Qed.

  
  (** * [equal] *)

  Definition check (k:key)(e:elt)(m': farray) :=
    match find k m' with
    | None => false
    | Some e' => eqb_elt e e'
    end.

  Definition submap (m m' : farray) : bool :=
    fold (fun k e b => andb (check k e m') b) m true.

  Definition equal (m m' : farray) : bool :=
    andb (submap m m') (submap m' m).

  Definition Submap m m' :=
    (forall k, In k m -> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eqb_elt e e' = true).

  Definition Equivb m m' :=
    (forall k, In k m <-> In k m') /\
    (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eqb_elt e e' = true).

  Lemma submap_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m'),
      Submap m m' -> submap m m' = true.
  Proof.
    unfold Submap, submap.
    induction m.
    simpl; auto.
    destruct a; simpl; intros.
    destruct H.
    inversion_clear Hm.
    assert (H3 : In k m').
    apply H; exists e; auto.
    destruct H3 as (e', H3).
    unfold check at 2; rewrite (find_1 Hm' H3).
    rewrite (H0 k); simpl; auto.
    eapply IHm; auto.
    split; intuition.
    apply H.
    destruct H5 as (e'',H5); exists e''; auto.
    apply (H0 k0); auto.
  Qed.

  Lemma submap_2 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m'),
      submap m m' = true -> Submap m m'.
  Proof.
    unfold Submap, submap.
    induction m.
    simpl; auto.
    intuition.
    destruct H0; inversion H0.
    inversion H0.

    destruct a; simpl; intros.
    inversion_clear Hm.
    rewrite andb_b_true in H.
    assert (check k e m' = true).
    clear H1 H0 Hm' IHm.
    set (b:=check k e m') in *.
    generalize H; clear H; generalize b; clear b.
    induction m; simpl; auto; intros.
    destruct a; simpl in *.
    destruct (andb_prop _ _ (IHm _ H)); auto.
    rewrite H2 in H.
    destruct (IHm H1 m' Hm' H); auto.
    unfold check in H2.
    case_eq (find k m'); [intros e' H5 | intros H5];
      rewrite H5 in H2; try discriminate.
    split; intros.
    destruct H6 as (e0,H6); inversion_clear H6.
    compute in H7; destruct H7; subst.
    exists e'.
    apply MapsTo_eq with k; auto.
    apply find_2; auto.
    apply H3.
    exists e0; auto.
    inversion_clear H6.
    compute in H8; destruct H8; subst e0.
    rewrite (find_1 Hm' (MapsTo_eq H6 H7)) in H5; congruence.
    apply H4 with k0; auto.
  Qed.

  
  (** Specification of [equal] *)

  Lemma equal_1 : forall m (Hm:NoDupA m) m' (Hm': NoDupA m'),
      Equivb m m' -> equal m m' = true.
  Proof.
    unfold Equivb, equal.
    intuition.
    apply andb_true_intro; split; apply submap_1; unfold Submap; firstorder.
    apply eqb_elt_eq. symmetry. apply eqb_elt_eq. 
    apply (H1 k e' e); auto.
  Qed.

  Lemma equal_2 : forall m (Hm:NoDupA m) m' (Hm':NoDupA m'),
      equal m m' = true -> Equivb m m'.
  Proof.
    unfold Equivb, equal.
    intros.
    destruct (andb_prop _ _ H); clear H.
    generalize (submap_2 Hm Hm' H0).
    generalize (submap_2 Hm' Hm H1).
    firstorder.
  Qed.





  Record slist :=
    {this :> farray; NoDup : NoDupA this}.
  Definition _farray := slist.

  (* Definition _MapsTo (k:key)(e:elt) m := InA eqke (k,e) m.(this). *)
  (* Definition _In k m := exists e:elt, _MapsTo k e m. *)

  (* Definition _MapsTo (k:key)(e:elt) m := MapsTo k e m.(this). *)
  (* Definition _In k m := In k m.(this). *)

  Definition _empty : _farray := Build_slist empty_NoDup.
  Definition _is_empty m : bool := is_empty m.(this).
  Definition _add x e m : _farray := Build_slist (add_NoDup m.(NoDup) x e).
  Definition _find x m : option elt := find x m.(this).
  Definition _remove x m : _farray := Build_slist (remove_NoDup m.(NoDup) x).
  Definition _mem x m : bool := mem x m.(this).
  (* Definition _map f m : _farray := Build_slist (map_NoDup m.(NoDup) f). *)
  (* Definition _mapi (f:key->elt->elt') m : _farray' := Build_slist (mapi_NoDup m.(NoDup) f). *)
  (* Definition _map2 f m (m':_farray') : _farray'' := *)
  (*   Build_slist (map2_NoDup f m.(NoDup) m'.(NoDup)). *)
  Definition _elements m : list (key*elt) := @elements m.(this).
  Definition _cardinal m := length m.(this).
  Definition _fold (A:Type)(f:key->elt->A->A) m (i:A) : A := @fold A f m.(this) i.
  Definition _equal m m' : bool := @equal m.(this) m'.(this).
  Definition _MapsTo x e m : Prop := MapsTo x e m.(this).
  Definition _In x m : Prop := In x m.(this).
  Definition _Empty m : Prop := Empty m.(this).

  Definition _Equal m m' := forall y, _find y m = _find y m'.
  Definition _Equiv m m' :=
    (forall k, _In k m <-> _In k m') /\
    (forall k e e', _MapsTo k e m -> _MapsTo k e' m' -> e = e').
  Definition _Equivb m m' : Prop := @Equivb m.(this) m'.(this).

  Definition _eq_key : (key*elt) -> (key*elt) -> Prop := eqk.
  Definition _eq_key_elt : (key*elt) -> (key*elt) -> Prop:= @eqke.

  Lemma MapsTo_1 : forall m x y e, x = y -> _MapsTo x e m -> _MapsTo y e m.
  Proof. intros m; exact (@MapsTo_eq m.(this)). Qed.

  Lemma _mem_1 : forall m x, _In x m -> _mem x m = true.
  Proof. intros m; exact (@mem_1 m.(this) m.(NoDup)). Qed.
  
  Lemma _mem_2 : forall m x, _mem x m = true -> _In x m.
  Proof. intros m; exact (@mem_2 m.(this) m.(NoDup)). Qed.

  Lemma _empty_1 : _Empty _empty.
  Proof. exact (@empty_1). Qed.

  Lemma _is_empty_1 : forall m, _Empty m -> _is_empty m = true.
  Proof. intros m; exact (@is_empty_1 m.(this)). Qed.
  Lemma _is_empty_2 :  forall m, _is_empty m = true -> _Empty m.
  Proof. intros m; exact (@is_empty_2 m.(this)). Qed.

  Lemma _add_1 : forall m x y e, x = y -> _MapsTo y e (_add x e m).
  Proof. intros m; exact (@add_1 m.(this)). Qed.
  
  Lemma _add_2 : forall m x y e e', x <> y -> _MapsTo y e m -> _MapsTo y e (_add x e' m).
  Proof. intros m; exact (@add_2 m.(this)). Qed.
  
  Lemma _add_3 : forall m x y e e', x <> y -> _MapsTo y e (_add x e' m) -> _MapsTo y e m.
  Proof. intros m; exact (@add_3 m.(this)). Qed.

  Lemma _remove_1 : forall m x y, x = y -> ~ _In y (_remove x m).
  Proof. intros m; exact (@remove_1 m.(this) m.(NoDup)). Qed.
  
  Lemma _remove_2 : forall m x y e, x <> y -> _MapsTo y e m -> _MapsTo y e (_remove x m).
  Proof. intros m; exact (@remove_2 m.(this) m.(NoDup)). Qed.
  Lemma _remove_3 : forall m x y e, _MapsTo y e (_remove x m) -> _MapsTo y e m.
  Proof. intros m; exact (@remove_3 m.(this) m.(NoDup)). Qed.

  Lemma _find_1 : forall m x e, _MapsTo x e m -> _find x m = Some e.
  Proof. intros m; exact (@find_1 m.(this) m.(NoDup)). Qed.
  Lemma _find_2 : forall m x e, _find x m = Some e -> _MapsTo x e m.
  Proof. intros m; exact (@find_2 m.(this)). Qed.

  Lemma _elements_1 : forall m x e, _MapsTo x e m -> InA eqke (x,e) (_elements m).
  Proof. intros m; exact (@elements_1 m.(this)). Qed.
  Lemma _elements_2 : forall m x e, InA eqke (x,e) (_elements m) -> _MapsTo x e m.
  Proof. intros m; exact (@elements_2 m.(this)). Qed.
  Lemma _elements_3w : forall m, NoDupA (_elements m).
  Proof. intros m; exact (@elements_3w m.(this) m.(NoDup)). Qed.

  Lemma _cardinal_1 : forall m, _cardinal m = length (_elements m).
  Proof. intros; reflexivity. Qed.

  Lemma _fold_1 : forall m (A : Type) (i : A) (f : key -> elt -> A -> A),
      _fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (_elements m) i.
  Proof. intros m; exact (@fold_1 m.(this)). Qed.

  Lemma _equal_1 : forall m m', _Equivb m m' -> _equal m m' = true.
  Proof. intros m m'; exact (@equal_1 m.(this) m.(NoDup) m'.(this) m'.(NoDup)). Qed.
  Lemma _equal_2 : forall m m', _equal m m' = true -> _Equivb m m'.
  Proof. intros m m'; exact (@equal_2 m.(this) m.(NoDup) m'.(this) m'.(NoDup)). Qed.

  
  
  Lemma eq_option_alt : forall (elt:Type)(o o':option elt),
      o=o' <-> (forall e, o=Some e <-> o'=Some e).
  Proof.
    split; intros.
    subst; split; auto.
    destruct o; destruct o'; try rewrite H; auto.
    symmetry; rewrite <- H; auto.
  Qed.

  Lemma find_mapsto_iff : forall m x e, _MapsTo x e m <-> _find x m = Some e.
  Proof.
    split; [apply _find_1|apply _find_2].
  Qed.

  Lemma add_neq_mapsto_iff : forall m x y e e',
      x <> y -> (_MapsTo y e' (_add x e m)  <-> _MapsTo y e' m).
  Proof.
    split; [apply _add_3|apply _add_2]; auto.
  Qed.


 Lemma add_eq_o : forall m x y e,
      x = y -> _find y (_add x e m) = Some e.
  Proof. intros.
    apply _find_1.
    apply _add_1. auto.
Qed.

  Lemma add_neq_o : forall m x y e,
      ~ x = y -> _find y (_add x e m) = _find y m.
  Proof.
    intros. rewrite eq_option_alt. intro e'. rewrite <- 2 find_mapsto_iff.
    apply add_neq_mapsto_iff; auto.
  Qed.
  Hint Resolve add_neq_o.




  Lemma MapsTo_fun : forall m x (e e':elt),
      _MapsTo x e m -> _MapsTo x e' m -> e=e'.
  Proof.
    intros.
    generalize (_find_1 H) (_find_1 H0); clear H H0.
    intros; rewrite H in H0; injection H0; auto.
  Qed.


  (** Another characterisation of [Equal] *)

  Lemma Equal_mapsto_iff : forall m1 m2 : _farray,
      _Equal m1 m2 <-> (forall k e, _MapsTo k e m1 <-> _MapsTo k e m2).
  Proof.
    intros m1 m2. split; [intros Heq k e|intros Hiff].
    rewrite 2 find_mapsto_iff, Heq. split; auto.
    intro k. rewrite eq_option_alt. intro e.
    rewrite <- 2 find_mapsto_iff; auto.
  Qed.

  (** * Relations between [Equal], [Equiv] and [Equivb]. *)

  (** First, [Equal] is [Equiv] with Leibniz on elements. *)

  Lemma Equal_Equiv : forall (m m' : _farray),
      _Equal m m' <-> _Equiv m m'.
  Proof.
    intros. rewrite Equal_mapsto_iff. split; intros.
    split.
    split; intros (e,Hin); exists e; unfold _MapsTo in H; [rewrite <- H|rewrite H]; auto.
    intros; apply MapsTo_fun with m k; auto; rewrite H; auto.
    split; intros H'.
    destruct H.
    assert (Hin : _In k m') by (rewrite <- H; exists e; auto).
    destruct Hin as (e',He').
    rewrite (H0 k e e'); auto.
    destruct H.
    assert (Hin : _In k m) by (rewrite H; exists e; auto).
    destruct Hin as (e',He').
    rewrite <- (H0 k e' e); auto.
  Qed.

  Lemma Equiv_Equivb : forall m m', _Equiv m m' <-> _Equivb m m'.
  Proof.
    unfold _Equivb, _Equiv, Equivb; intuition.
    rewrite eqb_elt_eq; apply H1 with k; unfold _MapsTo; auto.
    rewrite <- eqb_elt_eq; apply H1 with k; unfold _MapsTo; auto.
  Qed.


  (** Composition of the two last results: relation between [Equal]
    and [Equivb]. *)

  Lemma Equal_Equivb : forall (m m':_farray), _Equal m m' <-> _Equivb m m'.
  Proof.
    intros; rewrite Equal_Equiv.
    apply Equiv_Equivb; auto.
  Qed.

  

  (** * Functional arrays *)

  
  Definition select (a: _farray) (i: key) : option elt := _find i a.


  Definition store (a: _farray) (i: key) (v: elt) : _farray := _add i v a.


  Lemma read_over_same_write : forall a i j v, i = j -> select (store a i v) j = Some v.
  Proof.
    intros a i j v Heq.
    unfold select, store.
    intros. rewrite add_eq_o; auto.
  Qed.  


  Lemma read_over_other_write : forall a i j v,
      i <> j -> select (store a i v) j = select a j.
  Proof.
    intros a i j v Hneq.
    unfold select, store.
    rewrite add_neq_o; auto.
  Qed. 


  (* TODO *)
  Lemma find_ext_dec:
    (forall m1 m2: _farray, _Equal m1 m2 -> (_equal m1 m2) = true).
  Proof. intros.
    apply Equal_Equivb in H.
    apply _equal_1.
    exact H.
  Qed.


  Lemma extensionnality : forall a b,
      (forall i, select a i = select b i) -> _equal a b = true.
  Proof.
    intros.
    unfold select in H.
    apply find_ext_dec in H.
    exact H.
  Qed.

End Array.


(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

Require Import SetoidList Bool OrderedType OrdersLists RelationPairs Orders.
Require Import RelationClasses.
Require Import ProofIrrelevance.


Definition eqb_to_eq_dec : forall T (eqb : T -> T -> bool) (eqb_spec : forall x y, eqb x y = true <-> x = y)
                      (x y : T), { x = y } + { x <> y }.
  intros.
  case_eq (eqb x y); intro.
  left. apply eqb_spec; auto.
  right. red. intro. apply eqb_spec in H0. rewrite H in H0. now contradict H0.
  Defined.
  


Class EqbType T := {
 eqb : T -> T -> bool;
 eqb_spec : forall x y, eqb x y = true <-> x = y
}.


Class DecType T := {
 eq_refl : forall x : T, x = x;
 eq_sym : forall x y : T, x = y -> y = x;
 eq_trans : forall x y z : T, x = y -> y = z -> x = z;
 eq_dec : forall x y : T, { x = y } + { x <> y }
}.


Instance EqbToDecType T `(EqbType T) : DecType T.
Proof.
  destruct H.
  split; auto.
  intros; subst; auto.
  apply (eqb_to_eq_dec _ eqb0); auto.
Defined.

Hint Immediate eq_sym.
Hint Resolve eq_refl eq_trans.

Class OrdType T := {
  lt: T -> T -> Prop;
  lt_trans : forall x y z : T, lt x y -> lt y z -> lt x z;
  lt_not_eq : forall x y : T, lt x y -> ~ eq x y
  (* compare : forall x y : T, Compare lt eq x y *)
}.


Hint Resolve lt_not_eq lt_trans.

(* Global Instance Comparable T `(OrdType T) : *)

Class Comparable T {ot:OrdType T} := {
  compare : forall x y : T, Compare lt eq x y
}.


Class Inhabited T := {
    default_value : T
  }.

Set Implicit Arguments.



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

  Hint Immediate eqb_key_eq eqb_elt_eq.
  
  Definition farray := list (key * elt).

  Definition eqk (a b : (key * elt)) := fst a = fst b.
  Definition eqe (a b : (key * elt)) := snd a = snd b.
  Definition eqke (a b : (key * elt)) := fst a = fst b /\ snd a = snd b.

  Definition ltk (a b : (key * elt)) := lt (fst a) (fst b).

  (* Definition ltke (a b : (key * elt)) := *)
  (*   lt (fst a) (fst b) \/ ( (fst a) = (fst b) /\ lt (snd a) (snd b)). *)
  
  Hint Unfold ltk (* ltke *) eqk eqke.
  Hint Extern 2 (eqke ?a ?b) => split.


  Global Instance StrictOrder_OrdType T `(OrdType T) :
    StrictOrder (lt : T -> T -> Prop).
  Proof.
    split.
    unfold Irreflexive, Reflexive, complement.
    intros. apply lt_not_eq in H0; auto.
    unfold Transitive. intros x y z. apply lt_trans.
  Qed.
  
  Global Instance lt_key_strorder : StrictOrder (lt : key -> key -> Prop).
  Proof. apply StrictOrder_OrdType. Qed.

  Global Instance lt_elt_strorder : StrictOrder (lt : elt -> elt -> Prop).
  Proof. apply StrictOrder_OrdType. Qed.

  
  Global Instance ke_dec : DecType (key * elt).
  Proof.
    split; auto.
    intros; destruct x, y, z.
    inversion H. inversion H0. trivial.
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
  Qed.


  (* ltk ignore the second components *)

   Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
   Proof. auto. Qed.

   Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
   Proof. auto. Qed.
   Hint Immediate ltk_right_r ltk_right_l.


  
  
  Notation Sort := (sort ltk).
  Notation Inf := (lelistA (ltk)).
  
  Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
  Definition In k m := exists e:elt, MapsTo k e m.

  Notation NoDupA := (NoDupA eqk).

  Hint Unfold MapsTo In.

  
  (* Instance ke_ord: OrdType (key * elt). *)
  (* Proof. *)
  (*   exists ltke. *)
  (*   unfold ltke. intros. *)
  (*   destruct H, H0. *)
  (*   left; apply (lt_trans _ (fst y)); auto. *)
  (*   destruct H0. left. rewrite <- H0. assumption. *)
  (*   destruct H. left. rewrite H. assumption. *)
  (*   destruct H, H0. *)
  (*   right. split. *)
  (*   apply (eq_trans _ (fst y)); trivial. *)
  (*   apply (lt_trans _ (snd y)); trivial. *)
  (*   unfold ltke. intros. *)
  (*   destruct x, y. simpl in H. *)
  (*   destruct H. *)
  (*   apply lt_not_eq in H. *)
  (*   unfold not in *. intro. inversion H0. apply H. trivial. *)
  (*   destruct H. apply lt_not_eq in H0. unfold not in *. intro.  *)
  (*   inversion H1. apply H0; trivial. *)
  (*   intros. *)
  (*   unfold ltke. *)
  (*   destruct (compare (fst x) (fst y)). *)
  (*   apply LT. left; assumption. *)
  (*   destruct (compare (snd x) (snd y)). *)
  (*   apply LT. right; split; assumption. *)
  (*   apply EQ. destruct x, y. simpl in *. rewrite e, e0; trivial. *)
  (*   apply GT. right; symmetry in e; split; assumption. *)
  (*   apply GT. left; assumption. *)
  (* Qed. *)

  
  (* Hint Immediate ke_ord. *)
  (* Let ke_ord := ke_ord. *)

  (* Instance keyelt_ord: OrdType (key * elt). *)


  (* Variable keyelt_ord : OrdType (key * elt). *)
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
   
  Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
  Proof. eauto. Qed.

  Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
  Proof. unfold ltk, eqk. intros. apply lt_not_eq; auto. Qed.

  Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
  Proof.
    unfold eqke, ltk; intuition; simpl in *; subst.
    apply lt_not_eq in H. auto.
  Qed.
  

  Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
  Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke.
  Hint Immediate eqk_sym eqke_sym.


  
  Global Instance eqk_equiv : Equivalence eqk.
  Proof. split; eauto. Qed.

  Global Instance eqke_equiv : Equivalence eqke.
  Proof. split; eauto. Qed.



  Global Instance ltk_strorder : StrictOrder ltk.
  Proof.
    split.
    unfold Irreflexive, Reflexive, complement.
    intros. apply lt_not_eq in H; auto.
    unfold Transitive. intros x y z. apply lt_trans.
  Qed.


  (* Instance ltke_strorder : StrictOrder ltke. *)
  (* Proof. *)
  (*   split. *)
  (*   unfold Irreflexive, Reflexive, complement. *)
  (*   intros. apply lt_not_eq in H; auto. *)
  (*   unfold Transitive. apply lt_trans. *)
  (* Qed. *)

  Global Instance eq_equiv : @Equivalence (key * elt) eq.
  Proof.
    split; auto.
    unfold Transitive. apply eq_trans.
  Qed.
    
  (* Instance ltke_compat : Proper (eq ==> eq ==> iff) ltke. *)
  (* Proof. *)
  (*   split; rewrite H, H0; trivial. *)
  (* Qed. *)
    
  Global Instance ltk_compat : Proper (eq ==> eq ==> iff) ltk.
  Proof.
    split; rewrite H, H0; trivial.
  Qed.

  
  Global Instance ltk_compatk : Proper (eqk==>eqk==>iff) ltk.
  Proof.
  intros (x,e) (x',e') Hxx' (y,f) (y',f') Hyy'; compute.
   compute in Hxx'; compute in Hyy'. rewrite Hxx', Hyy'; auto.
  Qed.

  Global Instance ltk_compat' : Proper (eqke==>eqke==>iff) ltk.
  Proof.
  intros (x,e) (x',e') (Hxx',_) (y,f) (y',f') (Hyy',_); compute.
   compute in Hxx'; compute in Hyy'. rewrite Hxx', Hyy'; auto.
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
    apply lt_not_eq in H. auto.
    subst. auto.
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
  Hint Resolve eqk_not_ltk.
  Hint Immediate ltk_eqk eqk_ltk.
  
  Lemma InA_eqke_eqk :
     forall x m, InA eqke x m -> InA eqk x m.
  Proof.
    unfold eqke; induction 1; intuition.
  Qed.

  Hint Resolve InA_eqke_eqk.

  (* Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m. *)
  (* Proof. *)
  (*  intros; apply InA_eqA with p; auto with *. *)
  (* Qed. *)

  (* Lemma In_eq : forall l x y, eq x y -> InA eqke x l -> InA eqke y l. *)
  (* Proof. intros. rewrite <- H; auto. Qed. *)

  (* Lemma ListIn_In : forall l x, List.In x l -> InA eqk x l. *)
  (* Proof. apply In_InA. split; auto. unfold Transitive. *)
  (*   unfold eqk; intros. rewrite H, <- H0. auto. *)
  (* Qed. *)
  
  (* Lemma Inf_lt : forall l x y, ltk x y -> Inf y l -> Inf x l. *)
  (* Proof. exact (InfA_ltA ltk_strorder). Qed. *)

  (* Lemma Inf_eq : forall l x y, x = y -> Inf y l -> Inf x l. *)
  (* Proof. exact (InfA_eqA eq_equiv ltk_compat). Qed. *)



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

  Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
  Proof.
  intros; unfold MapsTo in *; apply InA_eqA with (x,e); eauto with *.
  Qed.

  Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
  Proof.
  destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
  Qed.

  Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
  Proof. exact (InfA_eqA eqk_equiv ltk_compatk). Qed.

  Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
  Proof. exact (InfA_ltA ltk_strorder). Qed.

  Hint Immediate Inf_eq.
  Hint Resolve Inf_lt.

  

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
    eapply Sort_Inf_In; eauto.
    red; simpl; auto.
  Qed.

  Hint Resolve Sort_Inf_NotIn.
  
  Lemma Sort_NoDupA: forall l, Sort l -> NoDupA l.
  Proof.
    exact (SortA_NoDupA eqk_equiv ltk_strorder ltk_compatk).
  Qed.

  Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
  Proof.
    inversion 1; intros; eapply Sort_Inf_In; eauto.
  Qed.

  Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
                                   ltk e e' \/ eqk e e'.
  Proof.
    inversion_clear 2; auto.
    left; apply Sort_In_cons_1 with l; auto.
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
  Hint Resolve empty_1.

  Lemma empty_sorted : Sort empty.
  Proof.
    unfold empty; auto.
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
        unfold eqke in *. simpl in *. destruct H, H1; subst; auto.
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
    case m;auto.
    intros (k,e) l inlist.
    absurd (InA eqke (k, e) ((k, e) :: l));auto.
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
    functional induction (mem x m);intros sorted belong1;trivial.

    inversion belong1. inversion H.

    absurd (In x ((k', _x) :: l));try assumption.
    apply Sort_Inf_NotIn with _x;auto.

    apply IHb.
    elim (sort_inv sorted);auto.
    elim (In_inv belong1);auto.
    intro abs.
    absurd (eq x k'); auto.
    symmetry in abs.
    apply lt_not_eq in abs; auto.
  Qed.

  Lemma mem_2 : forall m (Hm:Sort m) x, mem x m = true -> In x m.
  Proof.
    intros m Hm x; generalize Hm; clear Hm; unfold In,MapsTo.
    functional induction (mem x m); intros sorted hyp;try ((inversion hyp);fail).
    exists _x; auto.
    induction IHb; auto.
    exists x0; auto.
    inversion_clear sorted; auto.
  Qed.

  Lemma mem_3 : forall m (Hm:Sort m) x, mem x m = false -> ~ In x m.
    intros.
    rewrite <- not_true_iff_false in H.
    unfold not in *. intros; apply H.
    now apply mem_1.
  Qed.
  

    
  
  (** * [find] *)

  Function find (k:key) (s: farray) {struct s} : option elt :=
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
    functional induction (find x m);simpl;intros e' eqfind; inversion eqfind; auto.
  Qed.

  Lemma find_1 :  forall m (Hm:Sort m) x e, MapsTo x e m -> find x m = Some e.
  Proof.
    intros m Hm x e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (find x m);simpl; subst; try clear H_eq_1.

    inversion 2.

    inversion_clear 2.
    clear e1;compute in H0; destruct H0.
    apply lt_not_eq in H; auto. now contradict H.

    clear e1;generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute.
    (* order. *)
    intros.
    apply (lt_trans k') in _x; auto.
    apply lt_not_eq in _x.
    now contradict _x.
    
    clear e1;inversion_clear 2.
    compute in H0; destruct H0; intuition congruence.
    generalize (Sort_In_cons_1 Hm (InA_eqke_eqk H0)); compute.
    (* order. *)
    intros.
    apply lt_not_eq in H. now contradict H.
    
    clear e1; do 2 inversion_clear 1; auto.
    compute in H2; destruct H2.
    (* order. *)
    subst. apply lt_not_eq in _x. now contradict _x.
  Qed.

  (** * [add] *)

  Function add (k : key) (x : elt) (s : farray) {struct s} : farray :=
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
    functional induction (add x e m);simpl;auto.
  Qed.

  Lemma add_2 : forall m x y e e',
      ~ eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
  Proof.
    intros m x  y e e'.
    generalize y e; clear y e; unfold MapsTo.
    functional induction (add x e' m) ;simpl;auto;  clear e0.
    subst;auto.

    intros y' e'' eqky';  inversion_clear 1;  destruct H0; simpl in *.
    (* order. *)
    subst. now contradict eqky'.
    auto.
    auto.
    intros y' e'' eqky'; inversion_clear 1; intuition.
  Qed.


  Lemma add_3 : forall m x y e e',
      ~ eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
  Proof.
    intros m x y e e'. generalize y e; clear y e; unfold MapsTo.
    functional induction (add x e' m);simpl; intros.
    apply (In_inv_3 H0); compute; auto.
    apply (In_inv_3 H0); compute; auto.
    constructor 2; apply (In_inv_3 H0); compute; auto.
    inversion_clear H0; auto.
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
  Hint Resolve add_Inf.

  Lemma add_sorted : forall m (Hm:Sort m) x e, Sort (add x e m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; case (compare x x'); intuition; inversion_clear Hm; auto.
    constructor; auto.
    apply Inf_eq with (x',e'); auto.
  Qed.

  (** * [remove] *)

  Function remove (k : key) (s : farray) {struct s} : farray :=
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
    functional induction (remove x m);simpl;intros;subst.

    red; inversion 1; inversion H0.

    apply Sort_Inf_NotIn with x0; auto.

    clear e0. inversion Hm. subst.
    apply Sort_Inf_NotIn with x0; auto.
    

    (* clear e0;inversion_clear Hm. *)
    (* apply Sort_Inf_NotIn with x0; auto. *)
    (* apply Inf_eq with (k',x0);auto; compute; apply eq_trans with x; auto. *)

    clear e0;inversion_clear Hm.
    assert (notin:~ In y (remove y l)) by auto.
    intros (x1,abs).
    inversion_clear abs.
    compute in H1; destruct H1.
    subst. apply lt_not_eq in _x; now contradict _x.
    apply notin; exists x1; auto.
  Qed.


  Lemma remove_2 : forall m (Hm:Sort m) x y e,
      ~ eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (remove x m);subst;auto;
      match goal with
      | [H: compare _ _ = _ |- _ ] => clear H
      | _ => idtac
      end.

    inversion_clear 3; auto.
    compute in H1; destruct H1.
    subst; now contradict H.
    inversion_clear 1; inversion_clear 2; auto.
  Qed.

  Lemma remove_3 : forall m (Hm:Sort m) x y e,
      MapsTo y e (remove x m) -> MapsTo y e m.
  Proof.
    intros m Hm x y e; generalize Hm; clear Hm; unfold MapsTo.
    functional induction (remove x m);subst;auto.
    inversion_clear 1; inversion_clear 1; auto.
  Qed.

  Lemma remove_4_aux : forall m (Hm:Sort m) x y,
      ~ eq x y -> In y m -> In y (remove x m).
  Proof.
    intros m Hm x y; generalize Hm; clear Hm.
    functional induction (remove x m);subst;auto;
      match goal with
      | [H: compare _ _ = _ |- _ ] => clear H
      | _ => idtac
      end.
    rewrite In_alt.
    inversion_clear 3; auto.
    inversion H2.
    unfold eqk in H3. simpl in H3. subst. now contradict H0.
    apply In_alt.
    exists x1. auto.
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
    split; simpl; auto.
    inversion H3.
    unfold eqk in H4. simpl in H4; subst. now contradict n.
    assert ((exists e : elt, MapsTo y e (remove x l)) -> (exists e : elt, MapsTo y e ((k', x0) :: remove x l))).
    intros.
    destruct H6. exists x2.
    apply InA_cons_tl. auto.
    apply H6.
    apply IHf; auto.
    apply In_alt.
    exists x1. auto.
  Qed.    

  Lemma remove_4 : forall m (Hm:Sort m) x y,
      ~ eq x y -> In y m <-> In y (remove x m).
  Proof.
    split.
    apply remove_4_aux; auto.
    revert H.
    generalize Hm; clear Hm.
    functional induction (remove x m);subst;auto;
      match goal with
      | [H: compare _ _ = _ |- _ ] => clear H
      | _ => idtac
      end.
    intros.
    (* rewrite In_alt in *. *)
    destruct H0 as (e, H0).
    exists e.
    apply InA_cons_tl. auto.
    intros.
    apply lt_not_eq in _x.
    inversion_clear Hm.
    apply In_inv in H0.
    destruct H0.
    (* destruct (eq_dec k' y). *)
    exists x0.
    apply InA_cons_hd. split; simpl; auto.
    specialize (IHf H1 H H0).
    inversion IHf.
    exists x1.
    apply InA_cons_tl. auto.
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
    apply Inf_lt with (x'',e''); auto.
  Qed.
  Hint Resolve remove_Inf.

  Lemma remove_sorted : forall m (Hm:Sort m) x, Sort (remove x m).
  Proof.
    induction m.
    simpl; intuition.
    intros.
    destruct a as (x',e').
    simpl; case (compare x x'); intuition; inversion_clear Hm; auto.
  Qed.

  (** * [elements] *)

  Definition elements (m: farray) := m.

  Lemma elements_1 : forall m x e,
      MapsTo x e m -> InA eqke (x,e) (elements m).
  Proof.
    auto.
  Qed.

  Lemma elements_2 : forall m x e,
      InA eqke (x,e) (elements m) -> MapsTo x e m.
  Proof.
    auto.
  Qed.

  Lemma elements_3 : forall m (Hm:Sort m), sort ltk (elements m).
  Proof.
    auto.
  Qed.

  Lemma elements_3w : forall m (Hm:Sort m), NoDupA (elements m).
  Proof.
    intros.
    apply Sort_NoDupA.
    apply elements_3; auto.
  Qed.

  (** * [fold] *)

  Function fold (A:Type)(f:key->elt->A->A)(m:farray) (acc:A) {struct m} :  A :=
    match m with
    | nil => acc
    | (k,e)::m' => fold f m' (f k e acc)
    end.

  Lemma fold_1 : forall m (A:Type)(i:A)(f:key->elt->A->A),
      fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
  Proof.
    intros; functional induction (fold f m i); auto.
  Qed.

  (** * [equal] *)

  Function equal (cmp:elt->elt->bool)(m m' : farray) {struct m} : bool :=
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
    functional induction (equal cmp m m'); simpl; subst;auto; unfold Equivb;
      intuition; subst.
    match goal with H: compare _ _ = _ |- _ => clear H end.
    assert (cmp_e_e':cmp e e' = true).
    apply H1 with x; auto.
    rewrite cmp_e_e'; simpl.
    apply IHb; auto.
    inversion_clear Hm; auto.
    inversion_clear Hm'; auto.
    unfold Equivb; intuition.
    destruct (H0 k).
    assert (In k ((x,e) ::l)).
    destruct H as (e'', hyp); exists e''; auto.
    destruct (In_inv (H2 H4)); auto.
    inversion_clear Hm.
    elim (Sort_Inf_NotIn H6 H7).
    destruct H as (e'', hyp); exists e''; auto.
    apply MapsTo_eq with k; auto.
    destruct (H0 k).
    assert (In k ((x,e') ::l')).
    destruct H as (e'', hyp); exists e''; auto.
    destruct (In_inv (H3 H4)); auto.
    subst.
    inversion_clear Hm'.
    now elim (Sort_Inf_NotIn H5 H6).
    apply H1 with k; destruct (eq_dec x k); auto.


    destruct (compare x x') as [Hlt|Heq|Hlt]; try contradiction; clear y.
    destruct (H0 x).
    assert (In x ((x',e')::l')).
    apply H; auto.
    exists e; auto.
    destruct (In_inv H3).
    (* order. *)
    apply lt_not_eq in Hlt; now contradict Hlt.
    inversion_clear Hm'.
    assert (Inf (x,e) l').
    apply Inf_lt with (x',e'); auto.
    elim (Sort_Inf_NotIn H5 H7 H4).

    destruct (H0 x').
    assert (In x' ((x,e)::l)).
    apply H2; auto.
    exists e'; auto.
    destruct (In_inv H3).
    (* order. *)
    subst; apply lt_not_eq in Hlt; now contradict Hlt.
    inversion_clear Hm.
    assert (Inf (x',e') l).
    apply Inf_lt with (x,e); auto.
    elim (Sort_Inf_NotIn H5 H7 H4).

    destruct m;
      destruct m';try contradiction.

    clear H1;destruct p as (k,e).
    destruct (H0 k).
    destruct H1.
    exists e; auto.
    inversion H1.

    destruct p as (x,e).
    destruct (H0 x).
    destruct H.
    exists e; auto.
    inversion H.

    destruct p;destruct p0;contradiction.
  Qed.


  Lemma equal_2 : forall m (Hm:Sort m) m' (Hm:Sort m') cmp,
      equal cmp m m' = true -> Equivb cmp m m'.
  Proof.
    intros m Hm m' Hm' cmp; generalize Hm Hm'; clear Hm Hm'.
    functional induction (equal cmp m m'); simpl; subst;auto; unfold Equivb;
      intuition; try discriminate; subst;
        try match goal with H: compare _ _ = _ |- _ => clear H end.

    inversion H0.

    inversion_clear Hm;inversion_clear Hm'.
    destruct (andb_prop _ _ H); clear H.
    destruct (IHb H1 H3 H6).
    destruct (In_inv H0).
    exists e'; constructor; split; trivial; apply eq_trans with x; auto.
    destruct (H k).
    destruct (H9 H8) as (e'',hyp).
    exists e''; auto.

    inversion_clear Hm;inversion_clear Hm'.
    destruct (andb_prop _ _ H); clear H.
    destruct (IHb H1 H3 H6).
    destruct (In_inv H0).
    exists e; constructor; split; trivial; apply eq_trans with x'; auto.
    destruct (H k).
    destruct (H10 H8) as (e'',hyp).
    exists e''; auto.

    inversion_clear Hm;inversion_clear Hm'.
    destruct (andb_prop _ _ H); clear H.
    destruct (IHb H2 H4 H7).
    inversion_clear H0.
    destruct H9; simpl in *; subst.
    inversion_clear H1.
    destruct H0; simpl in *; subst; auto.
    elim (Sort_Inf_NotIn H4 H5).
    exists e'0; apply MapsTo_eq with x; auto.
      (* order. *)
    inversion_clear H1.
    destruct H0; simpl in *; subst; auto.
    elim (Sort_Inf_NotIn H2 H3).
    exists e0; apply MapsTo_eq with x; auto.
    (* order. *)
    apply H8 with k; auto.
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
    apply equal_2; auto.
    simpl.
    case (compare k k0);
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH).
    rewrite H2; simpl.
    apply equal_1; auto.
    apply equal_2; auto.
    generalize (equal_1 H H0 H3).
    simpl.
    case (compare k k0);
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH).
    rewrite H2; simpl; auto.
  Qed.

End Array.

End Raw.



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

  Record slist :=
    {this :> Raw.farray key elt;
     sorted : sort (Raw.ltk key_ord) this;
     nodefault : NoDefault this
    }.
  Definition farray := slist.


  Lemma empty_nodefault : NoDefault (Raw.empty key elt).
    unfold NoDefault.
    intros.
    apply Raw.empty_1.
  Qed.

  (* Boolean comparison over elements *)
  Definition cmp (e e':elt) :=
    match compare e e' with EQ _ => true | _ => false end.


  Lemma cmp_refl : forall e, cmp e e = true.
    unfold cmp.
    intros.
    destruct (compare e e); auto;
      apply lt_not_eq in l; now contradict l.
  Qed.
  

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
    intros.
    unfold raw_add_nodefault.
    case_eq (cmp e default_value); intro; auto.
    case_eq (Raw.mem key_comp x l); intro; auto.
    apply remove_nodefault; auto.
    unfold NoDefault; intros.
    assert (e <> default_value).
      unfold cmp in H.
      case (compare e default_value) in H; try now contradict H.
      apply lt_not_eq in l0; auto.
      apply lt_not_eq in l0; now auto.
    destruct (eq_dec k x).
    - symmetry in e0.
      apply (Raw.add_1 key_dec key_comp l e) in e0.
      unfold not; intro.
      specialize (Raw.add_sorted key_dec key_comp Hs x e).
      intro Hsadd.
      specialize (Raw.MapsTo_inj key_dec Hsadd e0 H1).
      intro. contradiction.
    - unfold not; intro.
      assert (x <> k). unfold not in *. intro. apply n. symmetry; auto.
      specialize (Raw.add_3 key_dec key_comp l e H2 H1).
      intro. now apply Hd in H3.
  Qed.
    
  
  Definition empty : farray :=
    Build_slist (Raw.empty_sorted elt key_ord) empty_nodefault.
  
  Definition is_empty m : bool := Raw.is_empty m.(this).
  
  Definition add x e m : farray :=
    Build_slist (add_sorted m.(sorted) x e)
                (add_nodefault m.(nodefault) m.(sorted) x e).
  
  Definition find x m : option elt := Raw.find key_comp x m.(this).
  
  Definition remove x m : farray :=
    Build_slist (Raw.remove_sorted key_comp m.(sorted) x) (remove_nodefault m.(nodefault) m.(sorted) x).
  
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
  Proof. intros m.
    apply (Raw.MapsTo_eq key_dec elt_dec). Qed.

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
  Proof. intros.
    unfold add, raw_add_nodefault.
    unfold MapsTo. simpl.
    case_eq (cmp e default_value); intro; auto.
    unfold cmp in H1. destruct (compare e default_value); try now contradict H1.
    apply Raw.add_1; auto.
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
  Proof. intros m; apply (Raw.elements_3w key_dec m.(sorted)). Qed.

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


  
  Lemma raw_equal_eq : forall a (Ha: Sorted (Raw.ltk key_ord) a) b (Hb: Sorted (Raw.ltk key_ord) b),
      Raw.equal key_comp cmp a b = true -> a = b.
  Proof.
    induction a; intros.
    simpl in H.
    case b in *; auto.
    now contradict H.
    destruct a as (xa, ea).
    simpl in H.
    case b in *.
    now contradict H.
    destruct p as (xb, eb).
    destruct (compare xa xb); auto; try (now contradict H).
    rewrite andb_true_iff in H. destruct H.
    unfold cmp in H.
    destruct (compare ea eb); auto; try (now contradict H).
    subst. apply f_equal.
    apply IHa; auto.
    now inversion Ha.
    now inversion Hb.
  Qed.
  
  
  Lemma eq_equal : forall m m', eq m m' <-> equal m m' = true.
  Proof.
    intros (l,Hl,Hd); induction l.
    intros (l',Hl',Hd'); unfold eq; simpl.
    destruct l'; unfold equal; simpl; intuition.
    intros (l',Hl',Hd'); unfold eq.
    destruct l'.
    destruct a; unfold equal; simpl; intuition.
    destruct a as (x,e).
    destruct p as (x',e').
    unfold equal; simpl.
    destruct (compare x x') as [Hlt|Heq|Hlt]; simpl; intuition.
    unfold cmp at 1.
    case (compare e e');
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH);
    clear HH; simpl.
    inversion_clear Hl.
    inversion_clear Hl'.
    apply nodefault_tail in Hd.
    apply nodefault_tail in Hd'.
    destruct (IHl H Hd (Build_slist H2 Hd')).
    unfold equal, eq in H5; simpl in H5; auto.
    destruct (andb_prop _ _ H); clear H.
    generalize H0; unfold cmp.
    case (compare e e');
    subst; intro HH; try (apply lt_not_eq in HH; now contradict HH);
      auto; intro; discriminate.
    destruct (andb_prop _ _ H); clear H.
    inversion_clear Hl.
    inversion_clear Hl'.
    apply nodefault_tail in Hd.
    apply nodefault_tail in Hd'.
    destruct (IHl H Hd (Build_slist H3 Hd')).
    unfold equal, eq in H6; simpl in H6; auto.
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
    apply (IHm H Hd (Build_slist H1 Hd')); auto.
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
    apply (IHm1 H Hd1 (Build_slist H3 Hd2) (Build_slist H5 Hd3)); intuition.
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
    apply (IHm1 H Hd1 (Build_slist H3 Hd2) (Build_slist H5 Hd3)); intuition.
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
    apply (IHm1 H0 H6 (Build_slist H4 H7)); intuition.
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
    destruct (IHm1 Hm11 Hd11 (Build_slist Hm22 Hd22));
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
  (* TODO *)

  
  
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
    intros.
    unfold raw_add_nodefault.
    rewrite cmp_refl.
    case_eq (Raw.mem key_comp x m); intro.
    auto.
    apply Raw.mem_3 in H; auto.
    apply raw_equal_eq; auto.
    apply Raw.remove_sorted; auto.
    apply Raw.equal_1; auto.
    apply Raw.remove_sorted; auto.
    unfold Raw.Equivb.
    split.
    intros.
    destruct (eq_dec x k). subst.
    split. intro. contradiction.
    intro. contradict H0.
    apply Raw.remove_1; auto.
    apply Raw.remove_4; auto.

    intros.
    destruct (eq_dec x k).
    assert (exists e, InA (Raw.eqk (elt:=elt)) (k, e) (Raw.remove key_comp x m)).
    exists e'. apply Raw.InA_eqke_eqk; auto.
    rewrite <- Raw.In_alt in H2; auto.
    contradict H2.
    apply Raw.remove_1; auto.
    apply key_comp.
    apply (Raw.remove_2 key_comp Hm n) in H0.
    specialize (Raw.remove_sorted key_comp Hm x). intros.
    specialize (Raw.MapsTo_inj key_dec H2 H0 H1).
    intro. subst. apply cmp_refl.
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
    intros.
    simpl.
    rewrite add_d_rem.
    case_eq (find y (remove x m)); auto.
    intros.
    apply find_2 in H0.
    unfold MapsTo, Raw.MapsTo in H0.
    assert (exists e, InA (Raw.eqk (elt:=elt)) (y, e) (remove x m).(this)).
    exists e. apply Raw.InA_eqke_eqk in H0. auto.
    rewrite <- Raw.In_alt in H1; auto.
    contradict H1.
    apply remove_1; auto.
    apply key_comp.
  Qed.
  
  Lemma add_neq_o : forall m x y e,
      ~ x = y -> find y (add x e m) = find y m.
  Proof.
    intros. rewrite eq_option_alt. intro e'. rewrite <- 2 find_mapsto_iff.
    apply add_neq_mapsto_iff; auto.
  Qed.
  Hint Resolve add_neq_o.



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
    destruct (compare e e'); auto; apply lt_not_eq in l; auto.
    destruct (compare e e'); auto; now contradict H1.
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
    case_eq (cmp v default_value); intro; auto.
    unfold cmp in H.
    case (compare v default_value) in H; auto; try now contradict H.
    rewrite e.
    rewrite add_eq_d; auto.
    assert (v <> default_value).
    unfold cmp in H.
    case (compare v default_value) in H; auto; try now contradict H.
    apply lt_not_eq in l. auto.
    apply lt_not_eq in l. auto.
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

  
  (* TODO *)
  Lemma find_ext_dec:
    (forall m1 m2: farray, Equal m1 m2 -> (equal m1 m2) = true).
  Proof. intros.
    apply Equal_Equivb in H.
    apply equal_1.
    exact H.
  Qed.


  Lemma extensionnality_eqb : forall a b,
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
      
  Lemma extensionnality : forall a b, (forall i, select a i = select b i) -> a = b.
  Proof.
    intros; apply equal_eq; apply extensionnality_eqb; auto.
  Qed.

  Section Classical_extensionnality.

    Require Import Classical_Pred_Type ClassicalEpsilon.

    
    Lemma extensionnality2 : forall a b, a <> b -> (exists i, select a i <> select b i).
    Proof.
      intros.
      apply not_all_ex_not.
      unfold not in *.
      intros. apply H. apply extensionnality; auto.
    Qed.

    Definition diff_index_p : forall a b, a <> b -> { i | select a i <> select b i } :=
      (fun a b u => constructive_indefinite_description _ (@extensionnality2 _ _ u)).

    Definition diff_index : forall a b, a <> b -> key :=
      (fun a b u => proj1_sig (diff_index_p u)).


    Example d : forall a b (u:a <> b), let i := diff_index u in select a i <> select b i.
      unfold diff_index.
      intros.
      destruct (diff_index_p u). simpl. auto.
    Qed.

    Definition diff (a b: farray) : key.
      case_eq (equal a b); intro.
      - apply default_value.
      - apply (diff_index (notequal_neq H)).
        (* destruct (diff_index_p H). apply x. *)
    Defined.

    
   Lemma select_over_diff: forall a b, a <> b ->
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

       
  End Classical_extensionnality.

End FArray.

(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

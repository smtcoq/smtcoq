(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(*** Spl -- a small checker for simplifications ***)

Require Import List PArray Bool Int63 ZMicromega.
Require Import Misc State SMT_terms.

Local Open Scope array_scope.
Local Open Scope int63_scope.


(* Simplification of SMTLIB-2 operators *)

Section Operators.

  Import Form.

  Variable t_form : PArray.array Form.form.
  Variable t_atom : PArray.array Atom.atom.

  Local Notation get_form := (PArray.get t_form).
  Local Notation get_atom := (PArray.get t_atom).


  Fixpoint check_in x l :=
    match l with
      | nil => false
      | t::q => if x =? t then true else check_in x q
    end.


  Lemma check_in_spec : forall x l, check_in x l = true <-> In x l.
  Proof.
    intro x; induction l as [ |t q IHq]; simpl.
    split; intro H; try discriminate; elim H.
    case_eq (x =? t).
    rewrite eqb_spec; intro; subst t; split; auto.
    intro H; rewrite IHq; split; auto; intros [H1|H1]; auto; rewrite H1, eqb_refl in H; discriminate.
  Qed.


  Fixpoint check_diseqs_complete_aux a dist t :=
    match dist with
      | nil => true
      | b::q => if aexistsbi (fun _ (x:option (int*int)) =>
        match x with
          | Some (a',b') => ((a =? a') && (b =? b')) || ((a =? b') && (b =? a'))
          | None => false
        end
      ) t then check_diseqs_complete_aux a q t else false
    end.


  Lemma check_diseqs_complete_aux_spec : forall a dist t,
    check_diseqs_complete_aux a dist t = true <->
    forall y, In y dist -> exists i, i <? length t /\
      (t.[i] = Some (a,y) \/ t.[i] = Some (y,a)).
  Proof.
    intros a dist t; induction dist as [ |b q IHq]; simpl; split; auto.
    intros _ y H; inversion H.
    case_eq (aexistsbi (fun _ (x : option (int * int)) => match x with | Some (a', b') => (a =? a') && (b =? b') || (a =? b') && (b =? a') | None => false end) t); try discriminate; rewrite aexistsbi_spec; intros [i [H1 H2]]; rewrite IHq; clear IHq; intros H3 y [H4|H4]; auto; subst y; exists i; split; auto; generalize H2; case (t .[ i]); try discriminate; intros [a' b']; rewrite orb_true_iff, !andb_true_iff, !Int63.eqb_spec; intros [[H4 H5]|[H4 H5]]; subst a' b'; auto.
    intro H1; case_eq (aexistsbi (fun _ (x : option (int * int)) => match x with | Some (a', b') => (a =? a') && (b =? b') || (a =? b') && (b =? a') | None => false end) t).
    intros _; rewrite IHq; clear IHq; intros y Hy; apply H1; auto.
    rewrite aexistsbi_false_spec; destruct (H1 b (or_introl (refl_equal b))) as [i [H2 H3]]; intro H; rewrite <- (H _ H2); destruct H3 as [H3|H3]; rewrite H3; rewrite !eqb_refl; auto; rewrite orb_true_r; auto.
  Qed.


  Lemma check_diseqs_complete_aux_false_spec : forall a dist t,
    check_diseqs_complete_aux a dist t = false <->
    exists y, In y dist /\ forall i, i <? length t ->
      (t.[i] <> Some (a,y) /\ t.[i] <> Some (y,a)).
  Proof.
    intros a dist t; induction dist as [ |b q IHq]; simpl; split; try discriminate.
    intros [y [H _]]; elim H.
    case_eq (aexistsbi (fun _ (x : option (int * int)) => match x with | Some (a', b') => (a =? a') && (b =? b') || (a =? b') && (b =? a') | None => false end) t).
    intros _; rewrite IHq; clear IHq; intros [y [H3 H4]]; exists y; auto.
    rewrite aexistsbi_false_spec; intros H _; exists b; split; auto; intros i Hi; split; intro H1; generalize (H _ Hi); rewrite H1, !eqb_refl; try discriminate; rewrite orb_true_r; discriminate.
    intros [y [H1 H2]]; case_eq (aexistsbi (fun _ (x : option (int * int)) => match x with | Some (a', b') => (a =? a') && (b =? b') || (a =? b') && (b =? a') | None => false end) t); auto; rewrite aexistsbi_spec; intros [i [H3 H4]]; rewrite IHq; clear IHq; exists y; destruct H1 as [H1|H1]; auto; subst y; case_eq (t.[i]); [intros [a' b'] Heq|intro Heq]; rewrite Heq in H4; try discriminate; rewrite orb_true_iff, !andb_true_iff, !eqb_spec in H4; destruct H4 as [[H4 H5]|[H4 H5]]; subst a' b'; generalize (H2 _ H3); rewrite Heq; intros [H4 H5]; [elim H4|elim H5]; auto.
  Qed.


  Fixpoint check_diseqs_complete dist t :=
    match dist with
      | nil => true
      | a::q => if check_diseqs_complete_aux a q t then check_diseqs_complete q t else false
    end.


  Lemma check_diseqs_complete_spec : forall dist t,
    check_diseqs_complete dist t = true <->
    forall x y, In2 x y dist -> exists i, i <? length t /\
      (t.[i] = Some (x,y) \/ t.[i] = Some (y,x)).
  Proof.
    intros dist t; induction dist as [ |a q IHq]; simpl; split; auto.
    intros _ x y H; inversion H.
    case_eq (check_diseqs_complete_aux a q t); try discriminate; rewrite check_diseqs_complete_aux_spec, IHq; clear IHq; intros H1 H2 x y H3; inversion H3; auto.
    intro H; case_eq (check_diseqs_complete_aux a q t).
    rewrite IHq; clear IHq; intros _ x y H1; apply H; constructor 2; auto.
    rewrite check_diseqs_complete_aux_false_spec; clear IHq; intros [y [H1 H2]]; destruct (H _ _ (In2_hd _ a _ _ H1)) as [i [H3 [H4|H4]]]; elim (H2 _ H3); rewrite H4; intros H5 H6; [elim H5|elim H6]; auto.
  Qed.


  Lemma check_diseqs_complete_false_spec : forall dist t,
    check_diseqs_complete dist t = false <->
    exists x y, In2 x y dist /\ forall i, i <? length t ->
      (t.[i] <> Some (x,y) /\ t.[i] <> Some (y,x)).
  Proof.
    intros dist t; induction dist as [ |a q IHq]; simpl; split; try discriminate.
    intros [x [y [H _]]]; inversion H.
    case_eq (check_diseqs_complete_aux a q t).
    rewrite IHq; clear IHq; intros _ [x [y [H2 H3]]]; inversion H2; clear H2; subst q; exists x; exists y; split; auto; constructor 2.
    constructor 1; auto.
    constructor 2; auto.
    rewrite check_diseqs_complete_aux_false_spec; intros [y [H1 H2]] _; clear IHq; exists a; exists y; split; auto; constructor; auto.
    intros [x [y [H1 H2]]]; case_eq (check_diseqs_complete_aux a q t); auto; rewrite IHq; clear IHq; inversion H1; clear H1.
    subst x q; rewrite check_diseqs_complete_aux_spec; intro H; destruct (H _ H0) as [i [H1 H3]]; elim (H2 _ H1); intros H4 H5; destruct H3; [elim H4|elim H5]; auto.
    subst k q; intros _; exists x; exists y; split; auto.
  Qed.


  Definition check_diseqs ty dist diseq :=
    let t := amap (fun t =>
      if Lit.is_pos t then None else
        match get_form (Lit.blit t) with
          | Fatom a =>
            match get_atom a with
              | Atom.Abop (Atom.BO_eq A) h1 h2 =>
                if (Typ.eqb ty A) && (negb (h1 =? h2)) && (check_in h1 dist) && (check_in h2 dist) then
                  Some (h1,h2)
                else
                  None
              | _ => None
            end
          | _ => None
        end
    ) diseq in
    aforallbi (fun _ x => match x with | None => false | _ => true end) t &&
    check_diseqs_complete dist t.


  Lemma check_diseqs_spec : forall A dist diseq,
    check_diseqs A dist diseq = true <->
    ((forall i, i <? length diseq ->
      let t := diseq.[i] in
        ~ Lit.is_pos t /\
        exists a, get_form (Lit.blit t) = Fatom a /\
          exists h1 h2, get_atom a = Atom.Abop (Atom.BO_eq A) h1 h2 /\
            h1 <> h2 /\ (In2 h1 h2 dist \/ In2 h2 h1 dist))
    /\
    (forall x y, In2 x y dist -> exists i, i <? length diseq /\
      let t := diseq.[i] in
        ~ Lit.is_pos t /\
        exists a, get_form (Lit.blit t) = Fatom a /\
          x <> y /\
          (get_atom a = Atom.Abop (Atom.BO_eq A) x y \/
            get_atom a = Atom.Abop (Atom.BO_eq A) y x))).
  Proof.
    intros A dist diseq; unfold check_diseqs; rewrite andb_true_iff,
     aforallbi_spec, check_diseqs_complete_spec, length_amap; split; intros [H1 H2]; split.
    clear H2; intros i Hi; generalize (H1 _ Hi); rewrite get_amap; 
    auto; case_eq (Lit.is_pos (diseq .[ i])); try discriminate; intro Heq1; case_eq (get_form (Lit.blit (diseq .[ i]))); 
    try discriminate; intros a Heq2; case_eq (get_atom a); try discriminate; intros [ | | | | | | | B | | | | | | | | | | | | ]; try discriminate; intros h1 h2 Heq3; case_eq (Typ.eqb A B); try discriminate; change (Typ.eqb A B = true) with (is_true (Typ.eqb A B)); rewrite Typ.eqb_spec; intro; subst B; case_eq (h1 =? h2); try discriminate; rewrite eqb_false_spec; intro H2; case_eq (check_in h1 dist); try discriminate; case_eq (check_in h2 dist); try discriminate; rewrite !check_in_spec; intros H3 H4 _; split; try discriminate; exists a; split; auto; exists h1, h2; repeat split; auto; rewrite <- In2_In; auto.
    clear H1; intros x y Hxy; destruct (H2 _ _ Hxy) as [i [H1 H4]]; clear H2; rewrite get_amap in H4; auto; exists i; split; auto; generalize H4; 
    
    case_eq (Lit.is_pos (diseq .[ i])); intro Heq; try (intros [H|H]; discriminate); case_eq (get_form (Lit.blit (diseq .[ i]))); [intros a| | |intros a1 a2|intros a1|intros a1|intros a1|intros a1 a2|intros a1 a2| intros a1 a2 a3|intros a ls]; intro Heq2; try (intros [H|H]; discriminate); case_eq (get_atom a); [intros a1|intros a1 a2|intros [ | | | | | | | B | | | | | | | | | | | | ] h1 h2|intros a1 a2|intros a1 a2 | intros a1 a2]; intro Heq3; try (intros [H|H]; discriminate); try (case_eq (Typ.eqb A B); try (intros _ [H|H]; discriminate); change (Typ.eqb A B = true) with (is_true (Typ.eqb A B)); rewrite Typ.eqb_spec; intro; subst B; case_eq (h1 =? h2); try (intros _ [H|H]; discriminate); rewrite eqb_false_spec; intro H10; case (check_in h1 dist); try (intros [H|H]; discriminate); case (check_in h2 dist); try (intros [H|H]; discriminate); simpl; intro H3; split; try discriminate; exists a; split; auto; destruct H3 as [H3|H3]; inversion H3; subst; auto).
intros. destruct H0; now contradict H0.
    
    clear H2; intros i Hi; rewrite get_amap; auto; destruct (H1 _ Hi) as [H2 [a [H3 [h1 [h2 [H4 [H5 H6]]]]]]]; clear H1; replace (Lit.is_pos (diseq .[ i])) with false by (case_eq (Lit.is_pos (diseq .[ i])); auto); rewrite H3, H4, Typ.eqb_refl; simpl; replace (h1 =? h2) with false by (case_eq (h1 =? h2); auto; rewrite eqb_spec; intro H; elim H5; auto); simpl; rewrite <- In2_In, <- !check_in_spec in H6; auto; destruct H6 as [H6 H7]; rewrite H6, H7; auto.
    clear H1; intros x y Hxy; destruct (H2 _ _ Hxy) as [i [H1 [H3 [a [H4 [H6 H5]]]]]]; clear H2; exists i; split; auto; rewrite get_amap; auto; replace (Lit.is_pos (diseq .[ i])) with false by (case_eq (Lit.is_pos (diseq .[ i])); auto); rewrite H4; assert (H7 := or_introl (In2 y x dist) Hxy); rewrite <- In2_In, <- !check_in_spec in H7; auto; destruct H7 as [H7 H8]; destruct H5 as [H5|H5]; rewrite H5, Typ.eqb_refl; [replace (x =? y) with false by (case_eq (x =? y); auto; rewrite eqb_spec; auto)|replace (y =? x) with false by (case_eq (y =? x); auto; rewrite eqb_spec; auto)]; simpl; rewrite H7, H8; auto.
  Qed.


  (* Definition check_diseqs ty dist diseq := *)
  (*   PArray.forallb (fun t => *)
  (*     if Lit.is_pos t then false else *)
  (*       match get_form (Lit.blit t) with *)
  (*         | Fatom a => *)
  (*           match get_atom a with *)
  (*             | Atom.Abop (Atom.BO_eq A) h1 h2 => *)
  (*               (Typ.eqb ty A) && (negb (h1 =? h2)) && (check_in h1 dist) && (check_in h2 dist) *)
  (*             | _ => false *)
  (*           end *)
  (*         | _ => false *)
  (*       end) diseq. *)


  (* Lemma check_diseqs_spec : forall A dist diseq, *)
  (*   check_diseqs A dist diseq <-> forall i, i <? length diseq -> *)
  (*     let t := diseq.[i] in *)
  (*     ~ Lit.is_pos t /\ *)
  (*     exists a, get_form (Lit.blit t) = Fatom a /\ *)
  (*       exists h1 h2, get_atom a = Atom.Abop (Atom.BO_eq A) h1 h2 /\ *)
  (*         (h1 <> h2) /\ ((In2 h1 h2 dist) \/ (In2 h2 h1 dist)). *)
  (* Proof. *)
  (*   intros A dist diseq; unfold check_diseqs; unfold is_true at 1; rewrite PArray.forallb_spec; split. *)
  (*   intros H i Hi; generalize (H _ Hi); clear H; case (Lit.is_pos (diseq .[ i])); try discriminate; case (get_form (Lit.blit (diseq .[ i]))); try discriminate; intros a H1; split; try discriminate; exists a; split; auto; generalize H1; clear H1; case (get_atom a); try discriminate; intros [ | | | | | | |B] h1 h2; try discriminate; rewrite !andb_true_iff; change (check_in h1 dist = true) with (is_true (check_in h1 dist)); change (check_in h2 dist = true) with (is_true (check_in h2 dist)); rewrite !check_in_spec; intros [[[H1 H4] H2] H3]; change (is_true (Typ.eqb A B)) in H1; rewrite Typ.eqb_spec in H1; subst B; exists h1; exists h2; split; auto; assert (H5: h1 <> h2) by (intro H; rewrite H, eqb_refl in H4; discriminate); split; auto; rewrite <- In2_In; auto. *)
  (*   intros H i Hi; generalize (H _ Hi); clear H; case (Lit.is_pos (diseq .[ i])); try (intros [H _]; elim H; reflexivity); intros [_ [a [H1 [h1 [h2 [H2 [H3 H4]]]]]]]; rewrite H1, H2; rewrite !andb_true_iff; rewrite <- (In2_In H3) in H4; destruct H4 as [H4 H5]; change (check_in h1 dist = true) with (is_true (check_in h1 dist)); change (check_in h2 dist = true) with (is_true (check_in h2 dist)); rewrite !check_in_spec; repeat split; auto; case_eq (h1 =? h2); auto; try (rewrite Typ.eqb_refl; auto); rewrite eqb_spec; intro; subst h1; elim H3; auto. *)
  (* Qed. *)


  Definition check_distinct ha diseq :=
    match get_atom ha with
      | Atom.Anop (Atom.NO_distinct ty) dist =>
        check_diseqs ty dist diseq
      | _ => false
    end.


  Lemma check_distinct_spec : forall ha diseq,
    check_distinct ha diseq = true <-> exists A dist,
      get_atom ha = Atom.Anop (Atom.NO_distinct A) dist /\
      check_diseqs A dist diseq = true.
  Proof.
    intros ha diseq; unfold check_distinct; split.
    case (get_atom ha); try discriminate; intros [A] l H; exists A; exists l; auto.
    intros [A [dist [H1 H2]]]; rewrite H1; auto.
  Qed.


  Definition check_distinct_two_args f1 f2 :=
    match get_form f1, get_form f2 with
      | Fatom ha, Fatom hb =>
        match get_atom ha, get_atom hb with
          | Atom.Anop (Atom.NO_distinct ty) (x::y::nil), Atom.Abop (Atom.BO_eq ty') x' y' => (Typ.eqb ty ty') && (((x =? x') && (y =? y')) || ((x =? y') && (y =? x')))
          | _, _ => false
        end
      | _, _ => false
    end.


  Lemma check_distinct_two_args_spec : forall f1 f2,
    check_distinct_two_args f1 f2 = true <-> exists ha hb ty x y,
      get_form f1 = Fatom ha /\
      get_form f2 = Fatom hb /\
      get_atom ha = Atom.Anop (Atom.NO_distinct ty) (x::y::nil) /\
      (get_atom hb = Atom.Abop (Atom.BO_eq ty) x y \/
       get_atom hb = Atom.Abop (Atom.BO_eq ty) y x).
  Proof.
    intros f1 f2; unfold check_distinct_two_args; split.
    case (get_form f1); try discriminate; intro ha; case (get_form f2); try discriminate; intro hb; case_eq (get_atom ha); try discriminate; intros [A] [ |x [ |y [ |l]]] Heq1; try discriminate; case_eq (get_atom hb); try discriminate; intros [ | | | | | | |B | | | | | | | | | | | | ] x' y' Heq2; try discriminate; rewrite !andb_true_iff, orb_true_iff, !andb_true_iff; change (Typ.eqb A B = true) with (is_true (Typ.eqb A B)); rewrite Typ.eqb_spec, !Int63.eqb_spec; intros [H1 [[H2 H3]|[H2 H3]]]; subst B x' y'; exists ha, hb, A, x, y; auto.
    intros [ha [hb [A [x [y [H1 [H2 [H3 [H4|H4]]]]]]]]]; rewrite H1, H2, H3, H4, Typ.eqb_refl, !eqb_refl; auto; rewrite orb_true_r; auto.
  Qed.


  Section Valid1.

    Variables (t_i : array SMT_classes.typ_compdec)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).
    Local Notation interp_form_hatom_bv :=
      (Atom.interp_form_hatom_bv t_i t_func t_atom).
    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom interp_form_hatom_bv t_form).

    Let wf_t_atom : Atom.wf t_atom.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let default_t_atom : default t_atom = Atom.Acop Atom.CO_xH.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Lemma default_t_form : default t_form = Ftrue.
    Proof. destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as [[H _] _]; auto. Qed.

    Lemma wf_t_form : wf t_form.
    Proof. destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as [[_ H] _]; auto. Qed.

    Local Hint Immediate wf_t_atom default_t_atom default_t_form wf_t_form : smtcoq_spl_op.

    Lemma interp_check_distinct : forall ha diseq,
      check_distinct ha diseq = true ->
      interp_form_hatom ha = afold_left bool true andb (amap (Lit.interp rho) diseq).
    Proof.
      intros ha diseq; rewrite check_distinct_spec; intros [A [dist [H1 H2]]]; rewrite check_diseqs_spec in H2; destruct H2 as [H2 H3]; unfold Atom.interp_form_hatom, Atom.interp_bool, Atom.interp_hatom; rewrite Atom.t_interp_wf; auto with smtcoq_spl_op; rewrite H1; simpl; generalize (Atom.compute_interp_spec_rev t_i (get (Atom.t_interp t_i t_func t_atom)) A dist); case (Atom.compute_interp t_i (get (Atom.t_interp t_i t_func t_atom)) A nil); simpl.
      intros l H4; case_eq (distinct (Typ.i_eqb t_i A) (rev l)).
      rewrite distinct_spec; intro H5; symmetry; apply afold_left_andb_true; rewrite length_amap; intros i Hi; rewrite get_amap by exact Hi; destruct (H2 _ Hi) as [H9 [a [H10 [h1 [h2 [H6 [H7 H8]]]]]]]; unfold Lit.interp; replace (Lit.is_pos (diseq .[ i])) with false by (case_eq (Lit.is_pos (diseq .[ i])); auto with smtcoq_spl_op smtcoq_core); unfold Var.interp; rewrite Form.wf_interp_form; auto with smtcoq_spl_op smtcoq_core; rewrite H10; simpl; rewrite Atom.t_interp_wf; auto with smtcoq_spl_op smtcoq_core; rewrite H6; simpl; unfold Atom.apply_binop; unfold Atom.wt in wt_t_atom; unfold is_true in wt_t_atom; rewrite aforallbi_spec in wt_t_atom; assert (H11: a <? length t_atom).
      case_eq (a <? length t_atom); auto with smtcoq_spl_op smtcoq_core; intro H11; rewrite (get_out_of_bounds _ _ _ H11) in H6; rewrite default_t_atom in H6; inversion H6.
      generalize (wt_t_atom _ H11); rewrite H6; simpl; rewrite !andb_true_iff; change (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) h1) A = true) with (is_true (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) h1) A)); change (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) h2) A = true) with (is_true (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) h2) A)); rewrite !Typ.eqb_spec; intros [[_ H13] H12]; generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom h1); rewrite H13; intros [v1 HH1]; generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom h2); rewrite H12; intros [v2 HH2]; rewrite HH1, HH2; simpl; rewrite Typ.cast_refl; simpl; destruct H8 as [H8|H8]; [ |rewrite Typ.i_eqb_sym]; rewrite H5; auto with smtcoq_spl_op smtcoq_core; rewrite H4; [exists h2; exists h1|exists h1; exists h2]; auto with smtcoq_spl_op smtcoq_core.
      rewrite distinct_false_spec; intros [v2 [v1 [H5 H6]]]; rewrite H4 in H5; destruct H5 as [a [b [H5 [H7 H8]]]]; clear H4; change (Typ.i_eqb t_i A v2 v1 = true) with (is_true (Typ.i_eqb t_i A v2 v1)) in H6; rewrite Typ.i_eqb_spec in H6; subst v2; clear H2; destruct (H3 _ _ H5) as [i [H2 [H4 [hb [H6 [H9 H10]]]]]]; clear H3; symmetry; apply (afold_left_andb_false i); rewrite ?length_amap; auto with smtcoq_spl_op smtcoq_core; rewrite get_amap by assumption; unfold Lit.interp; replace (Lit.is_pos (diseq .[ i])) with false by (case_eq (Lit.is_pos (diseq .[ i])); auto with smtcoq_spl_op smtcoq_core); unfold Var.interp; rewrite Form.wf_interp_form; auto with smtcoq_spl_op smtcoq_core; rewrite H6; simpl; rewrite Atom.t_interp_wf; auto with smtcoq_spl_op smtcoq_core; destruct H10 as [H10|H10]; rewrite H10; simpl; rewrite H7, H8; simpl; rewrite Typ.cast_refl; simpl; replace (Typ.i_eqb t_i A v1 v1) with true; auto with smtcoq_spl_op smtcoq_core; symmetry; change (is_true (Typ.i_eqb t_i A v1 v1)); rewrite Typ.i_eqb_spec; auto with smtcoq_spl_op smtcoq_core.
      intros [a [H20 H21]]; assert (H4: ha <? length t_atom).
      case_eq (ha <? length t_atom); auto with smtcoq_spl_op smtcoq_core; intro Heq; generalize H1; rewrite get_out_of_bounds; auto with smtcoq_spl_op smtcoq_core; rewrite default_t_atom; discriminate.
      unfold Atom.wt in wt_t_atom; unfold is_true in wt_t_atom; rewrite aforallbi_spec in wt_t_atom; generalize (wt_t_atom _ H4); rewrite H1; simpl; rewrite andb_true_iff, forallb_forall; intros [_ H5]; assert (H6 := H5 _ H20); generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a); intros [va Ha]; rewrite Ha in H21; simpl in H21; elim H21; apply Typ.eqb_spec; auto with smtcoq_spl_op smtcoq_core.
    Qed.

    Lemma interp_check_distinct_two_args : forall f1 f2,
      check_distinct_two_args f1 f2 = true ->
      rho f1 = negb (rho f2).
    Proof.
      intros f1 f2; rewrite check_distinct_two_args_spec; intros [ha [hb [A [x [y [H1 [H2 [H3 [H4|H4]]]]]]]]]; unfold Form.interp_state_var; assert (H5: f1 <? length t_form) by (case_eq (f1 <? length t_form); auto with smtcoq_spl_op smtcoq_core; intro Heq; generalize H1; rewrite get_out_of_bounds; auto with smtcoq_spl_op smtcoq_core; rewrite default_t_form; discriminate); assert (H6: f2 <? length t_form) by (case_eq (f2 <? length t_form); auto with smtcoq_spl_op smtcoq_core; intro Heq; generalize H2; rewrite get_out_of_bounds; auto with smtcoq_spl_op smtcoq_core; rewrite default_t_form; discriminate); rewrite !Form.t_interp_wf; auto with smtcoq_spl_op smtcoq_core; rewrite H1, H2; simpl; unfold Atom.interp_form_hatom, Atom.interp_hatom; rewrite !Atom.t_interp_wf; auto with smtcoq_spl_op smtcoq_core; rewrite H3, H4; simpl; unfold Atom.wt,is_true in wt_t_atom; rewrite aforallbi_spec in wt_t_atom; assert (H7: hb <? length t_atom) by (case_eq (hb <? length t_atom); auto with smtcoq_spl_op smtcoq_core; intro Heq; generalize H4; rewrite get_out_of_bounds; auto with smtcoq_spl_op smtcoq_core; rewrite default_t_atom; discriminate); generalize (wt_t_atom _ H7); rewrite H4; simpl; case (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) hb); try discriminate; simpl; rewrite andb_true_iff; change (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) x) A = true) with (is_true (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) x) A)); change (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) y) A = true) with (is_true (Typ.eqb (Atom.get_type' t_i (Atom.t_interp t_i t_func t_atom) y) A)); rewrite !Typ.eqb_spec; intros [H8 H9]; generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom x), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom y); rewrite H8, H9; intros [v1 HH1] [v2 HH2]; rewrite HH1, HH2; simpl; rewrite Typ.cast_refl; auto with smtcoq_spl_op smtcoq_core; rewrite Typ.i_eqb_sym; auto with smtcoq_spl_op smtcoq_core.
    Qed.


    (* Lemma interp_check_distinct : forall ha diseq, *)
    (*   check_distinct ha diseq -> *)
    (*   interp_form_hatom ha -> afold_left bool int true andb (Lit.interp rho) diseq. *)
    (* Proof. *)
  (*     intros ha diseq; rewrite check_distinct_spec; intros [A [dist [H1 H]]]; rewrite check_diseqs_spec in H; unfold Atom.interp_form_hatom, Atom.interp_bool, Atom.interp_hatom; rewrite Atom.t_interp_wf; auto with smtcoq_spl_op smtcoq_core; rewrite H1; simpl; generalize (Atom.compute_interp_spec_rev t_i (get (Atom.t_interp t_i t_func t_atom)) A dist); case (Atom.compute_interp t_i (get (Atom.t_interp t_i t_func t_atom)) A nil); simpl. *)
  (*     intros l H2; unfold is_true; rewrite distinct_spec; intro H3; apply afold_left_andb_true; intros i Hi; destruct (H _ Hi) as [H4 [a [H5 [h1 [h2 [H6 [H7 H8]]]]]]]; unfold Lit.interp; replace (Lit.is_pos (diseq .[ i])) with false by (case_eq (Lit.is_pos (diseq .[ i])); auto with smtcoq_spl_op smtcoq_core); unfold Var.interp; rewrite Form.wf_interp_form; auto with smtcoq_spl_op smtcoq_core; rewrite H5; simpl; rewrite Atom.t_interp_wf; auto with smtcoq_spl_op smtcoq_core; rewrite H6; simpl; unfold Atom.apply_binop; unfold Atom.wt in wt_t_atom; unfold is_true in wt_t_atom; rewrite aforallbi_spec in wt_t_atom; assert (H10: a <? length t_atom). *)
  (*     case_eq (a <? length t_atom); auto with smtcoq_spl_op smtcoq_core; intro H10; rewrite (get_out_of_bounds _ _ _ H10) in H6; rewrite default_t_atom in H6; inversion H6. *)
  (*     generalize (wt_t_atom _ H10); rewrite H6; simpl; rewrite !andb_true_iff. change (Typ.eqb (Atom.get_type t_i t_func t_atom h1) A = true) with (is_true (Typ.eqb (Atom.get_type t_i t_func t_atom h1) A)); change (Typ.eqb (Atom.get_type t_i t_func t_atom h2) A = true) with (is_true (Typ.eqb (Atom.get_type t_i t_func t_atom h2) A)); rewrite !Typ.eqb_spec; intros [[_ H11] H12]; generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom h1); rewrite H11; intros [v1 HH1]; generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom h2); rewrite H12; intros [v2 HH2]; rewrite HH1, HH2; simpl; rewrite Typ.cast_refl; simpl; destruct H8 as [H8|H8]; [ |rewrite Typ.i_eqb_sym]; rewrite H3; auto with smtcoq_spl_op smtcoq_core; rewrite H2; [exists h2; exists h1|exists h1; exists h2]; auto with smtcoq_spl_op smtcoq_core. *)
  (*     intros [a [H2 H3]] _; assert (H4: ha <? length t_atom). *)
  (*     case_eq (ha <? length t_atom); auto with smtcoq_spl_op smtcoq_core; intro Heq; generalize H1; rewrite get_out_of_bounds; auto with smtcoq_spl_op smtcoq_core; rewrite default_t_atom; discriminate. *)
  (*     unfold Atom.wt in wt_t_atom; unfold is_true in wt_t_atom; rewrite aforallbi_spec in wt_t_atom; generalize (wt_t_atom _ H4); rewrite H1; simpl; rewrite andb_true_iff, forallb_forall; intros [_ H5]; assert (H6 := H5 _ H2); generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a); intros [va Ha]; rewrite Ha in H3; simpl in H3; elim H3; apply Typ.eqb_spec; auto with smtcoq_spl_op smtcoq_core. *)
  (*   Qed. *)

  End Valid1.


  Section AUX.

    Variable check_var : var -> var -> bool.

    Definition check_lit l1 l2 :=
      (l1 =? l2) || ((Bool.eqb (Lit.is_pos l1) (Lit.is_pos l2)) && (check_var (Lit.blit l1) (Lit.blit l2))) || ((Bool.eqb (Lit.is_pos l1) (negb (Lit.is_pos l2))) && (check_distinct_two_args (Lit.blit l1) (Lit.blit l2))).

    (* Definition check_lit l1 l2 := *)
    (*   (l1 =? l2) || ((Lit.is_pos l1) && (Lit.is_pos l2) && (check_var (Lit.blit l1) (Lit.blit l2))) || ((negb (Lit.is_pos l1)) && (negb (Lit.is_pos l2)) && (check_var (Lit.blit l2) (Lit.blit l1))). *)

    Definition check_form_aux a b :=
      match a, b with
        | Fatom ha, Fand diseq => check_distinct ha diseq
        | Fatom a, Fatom b => a =? b
        | Ftrue, Ftrue => true
        | Ffalse, Ffalse => true
        | Fnot2 i1 l1, Fnot2 i2 l2 => (i1 =? i2) && (check_lit l1 l2)
        | Fand a1, Fand a2 => (length a1 =? length a2) && (aforallbi (fun i l => check_lit l (a2.[i])) a1)
        | For a1, For a2 => (length a1 =? length a2) && (aforallbi (fun i l => check_lit l (a2.[i])) a1)
        | Fimp a1, Fimp a2 => (length a1 =? length a2) && (aforallbi (fun i l => check_lit l (a2.[i])) a1)
          (* (length a1 =? length a2) && (aforallbi (fun i l => if i <? length a1 - 1 then check_lit (a2.[i]) l else check_lit l (a2.[i])) a1) *)
        | Fxor l1 l2, Fxor j1 j2 => check_lit l1 j1 && check_lit l2 j2
          (* check_lit l1 j1 && check_lit j1 l1 && check_lit l2 j2 && check_lit j2 l2 *)
          (* (* let a := check_lit l1 j1 in *) *)
          (* (* let b := check_lit l2 j2 in *) *)
          (* (* let c := check_lit l1 j2 in *) *)
          (* (* let d := check_lit l2 j1 in *) *)
          (* (* let e := check_lit j1 l1 in *) *)
          (* (* let f := check_lit j1 l2 in *) *)
          (* (*   negb (((negb a) && b && (negb c)) || (c && e && (negb f)) || (b && (negb e) && f) || (a && (negb b) && (negb d))) *) *)
        | Fiff l1 l2, Fiff j1 j2 => check_lit l1 j1 && check_lit l2 j2
          (* check_lit l1 j1 && check_lit j1 l1 && check_lit l2 j2 && check_lit j2 l2 *)
        | Fite l1 l2 l3, Fite j1 j2 j3 => check_lit l1 j1 && check_lit l2 j2 && check_lit l3 j3
          (* check_lit l1 j1 && check_lit j1 l1 && check_lit l2 j2 && check_lit l3 j3 *)
        | _, _ => false
      end.

    Variables (t_i : array SMT_classes.typ_compdec)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).
    Local Notation interp_form_hatom_bv :=
      (Atom.interp_form_hatom_bv t_i t_func t_atom).
    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom interp_form_hatom_bv t_form).

    Hypothesis interp_check_var : forall x y,
      check_var x y -> Var.interp rho x = Var.interp rho y.

    (* Hypothesis interp_check_var : forall x y, *)
    (*   check_var x y -> Var.interp rho x -> Var.interp rho y. *)

    (* Local Hint Resolve interp_check_var. *)

    Lemma interp_check_lit : forall l1 l2,
      check_lit l1 l2 -> Lit.interp rho l1 = Lit.interp rho l2.
    Proof.
      unfold check_lit; intros l1 l2; unfold is_true; rewrite !orb_true_iff, !andb_true_iff; intros [[H1|[H1 H2]]|[H1 H2]].
      rewrite eqb_spec in H1; rewrite H1; auto with smtcoq_core.
      rewrite Bool.eqb_true_iff in H1; unfold Lit.interp; rewrite H1, (interp_check_var _ _ H2); auto with smtcoq_core.
      generalize H1; unfold Lit.interp; case (Lit.is_pos l1); case (Lit.is_pos l2); try discriminate; intros _; unfold Var.interp; rewrite (interp_check_distinct_two_args _ t_func ch_atom ch_form wt_t_atom _ _ H2); auto with smtcoq_core; case (rho (Lit.blit l2)); auto with smtcoq_core.
    Qed.

    (* Lemma interp_check_lit : forall l1 l2, *)
    (*   check_lit l1 l2 -> Lit.interp rho l1 -> Lit.interp rho l2 = true. *)
    (* Proof. *)
    (*   unfold check_lit; intros l1 l2; unfold is_true; rewrite !orb_true_iff, !andb_true_iff; intros [[H1|[[H1 H2] H3]]|[[H1 H2] H3]]. *)
    (*   rewrite Int63.eqb_spec in H1; subst l1; auto with smtcoq_core. *)
    (*   unfold Lit.interp; rewrite H1, H2; apply interp_check_var; auto with smtcoq_core. *)
    (*   unfold Lit.interp; case_eq (Lit.is_pos l1); intro Heq; rewrite Heq in H1; try discriminate; clear Heq H1; case_eq (Lit.is_pos l2); intro Heq; rewrite Heq in H2; try discriminate; clear Heq H2; case_eq (Var.interp rho (Lit.blit l1)); try discriminate; intros H4 _; case_eq (Var.interp rho (Lit.blit l2)); auto with smtcoq_core; intro H5; rewrite (interp_check_var _ _ H3 H5) in H4; discriminate. *)
    (* Qed. *)

    (* Local Hint Resolve interp_check_lit. *)

    Lemma interp_check_form_aux : forall a b,
      check_form_aux a b ->
      Form.interp interp_form_hatom interp_form_hatom_bv t_form a = Form.interp interp_form_hatom interp_form_hatom_bv t_form b.
    Proof.
      intros [a| | |i1 l1|a1|a1|a1|l1 l2|l1 l2|l1 l2 l3|a l1] [b| | |j1 m1|a2|a2|a2|j1 j2|j1 j2|j1 j2 j3|b m1]; simpl; try discriminate;auto with smtcoq_core.
      (* Atom *)
      unfold is_true; rewrite Int63.eqb_spec; intro; subst a; auto with smtcoq_core.
      (* Interesting case *)
      apply interp_check_distinct; auto with smtcoq_core.
      (* Double negation *)
      unfold is_true; rewrite andb_true_iff, Int63.eqb_spec; intros [H1 H2]; subst j1. rewrite (interp_check_lit _ _ H2). auto with smtcoq_core.
      (* Conjunction *)
      unfold is_true; rewrite andb_true_iff, eqb_spec, aforallbi_spec; intros [H1 H2]; apply afold_left_eq; rewrite ?length_amap; auto with smtcoq_core; intros i Hi; rewrite 2!get_amap by (rewrite <- ?H1; assumption); apply interp_check_lit; auto with smtcoq_core.
      (* Disjunction *)
      unfold is_true; rewrite andb_true_iff, eqb_spec, aforallbi_spec; intros [H1 H2]; apply afold_left_eq; rewrite ?length_amap; auto with smtcoq_core; intros i Hi; rewrite 2!get_amap by (rewrite <- ?H1; assumption); apply interp_check_lit; auto with smtcoq_core.
      (* Implication *)
      unfold is_true; rewrite andb_true_iff, eqb_spec, aforallbi_spec; intros [H1 H2]; apply afold_right_eq; rewrite ?length_amap; auto with smtcoq_core; intros i Hi; rewrite 2!get_amap by (rewrite <- ?H1; assumption); apply interp_check_lit; auto with smtcoq_core.
      (* Xor *)
      unfold is_true; rewrite andb_true_iff; intros [H1 H2]; rewrite (interp_check_lit _ _ H1), (interp_check_lit _ _ H2); auto with smtcoq_core.
      (* Iff *)
      unfold is_true; rewrite andb_true_iff; intros [H1 H2]; rewrite (interp_check_lit _ _ H1), (interp_check_lit _ _ H2); auto with smtcoq_core.
      (* Ite *)
      unfold is_true; rewrite !andb_true_iff; intros [[H1 H2] H3]; rewrite (interp_check_lit _ _ H1), (interp_check_lit _ _ H2), (interp_check_lit _ _ H3); auto with smtcoq_core.
    Qed.

    (* Lemma interp_check_lit_equiv : forall l1 l2, *)
    (*   check_lit l1 l2 -> check_lit l2 l1 -> *)
    (*   Lit.interp rho l1 = Lit.interp rho l2. *)
    (* Proof. *)
    (*   intros l1 l2 H1 H2; generalize (interp_check_lit _ _ H1) (interp_check_lit _ _ H2); case (Lit.interp rho l1); case (Lit.interp rho l2); auto with smtcoq_core; symmetry; auto with smtcoq_core. *)
    (* Qed. *)

    (* Lemma interp_check_form_aux : forall a b, *)
    (*   check_form_aux a b -> *)
    (*   Form.interp interp_form_hatom t_form a -> Form.interp interp_form_hatom t_form b. *)
    (* Proof. *)
    (*   intros [a| | |i1 l1|a1|a1|a1|l1 l2|l1 l2|l1 l2 l3] [b| | |j1 m1|a2|a2|a2|j1 j2|j1 j2|j1 j2 j3]; simpl; try discriminate;auto with smtcoq_core. *)
    (*   (* Atom *) *)
    (*   unfold is_true; rewrite Int63Properties.eqb_spec; intro; subst a; auto with smtcoq_core. *)
    (*   (* Interesting case *) *)
    (*   apply interp_check_distinct; auto with smtcoq_core. *)
    (*   (* Double negation *) *)
    (*   unfold is_true; rewrite andb_true_iff, Int63Properties.eqb_spec; intros [H1 H2]; subst j1; apply (fold_ind2 _ _ (fun x y => x = true -> y = true)). *)
    (*   apply interp_check_lit; auto with smtcoq_core. *)
    (*   intros a b; case a; try discriminate; intros H _; rewrite H; auto with smtcoq_core. *)
    (*   (* Conjunction *) *)
    (*   unfold is_true; rewrite andb_true_iff, Int63Properties.eqb_spec; intros [H1 H2]; rewrite aforallbi_spec in H2; intro H3; assert (H4 := afold_left_andb_true_inv _ _ _ H3); clear H3; apply afold_left_andb_true; rewrite <- H1; intros i Hi; eapply interp_check_lit; eauto with smtcoq_core. *)
    (*   (* Disjunction *) *)
    (*   unfold is_true; rewrite andb_true_iff, Int63Properties.eqb_spec; intros [H1 H2]; rewrite aforallbi_spec in H2; intro H3; assert (H4 := afold_left_orb_true_inv _ _ _ H3); clear H3; destruct H4 as [i [H3 H4]]; eapply afold_left_orb_true. *)
    (*   rewrite <- H1; eauto with smtcoq_core. *)
    (*   eapply interp_check_lit; eauto with smtcoq_core. *)
    (*   (* Implication *) *)
    (*   unfold is_true; rewrite andb_true_iff, Int63Properties.eqb_spec; intros [H1 H2]; rewrite aforallbi_spec in H2; intro H3; apply afold_right_implb_true; case_eq (length a1 =? 0); intro Heq. *)
    (*   left; rewrite eqb_spec in Heq; rewrite <- H1; auto with smtcoq_core. *)
    (*   destruct (afold_right_implb_true_inv _ _ _ H3) as [H4|[[i [H4 H5]]|H4]]. *)
    (*   rewrite H4 in Heq; discriminate. *)
    (*   right; left; exists i; rewrite <- H1; split; auto with smtcoq_core; case_eq (Lit.interp rho (a2 .[ i])); auto with smtcoq_core; intro H6; assert (H7: i <? length a1 = true). *)
    (*   rewrite ltb_spec in *; rewrite eqb_false_spec in Heq; rewrite to_Z_sub_1_diff in H4; auto with smtcoq_core; omega. *)
    (*   generalize (H2 _ H7); rewrite H4; intro H8; rewrite (interp_check_lit _ _ H8 H6) in H5; auto with smtcoq_core. *)
    (*   right; case_eq (aexistsbi (fun i l => (i <? length a2 - 1) && (negb (Lit.interp rho l))) a2). *)
    (*   rewrite aexistsbi_spec; intros [i [_ H5]]; rewrite andb_true_iff in H5; destruct H5 as [H5 H6]; left; exists i; split; auto with smtcoq_core; generalize H6; case (Lit.interp rho (a2 .[ i])); auto with smtcoq_core; discriminate. *)
    (*   rewrite aexistsbi_false_spec; intro H; right; intros i Hi; assert (Hi' := Hi); rewrite <- H1 in Hi'; generalize (H2 _ Hi') (H _ Hi); rewrite <- H1; case (i <? length a1 - 1); simpl. *)
    (*   intros _; case (Lit.interp rho (a2 .[ i])); auto with smtcoq_core; discriminate. *)
    (*   intros H5 _; apply (interp_check_lit _ _ H5); apply H4; auto with smtcoq_core. *)
    (*   (* Xor *) *)
    (*   unfold is_true; rewrite !andb_true_iff; intros [[[H1 H2] H3] H4]; rewrite (interp_check_lit_equiv _ _ H1 H2), (interp_check_lit_equiv _ _ H3 H4); auto with smtcoq_core. *)
    (*   (* Iff *) *)
    (*   unfold is_true; rewrite !andb_true_iff; intros [[[H1 H2] H3] H4]; rewrite (interp_check_lit_equiv _ _ H1 H2), (interp_check_lit_equiv _ _ H3 H4); auto with smtcoq_core. *)
    (*   (* Ite *) *)
    (*   unfold is_true; rewrite !andb_true_iff; intros [[[H1 H2] H3] H4]; rewrite (interp_check_lit_equiv _ _ H1 H2); case (Lit.interp rho j1); apply interp_check_lit; auto with smtcoq_core. *)
    (* Qed. *)

  End AUX.

  Definition check_hform h1 h2 :=
    foldi
    (fun _ cont h1 h2 => (h1 =? h2) || check_form_aux cont (get_form h1) (get_form h2))
    0 (PArray.length t_form) (fun h1 h2 => false) h1 h2.

  Definition check_form := check_form_aux check_hform.

  Definition check_lit' := check_lit check_hform.

  Fixpoint check_distinct_elim input res :=
    match input with
      | nil => nil
      | l::q => if check_lit' l res then res::q else l::(check_distinct_elim q res)
    end.


  Section Valid.

    Variables (t_i : array SMT_classes.typ_compdec)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).
    Local Notation interp_form_hatom_bv :=
      (Atom.interp_form_hatom_bv t_i t_func t_atom).
    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom interp_form_hatom_bv t_form).


    Let wf_rho : Valuation.wf rho.
    Proof. destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form); auto with smtcoq_core. Qed.

    Let default_t_form : default t_form = Ftrue.
    Proof. destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as [[H _] _]; auto with smtcoq_core. Qed.

    Let wf_t_form : wf t_form.
    Proof. destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as [[_ H] _]; auto with smtcoq_core. Qed.


    Lemma interp_check_hform : forall h1 h2,
      check_hform h1 h2 -> Var.interp rho h1 = Var.interp rho h2.
    Proof.
      unfold check_hform; apply foldi_ind; try discriminate. apply leb_0. intros i cont _ _ Hrec h1 h2. unfold is_true; rewrite orb_true_iff; intros [H|H].
      rewrite Int63.eqb_spec in H; rewrite H; auto with smtcoq_core.
      unfold Var.interp; rewrite !wf_interp_form; auto with smtcoq_core; eapply interp_check_form_aux; eauto with smtcoq_core.
    Qed.


    Lemma interp_check_form : forall a b,
      check_form a b ->
      Form.interp interp_form_hatom interp_form_hatom_bv t_form a = Form.interp interp_form_hatom interp_form_hatom_bv t_form b.
    Proof. apply interp_check_form_aux, interp_check_hform; auto with smtcoq_core. Qed.


    Lemma interp_check_lit' : forall l res,
      check_lit' l res -> Lit.interp rho l = Lit.interp rho res.
    Proof. apply interp_check_lit, interp_check_hform; auto with smtcoq_core. Qed.


    Lemma valid_check_distinct_elim :
      forall input, C.valid rho input ->
        forall res, C.valid rho (check_distinct_elim input res).
    Proof.
      induction input as [ |l c IHc]; auto with smtcoq_core; simpl; unfold C.valid; simpl; rewrite orb_true_iff; intros [H|H] res.
      case_eq (check_lit' l res); intro Heq; simpl.
      rewrite <- (interp_check_lit' _ _ Heq), H; auto with smtcoq_core.
      rewrite H; auto with smtcoq_core.
      case (check_lit' l res).
      simpl; rewrite H, orb_true_r; auto with smtcoq_core.
      simpl; rewrite (IHc H), orb_true_r; auto with smtcoq_core.
    Qed.

  End Valid.

End Operators.



(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

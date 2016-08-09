(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool List Int63 PArray Eqdep_dec.
(*Add LoadPath "/home/burak/Desktop/smtcoq/src/bva".*)
Require Import State SMT_terms.
Local Open Scope array_scope.
Local Open Scope int63_scope.

Section certif.

  Variable t_form : PArray.array Form.form.
  Variable t_atom : PArray.array Atom.atom.

  Local Notation get_atom := (PArray.get t_atom) (only parsing).
  Local Notation get_form := (PArray.get t_form) (only parsing).

  Definition get_eq (x:var) (f : int -> int -> C.t) :=
    match get_form x with
    | Form.Fatom xa =>
      match get_atom xa with
      | Atom.Abop (Atom.BO_eq _) a b => f a b
      | _ => C._true
      end
    | _ => C._true
    end.
  (* Register get_eq as PrimInline. *)

  Fixpoint check_trans_aux (t1 t2:int)
      (eqs:list _lit) (res:_lit) (clause:C.t) : C.t :=
    match eqs with
    | nil =>
      let xres := Lit.blit res in
      get_eq xres (fun t1' t2' =>
         if ((t1 == t1') && (t2 == t2')) ||
            ((t1 == t2') && (t2 == t1')) then
            Lit.lit xres :: clause
         else C._true)
    | leq::eqs =>
      let xeq := Lit.blit leq in
      get_eq xeq (fun t t' =>
          if t2 == t' then
            check_trans_aux t1 t eqs res (Lit.nlit xeq :: clause)
          else
            if t2 == t then
              check_trans_aux t1 t' eqs res (Lit.nlit xeq :: clause)
            else
              if t1 == t' then
                check_trans_aux t t2 eqs res (Lit.nlit xeq :: clause)
              else
                if t1 == t then
                  check_trans_aux t' t2 eqs res (Lit.nlit xeq :: clause)
                else C._true)
    end.

  Definition check_trans (res:_lit) (eqs:list _lit) : C.t :=
    match eqs with
    | nil =>
      let xres := Lit.blit res in
        get_eq xres (fun t1 t2 =>
         if t1 == t2 then Lit.lit xres :: nil else C._true)
    | leq :: eqs =>
      let xeq := Lit.blit leq in
      get_eq xeq
        (fun t1 t2 => check_trans_aux t1 t2 eqs res (Lit.nlit xeq :: nil))
    end.

  Fixpoint build_congr (eqs:list (option _lit))
       (l r:list int) (c:C.t) {struct eqs} :=
    match eqs, l, r with
    | nil, nil, nil => c
    | eq::eqs, t1::l, t2::r =>
      match eq with
      | None => if t1 == t2 then build_congr eqs l r c else C._true
      | Some leq =>
        let xeq := Lit.blit leq in
        get_eq xeq (fun t1' t2' =>
          if ((t1 == t1') && (t2 == t2')) ||
             ((t1 == t2') && (t2 == t1')) then
            build_congr eqs l r (Lit.nlit xeq :: c)
          else C._true)
      end
    | _, _, _ => C._true
    end.

  Definition check_congr (leq:_lit) (eqs:list (option _lit)) :=
    let xeq := Lit.blit leq in
    get_eq xeq (fun t1 t2 =>
      match get_atom t1, get_atom t2 with
      | Atom.Abop o1 a1 a2, Atom.Abop o2 b1 b2 =>
        if Atom.bop_eqb o1 o2 then
           build_congr eqs (a1::a2::nil) (b1::b2::nil) (Lit.lit xeq :: nil)
        else C._true
      | Atom.Auop o1 a, Atom.Auop o2 b =>
        if Atom.uop_eqb o1 o2 then
           build_congr eqs (a::nil) (b::nil) (Lit.lit xeq :: nil)
        else C._true
      | Atom.Aapp f1 args1, Atom.Aapp f2 args2 =>
        if f1 == f2 then build_congr eqs args1 args2 (Lit.lit xeq :: nil)
        else C._true
      | _, _ => C._true
      end).

  Definition check_congr_pred (PA:_lit) (PB:_lit) (eqs:list (option _lit)) :=
    let xPA := Lit.blit PA in
    let xPB := Lit.blit PB in
    match get_form xPA, get_form xPB with
    | Form.Fatom pa, Form.Fatom pb =>
      match get_atom pa, get_atom pb with
      | Atom.Abop o1 a1 a2, Atom.Abop o2 b1 b2 =>
         if Atom.bop_eqb o1 o2 then
          build_congr eqs
          (a1::a2::nil) (b1::b2::nil) (Lit.nlit xPA :: Lit.lit xPB :: nil)
        else C._true
      | Atom.Auop o1 a, Atom.Auop o2 b =>
         if Atom.uop_eqb o1 o2 then
          build_congr eqs
          (a::nil) (b::nil) (Lit.nlit xPA :: Lit.lit xPB :: nil)
        else C._true
      | Atom.Aapp p a, Atom.Aapp p' b =>
        if p == p' then
          build_congr eqs a b (Lit.nlit xPA :: Lit.lit xPB :: nil)
        else C._true
      | _, _ => C._true
      end
    | _, _ => C._true
    end.

  Section Proof.

    Variables (t_i : array typ_eqb)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation interp_hatom :=
      (Atom.interp_hatom t_i t_func t_atom).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).

    Local Notation interp_form_hatom_bv :=
      (Atom.interp_form_hatom_bv t_i t_func t_atom).

    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom interp_form_hatom_bv t_form).

    Let wf_t_atom : Atom.wf t_atom.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_atom : default t_atom = Atom.Acop Atom.CO_xH.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_form : default t_form = Form.Ftrue.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_t_form : Form.wf t_form.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_rho : Valuation.wf rho.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form); auto.
    Qed.

    Lemma valid_C_true : C.interp rho C._true.
    Proof.
      apply C.interp_true.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form);trivial.
    Qed.
    Hint Resolve valid_C_true.

    Local Notation interp := (Atom.interp t_i t_func t_atom).

    Lemma wf_interp_form : forall x,
       rho x = Form.interp interp_form_hatom interp_form_hatom_bv t_form (t_form.[x]).
    Proof.
      destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form).
      destruct H; intros x;rewrite Form.wf_interp_form;trivial.
    Qed.

    Local Notation get_type :=
        (Atom.get_type t_i t_func t_atom).

    Local Notation check_type :=
        (Atom.check_aux t_i t_func get_type).

    Lemma get_eq_interp :
      forall (l:_lit) (f:Atom.hatom -> Atom.hatom -> C.t),
       (forall xa, t_form.[Lit.blit l] = Form.Fatom xa ->
        forall t a b, t_atom.[xa] = Atom.Abop (Atom.BO_eq t) a b ->
        rho (Lit.blit l) =
          Atom.interp_bool t_i
           (Atom.apply_binop t_i t t Typ.Tbool (Typ.i_eqb t_i t)
              (interp_hatom a) (interp_hatom b)) ->
        Typ.eqb (get_type a) t -> Typ.eqb (get_type b) t ->
        C.interp rho (f a b)) ->
      C.interp rho (get_eq (Lit.blit l) f).
    Proof.
      intros l f Hf;unfold get_eq.
      case_eq (t_form.[Lit.blit l]);trivial;intros.
      case_eq (t_atom.[i]);trivial;intros.
      destruct b;trivial.
      generalize wt_t_atom;unfold Atom.wt;unfold is_true;
       rewrite PArray.forallbi_spec;intros.
      assert (i < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H0, def_t_atom;discriminate.
      apply H1 in H2;clear H1;rewrite H0 in H2;simpl in H2.
      rewrite !andb_true_iff in H2;decompose [and] H2;clear H2.
      apply Hf with (2:= H0);trivial.
      rewrite wf_interp_form, H;simpl.
      unfold Atom.interp_form_hatom, Atom.interp_hatom at 1;simpl.
      rewrite Atom.t_interp_wf, H0;simpl;trivial.
    Qed.

    Let tunicity : forall A T U, Typ.eqb A T -> Typ.eqb A U -> T = U.
    Proof. intros A T U; rewrite !Typ.eqb_spec; intros; subst T U; auto. Qed.

    Ltac tunicity :=
      match goal with
      | [ H1 : is_true (Typ.eqb ?a ?t1),
          H2 : is_true (Typ.eqb ?a ?t2) |- _ ] =>
        assert (W:= tunicity _ _ _ H1 H2);try subst
      | _ => idtac
      end.

    Lemma interp_binop_eqb_sym :
      forall u a b,
      Atom.apply_binop t_i u u Typ.Tbool (Typ.i_eqb t_i u) a b =
      Atom.apply_binop t_i u u Typ.Tbool (Typ.i_eqb t_i u) b a.
    Proof.
      unfold Atom.apply_binop;simpl;intros u (ta,va) (tb,vb).
      destruct (Typ.cast ta u);destruct (Typ.cast tb u);trivial.
      apply f_equal; apply eq_true_iff_eq.
      match goal with |- ?x = _ <-> ?y = _ =>
                      change (is_true x <-> is_true y) end.
      split; intro; rewrite Typ.i_eqb_sym in H; auto.
    Qed.

    Lemma interp_binop_eqb_trans:
      forall u a b c,
      Typ.eqb (get_type a) u -> Typ.eqb (get_type b) u -> Typ.eqb (get_type c) u ->
      Atom.interp_bool t_i
        (Atom.apply_binop t_i u u Typ.Tbool (Typ.i_eqb t_i u)
           (interp_hatom a) (interp_hatom b)) ->
      Atom.interp_bool t_i
        (Atom.apply_binop t_i u u Typ.Tbool (Typ.i_eqb t_i u)
           (interp_hatom b) (interp_hatom c)) ->
      Atom.interp_bool t_i
        (Atom.apply_binop t_i u u Typ.Tbool (Typ.i_eqb t_i u)
           (interp_hatom a) (interp_hatom c)).
    Proof.
      intros u a b c Ha Hb Hc.
      generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom c). rewrite Typ.eqb_spec in Ha. rewrite Typ.eqb_spec in Hb. rewrite Typ.eqb_spec in Hc. unfold Atom.get_type in Ha, Hb, Hc. rewrite Ha, Hb, Hc. intros [va HHa] [vb HHb] [vc HHc].
      unfold Atom.interp_hatom.
      rewrite HHa, HHb, HHc;simpl;rewrite Typ.cast_refl.
      unfold Atom.interp_bool;simpl.
      apply Typ.i_eqb_trans.
    Qed.

    Lemma check_trans_aux_correct :
      forall eqs u t1 t2 res c,
       Typ.eqb (get_type t1) u -> Typ.eqb (get_type t2) u ->
       Atom.interp_bool t_i (interp (Atom.Abop (Atom.BO_eq u) t1 t2)) \/
       C.interp rho c ->
       C.interp rho (check_trans_aux t1 t2 eqs res c).
    Proof.
      induction eqs;simpl;intros.
      apply get_eq_interp;intros.
      match goal with |- context [if ?b then _ else _] => case_eq b end;
       intros;trivial.
      simpl;rewrite Lit.interp_lit;unfold Var.interp.
      destruct H1;[ | rewrite H1,orb_true_r;auto].
      rewrite orb_true_iff, !andb_true_iff in H7;destruct H7 as
        [[H7 H8] | [H7 H8]].
      rewrite eqb_spec in H7. rewrite eqb_spec in H8. subst.
      tunicity. rewrite H4, H1;auto.
      rewrite eqb_spec in H7. rewrite eqb_spec in H8. subst.
      tunicity;rewrite interp_binop_eqb_sym in H1;rewrite H4, H1;auto.
      apply get_eq_interp;intros.
      destruct (Int63Properties.reflect_eqb t2 b);subst;tunicity.
      apply (IHeqs u);trivial.
      simpl;unfold is_true;rewrite orb_true_iff.
      rewrite Lit.interp_nlit;unfold Var.interp.
      (* Attention ici on utilise la decidabilit'e de l'egalit'e sur u *)
      case_eq (rho (Lit.blit a));[rewrite H4; intros | simpl;auto].
      destruct H1;[left | auto].
      apply interp_binop_eqb_trans with (4:= H1);trivial.
      rewrite interp_binop_eqb_sym;trivial.
      destruct (Int63Properties.reflect_eqb t2 a0); subst;tunicity.
      apply (IHeqs u);trivial.
      simpl;unfold is_true;rewrite orb_true_iff.
      rewrite Lit.interp_nlit;unfold Var.interp.
      (* Attention ici on utilise la decidabilit'e de l'egalit'e sur u *)
      case_eq (rho (Lit.blit a));[rewrite H4; intros | simpl;auto].
      destruct H1;[left | auto].
      apply interp_binop_eqb_trans with (4:= H1);trivial.
      destruct (Int63Properties.reflect_eqb t1 b);subst;tunicity.
      apply (IHeqs u);trivial.
      simpl;unfold is_true;rewrite orb_true_iff.
      rewrite Lit.interp_nlit;unfold Var.interp.
      (* Attention ici on utilise la decidabilit'e de l'egalit'e sur u *)
      case_eq (rho (Lit.blit a));[rewrite H4; intros | simpl;auto].
      destruct H1;[left | auto].
      apply interp_binop_eqb_trans with (5:= H1);trivial.
      destruct (Int63Properties.reflect_eqb t1 a0);[subst;tunicity|auto].
      apply (IHeqs u);trivial.
      simpl;unfold is_true;rewrite orb_true_iff.
      rewrite Lit.interp_nlit;unfold Var.interp.
      (* Attention ici on utilise la decidabilit'e de l'egalit'e sur u *)
      case_eq (rho (Lit.blit a));[rewrite H4; intros | simpl;auto].
      destruct H1;[left | auto].
      apply interp_binop_eqb_trans with (5:= H1);trivial.
      rewrite interp_binop_eqb_sym;trivial.
    Qed.

    Lemma valid_check_trans :
      forall res eqs,
       C.interp rho (check_trans res eqs).
    Proof.
      unfold check_trans;intros res [ | leq eqs].
      apply get_eq_interp;intros.
      destruct (Int63Properties.reflect_eqb a b).
      unfold C.interp; simpl; rewrite orb_false_r.
      unfold Lit.interp; simpl; rewrite Lit.is_pos_lit.
      unfold Var.interp; simpl; rewrite Lit.blit_lit.
      rewrite H1.
      unfold Atom.interp_bool; simpl.
      rewrite e; simpl.
      generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b). rewrite Typ.eqb_spec in H3. unfold Atom.get_type in H3. rewrite H3. intros [vb HHb].
      unfold Atom.interp_hatom.
      rewrite HHb;simpl;rewrite Typ.cast_refl;simpl.
      apply Typ.i_eqb_refl.
      auto.
      apply get_eq_interp;intros.
      apply check_trans_aux_correct with t;trivial.
      simpl;rewrite Lit.interp_nlit;unfold Var.interp. rewrite <- H1.
      (* Attention ici on utilise la decidabilit'e de l'egalit'e sur t *)
      destruct (rho (Lit.blit leq));auto.
    Qed.

    Inductive Forall2 A B (P:A->B->Prop) : list A -> list B -> Prop :=
    | Forall2_nil : Forall2 A B P nil nil
    | Forall2_cons :
       forall a b la lb, P a b -> Forall2 A B P la lb ->
         Forall2 A B P (a::la) (b::lb).

    (** TODO (setoid rewrires with Typ.i_eqb)*)
    Section X.

      Require Import Setoid SetoidClass.
      Local Close Scope int63_scope.

      Existing Instance Typ.Interp_Setoid.


      (* Instance atom_val_Setoid : Setoid (Atom.val Typ.type (Typ.interp t_i)). *)
      (* Proof. *)
      (*   exists eq; constructor; auto. *)
      (*   unfold Transitive. intros; subst; auto. *)
      (* Defined. *)


      (* Definition type_equiv a b := if Typ.eqb a b then True else False. *)

      (* Instance type_setoid : Setoid Typ.type. Admitted. *)

      (* Check type_setoid. *)
      (* Check (equiv type_setoid). *)
      (* Check (relation (Setoid Typ.type)). *)

      (* Instance type_setoid_setoid : Setoid (Setoid Typ.type). *)
      (* destruct type_setoid. *)

      
      (* Check (equiv type_setoid). *)

      (* Variable t : Typ.type. *)
      (* Check ((Atom.Bval t_i t)). *)

      (* Variable equiv_type : (Setoid Typ.type) -> (Setoid Typ.type) -> Prop. *)

      (* Instance interptype_setoid t : Setoid (Typ.interp t_i t). *)
      (* exists eq. *)
      (* split; auto. *)
      (* unfold Transitive. intros; subst; auto. *)
      (* Defined. *)
                                                                   
      (* Lemma aproper : forall t,  Proper (@equiv _ (interptype_setoid t)  ==> Logic.eq)  (Atom.Bval t_i t). *)
      (*   unfold Proper. *)
      (*   unfold SetoidClass.equiv. *)
      (*   intro t. *)
      (*   unfold interptype_setoid. *)
      (*   intros x y. *)
      (*   unfold Atom.Bval. *)
      (*   intro. *)
      (*   apply f_equal. *)
      (*   auto. *)
      (* Qed. *)


      Definition Atomeq_prop t x va := x = Atom.Bval t_i t va.
      
      (* Lemma aproper : forall t,  Proper (@equiv _ (interptype_setoid t)  ==> Basics.impl) (forall x, Atomeq_prop t x). *)
      (*   unfold Proper. *)
      (*   unfold SetoidClass.equiv. *)
      (*   intro t. *)
      (*   unfold interptype_setoid. *)
      (*   intros x y. *)
      (*   unfold Atom.Bval. *)
      (*   intro. *)
      (*   apply f_equal. *)
      (*   auto. *)
      (* Qed. *)


      
      (* Lemma aproper : forall t,  Proper (SetoidClass.equiv ==> Logic.eq)  (Atom.Bval t_i t). *)
      (*   unfold Proper. *)
      (*   unfold SetoidClass.equiv. *)
      (*   intro t. *)
      (*   destruct (Typ.Interp_Setoid t_i t). *)
      (*   intros x y. *)
      (*   destruct setoid_equiv. *)
      (*   unfold Atom.Bval. *)
      (*   intro. *)
      (*   apply f_equal. *)
      (*   unfold. *)
        
      (*   unfold equiv. *)
      (*   intro *)
      (*     split. *)


      (* Variable t : Typ.type. *)
      (* Check (Atom.Bval t_i t). *)


      Definition equiv_val t (f1 f2 : Typ.interp t_i t -> Atom.val Typ.type (Typ.interp t_i)) :=
        forall v, f1 v = f2 v.
      
      Instance Atom_val_setoid t : Setoid (Typ.interp t_i t -> Atom.val Typ.type (Typ.interp t_i)).
      Proof.
        exists (equiv_val t).
        unfold equiv_val.
        split; auto.
        unfold Transitive. intros.
        specialize (H v).
        specialize (H0 v).
        rewrite <- H in H0. auto.
      Defined.

      (* Require Import FunctionalExtensionality. *)
      
      (* Lemma aproper4 : forall t f,  Proper (@equiv _ (Atom_val_setoid t) ==> Basics.impl) (Atom.Bval t_i t). *)
      (* Proof. *)
      (*     unfold Proper. *)
      (*     unfold SetoidClass.equiv. *)
      (*     unfold Atom_val_setoid. *)
      (*     intros t f. *)
      (*     unfold Basics.impl. *)
      (*     intros fx fy. *)
      (*     unfold equiv_val; intros. *)
      (*     subst; auto. *)
      (*     apply functional_extensionality. auto. *)
      (* Qed. *)


      (* Lemma l: forall t,  *)
      
      (* Lemma aproper : forall t,  Proper (@equiv _ (Typ.Interp_Setoid t)  ==> Basics.impl) (forall x, Atomeq_prop t x). *)
      (*   unfold Proper. *)
      (*   unfold SetoidClass.equiv. *)
      (*   intro t. *)
      (*   unfold interptype_setoid. *)
      (*   intros x y. *)
      (*   unfold Atom.Bval. *)
      (*   intro. *)
      (*   apply f_equal. *)
      (*   auto. *)
      (* Qed. *)
        

      (* Instance aproper2 t vb :  Proper (SetoidClass.equiv ==> Basics.flip Basics.impl) (eq (Atom.Bval t_i t vb)). *)
      (* Proof. *)
      (*     unfold Proper. *)
      (*     unfold SetoidClass.equiv. *)
      (*     unfold Atom_val_setoid. *)
      (*     intros x y. *)
      (*     intros. *)
      (*     unfold Basics.flip. *)
      (*     unfold Basics.impl. *)
      (*     subst; auto. *)
      (* Defined. *)

      (* Instance aproper3 t y :  Proper (SetoidClass.equiv ==> Basics.flip Basics.impl) *)
      (*                               (fun v => eq (Atom.Bval t_i t v) y). *)
      (* Proof. *)
      (*     unfold Proper. *)
      (*     unfold SetoidClass.equiv. *)
      (*     (* unfold Atom_val_setoid. *) *)
      (*     unfold Typ.Interp_Setoid. *)
      (*     intros a b. *)
      (*     intros. *)
      (*     unfold Basics.flip. *)
      (*     unfold Basics.impl. *)
      (*     subst; auto. *)
      (* Defined. *)

        
      
      (* Lemma i_eqb_atom2 : forall (t:Typ.type) x (va vb : Typ.interp t_i t), *)
      (*     (* Typ.i_eqb t_i t va vb -> *) *)
      (*     va == vb -> *)
      (*     x = Atom.Bval t_i t vb -> *)
      (*     x = Atom.Bval t_i t va. *)
      (*   intros. *)
      (*   setoid_rewrite H. auto. *)
      (* Qed. *)

        
      (* Lemma i_eqb_atom : forall (t:Typ.type) (va vb : Typ.interp t_i t), *)
      (*     (* Typ.i_eqb t_i t va vb -> *) *)
      (*     va == vb -> *)
      (*     Atom.Bval t_i t vb = Atom.Bval t_i t va. *)
      (*   intros. *)
      (*   setoid_rewrite H. auto. *)
      (* Qed. *)
      
    End X.


    (* Check i_eqb_atom. *)

    Existing Instance Typ.Interp_Setoid.

    Check interp_hatom.

    Lemma typ_eq_dec : forall a b : Typ.type, { a = b } + { a <> b }.
    Proof.
      intros a b.
      case_eq (Typ.eqb a b); intro.
      left. apply Typ.eqb_spec in H. exact H.
      right.
      apply not_true_iff_false in H.
      unfold not in *.
      intro. apply H. apply Typ.eqb_spec. exact H0.
    Qed.
    
    (* Definition i_eqb_atom (a b:atom) : bool. *)
    (*   destruct (interp_hatom a) as (ta, va), (interp_hatom b) as (tb, vb). *)
    (*   destruct (Typ.eqb_spec ta tb). *)
    (*   destruct (Typ.eqb ta tb). *)
    (*   assert true by constructor. *)
    (*   specialize (H H1). *)
    (*   subst tb. *)
    (*   apply (Typ.i_eqb t_i ta va vb). *)
    (*   apply false. *)
    (* Defined. *)

    
    Definition i_eqb_atom (a b:atom) : bool :=
      match interp_hatom a, interp_hatom b with
      | Atom.Val ta va, Atom.Val tb vb =>
        match Typ.cast tb ta with
        | Typ.Cast k => Typ.i_eqb t_i ta va (k (Typ.interp t_i) vb)
        | Typ.NoCast => false
        end
      end.
              
    (*   destruct (interp_hatom a) as (ta, va), (interp_hatom b) as (tb, vb). *)
    (*   destruct (typ_eq_dec ta tb). *)
    (*   rewrite <- e in vb. *)
    (*   (* subst tb. *) *)
    (*   apply (Typ.i_eqb t_i ta va vb). *)
    (*   apply false. *)
    (* Defined. *)

    
    (* Definition i_eqb_atom (a b:atom) : bool. *)
    (*   destruct (interp_hatom a) as (ta, va), (interp_hatom b) as (tb, vb). *)
    (*   destruct (typ_eq_dec ta tb). *)
    (*   rewrite <- e in vb. *)
    (*   (* subst tb. *) *)
    (*   apply (Typ.i_eqb t_i ta va vb). *)
    (*   apply false. *)
    (* Defined. *)

    
    

    Print i_eqb_atom.

    Require Import Program.
    
    Lemma build_congr_correct : forall lp l r c,
        (Forall2 _ _ (fun a b => i_eqb_atom a b = true) l r -> C.interp rho c) ->
        C.interp rho (build_congr lp l r c).
    Proof.
      induction lp;destruct l;destruct r;simpl;trivial;intros.
      apply H;constructor.
      destruct a.
      apply get_eq_interp;intros.
      match goal with |- context [if ?x then _ else _] =>
                      case_eq x;intros;auto end.
      apply IHlp;simpl;intros.
      rewrite Lit.interp_nlit;unfold Var.interp.
      case_eq (rho (Lit.blit i1));intros;simpl;[ | auto].
      apply H;constructor;trivial.
      generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b). rewrite Typ.eqb_spec in H3. rewrite Typ.eqb_spec in H4. unfold Atom.get_type in H3, H4. rewrite H3,H4. intros [va HHa] [vb HHb].
      revert H7;rewrite H2;unfold Atom.apply_binop; simpl.

      rewrite orb_true_iff, !andb_true_iff in H5;destruct H5 as
        [ [H5 H7] | [H5 H7]];
      rewrite eqb_spec in H5; rewrite eqb_spec in H7;
      subst i i0;
      unfold i_eqb_atom;
      unfold Atom.interp_hatom;
      rewrite HHa, HHb;simpl;rewrite Typ.cast_refl;simpl;
      intros W; [ | rewrite Typ.i_eqb_sym ]; auto.

      destruct (Int63Properties.reflect_eqb i i0);[subst | auto].
      apply IHlp;intros;apply H;constructor;auto.
      unfold i_eqb_atom.
      destruct (interp_hatom i0).
      rewrite Typ.cast_refl;simpl. apply Typ.i_eqb_refl.
    Qed.

      
    Lemma build_congr_correct2: forall lp l r c,
      (Forall2 _ _ (fun a b => interp_hatom a = interp_hatom b) l r -> C.interp rho c) ->
      C.interp rho (build_congr lp l r c).
    Proof.
      induction lp;destruct l;destruct r;simpl;trivial;intros.
      apply H;constructor.
      destruct a.
      apply get_eq_interp;intros.
      match goal with |- context [if ?x then _ else _] =>
       case_eq x;intros;auto end.
      apply IHlp;simpl;intros.
      rewrite Lit.interp_nlit;unfold Var.interp.
      case_eq (rho (Lit.blit i1));intros;simpl;[ | auto].
      apply H;constructor;trivial.
      
      generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b). rewrite Typ.eqb_spec in H3. rewrite Typ.eqb_spec in H4. unfold Atom.get_type in H3, H4. rewrite H3,H4. intros [va HHa] [vb HHb].
      revert H7;rewrite H2;unfold Atom.apply_binop; simpl.
      unfold Atom.interp_hatom.
      rewrite HHa, HHb;simpl;rewrite Typ.cast_refl;simpl.
      intros W.
      (* apply Typ.i_eqb_is_equiv in W. *)
      (* setoid_rewrite W in HHa. *)
      (* specialize (@i_eqb_atom2 t (Atom.t_interp t_i t_func t_atom .[ a]) va vb W). *)
      (* intro. *)
      (* apply H7 in W. *)
      
      change (is_true (Typ.i_eqb t_i t va vb)) in W.

      (* assert (va == vb). *)
      (* unfold equiv. *)
      (* unfold Typ.Interp_Setoid. *)
      (* (* unfold Typ.interp_compdec. *) *)
      (* unfold Typ.CompDec_Setoid. *)

      (* simpl. *)
      (* destruct (Typ.Interp_Setoid t_i t). *)
      (* unfold equiv. *)
      
      rewrite Typ.i_eqb_spec in W.
      rewrite orb_true_iff, !andb_true_iff in H5;destruct H5 as
        [ [H5 H7] | [H5 H7]].
      rewrite eqb_spec in H5. rewrite eqb_spec in H7. subst.
      rewrite HHa, HHb;trivial.
      rewrite eqb_spec in H5. rewrite eqb_spec in H7. subst.
      rewrite HHa, HHb;trivial.
      destruct (Int63Properties.reflect_eqb i i0);[subst | auto].
      apply IHlp;intros;apply H;constructor;auto.
    Qed.

    Lemma valid_check_congr :
       forall leq eqs,
          C.interp rho (check_congr leq eqs).
    Proof.
      unfold check_congr;intros leq eqs;apply get_eq_interp;intros.
      case_eq (t_atom .[ a]);intros;auto;
      case_eq (t_atom .[ b]);intros;auto.
      (* uop *)
      destruct (Atom.reflect_uop_eqb u u0);[subst | auto].
      apply build_congr_correct;intros.
      simpl;rewrite Lit.interp_lit, orb_false_r;unfold Var.interp.
      rewrite H1.
      generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b). rewrite Typ.eqb_spec in H2. rewrite Typ.eqb_spec in H3. unfold Atom.get_type in H2, H3. rewrite H2,H3. intros [va HHa] [vb HHb].
      unfold Atom.apply_binop;unfold Atom.interp_hatom;simpl.
      rewrite HHb, HHa. simpl.
      rewrite Atom.t_interp_wf in HHa; auto. rewrite H4 in HHa. simpl in HHa.
      rewrite Atom.t_interp_wf in HHb; auto. rewrite H5 in HHb. simpl in HHb.
      rewrite Typ.cast_refl;simpl.
      inversion_clear H6.
      unfold i_eqb_atom in H7.
      unfold Atom.interp_hatom in H7.
      destruct (Atom.t_interp t_i t_func t_atom .[ i]) as (ti, vi).
      destruct (Atom.t_interp t_i t_func t_atom .[ i0]) as (ti0, vi0).
      (* unfold Atom.Bval in HHa, HHb. *)
      destruct u0; simpl in HHa, HHb;
        destruct ti, ti0;
        try (
            simpl in HHa, HHb;
            rewrite HHb in HHa;
            apply Atom.Bval_inj2 in HHa;
            rewrite HHa; apply Typ.i_eqb_refl);
        try (
            simpl in HHa, HHb;
            inversion HHa;
            inversion HHb;
            rewrite <- H9 in H10; now contradict H10);
        
      simpl in H7;
      destruct t; try (inversion HHa);
      apply Atom.Bval_inj2 in HHa;
      apply Atom.Bval_inj2 in HHb;
      subst va vb; unfold is_true;
      unfold Typ.i_eqb in *;
      unfold Typ.eqb_of_compdec in *;
      simpl; simpl in H7.

      (* UO_xO *)
      unfold sumbool_rec, sumbool_rect .
      case (Pos.eq_dec vi vi0) in *; auto.

      (* UO_xI *)
      unfold sumbool_rec, sumbool_rect.
      case (Pos.eq_dec vi vi0) in *; auto.
      case (Pos.eq_dec vi vi0) in *; auto.
      case (Pos.eq_dec vi vi0) in *; auto.

      (* UO_Zopp *)
      case ( Z.eq_dec (- vi) (- vi0)) in *; auto.
      case ( Z.eq_dec (vi) (vi0)) in *; auto.
      subst; auto.

      (* Atom.UO_BVbitOf n n0 *)
      case ((if BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 as b
           return (BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 = b -> {vi = vi0} + {vi <> vi0})
          then fun H : BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 = true => in_left
             else fun H : BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 = false => in_right)) in *.
      subst; auto.
      case (bool_dec (BVList.BITVECTOR_LIST_FIXED.bitOf n0 vi0) (BVList.BITVECTOR_LIST_FIXED.bitOf n0 vi0)); auto.
      now contradict H7.


      (* UO_BVnot *)
      simpl in H7.
      case ((if BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 as b
           return (BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 = b -> {vi = vi0} + {vi <> vi0})
          then fun H : BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 = true => in_left
             else fun H : BVList.BITVECTOR_LIST_FIXED.bv_eq vi vi0 = false => in_right)) in *.
      subst; auto.

      Admitted.
      
    (*   (* bop *) *)
    (*   destruct (Atom.reflect_bop_eqb b0 b1);[subst | auto]. *)
    (*   apply build_congr_correct;intros. *)
    (*   simpl;rewrite Lit.interp_lit, orb_false_r;unfold Var.interp. *)
    (*   rewrite H1. *)
    (*   generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b). rewrite Typ.eqb_spec in H2. rewrite Typ.eqb_spec in H3. unfold Atom.get_type in H2, H3. rewrite H2,H3. intros [va HHa] [vb HHb]. *)
    (*   unfold Atom.apply_binop. unfold Atom.interp_hatom;simpl. *)
    (*   rewrite HHb, HHa;simpl. *)
    (*   rewrite Atom.t_interp_wf in HHa; auto. rewrite H4 in HHa. simpl in HHa. *)
    (*   rewrite Atom.t_interp_wf in HHb; auto. rewrite H5 in HHb. simpl in HHb. *)
    (*   rewrite Typ.cast_refl;simpl. *)
    (*   assert (Atom.Bval t_i t va = Atom.Bval t_i t vb). *)
    (*    inversion H6;clear H6;subst. *)
    (*    inversion H12;clear H12;subst. *)
    (*    unfold Atom.interp_hatom in H10, H8. *)
    (*    rewrite <- HHa. rewrite <- HHb, H10, H8;trivial. *)
    (*   inversion H7. *)
    (*   apply Eqdep_dec.inj_pair2_eq_dec in H9;trivial. *)
    (*   rewrite H9. *)
    (*   apply Typ.i_eqb_refl. *)
    (*   intros x y;destruct (Typ.reflect_eqb x y);auto. *)
    (*   (* op *) *)
    (*   destruct (Int63Properties.reflect_eqb i i0);[subst | auto]. *)
    (*   apply build_congr_correct;intros. *)
    (*   simpl;rewrite Lit.interp_lit, orb_false_r;unfold Var.interp. *)
    (*   rewrite H1. *)
    (*   generalize (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom a), (Atom.check_aux_interp_hatom _ t_func _ wf_t_atom b). rewrite Typ.eqb_spec in H2. rewrite Typ.eqb_spec in H3. unfold Atom.get_type in H2, H3. rewrite H2,H3. intros [va HHa] [vb HHb]. *)
    (*   unfold Atom.apply_binop;unfold Atom.interp_hatom;simpl. *)
    (*   rewrite HHb, HHa;simpl. *)
    (*   rewrite Atom.t_interp_wf in HHa; auto. rewrite H4 in HHa. simpl in HHa. *)
    (*   rewrite Atom.t_interp_wf in HHb; auto. rewrite H5 in HHb. simpl in HHb. *)
    (*   rewrite Typ.cast_refl;simpl. *)
    (*   assert (Atom.Bval t_i t va = Atom.Bval t_i t vb). *)
    (*     rewrite <- HHa;rewrite <- HHb;destruct (t_func.[i0]). *)
    (*     apply f_equal;clear HHa HHb va vb H5 H4. *)
    (*     induction H6;simpl;trivial. *)
    (*     unfold Atom.interp_hatom in H4. *)
    (*     rewrite IHForall2, H4;trivial. *)
    (*   inversion H7. *)
    (*   apply Eqdep_dec.inj_pair2_eq_dec in H9;trivial. *)
    (*   rewrite H9. *)
    (*   apply Typ.i_eqb_refl. *)
    (*   intros x y;destruct (Typ.reflect_eqb x y);auto. *)
    (* Qed. *)

    Lemma valid_check_congr_pred :
       forall lpa lpb eqs,
          C.interp rho (check_congr_pred lpa lpb eqs).
    Proof.
      unfold check_congr_pred;intros.
      case_eq (t_form.[Lit.blit lpa]);auto.
      case_eq (t_form.[Lit.blit lpb]);auto;intros.
      case_eq (t_atom.[i0]);auto; case_eq (t_atom.[i]);auto;intros.
      (* uop *)
      destruct (Atom.reflect_uop_eqb u0 u);[subst | auto].
      apply build_congr_correct;simpl;intros.
      rewrite orb_false_r, Lit.interp_lit, Lit.interp_nlit;unfold Var.interp.
      replace (rho (Lit.blit lpb)) with (rho (Lit.blit lpa)).
       destruct (rho (Lit.blit lpa));reflexivity.
      rewrite !wf_interp_form, H, H0;simpl.
      generalize wt_t_atom;unfold Atom.wt;unfold is_true;
       rewrite PArray.forallbi_spec;intros.
      assert (i < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H1, def_t_atom;discriminate.
      assert (i0 < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H2, def_t_atom;discriminate.
      apply H4 in H5;apply H4 in H6;clear H4.
      unfold Atom.interp_form_hatom, Atom.interp_hatom;simpl.
      rewrite !Atom.t_interp_wf, H1, H2;simpl;trivial.
      apply f_equal;apply f_equal.
      inversion H3;clear H3;subst;trivial.

      (* bop *)
      destruct (Atom.reflect_bop_eqb b0 b);[subst | auto].
      apply build_congr_correct;simpl;intros.
      rewrite orb_false_r, Lit.interp_lit, Lit.interp_nlit;unfold Var.interp.
      replace (rho (Lit.blit lpb)) with (rho (Lit.blit lpa)).
       destruct (rho (Lit.blit lpa));reflexivity.
      rewrite !wf_interp_form, H, H0;simpl.
      generalize wt_t_atom;unfold Atom.wt;unfold is_true;
       rewrite PArray.forallbi_spec;intros.
      assert (i < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H1, def_t_atom. discriminate.
      assert (i0 < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H2, def_t_atom;discriminate.
      apply H4 in H5;apply H4 in H6;clear H4.
      unfold Atom.interp_form_hatom, Atom.interp_hatom;simpl.
      rewrite !Atom.t_interp_wf, H1, H2;simpl;trivial.
      inversion H3;clear H3;subst.
      inversion H11;clear H11;subst.
      apply f_equal; apply f_equal2;trivial.

      (* op *)
      destruct (Int63Properties.reflect_eqb i2 i1);[subst | auto].
      apply build_congr_correct;simpl;intros.
      rewrite orb_false_r, Lit.interp_lit, Lit.interp_nlit;unfold Var.interp.
      replace (rho (Lit.blit lpb)) with (rho (Lit.blit lpa)).
       destruct (rho (Lit.blit lpa));reflexivity.
      rewrite !wf_interp_form, H, H0;simpl.
      generalize wt_t_atom;unfold Atom.wt;unfold is_true;
       rewrite PArray.forallbi_spec;intros.
      assert (i < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H1, def_t_atom;discriminate.
      assert (i0 < length t_atom).
        apply PArray.get_not_default_lt.
        rewrite H2, def_t_atom;discriminate.
      apply H4 in H5;apply H4 in H6;clear H4.
      unfold Atom.interp_form_hatom, Atom.interp_hatom;simpl.
      rewrite !Atom.t_interp_wf, H1, H2;simpl;trivial.
      apply f_equal;destruct (t_func.[i1]);apply f_equal.
      clear H H0 H1 H2 H5 H6.
      induction H3;simpl;trivial.
      unfold Atom.interp_hatom in H;rewrite H, IHForall2;trivial.
    Qed.

  End Proof.

End certif.


(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

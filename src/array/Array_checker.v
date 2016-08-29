(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller  *                                                  *)
(*     Alain   Mebsout ♯                                                  *)
(*     Burak   Ekici   ♯                                                  *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Add Rec LoadPath "." as SMTCoq.

Require Import Bool List Int63 PArray.
Require Import Misc State SMT_terms FArray.

Import Form.
Import Atom.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Section certif.

  Variable t_form : PArray.array Form.form.
  Variable t_atom : PArray.array Atom.atom.

  Local Notation get_atom := (PArray.get t_atom) (only parsing).
  Local Notation get_form := (PArray.get t_form) (only parsing).


  Definition check_roweq lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
      | Fatom a =>
        match get_atom a with
        | Abop (BO_eq te) xa v =>
          match get_atom xa with
          | Abop (BO_select ti1 te1) sa i =>
            match get_atom sa with
            | Atop (TO_store ti2 te2) fa j v2 =>
              if Typ.eqb ti1 ti2 &&
                 Typ.eqb te te1 && Typ.eqb te te2 &&
                 (i == j) && (v == v2)
              then lres::nil
              else C._true
            | _ => C._true
            end
          | _ => C._true
          end
        | _ => C._true
        end
      | _ => C._true
      end
    else C._true.

  Definition check_rowneq cl :=
    match cl with
    | leqij :: leqrow :: nil =>
      if Lit.is_pos leqij && Lit.is_pos leqrow then
        match get_form (Lit.blit leqij), get_form (Lit.blit leqrow) with
        | Fatom eqij, Fatom eqrow =>
          match get_atom eqij, get_atom eqrow with
          | Abop (BO_eq ti) i j, Abop (BO_eq te) xa x =>
            match get_atom xa, get_atom x with
            | Abop (BO_select ti1 te1) sa j1, Abop (BO_select ti2 te2) sa2 j2 =>
              if Typ.eqb ti ti1 && Typ.eqb ti ti2 &&
                 Typ.eqb te te1 && Typ.eqb te te2 then
                match get_atom sa, get_atom sa2 with

                | Atop (TO_store ti3 te3) sa1 i1 _, _ =>
                  if Typ.eqb ti ti3 && Typ.eqb te te3 &&
                     (sa1 == sa2) && 
                     (((i1 == i) && (j1 == j) && (j2 == j)) ||
                      ((i1 == j) && (j1 == i) && (j2 == i))) then
                    cl
                  else C._true
                  
                | _ , Atop (TO_store ti3 te3) sa1 i1 _ =>
                  if Typ.eqb ti ti3 && Typ.eqb te te3 &&
                     (sa1 == sa) && 
                     (((i1 == i) && (j1 == j) && (j2 == j)) ||
                      ((i1 == j) && (j1 == i) && (j2 == i))) then
                    cl
                  else C._true

                | _, _ => C._true
                end
              else C._true
            | _, _ => C._true
            end
          | _, _ => C._true
          end
        | _, _ => C._true
        end
      else C._true
    | _ => C._true
    end.


  Definition check_ext lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
      | For args =>
        if PArray.length args == 2 then
          let l1 := args.[0] in
          let l2 := args.[1] in
          if Lit.is_pos l1 && negb (Lit.is_pos l2) then
            match get_form (Lit.blit l1), get_form (Lit.blit l2) with
            | Fatom eqa, Fatom eqsel =>
              match get_atom eqa, get_atom eqsel with
              | Abop (BO_eq (Typ.TFArray ti te)) a b, Abop (BO_eq te') sela selb => 
                if Typ.eqb te te' then
                  match get_atom sela, get_atom selb with
                  | Abop (BO_select ti1 te1) a' d1, Abop (BO_select ti2 te2) b' d2 =>
                    if Typ.eqb ti ti1 && Typ.eqb ti ti2 &&
                       Typ.eqb te te1 && Typ.eqb te te2 &&
                       (a == a') && (b == b') && (d1 == d2) then
                      match get_atom d1 with
                      | Abop (BO_diffarray ti3 te3) a3 b3 =>
                        if Typ.eqb ti ti3 && Typ.eqb te te3 &&
                           (a3 == a) && (b3 == b) then
                          lres :: nil
                        else C._true
                      | _ => C._true
                      end
                    else C._true
                  | _, _ => C._true
                  end
                else C._true
              | _, _ => C._true
              end
            | _, _ => C._true
            end
          else C._true
        else C._true
      | _ => C._true
      end
    else C._true.


  Section Correct.

    Variables (t_i : array typ_eqb)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation check_atom :=
      (check_aux t_i t_func (get_type t_i t_func t_atom)).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).

    Local Notation interp_form_hatom_bv :=
      (Atom.interp_form_hatom_bv t_i t_func t_atom).

    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom interp_form_hatom_bv t_form).

    Local Notation t_interp := (t_interp t_i t_func t_atom).

    Local Notation interp_atom := (interp_aux t_i t_func (get t_interp)).

    Let wf_t_atom : Atom.wf t_atom.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_atom : default t_atom = Atom.Acop Atom.CO_xH.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_form : default t_form = Form.Ftrue.
    Proof.
      destruct (Form.check_form_correct
                  interp_form_hatom interp_form_hatom_bv _ ch_form) as [H _];
        destruct H; auto.
    Qed.

    Let wf_t_form : Form.wf t_form.
    Proof.
      destruct (Form.check_form_correct
                  interp_form_hatom interp_form_hatom_bv _ ch_form) as [H _];
        destruct H; auto.
    Qed.

    Let wf_rho : Valuation.wf rho.
    Proof.
      destruct (Form.check_form_correct
                  interp_form_hatom interp_form_hatom_bv _ ch_form); auto.
    Qed.

    Let rho_interp : forall x : int,
        rho x = Form.interp interp_form_hatom interp_form_hatom_bv t_form (t_form.[ x]).
    Proof. intros x;apply wf_interp_form;trivial. Qed.

    Definition wf := PArray.forallbi lt_form t_form.

    Hypothesis wf_t_i : wf.
    Notation atom := int (only parsing).

    
    Lemma valid_check_roweq lres : C.valid rho (check_roweq lres).
    Proof.
      unfold check_roweq.
      case_eq (Lit.is_pos lres); intro Heq; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a Heq2.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] a1 a2 Heq3; try (intros; now apply C.interp_true).
      case_eq (t_atom .[ a1]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] b1 b2 Heq4; try (intros; now apply C.interp_true).
      case_eq (t_atom .[ b1]); try (intros; now apply C.interp_true).
      intros [ ] c1 c2 c3 Heq5.
      (* roweq *)
      - case_eq (Typ.eqb t0 t2 && Typ.eqb t t1 && 
             Typ.eqb t t3 && (b2 == c2) && (a2 == c3)); simpl; intros Heq6; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq2. simpl.

        rewrite !andb_true_iff in Heq6.
        destruct Heq6 as ((((Heq6a, Heq6b), Heq6c), Heq6d), Heq6e).

        apply Typ.eqb_spec in Heq6a.
        apply Typ.eqb_spec in Heq6b.
        apply Typ.eqb_spec in Heq6c.
        apply Int63Properties.eqb_spec in Heq6d.
        apply Int63Properties.eqb_spec in Heq6e.

        pose proof (rho_interp (Lit.blit lres)) as Hrho.
        rewrite Heq2 in Hrho. simpl in Hrho.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq3. easy.
        specialize (H0 H1). simpl in H0.
        rewrite Heq3 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3, H0. unfold v_type in H2, H3, H0.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H0.
          case_eq v_typea; intros; rewrite H4 in H0; try now contradict H0.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2]).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq3 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.

        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.

        rewrite H2, H3, H4.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H5 Htia).

        pose proof (H a1). assert (a1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq4. easy.
        specialize (H6 H7). simpl in H6.
        rewrite Heq4 in H6. simpl in H6.
        rewrite !andb_true_iff in H6.
        destruct H6 as ((H6a, H6b), H6c).
        apply Typ.eqb_spec in H6a.
        apply Typ.eqb_spec in H6b.
        apply Typ.eqb_spec in H6c.

        pose proof (H b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H6 H8). simpl in H6.
        rewrite Heq5 in H6. simpl in H6.

        rewrite !andb_true_iff in H6.
        destruct H6 as (((H6d, H6e), H6f), H6h).
        apply Typ.eqb_spec in H6e.
        apply Typ.eqb_spec in H6f.
        apply Typ.eqb_spec in H6h.

        unfold get_type' in H6b, H6c, H6d.
        unfold v_type in H6b, H6c, H6d.
        case_eq (t_interp .[ b2]). 
          intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H6c.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        case_eq (t_interp .[ b1]). 
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H6d.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite <- Heq6d, <- Heq6e in *.

        rewrite Heq5 in Htib1. simpl in Htib1.

        generalize dependent v_valb2.

        rewrite H6c. intros.
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq3. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq4, Htia2. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq5, Htib2. simpl. 
        rewrite Htib1. simpl.

        rewrite Typ.cast_refl.
        unfold apply_binop.
        rewrite Typ.cast_refl.

        case_eq (t_interp .[ b1]); intros.
        pose proof H6.
        rewrite H6 in H6b.
        rewrite !Atom.t_interp_wf in H6; trivial.
        rewrite Heq5 in H6.
        simpl in H6. rewrite H6 in Htib1.
        inversion Htib1.

        generalize dependent v_val0.

        rewrite H6b.
        intros. rewrite Typ.cast_refl.
        simpl.
        unfold get_type' in H6a.
        unfold v_type in H6a.
        case_eq (t_interp .[ a1]).
        intros.
        rewrite H10 in H6a.
        rewrite !Atom.t_interp_wf in H10; trivial.
        rewrite H10 in Htia1.
        inversion Htia1.
        rewrite <- H6a in H14.

        generalize dependent v_val0.

        rewrite H14.
        intros.
        rewrite Typ.cast_refl.
        simpl.

        unfold apply_terop in H6.
        unfold get_type', v_type in H6e, H6f, H6h.
        case_eq ( t_interp .[ c1]); intros.
        rewrite H13 in H6e.
        rewrite H13 in H6.
        case_eq (t_interp .[ b2]); intros.
        rewrite H16 in H6f.
        rewrite H16 in H6.
        case_eq (t_interp .[ a2]); intros.
        rewrite H17 in H6h.
        rewrite H17 in H6.

        generalize dependent v_val2. generalize dependent v_val3.
        generalize dependent v_val4.

        rewrite H6e, H6f, H6h.
        rewrite !Typ.cast_refl.
        intros.
        unfold Bval in H6.

        rewrite <- H11 in H6d.
        rewrite H6b in H6d.
        rewrite andb_true_iff in H6d.
        destruct H6d as (H6d1, H6d2).
        apply Typ.eqb_spec in H6d1.
        apply Typ.eqb_spec in H6d2.

        generalize dependent v_val2. generalize dependent v_val3.
        generalize dependent v_val4.

        rewrite H6d1, H6d2, H14.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t0 t) 
        (store v_val2 v_val3 v_val4) (v_val0)).
        intros. specialize (H18 H6).
        rewrite <- H18.

        rewrite !Atom.t_interp_wf in H16; trivial.
        rewrite H16 in Htib2.
        specialize (Atom.Bval_inj2 t_i t0 v_val3 v_valb2).
        intros. specialize (H19 Htib2).
        rewrite <- H19.

        rewrite !Atom.t_interp_wf in H17; trivial.
        rewrite H17 in Htia2.
        specialize (Atom.Bval_inj2 t_i t v_val4 v_vala2).
        intros. specialize (H20 Htia2).
        rewrite <- H20.
        apply Typ.i_eqb_spec.

        apply read_over_write.
        exact (Typ.dec_interp _ _).
    Qed.

    Lemma valid_check_rowneq cl : C.valid rho (check_rowneq cl).
    Proof.
      unfold check_rowneq.
      case_eq (cl); [ intros | intros i l ]; simpl; try now apply C.interp_true.
      case_eq (l); [ intros | intros j xsl ]; simpl; try now apply C.interp_true.
      case_eq (xsl); intros; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos i); intro Heq; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos j); intro Heq2; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit i]); try (intros; now apply C.interp_true).
      intros a Heq3.
      case_eq (t_form .[ Lit.blit j]); try (intros; now apply C.interp_true).
      intros b Heq4.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] a1 a2 Heq5; try (intros; now apply C.interp_true).
      case_eq (t_atom .[ b]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] b1 b2 Heq6; try (intros; now apply C.interp_true).
      case_eq (t_atom .[ b1]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] c1 c2 Heq7; try (intros; now apply C.interp_true).
      case_eq (t_atom .[ b2]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] d1 d2 Heq8; try (intros; now apply C.interp_true).
      case_eq (Typ.eqb t t1 && Typ.eqb t t3 && Typ.eqb t0 t2 && Typ.eqb t0 t4); 
        try (intros; now apply C.interp_true). intros Heq9.

      case_eq (t_atom .[ c1]); try (intros; now apply C.interp_true).
      (* t5: cop *)
        intros c Heqc.
        case_eq (t_atom .[ d1]); try (intros; now apply C.interp_true).
        intros [ ] e1 e2 e3 Heq10.
        case_eq (
          Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == c1) &&
          ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
          simpl; intros Heq11; try (now apply C.interp_true).
        
        unfold C.valid. simpl. rewrite orb_false_r.

        case_eq (Lit.interp rho i). intros isit.
        easy. intros isif. rewrite orb_false_l.
        specialize (rho_interp ( Lit.blit i)).
        rewrite Heq3 in rho_interp.
        simpl in rho_interp.
        unfold Lit.interp in isif.
        rewrite Heq in isif. unfold Var.interp in isif.
        rewrite rho_interp in isif.
        unfold interp_form_hatom, interp_hatom in isif.
        rewrite Atom.t_interp_wf in isif; trivial.
        rewrite Heq5 in isif.
        simpl in isif.
        unfold interp_bool in isif.

        unfold Lit.interp. rewrite Heq2.
        unfold Var.interp.
        rewrite !wf_interp_form; trivial. rewrite Heq4. simpl.

        rewrite !andb_true_iff in Heq9.
        destruct Heq9 as (((Heq9a, Heq9b), Heq9c), Heq9d).

        apply Typ.eqb_spec in Heq9a.
        apply Typ.eqb_spec in Heq9b.
        apply Typ.eqb_spec in Heq9c.
        apply Typ.eqb_spec in Heq9d.

        rewrite !andb_true_iff in Heq11.
        destruct Heq11 as (((Heq11a, Heq11b), Heq11c), Heq11d).
        rewrite !orb_true_iff in Heq11d.
        destruct Heq11d as [ Heq11d | Heq11d ].

        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia1.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala1)).
        intros. specialize (H41 Htia1). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia2 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala2) (v_valc2)).
        intros. specialize (H42 Htic2''). now rewrite H42 in isif.
        (* symmetric case: cop *)
        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia2.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala2)).
        intros. specialize (H41 Htia2). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia1 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala1) (v_valc2)).
        intros. specialize (H42 Htic2''). rewrite H42 in isif.
        unfold not in *. intros.
        now apply isif.
   (* end t5: cop *)        

   (* t5: uop *)
        intros u ui Heqc.
        case_eq (t_atom .[ d1]); try (intros; now apply C.interp_true).
        intros [ ] e1 e2 e3 Heq10.
        case_eq (
          Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == c1) &&
          ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
          simpl; intros Heq11; try (now apply C.interp_true).
        
        unfold C.valid. simpl. rewrite orb_false_r.

        case_eq (Lit.interp rho i). intros isit.
        easy. intros isif. rewrite orb_false_l.
        specialize (rho_interp ( Lit.blit i)).
        rewrite Heq3 in rho_interp.
        simpl in rho_interp.
        unfold Lit.interp in isif.
        rewrite Heq in isif. unfold Var.interp in isif.
        rewrite rho_interp in isif.
        unfold interp_form_hatom, interp_hatom in isif.
        rewrite Atom.t_interp_wf in isif; trivial.
        rewrite Heq5 in isif.
        simpl in isif.
        unfold interp_bool in isif.

        unfold Lit.interp. rewrite Heq2.
        unfold Var.interp.
        rewrite !wf_interp_form; trivial. rewrite Heq4. simpl.

        rewrite !andb_true_iff in Heq9.
        destruct Heq9 as (((Heq9a, Heq9b), Heq9c), Heq9d).

        apply Typ.eqb_spec in Heq9a.
        apply Typ.eqb_spec in Heq9b.
        apply Typ.eqb_spec in Heq9c.
        apply Typ.eqb_spec in Heq9d.

        rewrite !andb_true_iff in Heq11.
        destruct Heq11 as (((Heq11a, Heq11b), Heq11c), Heq11d).
        rewrite !orb_true_iff in Heq11d.
        destruct Heq11d as [ Heq11d | Heq11d ].

        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia1.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala1)).
        intros. specialize (H41 Htia1). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia2 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala2) (v_valc2)).
        intros. specialize (H42 Htic2''). now rewrite H42 in isif.
        (* symmetric case: uop *)
        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia2.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala2)).
        intros. specialize (H41 Htia2). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia1 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala1) (v_valc2)).
        intros. specialize (H42 Htic2''). rewrite H42 in isif.
        unfold not in *. intros.
        now apply isif.
      (* end t5: unop *)

   (* t5: binop *)
        intros bo bi0 bi1 Heqc.
        case_eq (t_atom .[ d1]); try (intros; now apply C.interp_true).
        intros [ ] e1 e2 e3 Heq10.
        case_eq (
          Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == c1) &&
          ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
          simpl; intros Heq11; try (now apply C.interp_true).
        
        unfold C.valid. simpl. rewrite orb_false_r.

        case_eq (Lit.interp rho i). intros isit.
        easy. intros isif. rewrite orb_false_l.
        specialize (rho_interp ( Lit.blit i)).
        rewrite Heq3 in rho_interp.
        simpl in rho_interp.
        unfold Lit.interp in isif.
        rewrite Heq in isif. unfold Var.interp in isif.
        rewrite rho_interp in isif.
        unfold interp_form_hatom, interp_hatom in isif.
        rewrite Atom.t_interp_wf in isif; trivial.
        rewrite Heq5 in isif.
        simpl in isif.
        unfold interp_bool in isif.

        unfold Lit.interp. rewrite Heq2.
        unfold Var.interp.
        rewrite !wf_interp_form; trivial. rewrite Heq4. simpl.

        rewrite !andb_true_iff in Heq9.
        destruct Heq9 as (((Heq9a, Heq9b), Heq9c), Heq9d).

        apply Typ.eqb_spec in Heq9a.
        apply Typ.eqb_spec in Heq9b.
        apply Typ.eqb_spec in Heq9c.
        apply Typ.eqb_spec in Heq9d.

        rewrite !andb_true_iff in Heq11.
        destruct Heq11 as (((Heq11a, Heq11b), Heq11c), Heq11d).
        rewrite !orb_true_iff in Heq11d.
        destruct Heq11d as [ Heq11d | Heq11d ].

        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia1.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala1)).
        intros. specialize (H41 Htia1). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia2 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala2) (v_valc2)).
        intros. specialize (H42 Htic2''). now rewrite H42 in isif.
        (* symmetric case: binop *)
        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia2.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala2)).
        intros. specialize (H41 Htia2). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia1 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala1) (v_valc2)).
        intros. specialize (H42 Htic2''). rewrite H42 in isif.
        unfold not in *. intros.
        now apply isif.
      (* end t5: binop *)

      (* t5: terop *)
      intros [ ] e1 e2 e3 Heq10.

      case_eq (
        Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == d1) &&
        ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
        simpl; intros Heq11; try (now apply C.interp_true).

      unfold C.valid. simpl. rewrite orb_false_r.

      case_eq (Lit.interp rho i). intros isit.
      easy. intros isif. rewrite orb_false_l.
      specialize (rho_interp ( Lit.blit i)).
      rewrite Heq3 in rho_interp.
      simpl in rho_interp.
      unfold Lit.interp in isif.
      rewrite Heq in isif. unfold Var.interp in isif.
      rewrite rho_interp in isif.
      unfold interp_form_hatom, interp_hatom in isif.
      rewrite Atom.t_interp_wf in isif; trivial.
      rewrite Heq5 in isif.
      simpl in isif.
      unfold interp_bool in isif.

      unfold Lit.interp. rewrite Heq2.
      unfold Var.interp.
      rewrite !wf_interp_form; trivial. rewrite Heq4. simpl.

      rewrite !andb_true_iff in Heq9.
      destruct Heq9 as (((Heq9a, Heq9b), Heq9c), Heq9d).

      apply Typ.eqb_spec in Heq9a.
      apply Typ.eqb_spec in Heq9b.
      apply Typ.eqb_spec in Heq9c.
      apply Typ.eqb_spec in Heq9d.

      rewrite !andb_true_iff in Heq11.
      destruct Heq11 as (((Heq11a, Heq11b), Heq11c), Heq11d).
      rewrite !orb_true_iff in Heq11d.
      destruct Heq11d as [ Heq11d | Heq11d ].

      apply Typ.eqb_spec in Heq11a.
      apply Typ.eqb_spec in Heq11b.
      apply Int63Properties.eqb_spec in Heq11c.
      rewrite !andb_true_iff in Heq11d.
      destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
      apply Int63Properties.eqb_spec in Heq11d1.
      apply Int63Properties.eqb_spec in Heq11d2.
      apply Int63Properties.eqb_spec in Heq11d3.

      generalize wt_t_atom. unfold Atom.wt. unfold is_true.
      rewrite PArray.forallbi_spec;intros.

      pose proof (H2 a). assert (a < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
      specialize (H3 H4). simpl in H3.
      rewrite Heq5 in H3. simpl in H3.
      rewrite !andb_true_iff in H3. destruct H3. destruct H3.
      unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

      case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H3.
        case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

      case_eq (t_interp .[ a1]).
        intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
      case_eq (t_interp .[ a2]).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
      rewrite Atom.t_interp_wf in Htia; trivial.
      rewrite Atom.t_interp_wf in Htia1; trivial.
      rewrite Atom.t_interp_wf in Htia2; trivial.
      rewrite Heq5 in Htia. simpl in Htia.
      rewrite !Atom.t_interp_wf in Htia; trivial.
      rewrite Htia1, Htia2 in Htia. simpl in Htia.
      rewrite !Atom.t_interp_wf in isif; trivial.
      rewrite Htia1, Htia2 in isif. simpl in isif.
      unfold Bval in isif.

      apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

      generalize dependent v_vala1. generalize dependent v_vala2.
      generalize dependent v_vala.
      rewrite H5, H6, H7.
      rewrite !Typ.cast_refl. intros. simpl in Htia.
      unfold Bval in Htia.

      remember Atom.Bval_inj2.
      specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
      intros. specialize (H8 Htia).

      (* get the same kind of info for b, b1, b2 and c1 *)

      (* b *)
      pose proof (H2 b). assert (b < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
      specialize (H9 H10). simpl in H9.
      rewrite Heq6 in H9. simpl in H9.
      rewrite !andb_true_iff in H9. destruct H9. destruct H9.
      unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

      case_eq (t_interp .[ b]).
        intros v_typeb v_valb Htib. rewrite Htib in H9.
        case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

      case_eq (t_interp .[ b1]).
        intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
      case_eq (t_interp .[ b2]).
          intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
      rewrite Atom.t_interp_wf in Htib; trivial.
      rewrite Atom.t_interp_wf in Htib1; trivial.
      rewrite Atom.t_interp_wf in Htib2; trivial.
      rewrite Heq6 in Htib. simpl in Htib.
      rewrite !Atom.t_interp_wf in Htib; trivial.
      rewrite Htib1, Htib2 in Htib. simpl in Htib.

      apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb.
      rewrite H11, H12, H13.
      rewrite !Typ.cast_refl. intros. simpl in Htib.
      unfold Bval in Htib.

      remember Atom.Bval_inj2.
      specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
      intros. specialize (H14 Htib).

      (* b1; b2 *)
      pose proof (H2 b1). assert (b1 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
      specialize (H15 H16). simpl in H15.
      rewrite Heq7 in H15. simpl in H15.
      rewrite !andb_true_iff in H15. destruct H15. destruct H15.
      unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

     case_eq (t_interp .[ b1]).
        intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

      case_eq (t_interp .[ c1]).
        intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
      case_eq (t_interp .[ c2]).
          pose proof Htib1' as Htib1''.
          intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
          pose proof Htic2 as Htic2''.
      rewrite Atom.t_interp_wf in Htib1'; trivial.
      rewrite Atom.t_interp_wf in Htic1; trivial.
      rewrite Atom.t_interp_wf in Htic2; trivial.
      rewrite Heq7 in Htib1'. simpl in Htib1'.
      rewrite !Atom.t_interp_wf in Htib1'; trivial.
      rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

      apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
      apply Typ.eqb_spec in H15. 

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valb1'.
      rewrite H17, H18.
      rewrite !Typ.cast_refl. intros. simpl in Htib1'.
      unfold Bval in Htib1'.

      remember Atom.Bval_inj2.

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valb1'.

      rewrite H15. intros.
      specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
      intros. specialize (H19 Htib1').

      (* b2 *)
      pose proof (H2 b2). assert (b2 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
      specialize (H20 H21). simpl in H20.
      rewrite Heq8 in H20. simpl in H20.
      rewrite !andb_true_iff in H20. destruct H20. destruct H20.
      unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

     case_eq (t_interp .[ b2]).
        intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

      case_eq (t_interp .[ d1]).
        intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
      case_eq (t_interp .[ d2]).
          pose proof Htib2' as Htib2''.
          intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
      rewrite Atom.t_interp_wf in Htib2'; trivial.
      rewrite Atom.t_interp_wf in Htid1; trivial.
      rewrite Atom.t_interp_wf in Htid2; trivial.
      rewrite Heq8 in Htib2'. simpl in Htib2'.
      rewrite !Atom.t_interp_wf in Htib2'; trivial.
      rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

      apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
      apply Typ.eqb_spec in H20. 

      generalize dependent v_vald1. generalize dependent v_vald2.
      generalize dependent v_valb2'.
      rewrite H22, H23.
      rewrite !Typ.cast_refl. intros. simpl in Htib2'.
      unfold Bval in Htib2'.

      remember Atom.Bval_inj2.

      generalize dependent v_vald1. generalize dependent v_vald2.
      generalize dependent v_valb2'.

      rewrite H20. intros.
      specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
      intros. specialize (H24 Htib2').

      (* c1 *)
      pose proof (H2 c1). assert (c1 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
      specialize (H25 H26). simpl in H25.
      rewrite Heq10 in H25. simpl in H25.
      rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
      unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

     case_eq (t_interp .[ c1]).
        intros v_typec1' v_valc1' Htic1'. rewrite Htic1' in H25.
        case_eq v_typec1'; intros; rewrite H30 in H25; try now contradict H25.
        rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

      case_eq (t_interp .[ e1]).
        intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
      case_eq (t_interp .[ e2]).
        intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
      case_eq (t_interp .[ e3]).
        intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
          pose proof Htic1' as Htic1''.
      rewrite Atom.t_interp_wf in Htic1'; trivial.
      rewrite Atom.t_interp_wf in Htie1; trivial.
      rewrite Atom.t_interp_wf in Htie2; trivial.
      rewrite Atom.t_interp_wf in Htie3; trivial.
      rewrite Heq10 in Htic1'. simpl in Htic1'.
      rewrite !Atom.t_interp_wf in Htic1'; trivial.
      rewrite Htie1, Htie2, Htie3 in Htic1'. simpl in Htic1'.

      apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
      apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
      apply Typ.eqb_spec in H29.

      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_vale3. generalize dependent v_valc1'.
      rewrite H27, H28, H29.
      rewrite !Typ.cast_refl. intros. simpl in Htic1'.
      unfold Bval in Htic1'.

      remember Atom.Bval_inj2.

      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_vale3. generalize dependent v_valc1'.

      rewrite H25a, H25b, H30. intros.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
        (store v_vale1 v_vale2 v_vale3) (v_valc1')).
      intros. specialize (H25 Htic1').

      unfold interp_form_hatom, interp_hatom.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Heq6. simpl.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Heq7, Heq8. simpl.
      rewrite !Atom.t_interp_wf; trivial.

      rewrite Htic1, Htic2, Htid1, Htid2. simpl.
      rewrite H15, H20.
      rewrite !Typ.cast_refl.
      unfold apply_binop.
      unfold Bval.
      rewrite !Atom.t_interp_wf in Htib1''; trivial.
      rewrite Htib1 in Htib1''.
      inversion Htib1''.
      rewrite !Atom.t_interp_wf in Htib2''; trivial.
      rewrite Htib2 in Htib2''.
      inversion Htib2''.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb1'. generalize dependent v_valb2'.
      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'.

      rewrite <- H32, H34.
      rewrite !Typ.cast_refl. intros.

      unfold interp_bool. rewrite Typ.cast_refl.
      apply Typ.i_eqb_spec.

      rewrite !Atom.t_interp_wf in Htic1''; trivial.
      rewrite Htic1 in Htic1''.
      inversion Htic1''.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb1'. generalize dependent v_valb2'.
      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'.
      generalize dependent v_vald1. generalize dependent v_vald2.

      rewrite H36, H37.
      intros.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_valc1) (v_valc1')).
      intros. specialize (H31 Htic1'').
      rewrite H31.
      rewrite <- H25.
      rewrite <- Heq11c in Htid1.
      rewrite <- Heq9a, Heq9b in H36.

      generalize dependent v_vald1. generalize dependent v_vald2.

      rewrite H36.
      intros.
      rewrite Htid1 in Htie1. 
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vald1) (v_vale1)).
      intros. specialize (H39 Htie1).
      rewrite H39.

      (*c2 = d2*)
      rewrite <- Heq11d2 in Heq11d3.
      rewrite <- Heq11d3 in Htic2.
      rewrite Htid2 in Htic2.
      specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
      intros. specialize (H40 Htic2). rewrite H40.

      apply read_over_other_write.

      unfold Lit.interp in isif.
      apply Typ.i_eqb_spec_false in isif.
      rewrite H25a in Heq11a.

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'.
      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_vale3.
      generalize dependent v_vald1. generalize dependent v_vald2.

      rewrite <- Heq11a, Heq11d1. intros.
      rewrite Htie2 in Htia1.
      specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala1)).
      intros. specialize (H41 Htia1). rewrite <- H41 in isif.

      rewrite !Atom.t_interp_wf in Htic2''; trivial.
      rewrite Heq11d2 in Htic2''.
      rewrite Htia2 in Htic2''.
      specialize (Atom.Bval_inj2 t_i t (v_vala2) (v_valc2)).
      intros. specialize (H42 Htic2''). now rewrite H42 in isif.

      (* symmetic case *)

      rewrite !andb_true_iff in Heq11d.
      destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
      apply Int63Properties.eqb_spec in Heq11c.
      apply Int63Properties.eqb_spec in Heq11d1.
      apply Int63Properties.eqb_spec in Heq11d2.
      apply Int63Properties.eqb_spec in Heq11d3.

      generalize wt_t_atom. unfold Atom.wt. unfold is_true.
      rewrite PArray.forallbi_spec;intros.

      pose proof (H2 a). assert (a < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
      specialize (H3 H4). simpl in H3.
      rewrite Heq5 in H3. simpl in H3.
      rewrite !andb_true_iff in H3. destruct H3. destruct H3.
      unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

      case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H3.
        case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

      case_eq (t_interp .[ a1]).
        intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
      case_eq (t_interp .[ a2]).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
      rewrite Atom.t_interp_wf in Htia; trivial.
      rewrite Atom.t_interp_wf in Htia1; trivial.
      rewrite Atom.t_interp_wf in Htia2; trivial.
      rewrite Heq5 in Htia. simpl in Htia.
      rewrite !Atom.t_interp_wf in Htia; trivial.
      rewrite Htia1, Htia2 in Htia. simpl in Htia.
      rewrite !Atom.t_interp_wf in isif; trivial.
      rewrite Htia1, Htia2 in isif. simpl in isif.
      unfold Bval in isif.

      apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

      generalize dependent v_vala1. generalize dependent v_vala2.
      generalize dependent v_vala.
      rewrite H5, H6, H7.
      rewrite !Typ.cast_refl. intros. simpl in Htia.
      unfold Bval in Htia.

      remember Atom.Bval_inj2.
      specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
      intros. specialize (H8 Htia).

      (* get the same kind of info for b, b1, b2 and c1 *)

      (* b *)
      pose proof (H2 b). assert (b < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
      specialize (H9 H10). simpl in H9.
      rewrite Heq6 in H9. simpl in H9.
      rewrite !andb_true_iff in H9. destruct H9. destruct H9.
      unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

      case_eq (t_interp .[ b]).
        intros v_typeb v_valb Htib. rewrite Htib in H9.
        case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

      case_eq (t_interp .[ b1]).
        intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
      case_eq (t_interp .[ b2]).
          intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
      rewrite Atom.t_interp_wf in Htib; trivial.
      rewrite Atom.t_interp_wf in Htib1; trivial.
      rewrite Atom.t_interp_wf in Htib2; trivial.
      rewrite Heq6 in Htib. simpl in Htib.
      rewrite !Atom.t_interp_wf in Htib; trivial.
      rewrite Htib1, Htib2 in Htib. simpl in Htib.

      apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb.
      rewrite H11, H12, H13.
      rewrite !Typ.cast_refl. intros. simpl in Htib.
      unfold Bval in Htib.

      remember Atom.Bval_inj2.
      specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
      intros. specialize (H14 Htib).

      (* b1; b2 *)
      pose proof (H2 b1). assert (b1 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
      specialize (H15 H16). simpl in H15.
      rewrite Heq7 in H15. simpl in H15.
      rewrite !andb_true_iff in H15. destruct H15. destruct H15.
      unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

     case_eq (t_interp .[ b1]).
        intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

      case_eq (t_interp .[ c1]).
        intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
      case_eq (t_interp .[ c2]).
          pose proof Htib1' as Htib1''.
          intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
          pose proof Htic2 as Htic2''.
      rewrite Atom.t_interp_wf in Htib1'; trivial.
      rewrite Atom.t_interp_wf in Htic1; trivial.
      rewrite Atom.t_interp_wf in Htic2; trivial.
      rewrite Heq7 in Htib1'. simpl in Htib1'.
      rewrite !Atom.t_interp_wf in Htib1'; trivial.
      rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

      apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
      apply Typ.eqb_spec in H15. 

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valb1'.
      rewrite H17, H18.
      rewrite !Typ.cast_refl. intros. simpl in Htib1'.
      unfold Bval in Htib1'.

      remember Atom.Bval_inj2.

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valb1'.

      rewrite H15. intros.
      specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
      intros. specialize (H19 Htib1').

      (* b2 *)
      pose proof (H2 b2). assert (b2 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
      specialize (H20 H21). simpl in H20.
      rewrite Heq8 in H20. simpl in H20.
      rewrite !andb_true_iff in H20. destruct H20. destruct H20.
      unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

     case_eq (t_interp .[ b2]).
        intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

      case_eq (t_interp .[ d1]).
        intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
      case_eq (t_interp .[ d2]).
          pose proof Htib2' as Htib2''.
          intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
      rewrite Atom.t_interp_wf in Htib2'; trivial.
      rewrite Atom.t_interp_wf in Htid1; trivial.
      rewrite Atom.t_interp_wf in Htid2; trivial.
      rewrite Heq8 in Htib2'. simpl in Htib2'.
      rewrite !Atom.t_interp_wf in Htib2'; trivial.
      rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

      apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
      apply Typ.eqb_spec in H20. 

      generalize dependent v_vald1. generalize dependent v_vald2.
      generalize dependent v_valb2'.
      rewrite H22, H23.
      rewrite !Typ.cast_refl. intros. simpl in Htib2'.
      unfold Bval in Htib2'.

      remember Atom.Bval_inj2.

      generalize dependent v_vald1. generalize dependent v_vald2.
      generalize dependent v_valb2'.

      rewrite H20. intros.
      specialize (Atom.Bval_inj2 t_i (v_typeb2') 
                 (select v_vald1 v_vald2) (v_valb2')).
      intros. specialize (H24 Htib2').

      (* c1 *)
      pose proof (H2 c1). assert (c1 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
      specialize (H25 H26). simpl in H25.
      rewrite Heq10 in H25. simpl in H25.
      rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
      unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

     case_eq (t_interp .[ c1]).
        intros v_typec1' v_valc1' Htic1'. rewrite Htic1' in H25.
        case_eq v_typec1'; intros; rewrite H30 in H25; try now contradict H25.
        rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

      case_eq (t_interp .[ e1]).
        intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
      case_eq (t_interp .[ e2]).
        intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
      case_eq (t_interp .[ e3]).
        intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
          pose proof Htic1' as Htic1''.
      rewrite Atom.t_interp_wf in Htic1'; trivial.
      rewrite Atom.t_interp_wf in Htie1; trivial.
      rewrite Atom.t_interp_wf in Htie2; trivial.
      rewrite Atom.t_interp_wf in Htie3; trivial.
      rewrite Heq10 in Htic1'. simpl in Htic1'.
      rewrite !Atom.t_interp_wf in Htic1'; trivial.
      rewrite Htie1, Htie2, Htie3 in Htic1'. simpl in Htic1'.

      apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
      apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
      apply Typ.eqb_spec in H29.

      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_vale3. generalize dependent v_valc1'.

      rewrite H27, H28, H29.
      rewrite !Typ.cast_refl. intros. simpl in Htic1'.
      unfold Bval in Htic1'.

      remember Atom.Bval_inj2.

      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_vale3. generalize dependent v_valc1'.

      rewrite H25a, H25b, H30. intros.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
        (store v_vale1 v_vale2 v_vale3) (v_valc1')).
      intros. specialize (H25 Htic1').

      unfold interp_form_hatom, interp_hatom.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Heq6. simpl.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Heq7, Heq8. simpl.
      rewrite !Atom.t_interp_wf; trivial.

      rewrite Htic1, Htic2, Htid1, Htid2. simpl.
      rewrite H15, H20.

      rewrite !Typ.cast_refl.
      unfold apply_binop.
      unfold Bval.
      rewrite !Atom.t_interp_wf in Htib1''; trivial.
      rewrite Htib1 in Htib1''.
      inversion Htib1''.
      rewrite !Atom.t_interp_wf in Htib2''; trivial.
      rewrite Htib2 in Htib2''.
      inversion Htib2''.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb1'. generalize dependent v_valb2'.
      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'.

      rewrite <- H32, H34.
      rewrite !Typ.cast_refl. intros.

      unfold interp_bool. rewrite Typ.cast_refl.
      apply Typ.i_eqb_spec.

      rewrite !Atom.t_interp_wf in Htic1''; trivial.
      rewrite Htic1 in Htic1''.
      inversion Htic1''.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb1'. generalize dependent v_valb2'.
      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'.
      generalize dependent v_vald1. generalize dependent v_vald2.

      rewrite H36, H37.
      intros.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_valc1) (v_valc1')).
      intros. specialize (H31 Htic1'').
      rewrite H31.
      rewrite <- H25.
      rewrite <- Heq11c in Htid1.
      rewrite <- Heq9a, Heq9b in H36.

      generalize dependent v_vald1. generalize dependent v_vald2.

      rewrite H36.
      intros.
      rewrite Htid1 in Htie1. 
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vald1) (v_vale1)).
      intros. specialize (H39 Htie1).
      rewrite H39.

      (*c2 = d2*)
      rewrite <- Heq11d2 in Heq11d3.
      rewrite <- Heq11d3 in Htic2.
      rewrite Htid2 in Htic2.
      specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
      intros. specialize (H40 Htic2). rewrite H40.

      apply read_over_other_write.

      unfold Lit.interp in isif.
      apply Typ.i_eqb_spec_false in isif.
      rewrite H25a in Heq11a.

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'.
      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_vale3.
      generalize dependent v_vald1. generalize dependent v_vald2.

      apply Typ.eqb_spec in Heq11a.
      apply Typ.eqb_spec in Heq11b.
      rewrite <- Heq11a, Heq11d1. intros.
      rewrite Htie2 in Htia2.
      specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala2)).
      intros. specialize (H41 Htia2). rewrite <- H41 in isif.

      rewrite !Atom.t_interp_wf in Htic2''; trivial.
      rewrite Heq11d2 in Htic2''.
      rewrite Htia1 in Htic2''.
      specialize (Atom.Bval_inj2 t_i t (v_vala1) (v_valc2)).
      intros. specialize (H42 Htic2''). rewrite H42 in isif.
      unfold not in *. intros.
      now apply isif.
   (*end t5: terop*)

   (* t5: nop *)
        intros n l0 Heqc.
        case_eq (t_atom .[ d1]); try (intros; now apply C.interp_true).
        intros [ ] e1 e2 e3 Heq10.
        case_eq (
          Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == c1) &&
          ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
          simpl; intros Heq11; try (now apply C.interp_true).
        
        unfold C.valid. simpl. rewrite orb_false_r.

        case_eq (Lit.interp rho i). intros isit.
        easy. intros isif. rewrite orb_false_l.
        specialize (rho_interp ( Lit.blit i)).
        rewrite Heq3 in rho_interp.
        simpl in rho_interp.
        unfold Lit.interp in isif.
        rewrite Heq in isif. unfold Var.interp in isif.
        rewrite rho_interp in isif.
        unfold interp_form_hatom, interp_hatom in isif.
        rewrite Atom.t_interp_wf in isif; trivial.
        rewrite Heq5 in isif.
        simpl in isif.
        unfold interp_bool in isif.

        unfold Lit.interp. rewrite Heq2.
        unfold Var.interp.
        rewrite !wf_interp_form; trivial. rewrite Heq4. simpl.

        rewrite !andb_true_iff in Heq9.
        destruct Heq9 as (((Heq9a, Heq9b), Heq9c), Heq9d).

        apply Typ.eqb_spec in Heq9a.
        apply Typ.eqb_spec in Heq9b.
        apply Typ.eqb_spec in Heq9c.
        apply Typ.eqb_spec in Heq9d.

        rewrite !andb_true_iff in Heq11.
        destruct Heq11 as (((Heq11a, Heq11b), Heq11c), Heq11d).
        rewrite !orb_true_iff in Heq11d.
        destruct Heq11d as [ Heq11d | Heq11d ].

        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia1.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala1)).
        intros. specialize (H41 Htia1). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia2 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala2) (v_valc2)).
        intros. specialize (H42 Htic2''). now rewrite H42 in isif.
        (* symmetric case: nop *)
        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia2.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala2)).
        intros. specialize (H41 Htia2). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia1 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala1) (v_valc2)).
        intros. specialize (H42 Htic2''). rewrite H42 in isif.
        unfold not in *. intros.
        now apply isif.
   (* end t5: nop *)

   (* t5: Aapp *)
        intros i0 l0 Heqc.
        case_eq (t_atom .[ d1]); try (intros; now apply C.interp_true).
        intros [ ] e1 e2 e3 Heq10.
        case_eq (
          Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == c1) &&
          ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
          simpl; intros Heq11; try (now apply C.interp_true).
        
        unfold C.valid. simpl. rewrite orb_false_r.

        case_eq (Lit.interp rho i). intros isit.
        easy. intros isif. rewrite orb_false_l.
        specialize (rho_interp ( Lit.blit i)).
        rewrite Heq3 in rho_interp.
        simpl in rho_interp.
        unfold Lit.interp in isif.
        rewrite Heq in isif. unfold Var.interp in isif.
        rewrite rho_interp in isif.
        unfold interp_form_hatom, interp_hatom in isif.
        rewrite Atom.t_interp_wf in isif; trivial.
        rewrite Heq5 in isif.
        simpl in isif.
        unfold interp_bool in isif.

        unfold Lit.interp. rewrite Heq2.
        unfold Var.interp.
        rewrite !wf_interp_form; trivial. rewrite Heq4. simpl.

        rewrite !andb_true_iff in Heq9.
        destruct Heq9 as (((Heq9a, Heq9b), Heq9c), Heq9d).

        apply Typ.eqb_spec in Heq9a.
        apply Typ.eqb_spec in Heq9b.
        apply Typ.eqb_spec in Heq9c.
        apply Typ.eqb_spec in Heq9d.

        rewrite !andb_true_iff in Heq11.
        destruct Heq11 as (((Heq11a, Heq11b), Heq11c), Heq11d).
        rewrite !orb_true_iff in Heq11d.
        destruct Heq11d as [ Heq11d | Heq11d ].

        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia1.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala1)).
        intros. specialize (H41 Htia1). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia2 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala2) (v_valc2)).
        intros. specialize (H42 Htic2''). now rewrite H42 in isif.
        (* symmetric case: Aapp *)
        apply Typ.eqb_spec in Heq11a.
        apply Typ.eqb_spec in Heq11b.
        apply Int63Properties.eqb_spec in Heq11c.
        rewrite !andb_true_iff in Heq11d.
        destruct Heq11d as ((Heq11d1, Heq11d2), Heq11d3).
        apply Int63Properties.eqb_spec in Heq11d1.
        apply Int63Properties.eqb_spec in Heq11d2.
        apply Int63Properties.eqb_spec in Heq11d3.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H2 a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq5. easy.
        specialize (H3 H4). simpl in H3.
        rewrite Heq5 in H3. simpl in H3.
        rewrite !andb_true_iff in H3. destruct H3. destruct H3.
        unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

        case_eq (t_interp .[ a]).
          intros v_typea v_vala Htia. rewrite Htia in H3.
          case_eq v_typea; intros; rewrite H7 in H3; try now contradict H3.

        case_eq (t_interp .[ a1]).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H6.
        case_eq (t_interp .[ a2]).
            intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H5.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        rewrite Heq5 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1, Htia2 in Htia. simpl in Htia.
        rewrite !Atom.t_interp_wf in isif; trivial.
        rewrite Htia1, Htia2 in isif. simpl in isif.
        unfold Bval in isif.

        apply Typ.eqb_spec in H5. apply Typ.eqb_spec in H6.

        generalize dependent v_vala1. generalize dependent v_vala2.
        generalize dependent v_vala.
        rewrite H5, H6, H7.
        rewrite !Typ.cast_refl. intros. simpl in Htia.
        unfold Bval in Htia.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_vala1 v_vala2) (v_vala)).
        intros. specialize (H8 Htia).

        (* get the same kind of info for b, b1, b2 and c1 *)

        (* b *)
        pose proof (H2 b). assert (b < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6. easy.
        specialize (H9 H10). simpl in H9.
        rewrite Heq6 in H9. simpl in H9.
        rewrite !andb_true_iff in H9. destruct H9. destruct H9.
        unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

        case_eq (t_interp .[ b]).
          intros v_typeb v_valb Htib. rewrite Htib in H9.
          case_eq v_typeb; intros; rewrite H13 in H9; try now contradict H9.

        case_eq (t_interp .[ b1]).
          intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H12.
        case_eq (t_interp .[ b2]).
            intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H11.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Atom.t_interp_wf in Htib1; trivial.
        rewrite Atom.t_interp_wf in Htib2; trivial.
        rewrite Heq6 in Htib. simpl in Htib.
        rewrite !Atom.t_interp_wf in Htib; trivial.
        rewrite Htib1, Htib2 in Htib. simpl in Htib.

        apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb.
        rewrite H11, H12, H13.
        rewrite !Typ.cast_refl. intros. simpl in Htib.
        unfold Bval in Htib.

        remember Atom.Bval_inj2.
        specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t0 v_valb1 v_valb2) (v_valb)).
        intros. specialize (H14 Htib).

        (* b1; b2 *)
        pose proof (H2 b1). assert (b1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
        specialize (H15 H16). simpl in H15.
        rewrite Heq7 in H15. simpl in H15.
        rewrite !andb_true_iff in H15. destruct H15. destruct H15.
        unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

       case_eq (t_interp .[ b1]).
          intros v_typeb1' v_valb1' Htib1'. rewrite Htib1' in H15.

        case_eq (t_interp .[ c1]).
          intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H18.
        case_eq (t_interp .[ c2]).
            pose proof Htib1' as Htib1''.
            intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H17.
            pose proof Htic2 as Htic2''.
        rewrite Atom.t_interp_wf in Htib1'; trivial.
        rewrite Atom.t_interp_wf in Htic1; trivial.
        rewrite Atom.t_interp_wf in Htic2; trivial.
        rewrite Heq7 in Htib1'. simpl in Htib1'.
        rewrite !Atom.t_interp_wf in Htib1'; trivial.
        rewrite Htic1, Htic2 in Htib1'. simpl in Htib1'.

        apply Typ.eqb_spec in H17. apply Typ.eqb_spec in H18.
        apply Typ.eqb_spec in H15. 

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.
        rewrite H17, H18.
        rewrite !Typ.cast_refl. intros. simpl in Htib1'.
        unfold Bval in Htib1'.

        remember Atom.Bval_inj2.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_valb1'.

        rewrite H15. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb1') (select v_valc1 v_valc2) (v_valb1')).
        intros. specialize (H19 Htib1').

        (* b2 *)
        pose proof (H2 b2). assert (b2 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq8. easy.
        specialize (H20 H21). simpl in H20.
        rewrite Heq8 in H20. simpl in H20.
        rewrite !andb_true_iff in H20. destruct H20. destruct H20.
        unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

       case_eq (t_interp .[ b2]).
          intros v_typeb2' v_valb2' Htib2'. rewrite Htib2' in H20.

        case_eq (t_interp .[ d1]).
          intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H23.
        case_eq (t_interp .[ d2]).
            pose proof Htib2' as Htib2''.
            intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H22.
        rewrite Atom.t_interp_wf in Htib2'; trivial.
        rewrite Atom.t_interp_wf in Htid1; trivial.
        rewrite Atom.t_interp_wf in Htid2; trivial.
        rewrite Heq8 in Htib2'. simpl in Htib2'.
        rewrite !Atom.t_interp_wf in Htib2'; trivial.
        rewrite Htid1, Htid2 in Htib2'. simpl in Htib2'.

        apply Typ.eqb_spec in H22. apply Typ.eqb_spec in H23.
        apply Typ.eqb_spec in H20. 

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.
        rewrite H22, H23.
        rewrite !Typ.cast_refl. intros. simpl in Htib2'.
        unfold Bval in Htib2'.

        remember Atom.Bval_inj2.

        generalize dependent v_vald1. generalize dependent v_vald2.
        generalize dependent v_valb2'.

        rewrite H20. intros.
        specialize (Atom.Bval_inj2 t_i (v_typeb2') (select v_vald1 v_vald2) (v_valb2')).
        intros. specialize (H24 Htib2').

        (* d1 *)
        pose proof (H2 d1). assert (d1 < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq10. easy.
        specialize (H25 H26). simpl in H25.
        rewrite Heq10 in H25. simpl in H25.
        rewrite !andb_true_iff in H25. destruct H25. destruct H25. destruct H25.
        unfold get_type' in H25, H27, H28, H29. unfold v_type in H25, H27, H28, H29.

       case_eq (t_interp .[ d1]).
          intros v_typed1' v_vald1' Htid1'. rewrite Htid1' in H25.
          case_eq v_typed1'; intros; rewrite H30 in H25; try now contradict H25.
          rewrite andb_true_iff in H25; destruct H25 as (H25a, H25b).

        case_eq (t_interp .[ e1]).
          intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H29.
        case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H28.
        case_eq (t_interp .[ e3]).
          intros v_typee3 v_vale3 Htie3. rewrite Htie3 in H27.
            pose proof Htid1' as Htid1''.
        rewrite Atom.t_interp_wf in Htid1'; trivial.
        rewrite Atom.t_interp_wf in Htie1; trivial.
        rewrite Atom.t_interp_wf in Htie2; trivial.
        rewrite Atom.t_interp_wf in Htie3; trivial.
        rewrite Heq10 in Htid1'. simpl in Htid1'.
        rewrite !Atom.t_interp_wf in Htid1'; trivial.
        rewrite Htie1, Htie2, Htie3 in Htid1'. simpl in Htid1'.

        apply Typ.eqb_spec in H25a. apply Typ.eqb_spec in H25b.
        apply Typ.eqb_spec in H27.  apply Typ.eqb_spec in H28.
        apply Typ.eqb_spec in H29.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.
        rewrite H27, H28, H29.
        rewrite !Typ.cast_refl. intros. simpl in Htid1'.
        unfold Bval in Htid1'.

        remember Atom.Bval_inj2.

        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3. generalize dependent v_vald1'.

        rewrite H25a, H25b, H30. intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) 
          (store v_vale1 v_vale2 v_vale3) (v_vald1')).
        intros. specialize (H25 Htid1').
        
        unfold interp_form_hatom, interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq6. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq7, Heq8. simpl.
        rewrite !Atom.t_interp_wf; trivial.

        rewrite Htic1, Htic2, Htid1, Htid2. simpl.
        rewrite H15, H20.
        rewrite !Typ.cast_refl.
        unfold apply_binop.
        unfold Bval.
        rewrite !Atom.t_interp_wf in Htib1''; trivial.
        rewrite Htib1 in Htib1''.
        inversion Htib1''.
        rewrite !Atom.t_interp_wf in Htib2''; trivial.
        rewrite Htib2 in Htib2''.
        inversion Htib2''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.

        rewrite <- H32, H34.
        rewrite !Typ.cast_refl. intros.

        unfold interp_bool. rewrite Typ.cast_refl.
        apply Typ.i_eqb_spec.

        rewrite !Atom.t_interp_wf in Htid1''; trivial.
        rewrite Htid1 in Htid1''.
        inversion Htid1''.

        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_valb1'. generalize dependent v_valb2'.
        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite H36, H37.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8)(v_vald1) (v_vald1')).
        intros. specialize (H31 Htid1'').
        rewrite H31.
        rewrite <- H25.
        
        rewrite <- Heq11c in Htic1.
        rewrite Htie1 in Htic1.
        rewrite Heq9a in Heq9b.
        rewrite <- Heq9b in H36.

        generalize dependent v_valc1. generalize dependent v_valc2.
        rewrite H36. intros.

        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t8) (v_vale1) (v_valc1)).
        intros. specialize (H39 Htic1).
        rewrite H39.

        (*c2 = d2*)
        rewrite <- Heq11d2 in Heq11d3.
        rewrite <- Heq11d3 in Htic2.
        rewrite Htid2 in Htic2.
        specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_valc2)).
        intros. specialize (H40 Htic2). rewrite H40.

        symmetry; apply read_over_other_write.

        unfold Lit.interp in isif.
        apply Typ.i_eqb_spec_false in isif.
        rewrite H25a in Heq11a.

        generalize dependent v_valc1. generalize dependent v_valc2.
        generalize dependent v_vald1'.
        generalize dependent v_vale1. generalize dependent v_vale2.
        generalize dependent v_vale3.
        generalize dependent v_vald1. generalize dependent v_vald2.

        rewrite <- Heq11a, Heq11d1. intros.
        rewrite Htie2 in Htia2.
        specialize (Atom.Bval_inj2 t_i t (v_vale2) (v_vala2)).
        intros. specialize (H41 Htia2). rewrite <- H41 in isif.

        rewrite !Atom.t_interp_wf in Htic2''; trivial.
        rewrite Heq11d2 in Htic2''.
        rewrite Htia1 in Htic2''.
        specialize (Atom.Bval_inj2 t_i t (v_vala1) (v_valc2)).
        intros. specialize (H42 Htic2''). rewrite H42 in isif.
        unfold not in *. intros.
        now apply isif.
      (* end t5: Aapp *)
Qed.


  Axiom afold_left_or : forall a,
    afold_left bool int false orb (Lit.interp rho) a =
    C.interp rho (to_list a).

Require Import Psatz.

    Lemma valid_check_ext lres : C.valid rho (check_ext lres).
      unfold check_ext.
      case_eq (Lit.is_pos lres); intro Heq; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a Heq2.
      case_eq (length a == 2); [ intros Heq3 | intros Heq3; now apply C.interp_true].
      case_eq (Lit.is_pos (a .[ 0]) && negb (Lit.is_pos (a .[ 1])));
        [ intros Heq4 | intros Heq4; now apply C.interp_true].
      case_eq (t_form .[ Lit.blit (a .[0])]); try (intros; now apply C.interp_true).
      intros b Heq5.
      case_eq (t_form .[ Lit.blit (a .[1])]); try (intros; now apply C.interp_true).
      intros c Heq6.
      case_eq (t_atom .[ b]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] b1 b2 Heq7; try (intros; now apply C.interp_true).
      case_eq t; try (intros; now apply C.interp_true). intros t0 t1 Heq8.
      case_eq (t_atom .[ c]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] c1 c2 Heq9; try (intros; now apply C.interp_true).
      case_eq (Typ.eqb t1 t2); [ intros Heq10 | intros Heq10; now apply C.interp_true].
      case_eq (t_atom .[ c1]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] d1 d2 Heq11; try (intros; now apply C.interp_true).
      case_eq (t_atom .[ c2]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] e1 e2 Heq12; try (intros; now apply C.interp_true).
      case_eq (Typ.eqb t0 t3 && Typ.eqb t0 t5 && Typ.eqb t1 t4 && Typ.eqb t1 t6 && 
                  (b1 == d1) && (b2 == e1) && (d2 == e2)); 
                  [ intros Heq13 | intros Heq13; now apply C.interp_true].
      case_eq (t_atom .[ d2]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | |N|N|N|N|N|N|N|N|N| | ] f1 f2 Heq14; try (intros; now apply C.interp_true).

      case_eq (Typ.eqb t0 t7 && Typ.eqb t1 t8 && (f1 == b1) && (f2 == b2)); 
                [ intros Heq15 | intros Heq15; now apply C.interp_true].

      unfold C.valid. simpl. rewrite orb_false_r.

      rewrite !andb_true_iff in Heq13, Heq15.
      destruct Heq13 as ((Heq13a, Heq13b), Heq13c).
      rewrite andb_true_iff in Heq13a.
      destruct Heq13a as ((Heq13a, Heq13d), Heq13e).
      rewrite andb_true_iff in Heq13a.
      destruct Heq13a as (Heq13, Heq13a).
      rewrite andb_true_iff in Heq13.
      destruct Heq13 as (Heq13, Heq13f).

      destruct Heq15 as (((Heq15, Heq15a), Heq15b), Heq15c).

      apply Typ.eqb_spec in Heq13.
      apply Typ.eqb_spec in Heq13f.
      apply Typ.eqb_spec in Heq13a.
      apply Typ.eqb_spec in Heq13d.
      apply Typ.eqb_spec in Heq15.
      apply Typ.eqb_spec in Heq15a.

      apply Int63Properties.eqb_spec in Heq13e.
      apply Int63Properties.eqb_spec in Heq13b.
      apply Int63Properties.eqb_spec in Heq13c.
      apply Int63Properties.eqb_spec in Heq15b.
      apply Int63Properties.eqb_spec in Heq15c.

      unfold Lit.interp. rewrite Heq.
      unfold Var.interp.
      rewrite !wf_interp_form; trivial. rewrite Heq2. simpl.
      rewrite afold_left_or.
      unfold to_list.
      rewrite Int63Properties.eqb_spec in Heq3.
      rewrite Heq3. simpl. rewrite orb_false_r.
      assert (2 - 1 = 1). { auto. }
      rewrite H.

      case_eq (Lit.interp rho (a .[ 0])). intro Hisa0.
      rewrite orb_true_l. easy. intro Hisa. rewrite orb_false_l.

      pose proof (rho_interp (Lit.blit (a .[ 0]))).
      pose proof (rho_interp (Lit.blit (a .[ 1]))).

      rewrite Heq5 in H0. rewrite Heq6 in H1.
      simpl in H0, H1.
      unfold Lit.interp.
      rewrite andb_true_iff in Heq4.
      destruct Heq4 as (Heq4, Heq4a).
      apply negb_true_iff in Heq4a.

      unfold Lit.interp in Hisa.
      rewrite Heq4 in Hisa. unfold Var.interp in Hisa.
      rewrite Hisa in H0. symmetry in H0.
      rewrite Heq4a.
      unfold Var.interp.
      rewrite H1.

      generalize wt_t_atom. unfold Atom.wt. unfold is_true.
      rewrite PArray.forallbi_spec;intros.

    (* b *)
      pose proof (H2 b). assert (b < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq7. easy.
      specialize (H3 H4). simpl in H3.
      rewrite Heq7 in H3. simpl in H3.
      rewrite !andb_true_iff in H3. destruct H3. destruct H3.
      unfold get_type' in H3, H5, H6. unfold v_type in H3, H5, H6.

      case_eq (t_interp .[ b]).
        intros v_typeb v_valb Htib. rewrite Htib in H3.
        pose proof Htib as Htib''.
        case_eq v_typeb; intros; rewrite H7 in H3; try now contradict H3.

      case_eq (t_interp .[ b1]).
        intros v_typeb1 v_valb1 Htib1. rewrite Htib1 in H6.
        pose proof Htib1 as Htib1''.
      case_eq (t_interp .[ b2]).
          intros v_typeb2 v_valb2 Htib2. rewrite Htib2 in H5.
        pose proof Htib2 as Htib2''.
      rewrite Atom.t_interp_wf in Htib; trivial.
      rewrite Atom.t_interp_wf in Htib1; trivial.
      rewrite Atom.t_interp_wf in Htib2; trivial.
      rewrite Heq7 in Htib. simpl in Htib.
      rewrite !Atom.t_interp_wf in Htib; trivial.
      rewrite Htib1, Htib2 in Htib.
      unfold apply_binop in Htib.
      apply Typ.eqb_spec in H5.
      apply Typ.eqb_spec in H6.

      generalize dependent v_valb1. generalize dependent v_valb2.
      generalize dependent v_valb.
      rewrite H5, H6, H7. rewrite !Typ.cast_refl. intros.

      specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t v_valb1 v_valb2) (v_valb)).
      intros. specialize (H8 Htib).

     (* c *)
      pose proof (H2 c). assert (c < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy.
      specialize (H9 H10). simpl in H9.
      rewrite Heq9 in H9. simpl in H9.
      rewrite !andb_true_iff in H9. destruct H9. destruct H9.
      unfold get_type' in H9, H11, H12. unfold v_type in H9, H11, H12.

      case_eq (t_interp .[ c]).
        intros v_typec v_valc Htic. rewrite Htic in H9.
        pose proof Htic as Htic''.
        case_eq v_typec; intros; rewrite H13 in H9; try now contradict H9.

      case_eq (t_interp .[ c1]).
        intros v_typec1 v_valc1 Htic1. rewrite Htic1 in H12.
      case_eq (t_interp .[ c2]).
          intros v_typec2 v_valc2 Htic2. rewrite Htic2 in H11.
      rewrite Atom.t_interp_wf in Htic; trivial.
      rewrite Atom.t_interp_wf in Htic1; trivial.
      rewrite Atom.t_interp_wf in Htic2; trivial.
      rewrite Heq9 in Htic. simpl in Htic.
      rewrite !Atom.t_interp_wf in Htic; trivial.
      rewrite Htic1, Htic2 in Htic. simpl in Htic.

      apply Typ.eqb_spec in H11. apply Typ.eqb_spec in H12.

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc.
      rewrite H11, H12, H13.
      rewrite !Typ.cast_refl. intros. simpl in Htic.
      unfold Bval in Htic.

      remember Atom.Bval_inj2.
      specialize (Atom.Bval_inj2 t_i (Typ.Tbool) (Typ.i_eqb t_i t2 v_valc1 v_valc2) (v_valc)).
      intros. specialize (H14 Htic).

     (* c1 *)
      pose proof (H2 c1). assert (c1 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq11. easy.
      specialize (H15 H16). simpl in H15.
      rewrite Heq11 in H15. simpl in H15.
      rewrite !andb_true_iff in H15. destruct H15. destruct H15.
      unfold get_type' in H15, H17, H18. unfold v_type in H15, H17, H18.

      case_eq (t_interp .[ c1]).
        intros v_typec1' v_valc1' Htic1'. rewrite Htic1' in H15.
        pose proof Htic1' as Htic1'''.

      case_eq (t_interp .[ d1]).
        intros v_typed1 v_vald1 Htid1. rewrite Htid1 in H18.
      case_eq (t_interp .[ d2]).
          intros v_typed2 v_vald2 Htid2. rewrite Htid2 in H17.
      rewrite Atom.t_interp_wf in Htic1'; trivial.
      rewrite Atom.t_interp_wf in Htid1; trivial.
      rewrite Atom.t_interp_wf in Htid2; trivial.
      rewrite Heq11 in Htic1'. simpl in Htic1'.
      rewrite !Atom.t_interp_wf in Htic1'; trivial.
      rewrite Htid1, Htid2 in Htic1'. simpl in Htic1'.

      apply Typ.eqb_spec in H15. apply Typ.eqb_spec in H17.
      apply Typ.eqb_spec in H18.

      generalize dependent v_vald1. generalize dependent v_vald2.
      generalize dependent v_valc1'.

      rewrite H15, H17, H18.
      unfold Bval. rewrite <- H15.
      rewrite !Typ.cast_refl. intros.

      specialize (Atom.Bval_inj2 t_i t4 (select v_vald1 v_vald2) (v_valc1')).
      intros. specialize (H19 Htic1').

     (* c2 *)
      pose proof (H2 c2). assert (c2 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq12. easy.
      specialize (H20 H21). simpl in H20.
      rewrite Heq12 in H20. simpl in H20.
      rewrite !andb_true_iff in H20. destruct H20. destruct H20.
      unfold get_type' in H20, H22, H23. unfold v_type in H20, H22, H23.

      case_eq (t_interp .[ c2]).
        intros v_typec2' v_valc2' Htic2'. rewrite Htic2' in H20.
        pose proof Htic2' as Htic2'''.

      case_eq (t_interp .[ e1]).
        intros v_typee1 v_vale1 Htie1. rewrite Htie1 in H23.
      case_eq (t_interp .[ e2]).
          intros v_typee2 v_vale2 Htie2. rewrite Htie2 in H22.
          pose proof Htie2 as Htie2''.
      rewrite Atom.t_interp_wf in Htic2'; trivial.
      rewrite Atom.t_interp_wf in Htie1; trivial.
      rewrite Atom.t_interp_wf in Htie2; trivial.
      rewrite Heq12 in Htic2'. simpl in Htic2'.
      rewrite !Atom.t_interp_wf in Htic2'; trivial.
      rewrite Htie1, Htie2 in Htic2'. simpl in Htic2'.

      apply Typ.eqb_spec in H20. apply Typ.eqb_spec in H22.
      apply Typ.eqb_spec in H23.

      generalize dependent v_valc1'. generalize dependent v_valc2'.
      generalize dependent v_vale1. generalize dependent v_vale2.

      rewrite H20, H22, H23.
      unfold Bval. rewrite <- H20.
      rewrite !Typ.cast_refl. intros.

      specialize (Atom.Bval_inj2 t_i t6 (select v_vale1 v_vale2) (v_valc2')).
      intros. specialize (H24 Htic2').

     (* d2 *)
      pose proof (H2 d2). assert (d2 < PArray.length t_atom).
      apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq14. easy.
      specialize (H25 H26). simpl in H25.
      rewrite Heq14 in H25. simpl in H25.
      rewrite !andb_true_iff in H25. destruct H25. destruct H25.
      unfold get_type' in H25, H27, H28. unfold v_type in H25, H27, H28.

      case_eq (t_interp .[ d2]).
        intros v_typed2' v_vald2' Htid2'. rewrite Htid2' in H25.
        pose proof Htid2' as Htid2'''.

      case_eq (t_interp .[ f1]).
        intros v_typef1 v_valf1 Htif1. rewrite Htif1 in H28.
      case_eq (t_interp .[ f2]).
          intros v_typef2 v_valf2 Htif2. rewrite Htif2 in H27.
      rewrite Atom.t_interp_wf in Htid2'; trivial.
      rewrite Atom.t_interp_wf in Htif1; trivial.
      rewrite Atom.t_interp_wf in Htif2; trivial.
      rewrite Heq14 in Htid2'. simpl in Htid2'.
      rewrite !Atom.t_interp_wf in Htid2'; trivial.
      rewrite Htif1, Htif2 in Htid2'. simpl in Htid2'.

      apply Typ.eqb_spec in H25. apply Typ.eqb_spec in H27.
      apply Typ.eqb_spec in H28.

      generalize dependent v_valf1. generalize dependent v_valf2.
      generalize dependent v_vald2'.

      rewrite H25, H27, H28.
      unfold Bval. rewrite <- H25.
      rewrite !Typ.cast_refl. intros.

      specialize (Atom.Bval_inj2 t_i t7 (diff v_valf1 v_valf2) (v_vald2')).
      intros. specialize (H29 Htid2').

     (* semantics *)

      unfold interp_form_hatom, interp_hatom.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite (*Heq7,*) Heq9. simpl.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite (*Htib1, Htib2,*) Heq11, Heq12. simpl.
      (*rewrite !Typ.cast_refl.*)

      unfold apply_binop.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Htid1, Heq14, Htie1, Htie2.
      rewrite !Typ.cast_refl.
      unfold interp_atom.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Htif1, Htif2. simpl.
      rewrite !Typ.cast_refl. simpl.

      (* t7 = t3 *)
      rewrite !Atom.t_interp_wf in Htid2'''; trivial.
      rewrite Htid2 in Htid2'''.
      inversion Htid2'''.

      (* t2 = t6 *)
      rewrite !Atom.t_interp_wf in Htic1'''; trivial.
      rewrite Htic1 in Htic1'''.
      inversion Htic1'''.

      (* t4 = t6 *)
      rewrite !Atom.t_interp_wf in Htic2'''; trivial.
      rewrite Htic2 in Htic2'''.
      inversion Htic2'''.

      generalize dependent v_valc1. generalize dependent v_valc2.
      generalize dependent v_valc1'. generalize dependent v_valc2'.
      generalize dependent v_vald1. generalize dependent v_vald2.

      rewrite H31, H33.
      rewrite !Typ.cast_refl. simpl.
      rewrite !Typ.cast_refl.
      rewrite H33 in H35. rewrite H35.
      rewrite !Typ.cast_refl. intros. simpl.

      apply negb_true_iff.
      apply Typ.i_eqb_spec_false.

      generalize dependent v_vale1. generalize dependent v_vale2.
      generalize dependent v_valf1. generalize dependent v_valf2.


      rewrite <- Heq15a, Heq13d.
      rewrite <- Heq13f, Heq15. intros.
      rewrite  H29.

      (* d2' = d2 *)
      specialize (Atom.Bval_inj2 t_i t7 (v_vald2) (v_vald2')).
      intros. specialize (H30 Htid2''').
      rewrite <- H30.
      (* d2 = e2 *)
      rewrite Heq13c in Htid2.
      rewrite Htie2 in Htid2.
      specialize (Atom.Bval_inj2 t_i t7 (v_vale2) (v_vald2)).
      intros. specialize (H37 Htid2).
      rewrite H37.

      (* b1 <> b2 *)
      unfold interp_form_hatom, interp_hatom in H0.
      rewrite !Atom.t_interp_wf in H0; trivial.
      rewrite Heq7 in H0. simpl in H0.
      rewrite !Atom.t_interp_wf in H0; trivial.
      rewrite Htib1, Htib2 in H0. simpl in H0.
      rewrite !Typ.cast_refl in H0. simpl in H0.
      apply Typ.i_eqb_spec_false in H0.

      (* f1 = b1 *)

      generalize dependent v_vald1. generalize dependent v_vald2.
      generalize dependent v_valc1'. generalize dependent v_valc2'.
      generalize dependent v_vale1. generalize dependent v_vale2.

      rewrite <- Heq13e, <- Heq13b; intros.
      rewrite Htid1 in Htib1.
      rewrite Htie1 in Htib2.
      inversion Htib1.
      inversion Htib2.

      generalize dependent v_valb.
      generalize dependent v_valb1. generalize dependent v_valb2.

      rewrite <- H39. intros.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t6) (v_vald1) (v_valb1)).
      intros. specialize (H38 Htib1). rewrite H38.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t6) (v_vale1) (v_valb2)).
      intros. specialize (H43 Htib2). rewrite H43.

      rewrite H30, <- H29.

      (* b1 = f1 and b2 = f2 *)
      rewrite Heq15b, Heq15c in *.
      rewrite !Atom.t_interp_wf in Htib1''; trivial.
      rewrite !Atom.t_interp_wf in Htib2''; trivial.
      rewrite Htib1'' in Htif1.
      rewrite Htib2'' in Htif2.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t6) (v_valb1) (v_valf1)).
      intros. specialize (H44 Htif1). rewrite H44.
      specialize (Atom.Bval_inj2 t_i (Typ.TFArray t7 t6) (v_valb2) (v_valf2)).
      intros. specialize (H45 Htif2). rewrite H45.

      apply select_over_diff.
      now rewrite H44, H45 in H0.
      
Qed.

  End Correct.

End certif.
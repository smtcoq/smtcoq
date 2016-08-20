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
                match get_atom sa with
                | Atop (TO_store ti3 te3) sa1 i1 _ =>
                  if Typ.eqb ti ti3 && Typ.eqb te te3 &&
                     (sa1 == sa2) && 
                     (((i1 == i) && (j1 == j) && (j2 == j)) ||
                      ((i1 == j) && (j1 == i) && (j2 == i))) then
                    cl
                  else C._true
                | _ => C._true
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


    Lemma wrap_read_over_write: forall ti te (a:Typ.interp t_i (Typ.TFArray ti te))
                                (i:Typ.interp t_i ti) (v:Typ.interp t_i te),
        farray_select t_i ti te (farray_store t_i ti te a i v) i = v.
      intros.
      unfold farray_select, farray_store.
      unfold eq_rect_r,eq_rect,eq_sym.
      generalize a.
      rewrite interp_farray_is_farray.
      intro; simpl.
      apply FArray.read_over_write.
      exact (Typ.dec_interp t_i te).
    Qed.

    Lemma wrap_read_over_other_write: forall ti te (a:Typ.interp t_i (Typ.TFArray ti te))
                                      (i j :Typ.interp t_i ti) (v:Typ.interp t_i te),
        i <> j -> farray_select t_i ti te (farray_store t_i ti te a i v) j = farray_select t_i ti te a j.
      intros.
      unfold farray_select, farray_store.
      unfold eq_rect_r,eq_rect,eq_sym.
      generalize a.
      rewrite interp_farray_is_farray.
      intro. simpl.
      apply FArray.read_over_other_write.
      exact H.
    Qed.

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
        
        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_vala1. generalize dependent v_vala2.
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
        
        generalize dependent v_valb1. generalize dependent v_valb2.
        generalize dependent v_vala1. generalize dependent v_vala2.
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
        
        generalize dependent v_val0.
        generalize dependent v_val1.
        generalize dependent v_val2.
        generalize dependent v_val3.
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
        
        generalize dependent v_val0.
        generalize dependent v_val1.
        generalize dependent v_val2.
        generalize dependent v_val3.
        generalize dependent v_val4.
        
        rewrite H6d1, H6d2, H14.
        intros.
        specialize (Atom.Bval_inj2 t_i (Typ.TFArray t0 t) 
        (farray_store t_i t0 t v_val2 v_val3 v_val4) (v_val0)).
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

        apply wrap_read_over_write.
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
      intros [ ] e1 e2 e3 Heq10.

      case_eq (
        Typ.eqb t t5 && Typ.eqb t0 t6 && (e1 == d1) &&
        ((e2 == a1) && (c2 == a2) && (d2 == a2) || (e2 == a2) && (c2 == a1) && (d2 == a1)));
        simpl; intros Heq11; try (now apply C.interp_true).
        
      unfold C.valid. simpl. rewrite orb_false_r.
      unfold Lit.interp. rewrite Heq, Heq2.
      unfold Var.interp.
      rewrite !wf_interp_form; trivial. rewrite Heq3, Heq4. simpl.
      
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
         
      pose proof (rho_interp (Lit.blit i)) as Hrho.
      rewrite Heq3 in Hrho. simpl in Hrho.
        
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

      
      
      
    
    Admitted.
    

    
    Lemma valid_check_ext lres : C.valid rho (check_ext lres).
    Admitted.

    
  End Correct.
  
  
End certif.
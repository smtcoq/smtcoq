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
                 Typ.eqb te te2 && Typ.eqb te te2 &&
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
            | Abop (BO_select ti1 te1) sa i1, Abop (BO_select ti2 te2) sa2 i2 =>
              if Typ.eqb ti ti1 && Typ.eqb ti ti2 &&
                 Typ.eqb te te2 && Typ.eqb te te2 &&
                 (i1 == i) && (i2 == i) then
                match get_atom sa with
                | Atop (TO_store ti3 te3) sa1 j1 _ =>
                  if Typ.eqb ti ti3 && Typ.eqb ti ti3 &&
                     (j1 == j) && (sa1 == sa2) then
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
    Admitted.

    
    Lemma valid_check_rowneq cl : C.valid rho (check_rowneq cl).
    Admitted.

    
  End Correct.
  
  
End certif.
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
Require Lia.

Local Open Scope array_scope.
Local Open Scope int63_scope.


(* Arbritrary arithmetic simplifications *)

Section Arith.

  Variable t_form : PArray.array Form.form.
  Variable t_atom : PArray.array Atom.atom.

  Local Notation build_clause := (Lia.build_clause t_form t_atom).


  Definition check_spl_arith orig res l :=
    match orig with
      | li::nil =>
        let cl := (Lit.neg li)::res::nil in
        match build_clause Lia.empty_vmap cl with
          | Some (_, bf) =>
            if ZTautoChecker bf l then res::nil
            else C._true
          | None => C._true
        end
      | _ => C._true
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
    Proof. destruct (Form.check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form); auto. Qed.

    Hint Immediate wf_rho.


    Lemma valid_check_spl_arith :
      forall orig, C.valid rho orig ->
        forall res l, C.valid rho (check_spl_arith orig res l).
    Proof.
      unfold check_spl_arith; intros [ |li [ |t q]].
      (* Case nil *)
      intros; apply C.interp_true; auto.
      (* List with one element *)
      intros H res l; case_eq (build_clause Lia.empty_vmap (Lit.neg li :: res :: nil)); [ |intros; apply C.interp_true; auto].
      intros (vm1, bf) Heq; destruct (Lia.build_clause_correct _ _ _ t_func ch_atom ch_form wt_t_atom _ _ _ _ Heq) as [H1 H0].
      red; simpl; auto.
      decompose [and] H0; case_eq (ZTautoChecker bf l); [intros Heq3|intros; apply C.interp_true; auto].
      unfold C.valid; replace (C.interp rho (res :: nil)) with (C.interp rho (Lit.neg li :: res :: nil)).
      rewrite H6; apply ZTautoChecker_sound with l;trivial.
      simpl; replace (Lit.interp rho (Lit.neg li)) with false; auto.
      rewrite Lit.interp_neg; unfold C.valid in H; simpl in H; rewrite orb_false_r in H; rewrite H; auto.
      (* List with at least two elements *)
      intros; apply C.interp_true; auto.
    Qed.

  End Valid.

End Arith.

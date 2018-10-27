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


Require Import State SMT_terms.
Require Import List Bool PArray Int63.

Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.


(* User-friendly interpretation of clauses and of consequences *)
Section Interp_UF.

  Fixpoint interp_uf (rho:Valuation.t) (c:C.t) :=
    match c with
    | nil => false
    | l::nil => Lit.interp rho l
    | l::c => (Lit.interp rho l) || (interp_uf rho c)
    end.

  Lemma interp_equiv rho c : C.interp rho c = interp_uf rho c.
  Proof.
    induction c as [ |l c IHc]; simpl; auto.
    rewrite IHc. destruct c as [ |l' c]; simpl; auto.
    now rewrite orb_false_r.
  Qed.

  Fixpoint interp_conseq_uf (rho:Valuation.t) (prem:list C.t) (concl:C.t) :=
    match prem with
    | nil => is_true (interp_uf rho concl)
    | c::prem => is_true (interp_uf rho c) -> interp_conseq_uf rho prem concl
    end.

End Interp_UF.


(* Small checker for assumptions *)

Section Checker.

  Section Forallb2.

    Variables A B : Type.
    Variable P : A -> B -> bool.

    Fixpoint forallb2 (xs: list A) (ys:list B) {struct xs} : bool :=
      match xs, ys with
      | nil, nil => true
      | x::xs, y::ys => (P x y) && (forallb2 xs ys)
      | _, _ => false
      end.

  End Forallb2.

  Definition check_hole (s:S.t) (prem_id:list clause_id) (prem:list C.t) (concl:C.t) : C.t :=
    if forallb2 (fun id c => forallb2 (fun i j => i == j) (S.get s id) (S.sort_uniq c)) prem_id prem
    then concl
    else C._true.

End Checker.


Section Checker_correct.

  Variable t_i : array typ_eqb.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.

  Local Notation rho := (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form).

  Variable s : S.t.
  Hypothesis Hs : S.valid rho s.
  Hypothesis Ht3 : Valuation.wf
          (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
             t_form).

  Lemma interp_check_clause c1 : forall c2,
    forallb2 (fun i j => i == j) c1 c2 -> C.interp rho c1 = C.interp rho c2.
  Proof.
    induction c1 as [ |l1 c1 IHc1]; simpl; intros [ |l2 c2]; simpl; auto; try discriminate.
    unfold is_true. rewrite andb_true_iff. intros [H1 H2].
    rewrite Int63Properties.eqb_spec in H1. now rewrite (IHc1 _ H2), H1.
  Qed.

  Lemma valid_check_clause cid c :
    forallb2 (fun i j => i == j) (S.get s cid) (S.sort_uniq c) ->
    interp_uf rho c.
  Proof.
    intro H. rewrite <- interp_equiv, <- S.sort_uniq_correct; auto.
    rewrite <- (interp_check_clause _ _ H). now apply Hs.
  Qed.

  Lemma valid_check_forall_inst (lemma : Prop) :
    lemma ->
    forall concl,
    (lemma -> interp_uf rho concl) ->
    C.valid rho concl.

  Proof.
    intros pl concl applemma.
    unfold C.valid. rewrite interp_equiv.
    now apply applemma.
  Qed.

  Variable prem_id : list int.
  Variable prem : list C.t.
  Variable concl : C.t.
  Hypothesis p : interp_conseq_uf
        (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
           t_form) prem concl.

  Lemma valid_check_hole: C.valid rho (check_hole s prem_id prem concl).
  Proof.
    unfold check_hole. revert prem p. induction prem_id as [ |pid pids IHpids]; simpl;
      intros [ |p ps]; simpl; intro H.
    - unfold C.valid. now rewrite interp_equiv.
    - now apply C.interp_true.
    - now apply C.interp_true.
    - case_eq (forallb2 (fun i j => i == j) (S.get s pid) (S.sort_uniq p));
      simpl; intro Heq; [ |now apply C.interp_true].
      apply IHpids. apply H. apply (valid_check_clause _ _ Heq).
  Qed.

End Checker_correct.


Unset Implicit Arguments.

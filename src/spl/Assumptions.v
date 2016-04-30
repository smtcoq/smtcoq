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

  Definition check_hole (s:S.t) (prem_id:list clause_id) (prem:list C.t) (concl:C.t) :=
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

  (* H1 : Form.check_form t_form *)
  (* H2 : Atom.check_atom t_atom *)
  (* H10 : Atom.wt t_i t_func t_atom *)

  Variable s : S.t.
  Hypothesis Hs : S.valid rho s.

  (* Ht1 : default t_form = Form.Ftrue *)
  (* Ht2 : Form.wf t_form *)
  (* Ht3 : Valuation.wf *)
  (*         (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) *)
  (*            t_form) *)
  (* Ha1 : Atom.wf t_atom *)
  (* Ha2 : default t_atom = Atom.Acop Atom.CO_xH *)

  Variable pos : int.
  Variable prem_id : list int.
  Variable prem : list C.t.
  Variable concl : C.t.
  Hypothesis p : interp_conseq_uf
        (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
           t_form) prem concl.

  Lemma valid_check_hole: C.valid rho (check_hole s prem_id prem concl).
                              (* TODO *)
  Admitted.

End Checker_correct.


Unset Implicit Arguments.

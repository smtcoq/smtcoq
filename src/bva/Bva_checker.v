(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(** A small checker for bit-vectors bit-blasting *)

Require Import Int63 PArray.
Require Import Bool List BoolEq NZParity.

Require Import Misc State SMT_terms.


Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.


  Variable t_form : PArray.array form.
  Variable t_atom : PArray.array atom.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).

  (* Ex of an LFSC rule: (x = y) ↔ (x₀ ↔ y₀ ∧ ... ∧ xₙ ↔ yₙ) *)

  Definition check_bv_eq l :=
    match get_form l with
    | Fiff l1 l2 =>
      match get_form l1, get_form l2 with
      | Fatom a, Fand ls =>
        match get_atom a with
        | Abop (BO_eq Typ.TBV) h1 h2 =>
          (* TODO: add the check for the rhs *)
          if Lit.is_pos l then l::nil else C._true
        | _ => C._true
        end
      | _, _ => C._true
      end
    | _ => C._true
    end.


  Section Proof.

    Variables (t_i : array typ_eqb)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation check_atom :=
      (check_aux t_i t_func (get_type t_i t_func t_atom)).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).

    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom t_form).

    Local Notation t_interp := (t_interp t_i t_func t_atom).

    Local Notation interp_atom :=
      (interp_aux t_i t_func (get t_interp)).

    Let wf_t_atom : Atom.wf t_atom.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_atom : default t_atom = Atom.Acop Atom.CO_xH.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_form : default t_form = Form.Ftrue.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_t_form : Form.wf t_form.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_rho : Valuation.wf rho.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom _ ch_form); auto.
    Qed.

    Lemma lit_interp_true : Lit.interp rho Lit._true = true.
    Proof.
      apply Lit.interp_true.
      apply wf_rho.
    Qed.


    Let rho_interp : forall x : int, rho x = Form.interp interp_form_hatom t_form (t_form.[ x]).
    Proof.
      destruct (check_form_correct interp_form_hatom _ ch_form) as ((H,H0), _).
      intros x;apply wf_interp_form;trivial.
    Qed.

    Lemma bool_impl : forall a b, (b = true -> a = true) -> a = true \/ b = false.
    Proof.
      intros;destruct a;
      [(left;trivial) | (right;destruct b;[(symmetry;apply H;trivial) | trivial])].
    Qed.

    Lemma lit_interp_impl : forall a b rho,(Lit.interp rho b = true -> Lit.interp rho a = true) -> (Lit.interp rho a =true \/Lit.interp rho (Lit.neg b) = true).
    Proof.
      intros;rewrite (Lit.interp_neg rho b);rewrite negb_true_iff;apply bool_impl;apply H.
    Qed.


    Lemma valid_check_bv_eq : forall l, C.valid rho (check_bv_eq l).
    Admitted.

  End Proof.

End Checker.

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
Require Import Misc State SMT_terms BVList.
Require Import Bool List BoolEq NZParity.


Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.

  Variable (t_i : array typ_eqb).
  Variable (t_func : array (Atom.tval t_i)).
  Variable t_atom : PArray.array atom.
  Variable t_form : PArray.array form.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).


  (* Bit-blasting a variable:

       ----------------------- bbVar
        bbT(x, [x0; ...; xn])
   *)

  (* TODO: check the first argument of BVbitOf *)
  Fixpoint check_bb a bs i :=
    match bs with
    | nil => true
    | b::bs =>
      if Lit.is_pos b then
        match get_form (Lit.blit b) with
        | Fatom a' =>
          match get_atom a' with
          | Auop (UO_BVbitOf _ n) a' =>
            if (a == a') && (Nat_eqb i n)
            then check_bb a bs (S i)
            else false
          | _ => false
          end
        | _ => false
        end
      else false
    end.

  Definition check_bbVar lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
      | FbbT a bs =>
        if (* (Nat_eqb (N.to_nat (BITVECTOR_LIST.size (Atom.interp_form_hatom_bv t_i t_func t_atom a))) (List.length bs)) && *) (check_bb a bs O)
        then lres::nil
        else C._true
      | _ => C._true
      end
    else C._true.


  Variable s : S.t.


  (* Check the validity of a *symmetric* operator *)
  Fixpoint check_symop (bs1 bs2 bsres : list _lit) get_op :=
    match bs1, bs2, bsres with
    | nil, nil, nil => true
    | b1::bs1, b2::bs2, bres::bsres =>
      if Lit.is_pos bres then
        match get_op (get_form (Lit.blit bres)) with
        | Some (a1, a2) => ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
        | _ => false
        end
      else false
    | _, _, _ => false
    end.


  (* Bit-blasting bitwise operations: bbAnd, bbOr, ...
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a&b, [a0 /\ b0; ...; an /\ bn])
   *)

  Definition get_and f :=
    match f with
    | Fand args => if PArray.length args == 2 then Some (args.[0], args.[1]) else None
    | _ => None
    end.

  Definition get_or f :=
    match f with
    | For args => if PArray.length args == 2 then Some (args.[0], args.[1]) else None
    | _ => None
    end.

  (* TODO: check the first argument of BVand and BVor *)
  Definition check_bbOp pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
          match get_atom a with
          | Abop (BO_BVand _) a1' a2' =>
            if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                 && (check_symop bs1 bs2 bsres get_and)
            then lres::nil
            else C._true
          | Abop (BO_BVor _) a1' a2' =>
            if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                 && (check_symop bs1 bs2 bsres get_or)
            then lres::nil
            else C._true
          | _ => C._true
          end
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.


  (* Bit-blasting equality
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbEq
         (a = b) <-> [(a0 <-> b0) /\ ... /\ (an <-> bn)]
   *)

  Definition get_iff f :=
    match f with
    | Fiff l1 l2 => Some (l1, l2)
    | _ => None
    end.

  Definition check_bbEq pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff leq lbb =>
          match get_form (Lit.blit leq), get_form (Lit.blit lbb) with
          | Fatom a, Fand bsres | Fand bsres, Fatom a =>
            match get_atom a with
            | Abop (BO_eq (Typ.TBV _)) a1' a2' =>
              if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                   && (check_symop bs1 bs2 (PArray.to_list bsres) get_iff)
              then lres::nil
              else C._true
            | _ => C._true
            end
          | _, _ => C._true
          end
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.


  Section Proof.

    Variables (ch_atom : Atom.check_atom t_atom)
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

    Hypothesis Hs : S.valid rho s.

    Local Notation t_interp := (t_interp t_i t_func t_atom).

    Local Notation interp_atom :=
      (interp_aux t_i t_func (get t_interp)).

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

    Lemma lit_interp_true : Lit.interp rho Lit._true = true.
    Proof.
      apply Lit.interp_true.
      apply wf_rho.
    Qed.


    Let rho_interp : forall x : int, rho x = Form.interp interp_form_hatom interp_form_hatom_bv t_form (t_form.[ x]).
    Proof.
      destruct (check_form_correct interp_form_hatom interp_form_hatom_bv _ ch_form) as ((H,H0), _).
      intros x;apply wf_interp_form;trivial.
    Qed.


    Lemma valid_check_bbVar lres : C.valid rho (check_bbVar lres).
    Admitted.

    Lemma valid_check_bbOp pos1 pos2 lres : C.valid rho (check_bbOp pos1 pos2 lres).
    Admitted.

    Lemma valid_check_bbEq pos1 pos2 lres : C.valid rho (check_bbEq pos1 pos2 lres).
    Admitted.

  End Proof.

End Checker.

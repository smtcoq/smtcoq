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
(*Add LoadPath "/home/burak/Desktop/smtcoq/src/bva".*)
Require Import Misc State SMT_terms BVList.
Require Import Bool List BoolEq NZParity.

Import ListNotations.
Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.

  Variable t_atom : PArray.array atom.
  Variable t_form : PArray.array form.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).


  (* Bit-blasting a variable:

              x ∈ BV n
       ----------------------- bbVar
        bbT(x, [x₀; ...; xₙ₋₁])
   *)

  Fixpoint check_bb a bs i n :=
    match bs with
    | nil => Nat_eqb i n                     (* We go up to n *)
    | b::bs =>
      if Lit.is_pos b then
        match get_form (Lit.blit b) with
        | Fatom a' =>
          match get_atom a' with
          | Auop (UO_BVbitOf N p) a' =>
            (* TODO:
               Do not need to check [Nat_eqb l (N.to_nat N)] at every iteration *)
            if (a == a')                     (* We bit blast the right bv *)
                 && (Nat_eqb i p)            (* We consider bits after bits *)
                 && (Nat_eqb n (N.to_nat N)) (* The bv has indeed type BV n *)
            then check_bb a bs (S i) n
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
        if check_bb a bs O (List.length bs)
        then lres::nil
        else C._true
      | _ => C._true
      end
    else C._true.


  Variable s : S.t.


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

  Definition get_xor f :=
    match f with
    | Fxor arg0 arg1 => Some (arg0, arg1)
    | _ => None
    end.

(*
  Definition get_not f :=
    match f with
    | Fnot arg => Some arg
    | _ => None
    end.
*)

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

Lemma get_and_none: forall (n: int), (forall a, t_form .[ Lit.blit n] <> Fand a) ->
(get_and (get_form (Lit.blit n))) = None.
Proof. intros n H.
       unfold get_and.
       case_eq (t_form .[ Lit.blit n]); try reflexivity.
       intros. contradict H0. apply H.
Qed.

Lemma get_and_some: forall (n: int), 
(forall a, PArray.length a == 2 -> t_form .[ Lit.blit n] = Fand a ->
 (get_and (get_form (Lit.blit n))) = Some (a .[ 0], a .[ 1])).
Proof. intros. rewrite H0. unfold get_and. now rewrite H. Qed.

Lemma check_symop_and_some: 
forall a0 b0 c0 la lb lc,
let a := a0 :: la in
let b := b0 :: lb in
let c := c0 :: lc in
Lit.is_pos c0 -> get_and (get_form (Lit.blit c0)) = Some (a0, b0) -> 
check_symop a b c get_and = true.
Proof. intros. simpl.
       rewrite H.
       rewrite H0.
       cut (a0 == a0 = true).
       intros H1; rewrite H1.
       cut (b0 == b0 = true).
       intros H2; rewrite H2.
       simpl. reflexivity.
       now rewrite Lit.eqb_spec.
       now rewrite Lit.eqb_spec. 
Qed.

Lemma empty_false1: forall a b c, a = [] -> c <> [] -> check_symop a b c get_and = false.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros [ | ys IHys].
         + intros [ | zs IHzs].
           * intros. now contradict H0.
           * intros. simpl. reflexivity.
         + intros. simpl. reflexivity.
       - intros. contradict H. easy.
Qed.

Lemma empty_false2: forall a b c, b = [] -> c <> [] -> check_symop a b c get_and = false.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros [ | ys IHys].
         + intros [ | zs IHzs].
           * intros. now contradict H0.
           * intros. simpl. reflexivity.
         + intros. simpl. reflexivity.
       - intros. rewrite H. simpl. reflexivity.
Qed.

Lemma empty_false3: forall a b c, c = [] -> a <> [] -> check_symop a b c get_and = false.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros [ | ys IHys].
         + intros [ | zs IHzs].
           * intros. now contradict H0.
           * intros. simpl. reflexivity.
         + intros. simpl. reflexivity.
       - intros. rewrite H. simpl.
         case b; reflexivity.
Qed.

Lemma empty_false4: forall a b c, c = [] -> b <> [] -> check_symop a b c get_and = false.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros [ | ys IHys].
         + intros [ | zs IHzs].
           * intros. now contradict H0.
           * intros. simpl. reflexivity.
         + intros. simpl. reflexivity.
       - intros. rewrite H. simpl.
         case b; reflexivity.
Qed.


  (* TODO: check the first argument of BVand, BVor *)
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
          | Abop (BO_BVxor _) a1' a2' =>
            if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                 && (check_symop bs1 bs2 bsres get_xor)
            then lres::nil
            else C._true
    (*      | Abop (UO_BVneg _) a1' a2' =>
            if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                 && (check_symop bs1 bs2 bsres get_xor)
            then lres::nil
            else C._true
    *)
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

    (* Lemma lit_interp_true : Lit.interp rho Lit._true = true. *)
    (* Proof. *)
    (*   apply Lit.interp_true. *)
    (*   apply wf_rho. *)
    (* Qed. *)

    (* Let rho_interp : forall x : int, rho x = Form.interp interp_form_hatom interp_form_hatom_bv t_form (t_form.[ x]). *)
    (* Proof. intros x;apply wf_interp_form;trivial. Qed. *)


    Lemma valid_check_bbVar lres : C.valid rho (check_bbVar lres).
    Proof.
      unfold check_bbVar.
      case_eq (Lit.is_pos lres); intro Heq1; [ |now apply C.interp_true].
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bs Heq0.
      case_eq (check_bb a bs 0 (Datatypes.length bs)); intro Heq2; [ |now apply C.interp_true].
      unfold C.valid. simpl. rewrite orb_false_r.
      unfold Lit.interp. rewrite Heq1.
      unfold Var.interp.
      rewrite wf_interp_form. rewrite Heq0. simpl.
      unfold BITVECTOR_LIST.bv_eq, BITVECTOR_LIST.bv.
      simpl. destruct interp_form_hatom_bv.
      unfold RAWBITVECTOR_LIST.bv_eq,  RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.of_bits in *.
      rewrite wf0. rewrite N.eqb_compare. rewrite N.compare_refl.
      unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *.
      (* unfold BITVECTOR_LIST.bv_eq, BITVECTOR_LIST.bv. *)
      (* simpl. destruct interp_form_hatom_bv. *)
      (* unfold RAWBITVECTOR_LIST.bv_eq,  RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.of_bits in *. *)
      (* rewrite wf0. rewrite N.eqb_compare. rewrite N.compare_refl. *)
      (* unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *. *)
    Admitted.    

    Lemma valid_check_bbOp pos1 pos2 lres : C.valid rho (check_bbOp pos1 pos2 lres).
    Proof.
      unfold check_bbOp.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | |A|N|N|N|N|N|N] a1' a2' Heq9; try now apply C.interp_true.
      (* BVand *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (check_symop bs1 bs2 bsres get_and); simpl; intros Heq11; try (now apply C.interp_true).
        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
        unfold Atom.interp_form_hatom_bv at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial. rewrite Heq9. simpl. unfold apply_binop.
        case_eq (t_interp .[ a1']). intros V1 v1 Heq21.
        case_eq (t_interp .[ a2']). intros V2 v2 Heq22.
        admit.
        (* rewrite Typ.neq_cast. case_eq (Typ.eqb V1 (Typ.TBV N)); simpl. *)
        (* We need to define [interp_bv] otherwise. *)
      (* BVor *)
      - admit.
      (* BVxor *)
      - admit.


           (* unfold C.valid, check_bbOp. *)
           (* case_eq (S.get s pos1). intros; unfold C.interp; simpl;  now rewrite lit_interp_true. *)
           (* intros i l H. *)
           (* case l; [ | intros; unfold C.interp; simpl;  now rewrite lit_interp_true]. *)
           (* case_eq (S.get s pos2). intros; unfold C.interp; simpl;  now rewrite lit_interp_true. *)
           (* intros i0 l0 H0. *)
           (* case l0; [ | intros; unfold C.interp; simpl;  now rewrite lit_interp_true]. *)
           (* case_eq (Lit.is_pos i && Lit.is_pos i0 && Lit.is_pos lres); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (* intro Heq. *)
           (* case_eq (t_form .[ Lit.blit lres]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i1 Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 Heq2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 H2. *)
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i1 l1 Heq1. *)
           (*   case_eq (t_form .[ Lit.blit i]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i2 l2 Heq2. *)
             
           (*   case_eq (t_form .[ Lit.blit i0]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*   intros i3 l3 Heq3. *)
           (*     case_eq ( t_atom .[ i1]); try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*     intros. *)
           (*     case_eq b; try (intros; unfold C.interp; simpl;  now rewrite lit_interp_true). *)
           (*     intros n b'. *)
           (*     case_eq (((i2 == i4) && (i3 == i5) || (i2 == i5) && (i3 == i4)) && *)
           (*     check_symop l2 l3 l1 get_and). *)
           (*     intros;unfold C.interp; simpl. unfold Lit.interp in *. *)
           (*     rewrite ?andb_true_iff in Heq. destruct Heq. *)
           (*     rewrite H4. unfold Var.interp. rewrite rho_interp. simpl. rewrite Heq1. *)
           (*     simpl. unfold BITVECTOR_LIST.bv_eq, BITVECTOR_LIST.bv. simpl. *)
           (*     destruct interp_form_hatom_bv. *)
           (*     unfold RAWBITVECTOR_LIST.bv_eq,  RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.of_bits in *. *)
           (*     rewrite wf0. rewrite N.eqb_compare. rewrite N.compare_refl. *)
           (*     unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *. *)
           (*     rewrite orb_false_r. *)
           (*     rewrite ?andb_true_iff in H3. *)
    Admitted.

    Lemma valid_check_bbEq pos1 pos2 lres : C.valid rho (check_bbEq pos1 pos2 lres).
    Admitted.

  End Proof.

End Checker.

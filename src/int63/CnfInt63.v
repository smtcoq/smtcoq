(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Bool.
Require Import List.
Require Import Int63.
Require Import PArray.
Require Import BoolEq.
Require Import NZParity.

Add LoadPath ".." as SMTCoq.

Require Import Misc State.
Require Import SMT_terms.


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

  Variable s : S.t.


  Definition atom_to_int (a : atom) :=
    match a with
    | Acop (CO_int i) => i
    | Auop (UO_index i) a => i
    | _ => 0%int63
    end.

  Fixpoint clean {A:Type} (l:list A) := 
    match l with 
    | nil => nil
    | a::nil => a::nil
    | a::b::c => a::(clean c)
    end.

(*TODO : remplace egalité booléène par equivalent*)
 Definition check_BuildDefInt lits :=
  let n := PArray.length lits in
  if (n == Int63Op.digits + 1)&&(Lit.is_pos (lits.[0]))
  then (
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Abop b h1 h2 => 
        match (b,get_atom h1,get_atom h2) with
        | (BO_eq Tint,Acop (CO_int x),Acop (CO_int y)) => 
          let fonction_map i l := if i == 0 then l else (if Lit.is_pos l then Lit.neg l else l) in
          let test_correct i0 l :=
            if i0 == 0
            then true
            else (
              match get_form (Lit.blit l) with
              | Fiff l1 l2 =>
                match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
                | (Fatom a1,Fatom a2) =>
                  match (get_atom a1,get_atom a2) with
                  | (Auop (UO_index x1) j,Auop (UO_index y1) k) => (j == i0-1)&&(k == j)&&(x == x1)&&(y==y1)
                  | _ => false
                  end
                | _ => false
                end
              | _ => false
              end
                 )
          in
          if forallbi (fun i l => test_correct i l) lits
          then PArray.to_list (PArray.mapi fonction_map lits)
          else C._true
        | _ => C._true
        end
      | _ => C._true
      end
    | _ => C._true
    end
       )
  else C._true
  .


Definition check_BuildProjInt lits i :=
  let n := PArray.length lits in
  if (n == Int63Op.digits + 1)&&(i < Int63Op.digits)
  then (
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Abop b h1 h2 => 
        match (b,get_atom h1,get_atom h2) with
        | (BO_eq t,Acop (CO_int x),Acop (CO_int y)) => 
          let fonction_map i l := if Lit.is_pos l then l else Lit.neg l in
          let test_correct i0 l :=
            match get_form (Lit.blit l) with
            | Fiff l1 l2 =>
              match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
              | (Fatom a1,Fatom a2) =>
                match (get_atom a1,get_atom a2) with
                | (Auop (UO_index x1) j,Auop (UO_index y1) k) => (Lit.is_pos l1)&&(Lit.is_pos l2)&&(Typ.eqb t Typ.Tint)&&(j == i0)&&(k == j)&&(x == x1)&&(y==y1)
                | _ => false
                end
              | _ => false
              end
            | _ => false
            end            
          in
          if test_correct i (lits.[i+1]) 
          then (fonction_map i (lits.[i+1]))::(Lit.nlit (Lit.blit (lits.[0])))::nil
          else C._true
        | _ => C._true
        end
      | _ => C._true
      end
    | _ => C._true
    end
       )
  else C._true
  .




Variable interp_atom : hatom -> bool.

Local Notation rho := (Form.interp_state_var interp_atom t_form).

Hypothesis Hch_f : check_form t_form.

Check rho.

Let Hwfrho : Valuation.wf rho.
  Proof.
    destruct (check_form_correct interp_atom _ Hch_f) as (_, H);exact H. 
  Qed.


Lemma lit_interp_true : Lit.interp rho Lit._true = true.
  apply Lit.interp_true.
  apply Hwfrho.
Qed.


Let rho_interp : forall x : int,
    rho x = Form.interp interp_atom t_form (t_form.[ x]).
  Proof.
    destruct (check_form_correct interp_atom _ Hch_f) as ((H,H0), _).
    intros x;apply wf_interp_form;trivial.
  Qed.

Lemma bool_impl : forall a b, (b = true -> a = true) -> a = true \/ b = false.
Proof.
intros.
destruct a.
left.
trivial.
right.
destruct b.
symmetry.
apply H.
trivial.
trivial.
Qed.

Lemma lit_interp_impl : forall a b rho,(Lit.interp rho b = true -> Lit.interp rho a = true) -> (Lit.interp rho a =true \/Lit.interp rho (Lit.neg b) = true).
Proof.
  intros.
  rewrite (Lit.interp_neg rho b).
  rewrite negb_true_iff.
  apply bool_impl.
  apply H.
Qed.


Lemma valid_check_BuildProjInt : forall lits i, C.valid rho (check_BuildProjInt lits i).
  Proof.
   unfold check_BuildProjInt,C.valid;intros lits i.
   case_eq ((length lits == digits + 1) && (i < digits)).

   intros. case_eq (t_form.[Lit.blit (lits.[0])]).
   intros. case_eq (t_atom.[i0]);intros; auto using C.interp_true.
   case_eq b;intros; auto using C.interp_true.
   case_eq (t_atom.[i1]);intros; auto using C.interp_true.
   case_eq c;intros; auto using C.interp_true.
   case_eq (t_atom.[i2]);intros; auto using C.interp_true.
   case_eq c0;intros; auto using C.interp_true.
   case_eq (t_form.[Lit.blit (lits.[i+1])]);intros;auto using C.interp_true.
   case_eq (t_form.[Lit.blit i5]);intros;auto using C.interp_true.
   case_eq (t_form.[Lit.blit i6]);intros;auto using C.interp_true.
   case_eq (t_atom.[i7]);intros;auto using C.interp_true.
   case_eq u;intros;auto using C.interp_true.
   case_eq (t_atom.[i8]);intros;auto using C.interp_true.
   case_eq u0;intros;auto using C.interp_true.
   case_eq ((Lit.is_pos i5)&&(Lit.is_pos i6)&& Typ.eqb t Typ.Tint &&(i9 == i) && (i11 == i9) && (i3 == i10) && (i4 == i12));intros;case_eq (Lit.is_pos (lits.[i+1]));intros.
   apply andb_true_iff in H14. destruct H14. apply andb_true_iff in H14. destruct H14. apply andb_true_iff in H14. destruct H14. apply andb_true_iff in H14. destruct H14. apply andb_true_iff in H14. destruct H14. apply andb_true_iff in H14. destruct H14.
   simpl. rewrite orb_false_r. apply orb_true_iff. apply lit_interp_impl.
   intro. 

   unfold Lit.interp in H22. unfold Var.interp in H22. rewrite rho_interp in H22. rewrite Lit.is_pos_lit in H22. rewrite Lit.lit_blit in H22. rewrite H0 in H22.
   unfold Lit.interp. unfold Var.interp. rewrite rho_interp. rewrite H15. rewrite H7.

   unfold Form.interp. unfold Form.interp_aux. unfold Lit.interp. unfold Var.interp. rewrite H14. rewrite H21. rewrite rho_interp. rewrite H8. rewrite rho_interp. rewrite H9. unfold Form.interp. unfold Form.interp_aux. unfold Form.interp. unfold Form.interp_aux. unfold Form.interp in H22. unfold Form.interp_aux in H22.
   SearchAbout interp_atom.
  Qed.
 

End Checker.
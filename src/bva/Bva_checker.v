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


(* Add Rec LoadPath ".." as SMTCoq. *)
Require Import Int63 PArray.
Add LoadPath "/home/burak/Desktop/ndt/smtcoq-no-dependent-types/src/bva".
Require Import Misc State SMT_terms BVList Psatz.
Require Import Bool List BoolEq NZParity Nnat.
Require Import BinPos BinNat Pnat Init.Peano.
Import ListNotations.
Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.

  Print atom.

  Variable t_atom : PArray.array atom.
  Variable t_form : PArray.array form.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).


  (* Bit-blasting a variable:

              x ∈ BV n
       ----------------------- bbVar
        bbT(x, [x₀; ...; xₙ₋₁])
   *)

  Fixpoint check_bb (a: int) (bs: list _lit) (i n: nat) :=
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

 Check check_bbVar.

  Variable s : S.t.


  (* Bit-blasting bitwise operations: bbAnd, bbOr, ...
        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a&b, [a0 /\ b0; ...; an /\ bn])
   *)

  Definition get_and (f: form) :=
    match f with
    | Fand args => if PArray.length args == 2 then Some (args.[0], args.[1]) else None
    | _ => None
    end.

  Definition get_or (f: form) :=
    match f with
    | For args => if PArray.length args == 2 then Some (args.[0], args.[1]) else None
    | _ => None
    end.

  Definition get_xor (f: form) :=
    match f with
    | Fxor arg0 arg1 => Some (arg0, arg1)
    | _ => None
    end.


(*
  Definition get_not (f: form) :=
    match f with
    | Fnot arg => Some arg
    | _ => None
    end.
*)

  (* Check the validity of a *symmetric* operator *)
  Definition check_symop (bs1 bs2 bsres : list _lit) (get_op: form -> option (_lit * _lit)) :=
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

Lemma check_symop_op_some: 
forall a0 b0 c0 la lb lc get_op,
let a := a0 :: la in
let b := b0 :: lb in
let c := c0 :: lc in
Lit.is_pos c0 -> get_op (get_form (Lit.blit c0)) = Some (a0, b0) -> 
check_symop a b c get_op = true.
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

Lemma empty_false1: forall a b c get_op, a = [] -> c <> [] -> check_symop a b c get_op = false.
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

Fixpoint check_symopp (bs1 bs2 bsres : list _lit) (bvop: binop)  :=
    match bs1, bs2, bsres with
    | nil, nil, nil => true
    | b1::bs1, b2::bs2, bres::bsres =>
      if Lit.is_pos bres then
        let (ires, bvop) := 
        match get_form (Lit.blit bres), bvop with
          | Fand args, BO_BVand n  =>
            ((if PArray.length args == 2 then
                let a1 := args.[0] in
                let a2 := args.[1] in
                ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
              else false), BO_BVand (n-1))

          (* | For args, BO_BVor n  => *)
          (*   ((if PArray.length args == 2 then *)
          (*       let a1 := args.[0] in *)
          (*       let a2 := args.[1] in *)
          (*       ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)) *)
          (*     else false), BO_BVor (n-1)) *)

          (* | Fxor a1 a2, BO_BVxor n => *)
          (*   (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)), *)
          (*    BO_BVxor (n-1)) *)

          | _, _ => (false, bvop)
        end in
        if ires then check_symopp bs1 bs2 bsres bvop
        else false
          
      else false
    | _, _, _ => false
    end.

  Lemma empty_list_length: forall {A: Type} (a: list A), (length a = 0)%nat <-> a = [].
  Proof. intros A a.
         induction a; split; intros; auto; contradict H; easy.
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
          (* | Abop (BO_BVor _) a1' a2' => *)
          (*   if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1'))) *)
          (*        && (check_symop bs1 bs2 bsres get_or) *)
          (*   then lres::nil *)
          (*   else C._true *)
          (* | Abop (BO_BVxor _) a1' a2' => *)
          (*   if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1'))) *)
          (*        && (check_symop bs1 bs2 bsres get_xor) *)
          (*   then lres::nil *)
          (*   else C._true *)
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

  (* TODO: check the first argument of BVand, BVor *)
  Definition check_bbOpp pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
          match get_atom a with
          | Abop (BO_BVand n) a1' a2' =>
            if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                 && (@check_symopp bs1 bs2 bsres (BO_BVand n))
            then lres::nil
            else C._true
          (* | Abop (BO_BVor n) a1' a2' => *)
          (*   if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1'))) *)
          (*        && (check_symopp bs1 bs2 bsres  (BO_BVor n)) *)
          (*   then lres::nil *)
          (*   else C._true *)
          (* | Abop (BO_BVxor n) a1' a2' => *)
          (*   if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1'))) *)
          (*        && (check_symopp bs1 bs2 bsres  (BO_BVxor n)) *)
          (*   then lres::nil *)
          (*   else C._true *)
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


Lemma bbOp0: forall pos1 pos2 lres, S.get s pos1 = [] ->  check_bbOp pos1 pos2 lres = [Lit._true].
Proof. intros pos1 pos2 lres H0.
       unfold check_bbOp. rewrite H0.
       reflexivity.
Qed.

Lemma bbOp1: forall pos1 pos2 lres, S.get s pos2 = [] ->  check_bbOp pos1 pos2 lres = [Lit._true].
Proof. intros pos1 pos2 lres H0.
       unfold check_bbOp.
       case_eq (S.get s pos1). reflexivity.
       intros i l H1.
       induction l. 
       - now rewrite H0.
       - reflexivity.
Qed.

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
            | Abop (BO_eq (Typ.TBV)) a1' a2' =>
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

  Definition check_bbEqq pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff leq lbb =>
          match get_form (Lit.blit leq), get_form (Lit.blit lbb) with
          | Fatom a, Fand bsres | Fand bsres, Fatom a =>
            match get_atom a with
            | Abop (BO_eq (Typ.TBV)) a1' a2' =>
              if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                   && (check_symopp bs1 bs2 (PArray.to_list bsres) (BO_eq  (Typ.TBV)))
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

     Let rho_interp : forall x : int, rho x = Form.interp interp_form_hatom interp_form_hatom_bv t_form (t_form.[ x]).
     Proof. intros x;apply wf_interp_form;trivial. Qed.

      Definition wf := PArray.forallbi lt_form t_form.

      Hypothesis wf_t_i : wf.
      Variable interp_bvatom : atom -> BITVECTOR_LIST.bitvector.
      Notation atom := int (only parsing).
(*
Lemma prop_checkbb: forall (a: int) (bs: list _lit) (i n: nat),
                    (check_bb a bs i n = true) ->
                    (length bs = (n - i))%nat /\ 
                    (forall i0, (i0 < n )%nat ->
                    Lit.interp rho (nth i0 bs false) = 
                    BITVECTOR_LIST.bitOf i0 (interp_form_hatom_bv a (N.of_nat n))).
*)


Lemma id'' a : N.of_nat (N.to_nat a) = a.
Proof.
 destruct a as [ | p]; simpl; trivial.
 destruct (Pos2Nat.is_succ p) as (n,H). rewrite H. simpl. f_equal.
 apply Pos2Nat.inj. rewrite H. apply SuccNat2Pos.id_succ.
Qed.

Lemma inj a a' : N.to_nat a = N.to_nat a' -> a = a'.
Proof.
 intro H. rewrite <- (id'' a), <- (id'' a'). now f_equal.
Qed.

Lemma inj_iff a a' : N.to_nat a = N.to_nat a' <-> a = a'.
Proof.
 split. apply inj. intros; now subst.
Qed.

Lemma id' n : N.to_nat (N.of_nat n) = n.
Proof.
 induction n; simpl; trivial. apply SuccNat2Pos.id_succ.
Qed.

Lemma nth_eq1: forall i a xs,
nth (S i) (a :: xs) 1 = nth i xs 1.
Proof. intros.
       now simpl.
Qed.

Theorem nat_case: forall (n:nat) (P:nat -> Prop), P 0%nat -> (forall m:nat, P (S m)) -> P n.
Proof. induction n; auto. Qed.

Theorem le_lt_or_eq : forall (n m: nat), (n <= m)%nat -> (n < m)%nat \/ n = m.
Proof.
induction 1; auto with arith.
Qed.

Lemma le_le_S_eq : forall (n m: nat), (n <= m)%nat -> (S n <= m)%nat \/ n = m.
Proof le_lt_or_eq.

Lemma Nat_eqb_eq: forall n m, Nat_eqb n m = true -> n = m.
Proof. induction n.
       intros n Hm. simpl in Hm. case_eq n. reflexivity.
         intros. rewrite H in Hm. now contradict H.
       intros m Hm.
       case_eq m. intros. rewrite H in Hm. simpl in Hm.
        now contradict Hm.
       intros. rewrite H in Hm. simpl in Hm.
       specialize (@IHn n0 Hm). now rewrite IHn.
Qed.

Lemma prop_checkbb: forall (a: int) (bs: list _lit) (i n: nat),
                    (length bs = (n - i))%nat ->
                    (check_bb a bs i n = true) ->
                    (forall i0, (i <= i0 < n )%nat ->
                    Lit.interp rho (nth (i0 - i) bs 1) = 
                    (@BITVECTOR_LIST.bitOf i0 (interp_form_hatom_bv a))).
Proof. intros a bs.
       revert a.
       induction bs as [ | b ys IHys].
       - intros. simpl in H. 
         cut (i = n). intro Hn. rewrite Hn in H1.
         contradict H1. omega. omega.
       - intros. simpl in H0.
         case_eq (Lit.is_pos b). intros Heq0. rewrite Heq0 in H0.
         case_eq (t_form .[ Lit.blit b] ). intros i1 Heq1. rewrite Heq1 in H0.
         case_eq (t_atom .[ i1]). intros c Heq2. 
         rewrite Heq2 in H0; now contradict H0.
         intros u i2 Heq2. 
         rewrite Heq2 in H0.
         case_eq u; try (intro Heq'; rewrite Heq' in H0; now contradict H0).
         
         intros. rewrite H2 in H0.
         case_eq ((a == i2) && Nat_eqb i n1 && Nat_eqb n (N.to_nat n0)). intros Hif.
         rewrite Hif in H0.
         do 2 rewrite andb_true_iff in Hif. destruct Hif as ((Hif0 & Hif1) & Hif2).
         specialize (@IHys a (S i) n).
         inversion H.
         cut (Datatypes.length ys = (n - S i)%nat). intro HSi.
         specialize (@IHys HSi H0).

         cut (((S i) <= i0 < n)%nat \/ i = i0).
         intro Hd. destruct Hd as [Hd | Hd].
         inversion Hd.
         induction i0 as [ | k IHk].
         now contradict H3.
         specialize (@IHys (S k)).
         cut ((S k - i)%nat = S (k - i)%nat). intro ISk.
         rewrite ISk.
         rewrite (@nth_eq1 (k - i) b ys).
         cut ((S k - S i)%nat = (k - i)%nat). intro ISki.
         specialize (@IHys Hd).
         now rewrite ISki in IHys.
         now simpl. omega.
         rewrite Hd.
         cut ((i0 - i0 = 0)%nat). intro Hi0. rewrite Hi0.
         simpl.

         unfold Lit.interp.
         rewrite Heq0.
         unfold Var.interp.
         rewrite rho_interp.
         rewrite Heq1.

         rewrite Lit.eqb_spec in Hif0.
         rewrite Hif0. rewrite <- Hd.

         generalize wt_t_atom. unfold Atom.wt. unfold is_true.
         rewrite PArray.forallbi_spec;intros.
         assert (i1 < PArray.length t_atom).
         apply PArray.get_not_default_lt.
         rewrite Heq2. now rewrite def_t_atom.
         specialize (@H3 i1 H5).
         rewrite Heq2 in H3. simpl in H3.
         rewrite H2 in H3. simpl in H3.
         rewrite !andb_true_iff in H3.
         decompose [and] H3. clear H3.
     (*    cut (n0 = (N.of_nat n)). intro Hn0n. rewrite Hn0n in H7. *)
         unfold Typ.eqb in H7.
         simpl in H7.         

         unfold get_type' in H6, H7.
         unfold v_type in H6, H7.
         case_eq (t_interp .[ i1]).
         intros. rewrite H3 in H6. simpl in H6.
         case_eq (v_type0).
         intros. rewrite H8 in H6. now contradict H6.
         intros. rewrite H8 in H6. now contradict H6.
         intros. simpl.

         unfold Atom.interp_form_hatom_bv.
         unfold Atom.interp_form_hatom.
         unfold Atom.interp_hatom.
         rewrite Atom.t_interp_wf; trivial.
         rewrite Heq2.
         simpl.

         rewrite H2. simpl.
         cut (i = n1). intro Hin1. rewrite Hin1.
         cut (n = (N.to_nat n0)). intro Hnn0.
         (* rewrite Hnn0. *)
         (* rewrite id''. *)
         case_eq (t_interp .[ i2]).
         
         intros. rewrite H9 in H7. rewrite <- H9.
         case_eq v_type1.
         intros. rewrite H10 in H7. now contradict H7.
         intros. rewrite H10 in H7. now contradict H7.
         intros. rewrite H10 in H7. now contradict H7.
         intros. rewrite H10 in H7. now contradict H7.
         intros. rewrite H10 in H7.
         (* cut (n2 = n0)%N. intros Hn2n0. rewrite Hn2n0 in H10. *)
         
         rewrite H9. simpl.
         unfold interp_bool.
         case_eq (Typ.cast v_type1 (Typ.TBV)).
         (* split *)
         split. rewrite H10.
         simpl.
         (* rewrite Typ.N_cast_refl. intros. *)
         intros.
         contradict H11. easy.
         
         (* rewrite N.eqb_compare in H7. *)
         (* case_eq (n2 ?= n0)%N. *)
         
         (* intros. now rewrite N.compare_eq_iff in H11. *)
         (* intros. rewrite H11 in H7. now contradict H7. *)
         (* intros. rewrite H11 in H7. now contradict H7.          *)

         now apply Nat_eqb_eq in Hif2.
         now apply Nat_eqb_eq in Hif1.

         intros. rewrite H8 in H6. now contradict H6.
         intros. rewrite H8 in H6. now contradict H6.

        omega. destruct H1.
        specialize (@le_le_S_eq i i0). intros H11.
        specialize (@H11 H1).
        destruct H11. left. split. exact H5. exact H3.
        right. exact H5.
        omega.
        intro H3. rewrite H3 in H0. now contradict H0.
        intros b0 i2 i3 Heq. rewrite Heq in H0. now contradict H0.
        intros n0 l Heq. rewrite Heq in H0. now contradict H0.
        intros i2 l Heq. rewrite Heq in H0. now contradict H0.
        intros Heq. rewrite Heq in H0. now contradict H0.
        intros Heq. rewrite Heq in H0. now contradict H0.
        intros i1 i2 Heq. rewrite Heq in H0. now contradict H0.
        intros a0 Heq. rewrite Heq in H0. now contradict H0.
        intros a0 Heq. rewrite Heq in H0. now contradict H0.
        intros a0 Heq. rewrite Heq in H0. now contradict H0.
        intros i1 i2 Heq. rewrite Heq in H0. now contradict H0.
        intros i1 i2 Heq. rewrite Heq in H0. now contradict H0.
        intros i1 i2 i3 Heq. rewrite Heq in H0. now contradict H0.
        intros i1 l Heq. rewrite Heq in H0. now contradict H0.
        intros Heq. rewrite Heq in H0. now contradict H0.       
Qed.

Lemma prop_checkbb': forall (a: int) (bs: list _lit),
                     (check_bb a bs 0 (length bs) = true) ->
                     (forall i0, (i0 < (length bs) )%nat ->
                     (Lit.interp rho  (nth i0 bs 1)) = 
                     (@BITVECTOR_LIST.bitOf i0 (interp_form_hatom_bv a ))).
Proof. intros.
       specialize (@prop_checkbb a bs 0 (length bs)).
       intros Hp.
       cut ((i0 - 0)%nat = i0%nat).
       intro Hc.
       cut (Datatypes.length bs = (Datatypes.length bs - 0)%nat).
       intro Hc2.
       specialize (@Hp Hc2 H i0).
       cut ( (0 <= i0 < Datatypes.length bs)%nat). intro Hc3.
       specialize (@Hp Hc3).
       now rewrite Hc in Hp.
       omega. omega. omega.
Qed.

(*
  Lemma of_bits_bitOf: forall i l, (@BITVECTOR_LIST.bitOf (N.of_nat (length l)) i 
                                                          (BITVECTOR_LIST.of_bits l))
                                                           = nth i l (Lit.interp rho false).
*)


Lemma nth_eq0: forall i a b xs ys,
nth (S i) (a :: xs) false = nth (S i) (b :: ys) false -> nth i xs false = nth i ys false.
Proof. intros.
       now simpl in H.
Qed.   

Lemma nth_eq: forall (a b: list bool), (length a) = (length b) -> 
 (forall (i: nat), 
 (i < length a)%nat ->
 nth i a false = nth i b false) -> a = b.
Proof. intros a.
       induction a as [ | a xs IHxs].
       - intros. simpl in *. symmetry in H.
         now rewrite empty_list_length in H.
       - intros [ | b ys] H0.
         + simpl in *. now contradict H0.
         + specialize (@IHxs ys).
           inversion H0. specialize (@IHxs H1).
           intros.         
           pose proof (@H 0%nat). simpl in H2.
           cut ((0 < S (Datatypes.length xs))%nat). intro HS.
           specialize (@H2 HS). rewrite H2; apply f_equal.
           apply IHxs. intros. apply (@nth_eq0 i a b xs ys).
           apply H. simpl. omega. omega.
Qed.

Lemma is_even_0: is_even 0 = true.
Proof. apply refl_equal. Qed.

Lemma rho_1: Lit.interp rho 1 = false.
Proof. unfold Lit.interp.
       unfold Lit.is_pos.
       simpl.
       cut (is_even 1 = false). intro Hev. rewrite Hev.
       unfold Var.interp.
       destruct wf_rho. unfold Lit.blit.
       cut (1 >> 1 = 0). intros Heq0. rewrite Heq0. 
       unfold negb. now rewrite H.
       easy. easy.
Qed.

Lemma rho_false: Lit.interp rho false = true.
Proof. unfold Lit.interp.
       unfold Lit.is_pos.
       simpl.
       cut (is_even 0 = true). intro Hev. rewrite Hev.
       unfold Var.interp.
       destruct wf_rho. simpl. unfold Lit.blit.
       cut (0 >> 1 = 0). intros Heq0. rewrite Heq0. exact H.
       now rewrite lsr_0_l.
       apply is_even_0.
Qed.

Lemma bitOf_of_bits: forall l (a: BITVECTOR_LIST.bitvector),
                       N.of_nat (length l) = BITVECTOR_LIST.size a ->
                               (forall i, 
                               (i < (length l))%nat ->
                               nth i l false = 
                               (@BITVECTOR_LIST.bitOf i a))
                               ->
                               (BITVECTOR_LIST.bv_eq a (BITVECTOR_LIST.of_bits l)).
Proof. intros l a samelen H.
       unfold BITVECTOR_LIST.of_bits in *.
       unfold BITVECTOR_LIST.bitOf in *.
       unfold BITVECTOR_LIST.bv_eq, BITVECTOR_LIST.bv in *.
       unfold RAWBITVECTOR_LIST.bitOf in *.
       destruct a.
(*
       cut (Lit.interp rho false = true). intro HiR.
         rewrite HiR in H. 
*)
       unfold RAWBITVECTOR_LIST.of_bits.
       unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *.
       rewrite wf0.       
       rewrite N.eqb_compare.
       (* rewrite N.compare_refl. *)
       unfold BITVECTOR_LIST.size, RAWBITVECTOR_LIST.size in samelen.
       simpl in samelen.
       apply Nat2N.inj in samelen.
       
       apply (@nth_eq l bv samelen) in H.
       
       rewrite H.
       unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *.
       rewrite RAWBITVECTOR_LIST.List_eq_refl; auto.
       apply inj_iff in wf0.
       apply N2Nat.inj in wf0.
       rewrite wf0.
       now rewrite N.compare_refl.

Qed.


(* TODO: change *)
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
      rewrite wf_interp_form; trivial. rewrite Heq0. simpl.
      apply bitOf_of_bits.    

      admit. (*****)

(*
      unfold BITVECTOR_LIST.size, RAWBITVECTOR_LIST.size.
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite Htia1.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1. easy.
*)

      intros. 
      cut (Lit.interp rho 1 = false). intro Hr. rewrite <- Hr. 
      rewrite map_nth.
      remember (@prop_checkbb' a bs Heq2 i).
      rewrite map_length in H.
      clear Heqe.
      now apply e in H.
      now apply rho_1.
Qed.

Lemma eq_head: forall {A: Type} a b (l: list A), (a :: l) = (b :: l) <-> a = b.
Proof. intros A a b l; split; [intros H; inversion H|intros ->]; auto. Qed.

Axiom afold_left_and : forall a, 
      afold_left bool int true andb (Lit.interp rho) a = List.forallb (Lit.interp rho) (to_list a).

Lemma eqb_spec : forall x y, (x == y) = true <-> x = y.
Proof.
 split;auto using eqb_correct, eqb_complete.
Qed.

Lemma to_list_two: forall {A:Type} (a: PArray.array A), 
       PArray.length a = 2 -> (to_list a) = a .[0] :: a .[1] :: nil.
Proof. intros A a H.
       rewrite to_list_to_list_ntr. unfold to_list_ntr.
       rewrite H.
       cut (0 == 2 = false). intro H1.
       rewrite H1.
       unfold foldi_ntr. rewrite foldi_cont_lt; auto.
       auto.
Qed.

Lemma check_symopp_and: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres n,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_BVand (N.of_nat n)) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_BVand (N.of_nat (n - 1))) = true.
Proof. intros.
       induction n. simpl.
       simpl in H. 
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case (PArray.length a == 2) in H.
       case ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)
         || (a .[ 0] == ibs2) && (a .[ 1] == ibs1)) in H.
       exact H.
       now contradict H.
       now contradict H.
       now contradict H.
       simpl in H.
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case (PArray.length a == 2) in H.       
       admit. (*****)
       now contradict H.
       now contradict H.
Admitted.


Lemma check_symopp_bvand2: forall bs1 bs2 bsres,
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_symopp bs1 bs2 bsres (BO_BVand (N.of_nat n)) = true ->
  (forall i0, (i0 < n)%nat ->
         Lit.interp rho (nth i0 bsres 1) =
         andb (Lit.interp rho (nth i0 bs1 1)) (Lit.interp rho (nth i0 bs2 1))
  ).
Admitted. 

Lemma check_symopp_bvand: forall bs1 bs2 bsres, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_symopp bs1 bs2 bsres (BO_BVand (N.of_nat n)) = true ->
  (List.map (Lit.interp rho) bsres) = 
  (RAWBITVECTOR_LIST.map2 andb (List.map (Lit.interp rho) bs1) (List.map (Lit.interp rho) bs2)).
Proof. intro bs1.
         induction bs1 as [ | ibs1 xbs1 IHbs1].
         - intros. simpl in *. rewrite <- H0 in H.
           rewrite <- H in H0. unfold n in H0.
           symmetry in H0.
           rewrite empty_list_length in H0.
           unfold map. now rewrite H0.
         - intros [ | ibs2 ybs2].
           + intros.
             simpl in *. now contradict H1.
           + intros [ | ibsres zbsres ].
             * intros. simpl in *. now contradict H.
             * intros. simpl.
               specialize (IHbs1 ybs2 zbsres). 
               rewrite IHbs1. rewrite eq_head.
               unfold Lit.interp, Var.interp.
               case_eq (Lit.is_pos ibsres); intro Heq0.
               case_eq (Lit.is_pos ibs1); intro Heq1.
               case_eq (Lit.is_pos ibs2); intro Heq2.
               rewrite wf_interp_form; trivial.
               simpl in H1.
               rewrite Heq0 in H1.
               case_eq (t_form .[ Lit.blit ibsres]).
               try (intros i Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               intros. rewrite H2 in H1. simpl.
               rewrite afold_left_and.
 
                case_eq (PArray.length a == 2). intros. rewrite H3 in H1.
                rewrite eqb_spec in H3.
                apply to_list_two in H3.
             (*   apply length_to_list in H4. *)
                unfold forallb.
                rewrite H3.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite andb_true_r.
                intros. rewrite H4 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)).
                intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6.
                rewrite H5, H6. rewrite andb_true_r.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite andb_comm.
                intros. rewrite H5 in H1. now contradict H1.
                intros. rewrite H3 in H1. now contradict H1.
              
              try (intros a Heq; rewrite Heq in H1; now contradict H1).
              try (intros a Heq; rewrite Heq in H1; now contradict H1).
              try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
              try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
              try (intros i i0 i1 Heq; rewrite Heq in H1; now contradict H1).
              try (intros i l Heq; rewrite Heq in H1; now contradict H1).

              rewrite wf_interp_form; trivial. simpl in H1.
              case_eq (t_form .[ Lit.blit ibsres]).
              rewrite Heq0 in H1.
              case_eq (t_form .[ Lit.blit ibsres]).
               try (intros i Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               rewrite Heq0 in H1.
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               intros. rewrite H2 in H1. simpl.
               rewrite afold_left_and.

                case_eq (PArray.length a == 2). intros. rewrite H3 in H1.
                rewrite eqb_spec in H3.
                apply to_list_two in H3.
             (*   apply length_to_list in H3. *)
                unfold forallb.
                rewrite H3.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite andb_true_r.
                intros H4. rewrite H4 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7. rewrite andb_true_r.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite andb_comm.
                intros. rewrite H5 in H1. now contradict H1.
                intros. rewrite H3 in H1. now contradict H1.

               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 i1 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i l Heq; rewrite Heq in H1; now contradict H1).

               case_eq (Lit.is_pos ibs2).
               intro Heq2.

              rewrite wf_interp_form; trivial. simpl in H1.
              case_eq (t_form .[ Lit.blit ibsres]).
              rewrite Heq0 in H1.
              case_eq (t_form .[ Lit.blit ibsres]).
               try (intros i Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               rewrite Heq0 in H1.
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               intros. rewrite H2 in H1. simpl.
               rewrite afold_left_and.
                
                case_eq (PArray.length a == 2). intros. rewrite H3 in H1.
                rewrite eqb_spec in H3.
                apply to_list_two in H3.
             (*   apply length_to_list in H3. *)
                unfold forallb.
                rewrite H3.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite andb_true_r.
                intros. rewrite H4 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7. rewrite andb_true_r.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite andb_comm.
                intros. rewrite H5 in H1. now contradict H1.
                intros. rewrite H3 in H1. now contradict H1.
              
              rewrite Heq0 in H1.
              try (intros a Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros a Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i i0 i1 Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i l Heq; rewrite Heq in H1; now contradict H1).
              
              intros.

              rewrite wf_interp_form; trivial. simpl in H1.
              case_eq (t_form .[ Lit.blit ibsres]).
              rewrite Heq0 in H1.
              case_eq (t_form .[ Lit.blit ibsres]).
               try (intros i Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               intros. contradict H3. discriminate.
               rewrite Heq0 in H1.
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               intros. rewrite H3 in H1. simpl.
               rewrite afold_left_and.

               case_eq (PArray.length a == 2). intros H5.
                rewrite H5 in H1.
                rewrite eqb_spec in H5.
                apply to_list_two in H5.
             (*   apply length_to_list in H3. *)
                unfold forallb.
                rewrite H5.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H6.
                rewrite andb_true_iff in H6. destruct H6 as (H6 & H7).
                rewrite eqb_spec in H6, H7. rewrite H6, H7.
                unfold Lit.interp.
                rewrite Heq1, H2.
                unfold Var.interp. now rewrite andb_true_r.
                intros H6. rewrite H6 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)). intros H7.
                rewrite andb_true_iff in H7. destruct H7 as (H7 & H8).
                rewrite eqb_spec in H7, H8.
                rewrite H7, H8. rewrite andb_true_r.
                unfold Lit.interp.
                rewrite Heq1, H2.
                unfold Var.interp. now rewrite andb_comm.
                intros. rewrite H4 in H1. now contradict H1.
                intros. rewrite H4 in H1. now contradict H1.
            

              rewrite Heq0 in H1.
              try (intros a Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros a Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i i0 i1 Heq; rewrite Heq in H1; now contradict H1).
              rewrite Heq0 in H1.
              try (intros i l Heq; rewrite Heq in H1; now contradict H1).

              rewrite wf_interp_form; trivial. simpl in H1.
              rewrite Heq0 in H1. now contradict H1.
              now inversion H.
              now inversion H0.
              remember (@check_symopp_and ibs1 ibs2 xbs1 ybs2 ibsres zbsres).
              cut ((length zbsres = (n - 1))%nat). intros. rewrite H2.
              apply (@check_symopp_and ibs1 ibs2 xbs1 ybs2 ibsres zbsres).
              exact H1.
              unfold n. simpl. omega.
Qed.


Lemma check_symopp_bvand_length: forall bs1 bs2 bsres,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVand (N.of_nat n)) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 H.
  induction bsres as [ | r rbsres ].
  intros.
  simpl in H.
  case bs1 in *. simpl in H.
  case bs2 in *. simpl in *. easy. easy.
  case bs2 in *. simpl in *. easy.
  simpl in *. easy.
  intros.
  case bs1 in *.
  case bs2 in *.
  simpl in *. easy.
  simpl in *. easy.
  case bs2 in *. simpl in *. easy.
  set (n' := length rbsres).
  fold n' in n, IHrbsres, H.
  simpl in IHrbsres.
  assert (n = n' + 1)%nat.
  simpl in n.
  fold n' in n.
  unfold n.
  clear H. clear IHrbsres.
  induction n'.
  auto.
  simpl in IHn'.
  (* rewrite IHn'. *)
  assert ((S n' + 1 = 1 + S n')%nat).
  omega.
  omega.
  assert (n' = n - 1)%nat.
  omega.
  rewrite H0 in H.
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (PArray.length a == 2) in H; try easy.
  case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in H; try easy.
  assert ((n' + 1) - 1 = n')%nat.
  omega.
  assert (N.of_nat (n' + 1) - 1 = N.of_nat n')%N.
  Nat2N.nat2N.
  rewrite H3 in H.
  specialize (IHrbsres bs1 bs2 H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.


Lemma check_symopp_bvand_nl: forall bs1 bs2 bsres, 
  check_symopp bs1 bs2 bsres (BO_BVand (N.of_nat (length bsres))) = true ->
  (List.map (Lit.interp rho) bsres) = 
  (RAWBITVECTOR_LIST.map2 andb (List.map (Lit.interp rho) bs1)
                          (List.map (Lit.interp rho) bs2)).
Proof.
  intros.
  pose proof H.
  apply check_symopp_bvand_length in H.
  destruct H.
  apply check_symopp_bvand in H0. easy. easy. easy.
Qed.  

Lemma eq_rec: forall a b, BITVECTOR_LIST.bv a = BITVECTOR_LIST.bv b /\ 
                          BITVECTOR_LIST.n a = BITVECTOR_LIST.n b ->
                          a = b.
Proof. intros. destruct a, b. 
       unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n in H.
       destruct H.
       revert wf0.
       rewrite H0, H. intros.
       now rewrite (proof_irrelevance wf0 wf1).
Qed.


Lemma valid_check_bbOpp pos1 pos2 lres: C.valid rho (check_bbOpp pos1 pos2 lres).
Proof.
      unfold check_bbOpp.
      case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | |A|N] a1' a2' Heq9; try now apply C.interp_true.
      (* BVand *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (check_symopp bs1 bs2 bsres (BO_BVand N)); simpl; intros Heq11; try (now apply C.interp_true).
        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
      
        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Atom.interp_form_hatom_bv at 2, Atom.interp_hatom.

  (***)

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). assert (a < PArray.length t_atom).
        apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy.
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in  H0.

        generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.
       
       apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.
        destruct HSp1, HSp2.


        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H8. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval. rewrite Typ.cast_refl.
        

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia1.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1. easy.
        rewrite H9 in H5. rewrite Htia1 in H5.
        unfold interp_bv in H5. rewrite Typ.cast_refl in H5.
        rewrite H5.
        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia2.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia2. easy.

        rewrite H10 in H7. rewrite Htia2 in H7.
        unfold interp_bv in H7. rewrite Typ.cast_refl in H7.
        rewrite H7.
        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres).
        unfold BITVECTOR_LIST.bv_and, RAWBITVECTOR_LIST.bv_and.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.
     

        (****)
         cut ((Datatypes.length (map (Lit.interp rho) bs2)) =
                        (Datatypes.length (map (Lit.interp rho) bs1))).
        intros HC2.

        split.
        
        unfold BITVECTOR_LIST.size, RAWBITVECTOR_LIST.size.
        unfold BITVECTOR_LIST.bv.
        apply f_equal.
        rewrite HC2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        rewrite map_length.

        specialize (@check_symopp_bvand_nl bs1 bs2 bsres).
        intros Hcso.
        rewrite <- Hcso.
        now rewrite map_length.
        
        (**)
        admit.
       
        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.
        rewrite HC2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_and.
        unfold RAWBITVECTOR_LIST.size.
        rewrite HC2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal. 
        now apply RAWBITVECTOR_LIST.map2_and_length.
        
        admit.
        admit.


(**** symmetric case *****)


(** other cases, BVor and BVxor, would be the pretty similar with BVand **)
Admitted.


Lemma valid_check_bbEq pos1 pos2 lres : C.valid rho (check_bbEqq pos1 pos2 lres).
Proof. 
       unfold check_bbEqq.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_form .[ Lit.blit bsres]); try (intros; now apply C.interp_true). intros a4 Heq11.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true). intros b i i0 Heq12.
       case_eq b; try (intros; now apply C.interp_true). intros t Heq13.
       case_eq t; try (intros; now apply C.interp_true). intros Heq14.

       case_eq ((a1 == i) && (a2 == i0) || (a1 == i0) && (a2 == i)); simpl; intros Heq15; try (now apply C.interp_true).
       case_eq (check_symopp bs1 bs2 (to_list a4) (BO_eq (Typ.TBV))); simpl; intros Heq16; try (now apply C.interp_true).
       unfold C.valid. simpl. rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3). rewrite Heq13 in Heq12.
       assert (a3 < PArray.length t_atom).
       apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq12. easy.
       specialize (@H0 H1). rewrite Heq12 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.
       case_eq (v_typea3).
         intros i1 Hv. rewrite Hv in H0. now contradict H0.
         intros Hv. rewrite Hv in H0. now contradict H0.
         intros Hv.

       generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
       unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
       unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
       rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

       generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
       unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
       unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
       rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.
       rewrite Heq14 in H3, H2.

       unfold get_type' in H2, H3. unfold v_type in H2, H3.
       case_eq (t_interp .[ i]).
         intros v_typei v_vali Htii. rewrite Htii in H3.
       case_eq (t_interp .[ i0]).
         intros v_typei0 v_vali0 Htii0. rewrite Htii0 in H2.
       simpl in v_vali, v_vali0.
        
       admit. (*****)

       intros Hv. rewrite Hv in H0. now contradict H0.
       intros Hv. rewrite Hv in H0. now contradict H0.

       intros a3 Heq10.
       case_eq (t_form .[ Lit.blit bsres]); try (intros; now apply C.interp_true). intros a4 Heq11.
       case_eq (t_atom .[ a4]); try (intros; now apply C.interp_true). intros b i i0 Heq12.
       case_eq b; try (intros; now apply C.interp_true). intros t Heq13.
       case_eq t; try (intros; now apply C.interp_true). intros Heq14.
       admit. (*****)
Admitted.

  End Proof.

End Checker.

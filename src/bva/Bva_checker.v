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

Add LoadPath "/home/burak/Desktop/non-dep/src/bva".
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

  (** * Checker for bitblasting of bitvector variables *)
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

          | For args, BO_BVor n  =>
            ((if PArray.length args == 2 then
                let a1 := args.[0] in
                let a2 := args.[1] in
                ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
              else false), BO_BVor (n-1))

          | Fxor a1 a2, BO_BVxor n =>
             (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)),
             BO_BVxor (n-1))

          | Fiff a1 a2, (BO_eq (Typ.TBV))  =>
             (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)),
             BO_eq (Typ.TBV))

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

  (** * Checker for bitblasting of bitwise operators on bitvectors *)
  Definition check_bbOp pos1 pos2 lres :=
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

          | Abop (BO_BVor n) a1' a2' =>
             if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                  && (check_symopp bs1 bs2 bsres  (BO_BVor n))
             then lres::nil
             else C._true

          | Abop (BO_BVxor n) a1' a2' =>
             if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                  && (check_symopp bs1 bs2 bsres  (BO_BVxor n))
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

  (** * Checker for bitblasting of equality between bitvector terms  *)
  Definition check_bbEq pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff leq lbb =>
          if (Bool.eqb (Lit.is_pos leq) (Lit.is_pos lbb)) then
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
          else C._true
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.


  (** Representaion for symbolic carry computations *)
  Inductive carry : Type :=
  | Clit (_:_lit)
  | Cand (_:carry) (_:carry)
  | Cor (_:carry) (_:carry)
  | Cxor (_:carry) (_:carry)
  .

  
  (** Check if a symbolic carry computation is equal to a literal
     representation. This function does not account for potential symmetries *)
  (* c should always be a positive literal in carry computations *)
  Fixpoint eq_carry_lit (carry : carry) (c : _lit) :=
    if Lit.is_pos c then
      match carry with
        | Clit l => l == c
        | Cxor c1 c2  =>
          match get_form (Lit.blit c) with
            | Fxor a1 a2 => eq_carry_lit c1 a1 && eq_carry_lit c2 a2
            | _ => false
          end
        | Cand c1 c2  =>
          match get_form (Lit.blit c) with
          | Fand args =>
            if PArray.length args == 2 then
              eq_carry_lit c1 (args.[0]) && eq_carry_lit c2 (args.[1])
            else false
          | _ => false
          end
        | Cor c1 c2  =>
          match get_form (Lit.blit c) with
          | For args =>
            if PArray.length args == 2 then
              eq_carry_lit c1 (args.[0]) && eq_carry_lit c2 (args.[1])
            else false
          | _ => false
          end
      end
    else
      (* c can be negative only when it is literal false *)
      match carry with
        | Clit l => l == c
        | _ => false
      end.

  
  (** Checks if [bsres] is the result of bvand of bs1 and bs2. The inital
      value for the carry is [false]. *)
  Fixpoint check_add (bs1 bs2 bsres : list _lit) (carry : carry) :=
    match bs1, bs2, bsres with
      | nil, nil, nil => true
      | b1::bs1, b2::bs2, bres::bsres =>
        if Lit.is_pos bres then
          match get_form (Lit.blit bres) with
            | Fxor xab c  =>
             if Lit.is_pos xab then
              match get_form (Lit.blit xab) with
                | Fxor a1 a2  =>
                  (* This is the way LFSC computes carries *)
                  let carry' := Cor (Cand (Clit b1) (Clit b2))
                                   (Cand (Cxor (Clit b1) (Clit b2)) carry) in
                  (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)))
                    && eq_carry_lit carry c
                    && check_add bs1 bs2 bsres carry'
                | _ => false
              end
            else false
            | _ => false
          end
        else false
      | _, _, _ => false
    end.
  

  (** * Checker for bitblasting of bitvector addition *)
  Definition check_bbAdd pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVadd _) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                       && (check_add bs1 bs2 bsres (Clit Lit._false))
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.



  Fixpoint and_with_bit (a: list _lit) (bt: _lit) : list carry :=
    match a with
      | nil => nil
      | ai :: a' => (Cand (Clit bt) (Clit ai)) :: and_with_bit a' bt 
    end.
  

  Fixpoint mult_step_k_h (a b res: list carry) (c: carry) (k: int) : list carry :=
    match a, b with
      | nil, nil => res
      | ai :: a', bi :: b' =>
        if k - 1 < 0 then
          let carry_out := Cor (Cand ai bi) (Cand (Cxor ai bi) c) in
          let curr := Cxor (Cxor ai bi) c in
          mult_step_k_h a' b' (curr :: res) carry_out (k - 1)
        else
          mult_step_k_h a' b (ai :: res) c (k - 1)
      | _, _ => nil
    end.


  Fixpoint top_k_bits (a: list _lit) (k: int) : list _lit :=
    if k == 0 then nil
    else match a with
           | nil => nil
           | ai :: a' => ai :: top_k_bits a' (k - 1)
         end.


  Fixpoint mult_step (a b: list _lit) (res: list carry) (k k': nat) : list carry :=
    let ak := List.firstn k' a in
    let b' := and_with_bit ak (nth k b Lit._false) in
    let res' := mult_step_k_h res b' nil (Clit Lit._false) (of_Z (Z.of_nat k)) in
    match k' with
      | O => res'
      | S pk' => mult_step a b res' (k + 1) pk'
    end.

  
  Definition bblast_bvmult (a b: list _lit) (n: nat) : list carry :=
    let res := and_with_bit a (nth 0 b Lit._false) in
    match n with
      | O => res
      | S k => mult_step a b res 1 k
    end.


  Definition check_mult (bs1 bs2 bsres: list _lit) : bool :=
    let bvm12 := bblast_bvmult bs1 bs2 (length bsres) in
    forallb2 eq_carry_lit bvm12 bsres.
    
  (** * Checker for bitblasting of bitvector multiplication *)
  Definition check_bbMult pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVmult _) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                       && (check_mult bs1 bs2 bsres)
                  then lres::nil
                  else C._true

                | _ => C._true
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


  Fixpoint interp_carry (c: carry) : bool :=
    match c with
      | Clit l => (Lit.interp rho l)
      | Cand c1 c2 => (interp_carry c1) && (interp_carry c2)
      | Cor c1 c2 => (interp_carry  c1) || (interp_carry c2)
      | Cxor c1 c2 => xorb (interp_carry c1) (interp_carry c2)
    end.

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
Lemma prop_checkbb_len: forall (a: int) (bs: list _lit), 
                               (check_bb a bs 0 (length bs) = true) ->
                               BITVECTOR_LIST.size (interp_form_hatom_bv a ) = N.of_nat (length bs).
Proof. 

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
       destruct a.
       unfold BITVECTOR_LIST.of_bits in *.
       unfold BITVECTOR_LIST.bitOf in *.
       unfold BITVECTOR_LIST.bv_eq, BITVECTOR_LIST.bv in *.
       unfold RAWBITVECTOR_LIST.bitOf in *.
       unfold RAWBITVECTOR_LIST.of_bits.
       unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *.
       unfold BITVECTOR_LIST.size in *.
       simpl in samelen.
       apply Nat2N.inj in samelen.
       apply (@nth_eq l bv samelen) in H.
       rewrite H.
       now rewrite RAWBITVECTOR_LIST.List_eq_refl.
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
         
      admit (*****).

      intros. 
      cut (Lit.interp rho 1 = false). intro Hr. rewrite <- Hr. 
      rewrite map_nth.
      remember (@prop_checkbb' a bs Heq2 i).
      rewrite map_length in H.
      clear Heqe.
      now apply e in H.
      now apply rho_1.
Admitted.

Lemma eq_head: forall {A: Type} a b (l: list A), (a :: l) = (b :: l) <-> a = b.
Proof. intros A a b l; split; [intros H; inversion H|intros ->]; auto. Qed.

Axiom afold_left_and : forall a, 
      afold_left bool int true andb (Lit.interp rho) a = List.forallb (Lit.interp rho) (to_list a).

  Axiom afold_left_or : forall a,
    afold_left bool int false orb (Lit.interp rho) a =
    C.interp rho (to_list a).

  Axiom afold_left_xor : forall a,
    afold_left bool int false xorb (Lit.interp rho) a =
    C.interp rho (to_list a).


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

Lemma check_symopp_and: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres N,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_BVand N) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_BVand (N-1)) = true.
Proof. intros.
       induction N. simpl.
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
       unfold check_symopp in H.
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case (PArray.length a == 2) in H.
       case ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)
        || (a .[ 0] == ibs2) && (a .[ 1] == ibs1)) in H.
       apply H.
       now contradict H.
       now contradict H.
       now contradict H.
Qed.

Lemma check_symopp_or: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres N,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_BVor N) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_BVor (N-1)) = true.
Proof. intros.
       induction N. simpl.
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
       unfold check_symopp in H.
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case (PArray.length a == 2) in H.
       case ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)
        || (a .[ 0] == ibs2) && (a .[ 1] == ibs1)) in H.
       apply H.
       now contradict H.
       now contradict H.
       now contradict H.
Qed.

Lemma check_symopp_xor: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres N,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_BVxor N) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_BVxor (N-1)) = true.
Proof. intros.
       induction N. simpl.
       simpl in H. 
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case ((i == ibs1) && (i0 == ibs2) || (i == ibs2) && (i0 == ibs1)) in H.
       exact H.
       now contradict H.
       now contradict H.
       unfold check_symopp in H.
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case ((i == ibs1) && (i0 == ibs2) || (i == ibs2) && (i0 == ibs1)) in H.
       apply H.
       now contradict H.
       now contradict H.
Qed.


Lemma check_symopp_bvand: forall bs1 bs2 bsres N, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_symopp bs1 bs2 bsres (BO_BVand N) = true ->
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
               specialize (IHbs1 ybs2 zbsres (N-1)%N). 
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
              apply (@check_symopp_and ibs1 ibs2 xbs1 ybs2 ibsres zbsres N).
              exact H1.
Qed.
  
Lemma check_symopp_bvor: forall bs1 bs2 bsres N, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_symopp bs1 bs2 bsres (BO_BVor N) = true ->
  (List.map (Lit.interp rho) bsres) = 
  (RAWBITVECTOR_LIST.map2 orb (List.map (Lit.interp rho) bs1) (List.map (Lit.interp rho) bs2)).
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
               specialize (IHbs1 ybs2 zbsres (N-1)%N). 
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
               try (intros a Heq; rewrite Heq in H1; now contradict H1).

               intros. rewrite H2 in H1. simpl.
               rewrite afold_left_or.
 
                case_eq (PArray.length a == 2). intros. rewrite H3 in H1.
                rewrite eqb_spec in H3.
                apply to_list_two in H3.
             (*   apply length_to_list in H4. *)
                unfold forallb.
                rewrite H3.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold C.interp. unfold existsb. rewrite orb_false_r.
                
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                now unfold Var.interp.

                intros. rewrite H4 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)).
                intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6.
                rewrite H5, H6. rewrite orb_false_r.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite orb_comm.
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
               rewrite afold_left_or.

                case_eq (PArray.length a == 2). intros. rewrite H3 in H1.
                rewrite eqb_spec in H3.
                apply to_list_two in H3.
                unfold C.interp.
             (*   apply length_to_list in H3. *)
                unfold existsb.
                
                rewrite H3.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite orb_false_r.
                intros H4. rewrite H4 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7. rewrite orb_false_r.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite orb_comm.
                intros. rewrite H5, Heq0 in H1. now contradict H1.
                intros. rewrite H3, Heq0 in H1. now contradict H1.

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
               rewrite afold_left_or.
                
                case_eq (PArray.length a == 2). intros. rewrite H3 in H1.
                rewrite eqb_spec in H3.
                apply to_list_two in H3.
             (*   apply length_to_list in H3. *)
                unfold forallb.
                rewrite H3.
                case_eq ((a .[ 0] == ibs1) && (a .[ 1] == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold C.interp, existsb.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite orb_false_r.
                intros. rewrite H4 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7. rewrite orb_false_r.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite orb_comm.
                intros. rewrite Heq0, H5 in H1. now contradict H1.
                intros. rewrite Heq0, H3 in H1. now contradict H1.
              
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
               rewrite afold_left_or.

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
                unfold C.interp, Lit.interp, existsb.
                rewrite Heq1, H2.
                unfold Var.interp. now rewrite orb_false_r.
                intros H6. rewrite H6 in H1. simpl in *.
                case_eq ((a .[ 0] == ibs2) && (a .[ 1] == ibs1)). intros H7.
                rewrite andb_true_iff in H7. destruct H7 as (H7 & H8).
                rewrite eqb_spec in H7, H8.
                rewrite H7, H8. rewrite orb_false_r.
                unfold Lit.interp.
                rewrite Heq1, H2.
                unfold Var.interp. now rewrite orb_comm.
                intros. rewrite Heq0, H4 in H1. now contradict H1.
                intros. rewrite Heq0, H4 in H1. now contradict H1.
            

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
              apply (@check_symopp_or ibs1 ibs2 xbs1 ybs2 ibsres zbsres N).
              exact H1.
Qed.


Lemma check_symopp_bvxor: forall bs1 bs2 bsres N, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_symopp bs1 bs2 bsres (BO_BVxor N) = true ->
  (List.map (Lit.interp rho) bsres) = 
  (RAWBITVECTOR_LIST.map2 xorb (List.map (Lit.interp rho) bs1) (List.map (Lit.interp rho) bs2)).
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
               specialize (IHbs1 ybs2 zbsres (N-1)%N). 
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
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               intros. rewrite H2 in H1. simpl.
                case_eq ((i == ibs1) && (i0 == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                now unfold Var.interp.

                intros H4. rewrite H4 in H1. simpl in *.
                case_eq ((i == ibs2) && (i0 == ibs1)).
                intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6.
                rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite xorb_comm.
                intros. rewrite H3 in H1. now contradict H1.

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
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
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
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               
               intros. rewrite H2 in H1. simpl.
                case_eq ((i == ibs1) && (i0 == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                now unfold Var.interp.
                intros H4. rewrite Heq0, H4 in H1. simpl in *.
                case_eq ((i == ibs2) && (i0 == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite xorb_comm.
                intros. rewrite H3 in H1. now contradict H1.

               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
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
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
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
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).


               intros. rewrite H2 in H1. simpl.

                case_eq ((i == ibs1) && (i0 == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                now unfold Var.interp.
                intros H4. rewrite Heq0, H4 in H1. simpl in *.
                case_eq ((i == ibs2) && (i0 == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite xorb_comm.
                intros. rewrite H3 in H1. now contradict H1.

               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               try (intros i i0 i1 Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros i l Heq; rewrite Heq in H1; now contradict H1).

               intro Heq2.
               rewrite wf_interp_form; trivial. simpl in H1.
               case_eq (t_form .[ Lit.blit ibsres]).
               rewrite Heq0 in H1.
               case_eq (t_form .[ Lit.blit ibsres]).
               try (intros i Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros Heq; rewrite Heq in H1; now contradict H1).
               try (intros i i0 Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
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
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).
               rewrite Heq0 in H1.
               try (intros a Heq; rewrite Heq in H1; now contradict H1).


               intros. rewrite H2 in H1. simpl.
                case_eq ((i == ibs1) && (i0 == ibs2)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H5 & H6).
                rewrite eqb_spec in H5, H6. rewrite H5, H6.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                now unfold Var.interp.
                intros H4. rewrite Heq0, H4 in H1. simpl in *.
                case_eq ((i == ibs2) && (i0 == ibs1)). intros H5.
                rewrite andb_true_iff in H5. destruct H5 as (H6 & H7).
                rewrite eqb_spec in H6, H7.
                rewrite H6, H7.
                unfold Lit.interp.
                rewrite Heq1, Heq2.
                unfold Var.interp. now rewrite xorb_comm.
                intros. rewrite H3 in H1. now contradict H1.
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
              apply (@check_symopp_xor ibs1 ibs2 xbs1 ybs2 ibsres zbsres N).
              exact H1.
Qed.


Lemma check_symopp_bvand_length: forall bs1 bs2 bsres N,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVand N) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 N H.
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
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (PArray.length a == 2) in H; try easy.
  case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in H; try easy.
  specialize (IHrbsres bs1 bs2 (N - 1)%N H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.

Lemma check_symopp_bvor_length: forall bs1 bs2 bsres N,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVor N) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 N H.
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
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (PArray.length a == 2) in H; try easy.
  case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in H; try easy.
  specialize (IHrbsres bs1 bs2 (N - 1)%N H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.

Lemma check_symopp_bvxor_length: forall bs1 bs2 bsres N,
  let n := length bsres in
  check_symopp bs1 bs2 bsres (BO_BVxor N) = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 N H.
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
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case ((i1 == i) && (i2 == i0) || (i1 == i0) && (i2 == i)) in H; try easy.
  specialize (IHrbsres bs1 bs2 (N - 1)%N H).
  simpl.
  simpl in n.
  fold n' in n.
  unfold n.
  split; apply f_equal. easy. easy.
  easy.
Qed.


Lemma check_symopp_bvand_nl: forall bs1 bs2 bsres N, 
  check_symopp bs1 bs2 bsres (BO_BVand N) = true ->
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

Lemma check_symopp_bvor_nl: forall bs1 bs2 bsres N, 
  check_symopp bs1 bs2 bsres (BO_BVor N) = true ->
  (List.map (Lit.interp rho) bsres) = 
  (RAWBITVECTOR_LIST.map2 orb (List.map (Lit.interp rho) bs1)
                          (List.map (Lit.interp rho) bs2)).
Proof.
  intros.
  pose proof H.
  apply check_symopp_bvor_length in H.
  destruct H.
  apply check_symopp_bvor in H0. easy. easy. easy.
Qed.


Lemma check_symopp_bvxor_nl: forall bs1 bs2 bsres N, 
  check_symopp bs1 bs2 bsres (BO_BVxor N) = true ->
  (List.map (Lit.interp rho) bsres) = 
  (RAWBITVECTOR_LIST.map2 xorb (List.map (Lit.interp rho) bs1)
                          (List.map (Lit.interp rho) bs2)).
Proof.
  intros.
  pose proof H.
  apply check_symopp_bvxor_length in H.
  destruct H.
  apply check_symopp_bvxor in H0. easy. easy. easy.
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

Lemma valid_check_bbOp pos1 pos2 lres: C.valid rho (check_bbOp pos1 pos2 lres).
Proof.
      unfold check_bbOp.
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
      intros [ | | | | | | |[ A| | | | ]|N|N|N|N|N|N] a1' a2' Heq9; try now apply C.interp_true.
      (* BVand *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (check_symopp bs1 bs2 bsres (BO_BVand N)); simpl; intros Heq11; try (now apply C.interp_true).
        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
      
        apply BITVECTOR_LIST.bv_eq_reflect.


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
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.
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
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.

        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N).
        unfold BITVECTOR_LIST.bv_and, RAWBITVECTOR_LIST.bv_and.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.
    
        (** remaining split **)

        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.
        
        do 2 rewrite map_length.

        specialize(@check_symopp_bvand_length bs1 bs2 bsres N Heq11); intro Hlen.
        destruct Hlen as (Hlenbs1, Hlenbs2).
        rewrite Hlenbs1, Hlenbs2.
        
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_and.
        unfold RAWBITVECTOR_LIST.size.
        
        do 2 rewrite map_length.
        rewrite Hlenbs1 at 1. rewrite Hlenbs2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal.
        
        cut (length bs1 = Datatypes.length (map (Lit.interp rho) bs1)).
        intros HC1. rewrite HC1.  
        apply RAWBITVECTOR_LIST.map2_and_length.
        do 2 rewrite map_length. now rewrite Hlenbs1.
        now rewrite map_length.

        exact Heq11.
          
  (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.
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
        rewrite H6 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.


        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N).
        unfold BITVECTOR_LIST.bv_and, RAWBITVECTOR_LIST.bv_and.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.

        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.

        specialize(@check_symopp_bvand_length bs1 bs2 bsres N Heq11); intro Hlen.
        destruct Hlen as (Hlenbs1, Hlenbs2).
        
        do 2 rewrite map_length.
        rewrite Hlenbs1, Hlenbs2.
        
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split.  rewrite RAWBITVECTOR_LIST.map2_and_comm. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_and.
        unfold RAWBITVECTOR_LIST.size.
        
        do 2 rewrite map_length.
        rewrite Hlenbs1 at 1. rewrite Hlenbs2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal.

        rewrite <- Hlenbs1.

        specialize (@RAWBITVECTOR_LIST.map2_and_length (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
        intros HSP. rewrite <- HSP. now rewrite map_length.
        do 2 rewrite map_length. now rewrite Hlenbs1.

        exact Heq11.


      (* BVor *)
    - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (check_symopp bs1 bs2 bsres (BO_BVor N)); simpl; intros Heq11; try (now apply C.interp_true).
        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
      
        apply BITVECTOR_LIST.bv_eq_reflect.


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
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.
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
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.

        rewrite (@check_symopp_bvor_nl bs1 bs2 bsres N).
        unfold BITVECTOR_LIST.bv_or, RAWBITVECTOR_LIST.bv_or.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.
    
        (** remaining split **)

        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.
        
        do 2 rewrite map_length.

        specialize(@check_symopp_bvor_length bs1 bs2 bsres N Heq11); intro Hlen.
        destruct Hlen as (Hlenbs1, Hlenbs2).
        rewrite Hlenbs1, Hlenbs2.
        
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_or.
        unfold RAWBITVECTOR_LIST.size.
        
        do 2 rewrite map_length.
        rewrite Hlenbs1 at 1. rewrite Hlenbs2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal.
        
        cut (length bs1 = Datatypes.length (map (Lit.interp rho) bs1)).
        intros HC1. rewrite HC1.  
        apply RAWBITVECTOR_LIST.map2_or_length.
        do 2 rewrite map_length. now rewrite Hlenbs1.
        now rewrite map_length.

        exact Heq11.
        

  (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.
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
        rewrite H6 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.


        rewrite (@check_symopp_bvor_nl bs1 bs2 bsres N).
        unfold BITVECTOR_LIST.bv_or, RAWBITVECTOR_LIST.bv_or.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.

        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.

        specialize(@check_symopp_bvor_length bs1 bs2 bsres N Heq11); intro Hlen.
        destruct Hlen as (Hlenbs1, Hlenbs2).
        
        do 2 rewrite map_length.
        rewrite Hlenbs1, Hlenbs2.
        
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split.  rewrite RAWBITVECTOR_LIST.map2_or_comm. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_or.
        unfold RAWBITVECTOR_LIST.size.
        
        do 2 rewrite map_length.
        rewrite Hlenbs1 at 1. rewrite Hlenbs2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal.

        rewrite <- Hlenbs1.

        specialize (@RAWBITVECTOR_LIST.map2_or_length (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
        intros HSP. rewrite <- HSP. now rewrite map_length.
        do 2 rewrite map_length. now rewrite Hlenbs1.

        exact Heq11.

(** BVxor **)

     - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (check_symopp bs1 bs2 bsres (BO_BVxor N)); simpl; intros Heq11; try (now apply C.interp_true).
        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
      
        apply BITVECTOR_LIST.bv_eq_reflect.


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
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.
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
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.

        rewrite (@check_symopp_bvxor_nl bs1 bs2 bsres N).
        unfold BITVECTOR_LIST.bv_xor, RAWBITVECTOR_LIST.bv_xor.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.
    
        (** remaining split **)

        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.
        
        do 2 rewrite map_length.

        specialize(@check_symopp_bvxor_length bs1 bs2 bsres N Heq11); intro Hlen.
        destruct Hlen as (Hlenbs1, Hlenbs2).
        rewrite Hlenbs1, Hlenbs2.
        
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_xor.
        unfold RAWBITVECTOR_LIST.size.
        
        do 2 rewrite map_length.
        rewrite Hlenbs1 at 1. rewrite Hlenbs2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal.
        
        cut (length bs1 = Datatypes.length (map (Lit.interp rho) bs1)).
        intros HC1. rewrite HC1.  
        apply RAWBITVECTOR_LIST.map2_xor_length.
        do 2 rewrite map_length. now rewrite Hlenbs1.
        now rewrite map_length.

        exact Heq11.
        

  (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.
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
        rewrite H6 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.


        rewrite (@check_symopp_bvxor_nl bs1 bs2 bsres N).
        unfold BITVECTOR_LIST.bv_xor, RAWBITVECTOR_LIST.bv_xor.
        unfold RAWBITVECTOR_LIST.size, BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, 
        RAWBITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.bits.

        apply eq_rec.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.n.

        specialize(@check_symopp_bvxor_length bs1 bs2 bsres N Heq11); intro Hlen.
        destruct Hlen as (Hlenbs1, Hlenbs2).
        
        do 2 rewrite map_length.
        rewrite Hlenbs1, Hlenbs2.
        
        rewrite N.eqb_compare. rewrite N.compare_refl.
        split.  rewrite RAWBITVECTOR_LIST.map2_xor_comm. reflexivity.
        
        unfold RAWBITVECTOR_LIST.size_bv_xor.
        unfold RAWBITVECTOR_LIST.size.
        
        do 2 rewrite map_length.
        rewrite Hlenbs1 at 1. rewrite Hlenbs2.
        rewrite N.eqb_compare. rewrite N.compare_refl.
        apply f_equal.

        rewrite <- Hlenbs1.

        specialize (@RAWBITVECTOR_LIST.map2_xor_length (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
        intros HSP. rewrite <- HSP. now rewrite map_length.
        do 2 rewrite map_length. now rewrite Hlenbs1.

        exact Heq11.
Qed.


Lemma check_symopp_eq: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_eq (Typ.TBV)) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_eq (Typ.TBV))  = true.
Proof. intros.
       simpl in H. 
       case (Lit.is_pos ibsres) in H.
       case (t_form .[ Lit.blit ibsres]) in H; try (contradict H; easy).
       case ((i == ibs1) && (i0 == ibs2) || (i == ibs2) && (i0 == ibs1)) in H.
       exact H.
       now contradict H.
       now contradict H.
Qed.

Lemma bool_eqb_comm: forall ibs1 ibs2,  Bool.eqb ibs1 ibs2 = Bool.eqb ibs2 ibs1.
Proof. intros. case_eq ibs1. intros. case_eq ibs2. intros. easy. intros. easy. intros. easy. Qed.

Lemma check_symopp_eq': forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_eq (Typ.TBV)) = true ->
      Bool.eqb (Lit.interp rho ibs1) (Lit.interp rho ibs2) = Lit.interp rho ibsres.
Proof. intros.
       simpl in H.
       case_eq (Lit.is_pos ibsres). intros. rewrite H0 in H.
       case_eq (t_form .[ Lit.blit ibsres]); intros; rewrite H1 in H; try (now contradict H).
       specialize (@rho_interp ( Lit.blit ibsres)).
       rewrite H1 in rho_interp. simpl in rho_interp.
       case_eq ((i == ibs1) && (i0 == ibs2) || (i == ibs2) && (i0 == ibs1)).
       intros. rewrite orb_true_iff in H2. destruct H2.
       rewrite andb_true_iff in H2. destruct H2. rewrite eqb_spec in H2, H3.
       rewrite H2, H3 in rho_interp.
       rewrite <- rho_interp. unfold Lit.interp. rewrite H0. now unfold Var.interp.
       intros. rewrite andb_true_iff in H2. destruct H2. rewrite eqb_spec in H2, H3.
       rewrite H2, H3 in rho_interp. rewrite bool_eqb_comm in rho_interp.
       rewrite <- rho_interp. unfold Lit.interp. rewrite H0. now unfold Var.interp.
       intros. rewrite H2 in H. now contradict H.
       intros. rewrite H0 in H. now contradict H.
Qed.

Lemma  check_symopp_bveq: forall bs1 bs2 a4, check_symopp bs1 bs2 (to_list a4) (BO_eq Typ.TBV) = true ->
                          RAWBITVECTOR_LIST.beq_list (map (Lit.interp rho) bs1)
                          (map (Lit.interp rho) bs2) = forallb (Lit.interp rho) (to_list a4).
Proof. intros. revert bs1 bs2 H.
       induction (to_list a4) as [ | xa4 xsa4 IHa4].
       - intros.
         case_eq bs1. intros. rewrite H0 in H.
         case_eq bs2. intros. rewrite H1 in H.
         simpl. easy.
         intros. rewrite H1 in H. simpl in H. now contradict H.
         intros. rewrite H0 in H. simpl in H.
         case_eq bs2. intros. rewrite H1 in H. now contradict H.
         intros. rewrite H1 in H. now contradict H.
       - intros. unfold check_symopp in H.
         case_eq bs1. intros. rewrite H0 in H.
         case_eq bs2. intros. rewrite H1 in H. now contradict H.
         intros. rewrite H1 in H. now contradict H.
         intros. fold check_symopp in H.
         case_eq bs2. intros. rewrite H1 in H. simpl in H.
         rewrite H0 in H. simpl in H. now contradict H. 
         intros. rewrite H0, H1 in H.
         pose proof H. apply check_symopp_eq' in H2.
         apply check_symopp_eq in H.
         specialize (IHa4 l l0 H). simpl. rewrite IHa4.
         case (forallb (Lit.interp rho) xsa4); [ do 2 rewrite andb_true_r | now do 2 rewrite andb_false_r].
         exact H2.
Qed.

Lemma beq_list_comm: forall bs1 bs2, RAWBITVECTOR_LIST.beq_list bs2 bs1 =  
                                     RAWBITVECTOR_LIST.beq_list bs1 bs2.
Proof. intro bs1. 
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. case bs2. easy.
         intros. easy.
       - intros. case bs2. easy.
         intros.  simpl.
         specialize (@IHbs1 l). rewrite IHbs1.
         case (RAWBITVECTOR_LIST.beq_list xsbs1 l). do 2 rewrite andb_true_r.
         unfold Bool.eqb.
         case b. easy. easy.
         now do 2 rewrite andb_false_r.
Qed.


Lemma valid_check_bbEq pos1 pos2 lres : C.valid rho (check_bbEq pos1 pos2 lres).
Proof. 
       unfold check_bbEq.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_form .[ Lit.blit bsres]); try (intros; now apply C.interp_true). intros a4 Heq11.


       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

      intros [ | | | | | | | [ A | | | | ]|N|N|N|N|N|N] a1' a2' Heq9; try now apply C.interp_true.

       case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq15; try (now apply C.interp_true).
       case_eq (check_symopp bs1 bs2 (to_list a4) (BO_eq (Typ.TBV))); simpl; intros Heq16; try (now apply C.interp_true).
       unfold C.valid. simpl. rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy.
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
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

       unfold get_type' in H2, H3. unfold v_type in H2, H3.
       case_eq (t_interp .[ a1']).
         intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
       case_eq (t_interp .[ a2']).
         intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
       simpl in v_vala2, v_vala2.

       apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

       (** case a1 = a1' and a2 = a2' **)
       rewrite orb_true_iff in Heq15.
       do 2 rewrite andb_true_iff in Heq15.
       destruct Heq15 as [Heq15 | Heq15];
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.


        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1. easy.
        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. 

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia2. easy.
        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. 
        
        generalize dependent v_vala1. generalize dependent v_vala2.
        rewrite H2, H3. rewrite Typ.cast_refl. intros.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.
        
        rewrite Form.wf_interp_form; trivial.
        rewrite Heq11. simpl.
        rewrite afold_left_and.

        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        case_eq (Lit.is_pos bsres). intros.
        rewrite HSp1, HSp2.
        
        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.  
        apply check_symopp_bveq. exact Heq16.

        intros.
        apply f_equal.

        rewrite HSp1, HSp2.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        
        apply check_symopp_bveq. exact Heq16.

    (** case symmetry **)


        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1. easy.
        rewrite H4 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2. 

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia2. easy.
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1. 
        
        generalize dependent v_vala1. generalize dependent v_vala2.
        rewrite H2, H3. rewrite Typ.cast_refl. intros.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.
        
        rewrite Form.wf_interp_form; trivial.
        rewrite Heq11. simpl.
        rewrite afold_left_and.

        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        case_eq (Lit.is_pos bsres). intros.
        rewrite HSp1, HSp2.
        
        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        rewrite beq_list_comm.
        
        apply check_symopp_bveq. exact Heq16.

        intros.
        apply f_equal.

        rewrite HSp1, HSp2.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        rewrite beq_list_comm.

        apply check_symopp_bveq. exact Heq16.
    (****)

    (** contradictions **)
    intros Hv. rewrite Hv in H0. now contradict H0.
    intros Hv. rewrite Hv in H0. now contradict H0.



    (** right to left implication **)
    
    intros a3 Heq10.
    case_eq (t_form .[ Lit.blit bsres]); try (intros; now apply C.interp_true). intros a4 Heq11.
    case_eq (t_atom .[ a4]); try (intros; now apply C.interp_true).
    intros [ | | | | | | | [ A | | | | ]|N|N|N|N|N|N] a1' a2' Heq9; try now apply C.interp_true.

  case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq15; try (now apply C.interp_true).
       case_eq (check_symopp bs1 bs2 (to_list a3) (BO_eq (Typ.TBV))); simpl; intros Heq16; try (now apply C.interp_true).
       unfold C.valid. simpl. rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a4).
       assert (a4 < PArray.length t_atom).
       apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy.
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a4]).
       intros v_typea3 v_vala4 Htia4. rewrite Htia4 in H0.
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

       unfold get_type' in H2, H3. unfold v_type in H2, H3.
       case_eq (t_interp .[ a1']).
         intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
       case_eq (t_interp .[ a2']).
         intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
       simpl in v_vala2, v_vala2.

       apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

       (** case a1 = a1' and a2 = a2' **)
       rewrite orb_true_iff in Heq15.
       do 2 rewrite andb_true_iff in Heq15.
       destruct Heq15 as [Heq15 | Heq15];
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.

     (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1. easy.
        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. 

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia2. easy.
        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. 
        
        generalize dependent v_vala1. generalize dependent v_vala2.
        rewrite H2, H3. rewrite Typ.cast_refl. intros.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.

        unfold Atom.interp_form_hatom.
        rewrite Form.wf_interp_form; trivial.
        rewrite Heq11. simpl.


        rewrite afold_left_and.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.

        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        case_eq (Lit.is_pos bsres). intros.
        rewrite HSp1, HSp2.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        
        symmetry.
        apply check_symopp_bveq. exact Heq16.
        
        intros.
        apply f_equal.

        rewrite HSp1, HSp2.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        symmetry.
        apply check_symopp_bveq. exact Heq16.


    (** case symmetry **)


        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1. easy.
        rewrite H4 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2. 

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia2. easy.
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1. 
        
        generalize dependent v_vala1. generalize dependent v_vala2.
        rewrite H2, H3. rewrite Typ.cast_refl. intros.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.
        apply (@Bool.eqb_true_iff (Lit.interp rho a) (Lit.interp rho bsres)).

        unfold Lit.interp, Var.interp.
        rewrite rho_interp.
        rewrite Heq10. simpl.


        unfold Atom.interp_form_hatom.
        rewrite Form.wf_interp_form; trivial.
        rewrite Heq11. simpl.

        rewrite afold_left_and.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia1, Htia2. simpl.

        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        case_eq (Lit.is_pos bsres). intros.
        rewrite HSp1, HSp2.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        symmetry.
        rewrite beq_list_comm.
        
        apply check_symopp_bveq. exact Heq16.

        intros.
        apply f_equal.

        rewrite HSp1, HSp2.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        symmetry.
        rewrite beq_list_comm.

        apply check_symopp_bveq. exact Heq16.
    (****)

    (** contradictions **)
    intros Hv. rewrite Hv in H0. now contradict H0.
    intros Hv. rewrite Hv in H0. now contradict H0.
    intros. now apply C.interp_true.
Qed.


Lemma check_add_bvadd_length: forall bs1 bs2 bsres c,
  let n := length bsres in
  check_add bs1 bs2 bsres c = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof.
  intros.
  revert bs1 bs2 c H.
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
  simpl in H.
  case (Lit.is_pos r) in H.
  case (t_form .[ Lit.blit r]) in H; try easy.
  case (Lit.is_pos i1) in H.  
  case (t_form .[ Lit.blit i1]) in H; try now contradict H.
  rewrite andb_true_iff in H. destruct H.
  specialize (IHrbsres bs1 bs2 ((Cor (Cand (Clit i) (Clit i0)) (Cand (Cxor (Clit i) (Clit i0)) c))) H0). 
  simpl.
  simpl in n.
  split; apply f_equal. easy. easy.
  easy. easy.
Qed.

Lemma prop_eq_carry_lit: forall c i, eq_carry_lit c i = true -> interp_carry c = (Lit.interp rho i).
Proof. intro c.
       induction c. 
       - intros. simpl in *. 
         case (Lit.is_pos i0 ) in H; rewrite eqb_spec in H; now rewrite H.
       - intros. simpl. 
         pose proof IHc1. pose proof IHc2.
         simpl in H.
         case_eq ( Lit.is_pos i). intros Hip0.
         rewrite Hip0 in H.
         case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
         case_eq (PArray.length a == 2). intros Hl. rewrite Hl in H. rewrite andb_true_iff in H.
         destruct H.
         
         apply H0 in H.
         apply H1 in H3.
         rewrite H, H3.
         
         specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
         simpl in rho_interp.
         rewrite afold_left_and in rho_interp.
         rewrite eqb_spec in Hl.
         apply to_list_two in Hl.
         rewrite Hl in rho_interp.
         simpl in rho_interp.
         rewrite andb_true_r in rho_interp.
         unfold Lit.interp at 3. unfold Var.interp.
         rewrite Hip0. now rewrite rho_interp.
         
         intros. rewrite H3 in H. now contradict H.
         intros. rewrite H2 in H. now contradict H.
       - intros. simpl. 
         pose proof IHc1. pose proof IHc2.
         simpl in H.
         case_eq ( Lit.is_pos i). intros Hip0.
         rewrite Hip0 in H.
         case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
         case_eq (PArray.length a == 2). intros Hl. rewrite Hl in H. rewrite andb_true_iff in H.
         destruct H.
         
         apply H0 in H.
         apply H1 in H3.
         rewrite H, H3.
         
         specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
         simpl in rho_interp.
         rewrite afold_left_or in rho_interp.
         rewrite eqb_spec in Hl.
         apply to_list_two in Hl.
         rewrite Hl in rho_interp.
         simpl in rho_interp.
         rewrite orb_false_r in rho_interp.
         unfold Lit.interp at 3. unfold Var.interp.
         rewrite Hip0. now rewrite rho_interp.
         
         intros. rewrite H3 in H. now contradict H.
         intros. rewrite H2 in H. now contradict H.
       - intros. simpl. 
         pose proof IHc1. pose proof IHc2.
         simpl in H.
         case_eq ( Lit.is_pos i). intros Hip0.
         rewrite Hip0 in H.
         case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
         rewrite andb_true_iff in H. destruct H.
         
         apply H0 in H.
         apply H1 in H3.
         rewrite H, H3.
         
         specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
         simpl in rho_interp.
         unfold Lit.interp at 3. unfold Var.interp.
         rewrite Hip0. now rewrite rho_interp.
         
         intros. rewrite H2 in H. now contradict H.
Qed.


Lemma check_add_list:forall bs1 bs2 bsres c, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_add bs1 bs2 bsres c = true ->
                      RAWBITVECTOR_LIST.add_list_ingr
                        (BITVECTOR_LIST.bv
                           (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs1)))
                        (BITVECTOR_LIST.bv
                           (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs2)))
                        (interp_carry c)
                        =
                        (map (Lit.interp rho) bsres).
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros. simpl in H1.
         case_eq bs2. intros. rewrite H2 in H1. simpl.
         case_eq bsres. intros. rewrite H3 in H1. now simpl.
         intros. rewrite H3 in H1. now contradict H1.
         intros. rewrite H2 in H1. now contradict H1.
      - intros.
        case_eq bs2. intros. rewrite H2 in H1. simpl in H1. now contradict H1.
        intros. rewrite H2 in H1.
        case_eq bsres. intros. rewrite H3 in H1. simpl in H1. now contradict H1.
        intros. rewrite H3 in H1. simpl in H1.
        case_eq ( Lit.is_pos i0). intros. rewrite H4 in H1.
        case_eq ( t_form .[ Lit.blit i0]); intros; rewrite H5 in H1; try now contradict H.
        case_eq ( Lit.is_pos i1). intros. rewrite H6 in H1.
        case_eq ( t_form .[ Lit.blit i1]); intros; rewrite H7 in H1; try now contradict H.
        rewrite andb_true_iff in H1. destruct H1.
        unfold n in *.
        rewrite H3 in H.
        rewrite H2, H3 in H0.
        inversion H. inversion H0.
        
        specialize 
        (@IHbs1 l l0 
        ((Cor (Cand (Clit xbs1) (Clit i)) (Cand (Cxor (Clit xbs1) (Clit i)) c)))
        H10 H11 H8).
       
        
        simpl in *. unfold RAWBITVECTOR_LIST.of_bits in IHbs1.
        case_eq (RAWBITVECTOR_LIST.add_carry (Lit.interp rho xbs1) (Lit.interp rho i)
        (interp_carry c)). intros r c0 Heqrc.

        (** rho_interp Lit.blit i0 **)
        pose proof (rho_interp (Lit.blit i0)).
        rewrite H5 in H9. simpl in H9.
      (*  unfold Lit.interp, Var.interp in Heqrc. *)

        (** rho_interp Lit.blit i1 **)
        pose proof (rho_interp (Lit.blit i1)).
        rewrite H7 in H12. simpl in H12.

(*        unfold Lit.interp, Var.interp in Heqrc. *)
        
        unfold Lit.interp at 3.
        rewrite H4. unfold Var.interp. rewrite H9.
        rewrite <- IHbs1.
        simpl.
        cut (r = xorb (Lit.interp rho i1) (Lit.interp rho i2)).
        cut (c0 =  (Lit.interp rho xbs1 && Lit.interp rho i
        || xorb (Lit.interp rho xbs1) (Lit.interp rho i) && interp_carry c)).
        intros. now rewrite H13, H14.

(* c *)
        case ((Lit.interp rho xbs1)) in *.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.
        case ((interp_carry c)) in *.        
        inversion Heqrc. easy.
        inversion Heqrc. easy.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc. easy.
        inversion Heqrc. easy.
(* r *)

          rewrite andb_true_iff in H1.
          destruct H1.
          rewrite orb_true_iff in H1.
          destruct H1; rewrite andb_true_iff in H1; destruct H1.
          rewrite eqb_spec in H1, H14. rewrite H1, H14 in *.

          apply  prop_eq_carry_lit in H13. rewrite <- H13.

        case ((Lit.interp rho xbs1)) in *.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.       
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy. 
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.

          rewrite eqb_spec in H1, H14. rewrite H1, H14 in *.

          apply  prop_eq_carry_lit in H13. rewrite <- H13.


        case ((Lit.interp rho xbs1)) in *.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.       
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy. 
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((Lit.interp rho i)) in *.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        case ((interp_carry c)) in *.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.
        inversion Heqrc.
        unfold Lit.interp, Var.interp.
        rewrite H6, H12. easy.

        (** contradictions **)
        intros. rewrite H6 in H1. now contradict H1.
        intros. rewrite H4 in H1. now contradict H1.
Qed.

Lemma check_add_bvadd: forall bs1 bs2 bsres, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_add bs1 bs2 bsres (Clit Lit._false) = true ->
  BITVECTOR_LIST.bv_add (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs1))
  (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs2)) =
  BITVECTOR_LIST.of_bits (map (Lit.interp rho) bsres).
Proof. intros.
       specialize (@check_add_list bs1 bs2 bsres ( (Clit Lit._false)) H H0 H1). intros.
       unfold BITVECTOR_LIST.bv_add.
       unfold RAWBITVECTOR_LIST.bv_add.
       unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits.
       unfold BITVECTOR_LIST.of_bits.
       apply eq_rec.
       unfold BITVECTOR_LIST.n, BITVECTOR_LIST.bv.
       assert (
       (Datatypes.length
          (RAWBITVECTOR_LIST.of_bits (map (Lit.interp rho) bs1))) = n).
       unfold RAWBITVECTOR_LIST.of_bits. now rewrite map_length.
       assert (
       (Datatypes.length
          (RAWBITVECTOR_LIST.of_bits (map (Lit.interp rho) bs2))) = n).
       unfold RAWBITVECTOR_LIST.of_bits. now rewrite map_length.
       rewrite H3, H4.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       split.
       unfold RAWBITVECTOR_LIST.add_list.
       unfold interp_carry in H2.
       specialize (Lit.interp_false rho wf_rho). intros.
       unfold is_true in H5.
       rewrite not_true_iff_false in H5.
       rewrite H5 in H2.
       exact H2.
       
       unfold RAWBITVECTOR_LIST.size_bv_add.
       unfold RAWBITVECTOR_LIST.size.
       rewrite H3, H4.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       unfold n. now rewrite map_length.
Qed.


Lemma valid_check_bbAdd pos1 pos2 lres : C.valid rho (check_bbAdd pos1 pos2 lres).
Proof.
      unfold check_bbAdd.
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
      intros [ | | | | | | |[ A| | | | ]|N|N|N|N|N|N] a1' a2' Heq9; try now apply C.interp_true.
      (* BVadd *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq ( check_add bs1 bs2 bsres (Clit Lit._false) ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
      
        apply BITVECTOR_LIST.bv_eq_reflect.


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
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.
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
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.

        pose proof Heq11.
        apply check_add_bvadd_length in Heq11.
        apply check_add_bvadd.

        easy. easy. easy.
        
        (** symmetic case **)


     (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.
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
        rewrite H6 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.

        pose proof Heq11.
        assert (BITVECTOR_LIST.size (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs2)) = 
        BITVECTOR_LIST.size (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bsres))).
        unfold BITVECTOR_LIST.size, BITVECTOR_LIST.of_bits.
        unfold RAWBITVECTOR_LIST.size. unfold BITVECTOR_LIST.bv.
        unfold RAWBITVECTOR_LIST.of_bits. apply f_equal.
        do 2 rewrite map_length.
        pose proof H7.
        apply check_add_bvadd_length in H7.
        destruct H7. now rewrite H9.

        assert (BITVECTOR_LIST.size (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs1)) = 
        BITVECTOR_LIST.size (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bsres))).
        unfold BITVECTOR_LIST.size, BITVECTOR_LIST.of_bits.
        unfold RAWBITVECTOR_LIST.size. unfold BITVECTOR_LIST.bv.
        unfold RAWBITVECTOR_LIST.of_bits. apply f_equal.
        do 2 rewrite map_length.
        pose proof H7.
        apply check_add_bvadd_length in H7.
        destruct H7. now rewrite H7.

        specialize (BITVECTOR_LIST.bv_add_comm H8 H9). intros.
        rewrite BITVECTOR_LIST.bv_eq_reflect in H10.
        rewrite H10.
        
        apply check_add_bvadd_length in Heq11.
        apply check_add_bvadd.

        easy. easy. easy.
Qed.

Lemma check_add_bvmult_length: forall bs1 bs2 bsres,
  let n := length bsres in
  check_mult bs1 bs2 bsres = true ->
  (length bs1 = n)%nat /\ (length bs2 = n)%nat .
Proof. Admitted.

Lemma check_mult_list:forall bs1 bs2 bsres, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_mult bs1 bs2 bsres = true ->
                      RAWBITVECTOR_LIST.mult_list_carry
                        (BITVECTOR_LIST.bv
                           (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs1)))
                        (BITVECTOR_LIST.bv
                           (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs2)))
                        (length (map (Lit.interp rho) bs1))
                        =
                        (map (Lit.interp rho) bsres).
Admitted.

Lemma check_add_bvmult: forall bs1 bs2 bsres, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_mult bs1 bs2 bsres = true ->
  BITVECTOR_LIST.bv_mult (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs1))
  (BITVECTOR_LIST.of_bits (map (Lit.interp rho) bs2)) =
  BITVECTOR_LIST.of_bits (map (Lit.interp rho) bsres).
Admitted.

Lemma valid_check_bbMult pos1 pos2 lres : C.valid rho (check_bbMult pos1 pos2 lres).
Proof.  
      unfold check_bbMult.
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
      intros [ | | | | | | |[ A| | | | ]|N|N|N|N|N|N] a1' a2' Heq9; try now apply C.interp_true.
      (* BVmult *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq ( check_mult bs1 bs2 bsres ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.
      
        apply BITVECTOR_LIST.bv_eq_reflect.


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
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2
        ;rewrite Heq10a1, Heq10a2 in *.

   (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        rewrite !Atom.t_interp_wf in Htia; trivial.
        rewrite Htia.
        unfold Atom.interp_form_hatom_bv.
        unfold Atom.interp_hatom.
        rewrite !Atom.t_interp_wf; trivial.
        rewrite Htia. easy.
        rewrite H4. rewrite Heq9. simpl.
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
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. rewrite Typ.cast_refl in HSp1.
        rewrite HSp1.
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
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. rewrite Typ.cast_refl in HSp2.
        rewrite HSp2.
        
        pose proof Heq11.
        apply check_add_bvmult_length in Heq11.
        apply check_add_bvmult.

        easy. easy. easy.

        (** case symmetic **)

        admit (*****).
 Admitted.

  End Proof.

End Checker.

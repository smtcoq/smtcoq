(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller  *                                                  *)
(*     Alain   Mebsout ♯                                                  *)
(*     Burak   Ekici   ♯                                                  *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(** A small checker for bit-vectors bit-blasting *)

(*Add Rec LoadPath "." as SMTCoq.*)

Require Import Int63 Int63Properties PArray.

Require Import Misc State SMT_terms BVList Psatz.
Require Import Bool List BoolEq NZParity Nnat.
Require Import BinPos BinNat Pnat Init.Peano.

Require FArray.

Import ListNotations.
Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.
Local Open Scope list_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.

  Variable t_atom : PArray.array atom.
  Variable t_form : PArray.array form.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).

  (** * Bit-blasting a constant bitvector:

       --------------------------- bbConst
        bbT(#b0010, [0; 1; 0; 0])
   *)

  Fixpoint check_bbc (a_bv: list bool) (bs: list _lit) :=
    match a_bv, bs with
    | nil, nil => true
    | v :: a_bv, b::bs =>
      if Lit.is_pos b then
        match get_form (Lit.blit b), v with
          | Ftrue, true | Ffalse, false => check_bbc a_bv bs
          | _, _ => false
        end
      else false
    | _, _ => false
    end.

  (** Checker for bitblasting of bitvector constants *)
  Definition check_bbConst lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
        | FbbT a bs =>
          match get_atom a with
            | Acop (CO_BV bv N) =>
              if check_bbc bv bs && (N.of_nat (length bv) =? N)%N
              then lres::nil
              else C._true
            | _ => C._true
          end
        | _ => C._true
      end
    else C._true.

  (** * Bit-blasting a variable:

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

  (** Checker for bitblasting of bitvector variables *)
  Definition check_bbVar lres :=
    if Lit.is_pos lres then
      match get_form (Lit.blit lres) with
      | FbbT a bs =>
        if check_bb a bs O (List.length bs)%N
        then lres::nil
        else C._true
      | _ => C._true
      end
    else C._true.

  Variable s : S.t.

  (** * Bit-blasting bitvector not ...

           bbT(a, [a0; ...; an])
        ------------------------------ bbNot
         bbT(not a, [~a0; ...; ~an])
   *)

  (* Helper function for bv_not *)
  Fixpoint check_not (bs br : list _lit)  :=
    match bs, br with
    | nil, nil => true
    | b::bs, r::br => (r == Lit.neg b) && check_not bs br
    | _, _ => false
    end.

  (** Checker for bitblasting of bitvector not *)
  Definition check_bbNot pos lres :=
    match S.get s pos with
    | l::nil =>
      if (Lit.is_pos l) && (Lit.is_pos lres) then
        match get_form (Lit.blit l), get_form (Lit.blit lres) with
        | FbbT a bs, FbbT r br =>
          match get_atom r with
          | Auop (UO_BVnot N) a' =>
            if (a == a') && check_not bs br &&
              (N.of_nat (length bs) =? N)%N
            then lres::nil
            else C._true
          | _ => C._true
          end
        | _, _ => C._true
        end
      else C._true
    | _ => C._true
    end.

  (** * Bit-blasting bitwise operations: bbAnd, bbOr, ...

        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbAnd
             bbT(a&b, [a0 /\ b0; ...; an /\ bn])
   *)

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

          | Fiff a1 a2, (BO_eq (Typ.TBV n))  =>
             (((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1)),
             BO_eq (Typ.TBV n))

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

  (** Checker for bitblasting of bitwise operators on bitvectors *)
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
                 && (N.of_nat (length bs1) =? n)%N
            then lres::nil
            else C._true

          | Abop (BO_BVor n) a1' a2' =>
             if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                  && (check_symopp bs1 bs2 bsres  (BO_BVor n))
                  && (N.of_nat (length bs1) =? n)%N
             then lres::nil
             else C._true

          | Abop (BO_BVxor n) a1' a2' =>
             if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                  && (check_symopp bs1 bs2 bsres  (BO_BVxor n))
                  && (N.of_nat (length bs1) =? n)%N
             then lres::nil
             else C._true

       | _ => C._true
          end
        | _, _, _ => C._true
        end
      else C._true
    | _, _ => C._true
    end.

   (** * Bit-blasting bitvector equality

        bbT(a, [a0; ...; an])      bbT(b, [b0; ...; bn])
       -------------------------------------------------- bbEq
         (a = b) <-> ((a0 <-> b0) /\ ... /\ (an <-> bn))
   *)

  Fixpoint check_eq (bs1 bs2 bsres: list _lit) :=
    match bs1, bs2, bsres with
    | nil, nil, nil => true
    | b1::bs1, b2::bs2, bres :: bsres =>
      match bs1, bs2, bsres with
      | _::_, _::_, [] => 
        if Lit.is_pos bres then
          match get_form (Lit.blit bres) with
          | Fand args =>
            match PArray.to_list args with
            | bres :: bsres =>
              if Lit.is_pos bres then
                let ires := 
                    match get_form (Lit.blit bres) with
                    | Fiff a1 a2  =>
                      ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
                    | _ => false
                    end in
                if ires then check_eq bs1 bs2 bsres
                else false
              else false
            | _ => false
            end
          | _ => false
          end
        else false
      | _, _, _ =>
        if Lit.is_pos bres then
          let ires := 
              match get_form (Lit.blit bres) with
              | Fiff a1 a2  =>
                ((a1 == b1) && (a2 == b2)) || ((a1 == b2) && (a2 == b1))
              | _ => false
              end in
          if ires then check_eq bs1 bs2 bsres
          else false
        else false
      end
    | _, _, _ => false
    end.

  (** Checker for bitblasting of equality between bitvector terms  *)
  Definition check_bbEq pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff leq lbb =>
          if (Bool.eqb (Lit.is_pos leq) (Lit.is_pos lbb)) then
          match get_form (Lit.blit leq), get_form (Lit.blit lbb) with
          | Fatom a, _ (* | _, Fatom a *) =>
            match get_atom a with
            | Abop (BO_eq (Typ.TBV n)) a1' a2' =>
              if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                   && (check_eq bs1 bs2 [lbb])
                   && (N.of_nat (length bs1) =? n)%N
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

  (** * Bitvector Arithmetic *)

  (** Representaion for symbolic carry computations *)
  Inductive carry : Type :=
  | Clit (_:_lit)
  | Cand (_:carry) (_:carry)
  | Cxor (_:carry) (_:carry)
  | Cor (_:carry) (_:carry)
  | Ciff (_:carry) (_:carry)
  .

  
  (** Check if a symbolic carry computation is equal to a literal
     representation. This function does not account for potential symmetries *)
  (* c should always be a positive literal in carry computations *)
  Fixpoint eq_carry_lit (carry : carry) (c : _lit) :=
    if Lit.is_pos c then
      match carry with
        | Clit l => l == c

        | Cand c1 c2  =>
          match get_form (Lit.blit c) with
          | Fand args =>
            if PArray.length args == 2 then
              (eq_carry_lit c1 (args.[0]) && eq_carry_lit c2 (args.[1]))
              (* || (eq_carry_lit c1 (args.[1]) && eq_carry_lit c2 (args.[0])) *)
            else false
          | _ => false
          end

        | Cxor c1 c2  =>
          match get_form (Lit.blit c) with
            | Fxor a1 a2 =>
              (eq_carry_lit c1 a1 && eq_carry_lit c2 a2)
                (* || (eq_carry_lit c1 a2 && eq_carry_lit c2 a1) *)
            | _ => false
          end

        | Cor c1 c2  =>
          match get_form (Lit.blit c) with
          | For args =>
            if PArray.length args == 2 then
              (eq_carry_lit c1 (args.[0]) && eq_carry_lit c2 (args.[1]))
                (* || (eq_carry_lit c1 (args.[1]) && eq_carry_lit c2 (args.[0])) *)
            else false
          | _ => false
          end

        | Ciff c1 c2  =>
          match get_form (Lit.blit c) with
            | Fiff a1 a2 =>
              (eq_carry_lit c1 a1 && eq_carry_lit c2 a2)
                (* || (eq_carry_lit c1 a2 && eq_carry_lit c2 a1) *)
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

                | Abop (BO_BVadd n) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) || ((a1 == a2') && (a2 == a1')))
                       && (check_add bs1 bs2 bsres (Clit Lit._false))
                       && (N.of_nat (length bs1) =? n)%N
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.

  (** * Bit-blasting bitvector negation ...

           bbT(a, [a0; ...; an])
        ------------------------------ bbNeg
               bbT(-a, [...])
   *)

  (* Helper function for bv_neg *)
  Definition check_neg (bs br : list _lit) :=
    let z := map (fun _ => Lit._false) bs in
    let nbs := map (fun l => Lit.neg l) bs in
    check_add nbs z br (Clit Lit._true).

  (** Checker for bitblasting of bitvector negation *)
  Definition check_bbNeg pos lres :=
    match S.get s pos with
    | l::nil =>
      if (Lit.is_pos l) && (Lit.is_pos lres) then
        match get_form (Lit.blit l), get_form (Lit.blit lres) with
        | FbbT a bs, FbbT r br =>
          match get_atom r with
          | Auop (UO_BVneg n) a' =>
            if (a == a') && check_neg bs br &&
               (N.of_nat (length bs) =? n)%N
            then lres::nil
            else C._true
          | _ => C._true
          end
        | _, _ => C._true
        end
      else C._true
    | _ => C._true
    end.

  Fixpoint and_with_bit (a: list _lit) (bt: _lit) : list carry :=
    match a with
      | nil => nil
      | ai :: a' => (Cand (Clit bt) (Clit ai)) :: and_with_bit a' bt 
    end.

  Fixpoint mult_step_k_h (a b: list carry) (c: carry) (k: Z) : list carry :=
    match a, b with
      | nil, _ => []
      | ai :: a', bi :: b' =>
        if (k - 1 <? 0)%Z then
          let carry_out := Cor (Cand ai bi) (Cand (Cxor ai bi) c) in
          let curr := Cxor (Cxor ai bi) c in
          curr :: mult_step_k_h a' b' carry_out (k - 1)
        else
          ai :: mult_step_k_h a' b c (k - 1)
      | ai :: a', nil =>  ai :: mult_step_k_h a' b c k
    end.

  Fixpoint mult_step (a b: list _lit) (res: list carry) (k k': nat) : list carry :=
    let ak := List.firstn (S k') a in
    let b' := and_with_bit ak (nth k b Lit._false) in
    let res' := mult_step_k_h res b' (Clit Lit._false) (Z.of_nat k) in
    match k' with 
      | O => res'
      (* | S O => res' *)
      | S pk' => mult_step a b res' (S k) pk'
    end.

  Definition bblast_bvmult (a b: list _lit) (n: nat) : list carry :=
    let res := and_with_bit a (nth 0 b Lit._false) in
    match n with
      | O => res
      | S O => res
      | S (S k) => mult_step a b res 1 k
    end.

  Fixpoint mkzeros (k: nat) : list carry :=
    match k with
      | O => nil
      | S k => (Clit Lit._false) :: mkzeros k
    end .

  Fixpoint bblast_bvadd (a b: list carry) (c: carry) : list carry :=
    match a, b  with
      | nil, _ | _, nil => nil
      | ai :: a', bi :: b' =>
        let c' := (Cor (Cand ai bi) (Cand (Cxor ai bi) c)) in
        (Cxor (Cxor ai bi) c') :: (bblast_bvadd a' b' c')
    end.

  Fixpoint mult_shift (a b: list _lit) (n: nat) : list carry :=
    match a with
      | nil => mkzeros n
      | ai :: a' =>
        (bblast_bvadd (and_with_bit b ai)
                      (mult_shift a' (Lit._false :: b) n) (Clit Lit._false))
    end.

  Definition check_mult (bs1 bs2 bsres: list _lit) : bool :=
   if Nat_eqb (length bs1) (length bs2)%nat then
    let bvm12 := bblast_bvmult bs1 bs2 (length bs1) in
    forallb2 eq_carry_lit bvm12 bsres
   else false.

  (** * Checker for bitblasting of bitvector multiplication *)
  Definition check_bbMult pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVmult n) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_mult bs1 bs2 bsres)
                       && (N.of_nat (length bs1) =? n)%N
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.

  (** * Checker for bitblasting of bitvector comparison: lt *)

  Fixpoint ult_big_endian_lit_list (bs1 bs2: list _lit) :=
    match bs1, bs2 with
      | nil, _ => Clit (Lit._false)
      | _, nil => Clit (Lit._false)
      | xi :: nil, yi :: nil => (Cand (Clit (Lit.neg xi)) (Clit yi))
      | xi :: x', yi :: y'   =>
        (Cor (Cand (Ciff (Clit xi) (Clit yi)) (ult_big_endian_lit_list x' y'))
             (Cand (Clit (Lit.neg xi)) (Clit yi)))
    end.

  Definition ult_lit_list (x y: list _lit) :=
    ult_big_endian_lit_list (List.rev x) (List.rev y).

  Definition check_ult (bs1 bs2: list _lit) (bsres: _lit) : bool :=
    if Lit.is_pos bsres then
      eq_carry_lit (ult_lit_list bs1 bs2) bsres
    else false.

  Definition check_bbUlt pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff llt lbb =>
          if (Bool.eqb (Lit.is_pos llt) (Lit.is_pos lbb)) then
          match get_form (Lit.blit llt), get_form (Lit.blit lbb) with
          | Fatom a, _ (* | _, Fatom a *) =>
            match get_atom a with
            | Abop (BO_BVult n) a1' a2' =>
              if ((a1 == a1') && (a2 == a2'))
                   && (check_ult bs1 bs2 lbb)
                   && (N.of_nat (length bs1) =? n)%N
                   && (N.of_nat (length bs2) =? n)%N
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

  Definition slt_big_endian_lit_list (x y: list _lit) :=
    match x, y with
      | nil, _ => Clit (Lit._false)
      | _, nil => Clit (Lit._false)
      | xi :: nil, yi :: nil => (Cand (Clit xi) (Clit (Lit.neg yi)))
      | xi :: x', yi :: y'   =>
        (Cor (Cand (Ciff (Clit xi) (Clit yi)) (ult_big_endian_lit_list x' y')) 
             (Cand (Clit xi) (Clit (Lit.neg yi))))
    end.

  Definition slt_lit_list (x y: list _lit) :=
    slt_big_endian_lit_list (List.rev x) (List.rev y).

  Definition check_slt (bs1 bs2: list _lit) (bsres: _lit) : bool := 
    if Lit.is_pos bsres then
      eq_carry_lit (slt_lit_list bs1 bs2) bsres
    else false.

  Definition check_bbSlt pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
    | l1::nil, l2::nil =>
      if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
        match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
        | FbbT a1 bs1, FbbT a2 bs2, Fiff llt lbb =>
          if (Bool.eqb (Lit.is_pos llt) (Lit.is_pos lbb)) then
          match get_form (Lit.blit llt), get_form (Lit.blit lbb) with
          | Fatom a, _ (* | _, Fatom a *) =>
            match get_atom a with
            | Abop (BO_BVslt n) a1' a2' =>
              if ((a1 == a1') && (a2 == a2'))
                   && (check_slt bs1 bs2 lbb)
                   && (N.of_nat (length bs1) =? n)%N
                   && (N.of_nat (length bs2) =? n)%N
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

  (** * Checker for bitblasting of bitvector concatenation *)

(*
  Fixpoint lit_to_carry (bs: list _lit) : list carry :=
    match bs with
      | nil => []
      | xbs :: xsbs => Clit xbs :: lit_to_carry xsbs
    end.

  Fixpoint h_check_bbConcat (bs1 bs2: list _lit) {struct bs1}: list carry :=
    match bs1 with
      | nil => 
      match bs2 with
        | nil => []
        | xbs2 :: xsbs2 => lit_to_carry bs2
      end
      | xbs1 :: xsbs1 => Clit xbs1 :: (h_check_bbConcat xsbs1 bs2)
    end.
    *)

  Fixpoint lit_to_carry (bs: list _lit) : list carry :=
    match bs with
      | nil => []
      | xbs :: xsbs => Clit xbs :: lit_to_carry xsbs
    end.

  Definition check_concat (bs1 bs2 bsres: list _lit) : bool :=
    if (forallb2 eq_carry_lit (lit_to_carry (bs2 ++ bs1)) bsres) then true else false.

  Definition check_bbConcat pos1 pos2 lres :=
    match S.get s pos1, S.get s pos2 with
      | l1::nil, l2::nil =>
        if (Lit.is_pos l1) && (Lit.is_pos l2) && (Lit.is_pos lres) then
          match get_form (Lit.blit l1), get_form (Lit.blit l2), get_form (Lit.blit lres) with
            | FbbT a1 bs1, FbbT a2 bs2, FbbT a bsres =>
              match get_atom a with

                | Abop (BO_BVconcat n m) a1' a2' =>
                  if (((a1 == a1') && (a2 == a2')) (* || ((a1 == a2') && (a2 == a1')) *) )
                       && (check_concat bs1 bs2 bsres)
                       && (N.of_nat (length bs1) =? n)%N
                       && (N.of_nat (length bs2) =? m)%N
                  then lres::nil
                  else C._true

                | _ => C._true
              end
            | _, _, _ => C._true
          end
        else C._true
      | _, _ => C._true
    end.

(* bitwise disequality *)

  Fixpoint List_diseqb (a b: list bool) : bool :=
  match a, b with
    | nil, nil =>  false
    | xa :: xsa, xb :: xsb =>
      if (Bool.eqb xa false) then 
        (if (Bool.eqb xb false) then List_diseqb xsa xsb else  true)
      else (if (Bool.eqb xb true) then List_diseqb xsa xsb else  true)
    | _, _ => true
  end.


  (** Checker for bitvector inequality *)
  Definition check_bbDiseq lres :=
  if negb (Lit.is_pos lres) then
      match get_form (Lit.blit lres) with
          | Fatom f => 
          match (get_atom f) with
            |  Abop (BO_eq (Typ.TBV n)) a b =>
             match (get_atom a), (get_atom b) with
               | (Acop (CO_BV bv1 n1)), (Acop (CO_BV bv2 n2)) =>
                  if List_diseqb bv1 bv2 && (N.of_nat (length bv1) =? n)%N
                     && (N.of_nat (length bv2) =? n)%N
                     && (n1 =? n)%N && (n2 =? n)%N
                  then lres::nil
                  else C._true
               | _, _ => C._true
             end
           | _ => C._true
         end
          | _ => C._true
      end
    else C._true.

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
      | Ciff c1 c2 => Bool.eqb (interp_carry c1) (interp_carry c2)
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
      Variable interp_bvatom : atom -> forall s, BITVECTOR_LIST.bitvector s.
      Notation atom := int (only parsing).

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

Lemma diseq_neg_eq: forall (la lb: list bool),
      List_diseqb la lb = true -> negb (RAWBITVECTOR_LIST.beq_list la lb) = true.
Proof. intro la.
       induction la.
       - intros. simpl in H. case lb in *.
           now contradict H.
           now simpl.
       - intros.
         simpl in *.
         case lb in *.
          easy.
          case_eq (Bool.eqb a false).
          intros. rewrite H0 in H.
          case_eq (Bool.eqb b false).
          intros. rewrite H1 in H.
          case a in *. now contradict H0.
          case b in *. now contradict H1.
          simpl.
          apply IHla. easy.
          case a in *. now contradict H0.
          case b in *. intros.
          now simpl.
          intros. simpl.
          apply IHla.
          simpl in H. easy.
          intros. rewrite H0 in H.
          case_eq (Bool.eqb b true ). intros.
          case a in *. 
          case b in *. simpl.
          apply IHla. simpl in H. easy.
          now simpl.
          now contradict H0.
          intros.
          case a in *.
          case b in *. simpl in *. now contradict H1.
          now simpl in *.
          case b in *. now simpl in *.
          simpl in *. now contradict H.
Qed.

Lemma valid_check_bbDiseq lres : C.valid rho (check_bbDiseq lres).
Proof. 
      unfold check_bbDiseq.
      case_eq (Lit.is_pos lres); intro Heq; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
        intros f Heq2.
      case_eq (t_atom .[ f]); try (intros; now apply C.interp_true).

      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N|N|N|N|N| | ];
         try (intros; now apply C.interp_true). intros n a b Heq3.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros c Heq4.
      case_eq c; try (intros; now apply C.interp_true).
      intros la n1 Heq5.
      case_eq (t_atom .[ b]); try (intros; now apply C.interp_true).
      intros c0 Heq6.
      case_eq c0; try (intros; now apply C.interp_true).
      intros lb n2 Heq7.
      case_eq (List_diseqb la lb && (N.of_nat (Datatypes.length la) =? n)%N
              && (N.of_nat (Datatypes.length lb) =? n)%N 
              && (n1 =? n)%N && (n2 =? n)%N);
         try (intros; now apply C.interp_true). intros Heq8.

      unfold C.valid. simpl. rewrite orb_false_r.
      unfold Lit.interp. rewrite Heq.
      unfold Var.interp.
      rewrite wf_interp_form; trivial. rewrite Heq2. simpl.
      unfold interp_form_hatom, interp_hatom.
      rewrite Atom.t_interp_wf; trivial.
      rewrite Heq3. simpl.
      rewrite !Atom.t_interp_wf; trivial.
      rewrite Heq4, Heq6. simpl.
      rewrite Heq5, Heq7. simpl.

        rewrite !andb_true_iff in Heq8.
        destruct Heq8 as (((Heq8, Ha), Hb), Hc).
        destruct Heq8 as (Heq8, Hd).
        rewrite N.eqb_eq in Hb, Hc.
        rewrite Hb, Hc.
        rewrite Typ.N_cast_refl. simpl.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        (* a *)
        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq4, Heq5. easy. }
        specialize (@H0 H1). rewrite Heq4 in H0. simpl in H0.
        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        rewrite Atom.t_interp_wf in Htia; trivial.
        rewrite Heq4, Heq5 in Htia. simpl in Htia.
        rewrite Hb in Htia.
        unfold Bval in Htia.
        rewrite Heq5 in H0. simpl in H0.
        inversion Htia.

        generalize dependent v_vala.
        rewrite <- H3. intros.

        (* b *)
        pose proof (H b). 
        assert (b < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq6, Heq7. easy. }
        specialize (@H2 H4). rewrite Heq6 in H2. simpl in H2.
        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ b]).
        intros v_typeb v_valb Htib. rewrite Htib in H2.
        rewrite Atom.t_interp_wf in Htib; trivial.
        rewrite Heq6, Heq7 in Htib. simpl in Htib.
        rewrite Hc in Htib.
        unfold Bval in Htib.
        rewrite Heq7 in H2. simpl in H2.
        inversion Htib.

        generalize dependent v_valb.
        rewrite <- H6. intros.

        (* f *)
        pose proof (H f). 
        assert (f < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq3. easy. }
        specialize (@H5 H7). rewrite Heq3 in H5. simpl in H5.
        unfold get_type' in H5. unfold v_type in H5.
        case_eq (t_interp .[ f]).
        intros v_typef v_valf Htif. rewrite Htif in H5.
        rewrite Atom.t_interp_wf in Htif; trivial.
        rewrite Heq3 in Htif. simpl in Htif.
        rewrite !Atom.t_interp_wf in Htif; trivial.
        rewrite Heq4, Heq6 in Htif.
        rewrite Heq5, Heq7 in Htif.
        simpl in Htif.
        rewrite Hb, Hc in Htif.
        rewrite Typ.N_cast_refl in Htif.
        unfold Bval in Htif.
        rewrite !andb_true_iff in H5.
        destruct H5. destruct H5.

        inversion Htif.

        generalize dependent v_valf.
        rewrite <- H11. intros.

        unfold BITVECTOR_LIST._of_bits, RAWBITVECTOR_LIST._of_bits.
        rewrite N.eqb_eq in Ha, Hd.

        generalize (BITVECTOR_LIST._of_bits_size la n).

        unfold BITVECTOR_LIST._of_bits, RAWBITVECTOR_LIST._of_bits.

        rewrite Hd.

        generalize (BITVECTOR_LIST._of_bits_size lb n).
        unfold BITVECTOR_LIST._of_bits, RAWBITVECTOR_LIST._of_bits.
        rewrite Ha.
        intros.

        unfold Typ.i_eqb. simpl.
        unfold BITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bv_eq.
        simpl.
        rewrite e, e0.
        rewrite N.eqb_refl.
        unfold RAWBITVECTOR_LIST.bits.

        apply diseq_neg_eq. easy.
Qed.

Lemma prop_checkbb: forall (a: int) (bs: list _lit) (i n: nat),
                    (length bs = (n - i))%nat ->
                    (check_bb a bs i n = true) ->
                    (forall i0, (i <= i0 < n )%nat ->
                    Lit.interp rho (nth (i0 - i) bs 1) = 
                    (@BITVECTOR_LIST.bitOf (N.of_nat n) i0 (interp_form_hatom_bv a (N.of_nat n)))).
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
         {
           apply PArray.get_not_default_lt.
           rewrite Heq2. now rewrite def_t_atom.
         }

         specialize (@H3 i1 H5).
         rewrite Heq2 in H3. simpl in H3.
         rewrite H2 in H3. simpl in H3.
         rewrite !andb_true_iff in H3.
         decompose [and] H3. clear H3.
         simpl in H7.

         unfold get_type' in H6, H7.
         unfold v_type in H6, H7.
         case_eq (t_interp .[ i1]).
         intros. rewrite H3 in H6. simpl in H6.
         case_eq (v_type0); intros; try (rewrite H8 in H6; now contradict H6).
         simpl.

         unfold Atom.interp_form_hatom_bv.
         unfold Atom.interp_form_hatom.
         unfold Atom.interp_hatom.
         rewrite Atom.t_interp_wf; trivial.
         rewrite Heq2.
         simpl.

         rewrite H2. simpl.
         cut (i = n1). intro Hin1. rewrite Hin1.
         cut (n = (N.to_nat n0)). intro Hnn0.
         rewrite Hnn0. 
         rewrite id''.
         case_eq (t_interp .[ i2]).

         intros. rewrite H9 in H7. rewrite <- H9.
         case_eq v_type1; intros; rewrite H10 in H7; try (now contradict H7).
         cut (n2 = n0)%N. intros Hn2n0. rewrite Hn2n0 in H10. 

         rewrite H9. simpl.
         unfold interp_bool.
         case_eq (Typ.cast v_type1 (Typ.TBV n0)).
         (* split *)
         split. rewrite H10.
         simpl.
         rewrite Typ.N_cast_refl. intros.
         contradict H11. easy.

         apply Typ.eqb_spec in H7. inversion H7. easy.

         now apply Nat_eqb_eq in Hif2.
         now apply Nat_eqb_eq in Hif1.

         omega.
         destruct H1.
         specialize (@le_le_S_eq i i0). intros H11.
         specialize (@H11 H1).
         destruct H11. left. split. exact H5. exact H3.
         right. exact H5.
         omega.
         intro H3. rewrite H3 in H0. now contradict H0.
         intros n0 Hn. rewrite Hn in H0. now contradict H0.
         intros n0 Hn. rewrite Hn in H0. now contradict H0.
         intros b0 i2 i3 Heq. rewrite Heq in H0. now contradict H0.
         intros t i2 i3 i4 Heq. rewrite Heq in H0. now contradict H0.
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
                     (@BITVECTOR_LIST.bitOf (N.of_nat(length bs)) i0 
                     (interp_form_hatom_bv a (N.of_nat (length bs))))).
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


Lemma eq_rec: forall (n: N) (a b: BITVECTOR_LIST.bitvector n), BITVECTOR_LIST.bv a = BITVECTOR_LIST.bv b 
                         ->
                          a = b.
Proof. intros. destruct a, b. 
       unfold BITVECTOR_LIST.bv in H.
       revert wf0.
       rewrite H. intros.
       now rewrite (proof_irrelevance wf0 wf1).
Qed.

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

Lemma bitOf_of_bits: forall l (a: BITVECTOR_LIST.bitvector (N.of_nat (length l))), 
                               (forall i, 
                               (i < (length l))%nat ->
                               nth i l false = 
                               (@BITVECTOR_LIST.bitOf (N.of_nat (length l)) i a))
                               ->
                               (BITVECTOR_LIST.bv_eq a (BITVECTOR_LIST.of_bits l)).
Proof. intros l a H.
       unfold BITVECTOR_LIST.of_bits in *.
       unfold BITVECTOR_LIST.bitOf in *.
       unfold BITVECTOR_LIST.bv_eq, BITVECTOR_LIST.bv in *.
       unfold RAWBITVECTOR_LIST.bitOf in *.
       destruct a.
       unfold RAWBITVECTOR_LIST.of_bits.
       unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *.
       rewrite wf0.       
       rewrite N.eqb_compare.
       rewrite N.compare_refl.
       cut (Datatypes.length l = Datatypes.length bv). intro wf1.

       apply (@nth_eq l bv wf1) in H.

       rewrite H.
       unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits in *.
       rewrite RAWBITVECTOR_LIST.List_eq_refl; auto.
       apply inj_iff in wf0. now do 2 rewrite id' in wf0.

Qed.

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
      apply bitOf_of_bits. intros. 
      cut (Lit.interp rho 1 = false). intro Hr. rewrite <- Hr. 
      rewrite map_nth.
      remember (@prop_checkbb' a bs Heq2 i).
      rewrite map_length in H.
      rewrite map_length.
      clear Heqe.
      now apply e in H.
      now apply rho_1.
Qed.

Lemma check_bbc_length : forall bv bs, check_bbc bv bs = true -> length bv = length bs.
Proof.
  intro bv. induction bv.
  intro bs. case bs.
  simpl; trivial.
  simpl; easy.
  intro bs. case bs in *.
  simpl; easy.
  simpl.
  case (Lit.is_pos i); try easy.
  case (t_form .[ Lit.blit i]); try easy;
  case a; try easy; intro Hc; apply IHbv in Hc; now rewrite Hc.
Qed.

Lemma nth_nil : forall A i (d:A), nth i [] d = d.
Proof.
  intros. unfold nth. case i; trivial.
Qed.

Lemma prop_check_bbc: forall bv bs,
                     (check_bbc bv bs = true) ->
                     (forall i, (i < (length bs) )%nat ->
                     (Lit.interp rho (nth i bs 1)) = nth i bv false).
Proof.
  intro bv. induction bv.
  intros bs. case bs. 
  intros.
  do 2 rewrite nth_nil. easy.
  simpl. easy.
  intros bs.
  case bs. simpl. easy.
  intros b l Hc i Hlen.
  case i in *.
  simpl.
  simpl in Hc.
  case_eq (Lit.is_pos b).
  intro Hposb.
  rewrite Hposb in Hc.
  case_eq (t_form .[ Lit.blit b]); try (intros; rewrite H in Hc; now contradict Hc).
  intros Hb.
  rewrite Hb in Hc.
  generalize (rho_interp (Lit.blit b)). rewrite Hb. simpl.
  intro Hbb.
  unfold Lit.interp, Var.interp.
  rewrite Hbb, Hposb.
  case a in *.
  trivial. now contradict Hc.
  intro Hb.
  rewrite Hb in Hc.
  generalize (rho_interp (Lit.blit b)). rewrite Hb. simpl.
  intro Hbb.
  unfold Lit.interp, Var.interp.
  rewrite Hbb, Hposb.
  case a in *.
  now contradict Hc. trivial.
  intro Hposb. rewrite Hposb in Hc. now contradict Hc.
  simpl.
  apply IHbv.
  simpl in Hc.
  case (Lit.is_pos b) in Hc; try now contradict Hc.
  case (t_form .[ Lit.blit b]) in Hc; try now contradict Hc.
  case a in Hc; try now contradict Hc. exact Hc.
  case a in Hc; try now contradict Hc. exact Hc.
  simpl in Hlen. omega.
Qed.

Lemma prop_check_bbc2: forall l bs, check_bbc l bs = true ->
RAWBITVECTOR_LIST.beq_list l (map (Lit.interp rho) bs) = true.
Proof. intro l.
       induction l as [ | xl xsl IHl ].
       - intros. simpl in *.
         case bs in *. now simpl. now contradict H.
       - intros. simpl in H.
         case bs in *. now contradict H.
         simpl.
         case_eq (Lit.is_pos i); intros.
         rewrite H0 in H.
         case_eq (t_form .[ Lit.blit i]); intros; try (rewrite H1 in H; now contradict H).
         rewrite H1 in H.
         case xl in *.
         rewrite andb_true_iff. split.
         unfold Lit.interp. rewrite H0.
         unfold Var.interp.
         specialize (rho_interp (Lit.blit i)).
         rewrite H1 in rho_interp. simpl in rho_interp.
         rewrite rho_interp. easy.
         apply IHl; easy.
         now contradict H.
         rewrite H1 in H.
         case xl in *. now contradict H.
         rewrite andb_true_iff.
         split.
         specialize (rho_interp (Lit.blit i)).
         rewrite H1 in rho_interp. simpl in rho_interp.
         unfold Lit.interp. rewrite H0.
         unfold Var.interp.
         rewrite rho_interp. easy.
         apply IHl; easy.
         rewrite H0 in H. now contradict H.
Qed.

Lemma valid_check_bbConst lres : C.valid rho (check_bbConst lres).
Proof.
  unfold check_bbConst.
  case_eq (Lit.is_pos lres); intro Heq1; [ |now apply C.interp_true].
  case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
  intros a bs Heq0.
  case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
  intros c Ha.
  case_eq c; try (intros; now apply C.interp_true).
  intros l N Hc.
  case_eq (check_bbc l bs &&
      (N.of_nat (Datatypes.length l) =? N)%N);
  try (intros; now apply C.interp_true).
  intro Hcheck.
  unfold C.valid. simpl. rewrite orb_false_r.
  unfold Lit.interp. rewrite Heq1.
  unfold Var.interp.
  rewrite wf_interp_form; trivial. rewrite Heq0. simpl.

  assert (Hinterpa:
            (interp_form_hatom_bv a = interp_bv t_i (interp_atom (t_atom .[a])))).
  {
    unfold Atom.interp_form_hatom_bv.
    unfold Atom.interp_hatom.
    rewrite !Atom.t_interp_wf; trivial.
  }
    rewrite Hinterpa.
    rewrite Ha, Hc. simpl.

 unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

 assert ((N.of_nat (Datatypes.length (map (Lit.interp rho) bs))) = N).
  {
    rewrite andb_true_iff in Hcheck.
    destruct Hcheck as (Hcheck1 & Hcheck2).
    apply check_bbc_length in Hcheck1.
    rewrite N.eqb_eq in Hcheck2.
    rewrite Hcheck1 in Hcheck2.
    now rewrite map_length.
  }

 generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs)
        ).

 rewrite H.
 intros.

 rewrite Typ.N_cast_refl.

  unfold BITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bv_eq.
  simpl.
  unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST._of_bits.

 rewrite andb_true_iff in Hcheck.
 destruct Hcheck as (Hcheck1 & Hcheck2).
 pose proof Hcheck1.
 apply check_bbc_length in Hcheck1.
 rewrite N.eqb_eq in Hcheck2.
 rewrite Hcheck2.
 rewrite N.eqb_refl.
 rewrite Hcheck1, map_length, N.eqb_refl.
 unfold RAWBITVECTOR_LIST.bits.

 now apply prop_check_bbc2.
Qed.

Lemma prop_check_not:
  forall bs br, length bs = length br ->
           check_not bs br = true ->
           map (Lit.interp rho) br = map (fun l => negb (Lit.interp rho l)) bs.
Proof.
  intro bs; induction bs; intros br Hlen Hcheck.
  - simpl in Hlen. symmetry in Hlen. apply empty_list_length in Hlen. rewrite Hlen; now simpl.
  - case br in *.
    + simpl in Hcheck; now contradict Hcheck.
    + simpl in Hlen. inversion Hlen as [Hlen'].
      simpl in Hcheck. rewrite andb_true_iff in Hcheck; destruct Hcheck as (Hcheck1, Hcheck2).
      apply Int63Properties.eqb_spec in Hcheck1; rewrite Hcheck1.
      simpl. rewrite Lit.interp_neg. apply f_equal.
      apply IHbs; auto.
Qed.

Lemma check_not_length:
  forall bs br, check_not bs br = true -> length bs = length br.
Proof.
  intro bs; induction bs; intros br Hcheck.
  - case br in *.
    + auto.
    + simpl in Hcheck; now contradict Hcheck.
  - case br in *.
    + simpl in Hcheck; now contradict Hcheck.
    + simpl in *.
      rewrite andb_true_iff in Hcheck.
      destruct Hcheck as (_, Hcheck').
      apply IHbs in Hcheck'; auto.
Qed.

Lemma valid_check_bbNot pos lres : C.valid rho (check_bbNot pos lres).
Proof.
  unfold check_bbNot.
  case_eq (S.get s pos); [ (intros; now apply C.interp_true) | ].
  intros l ls Hpos.
  case_eq ls; [ | (intros; now apply C.interp_true) ].
  intro Hnil.
  case_eq (Lit.is_pos l && Lit.is_pos lres); [ | (intros; now apply C.interp_true) ].
  intro Hpos'.
  case_eq (t_form .[ Lit.blit l]); try (intros; now apply C.interp_true).
  intros a bs HBl.
  case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
  intros r br HBr.
  case_eq (t_atom .[ r]); try (intros; now apply C.interp_true).
  intros u a'.
  case_eq u; try (intros; now apply C.interp_true).
  intros n Huot Hr.
  case_eq ((a == a')
             && check_not bs br
             && (N.of_nat (Datatypes.length bs) =? n)%N);
    try (intros; now apply C.interp_true).
  intro Hc.
  rewrite !andb_true_iff in Hc.
  destruct Hc as ((Ha, Hcheck), Hlen).
  rewrite N.eqb_eq in Hlen.
  apply Int63Properties.eqb_spec in Ha.
  generalize (Hs pos).
  rewrite Hpos, Hnil.
  unfold C.valid, C.interp; simpl; rewrite !orb_false_r.
  unfold Lit.interp, Var.interp.
  rewrite andb_true_iff in Hpos'.
  destruct Hpos' as (Hposl, Hposlres).
  rewrite Hposl, Hposlres.
  rewrite !rho_interp. rewrite HBl, HBr. simpl.

  intro Heqa.
  apply BITVECTOR_LIST.bv_eq_reflect in Heqa.
  apply BITVECTOR_LIST.bv_eq_reflect.


  generalize wt_t_atom. unfold Atom.wt. unfold is_true.
  rewrite PArray.forallbi_spec;intros.

  pose proof (H r). 
  assert (r < PArray.length t_atom).
  {
    apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Hr. easy.
  }

  specialize (@H0 H1). rewrite Hr in H0. simpl in H0.
  rewrite !andb_true_iff in H0. destruct H0.

  unfold get_type' in H0. unfold v_type in H0.
  case_eq (t_interp .[ r]).
  intros v_typer v_valr Htir. rewrite Htir in H0.
  case_eq (v_typer); intros; rewrite H3 in H0; try (now contradict H1).
  rename H3 into Hv.

  (* interp_form_hatom_bv r = 
          interp_bv t_i (interp_atom (t_atom .[r])) *)
  assert (interp_form_hatom_bv r = 
          interp_bv t_i (interp_atom (t_atom .[r]))).
  {
    unfold Atom.interp_form_hatom_bv.
    unfold Atom.interp_hatom.
    rewrite !Atom.t_interp_wf; trivial.
  }

  rewrite H3, Hr. simpl.
  unfold interp_bv.
  apply Typ.eqb_spec in H2.
  unfold get_type' in H2.
  unfold v_type in H2.
  case_eq (t_interp .[ a']).
  intros. rewrite H4 in H2. simpl.

  revert v_val0 H4.  
  rewrite H2. intros.
  rewrite Typ.cast_refl.
  simpl.

  assert ( (N.of_nat (Datatypes.length (map (Lit.interp rho) br))) = n).
  {
    apply check_not_length in Hcheck. rewrite Hcheck in Hlen.
    now rewrite map_length.
  }

  unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

  generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) br)
        ).

  rewrite H5.
  intros.
  rewrite Typ.N_cast_refl.
  unfold BITVECTOR_LIST.bv_not, RAWBITVECTOR_LIST.bv_not.

  apply eq_rec.
  simpl.

  rewrite <- Ha in *.

   (* interp_form_hatom_bv a = 
          interp_bv t_i (interp_atom (t_atom .[a])) *)
  assert (interp_form_hatom_bv a = 
          interp_bv t_i (interp_atom (t_atom .[a]))).
  {
    unfold Atom.interp_form_hatom_bv.
    unfold Atom.interp_hatom.
    rewrite !Atom.t_interp_wf; trivial.
  }

  rewrite H6 in Heqa.
  unfold interp_bv in Heqa.
  rewrite <- !Atom.t_interp_wf in Heqa; trivial.
  rewrite H4 in Heqa.
  revert Heqa . 

  assert ( (N.of_nat (Datatypes.length (map (Lit.interp rho) bs))) = n).
  {
    now rewrite map_length.
  }

  unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

  generalize (
         BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs)
        ).

  rewrite H7.
  rewrite Typ.cast_refl. intros.
  rewrite Heqa. simpl.

  specialize (@prop_check_not bs br). intros.
  symmetry.
  unfold RAWBITVECTOR_LIST.bits.
  rewrite map_map; apply H8; auto.

  now apply check_not_length in Hcheck.

Qed.

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
              try (intros i Heq; rewrite Heq in H1; now contradict H1).
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
               try (intros i Heq; rewrite Heq in H1; now contradict H1).
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


Lemma check_symopp_bvand_length2: forall bs1 bs2 bsres N,
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

Lemma check_symopp_bvand_length3: forall bs1 bs2 bsres n,
  check_symopp bs1 bs2 bsres (BO_BVand (N.of_nat n)) = true ->
  (length bs1 = n)%nat ->
  (length bsres = n)%nat.
Proof. intros bs1 bs2 bsres.
       revert bs1 bs2.
       induction bsres as [ | xbsres xsbsres IHbsres ].
       - intros.
         case bs1 in *.
           simpl in H. 
           case bs2 in *.
             easy. now contradict H.
           case bs2 in *.
            simpl in H. now contradict H.
            simpl in H. now contradict H.
       - intros.
         case bs1 in *. 
         simpl in H.
         case bs2 in *.
           now contradict H.
           now contradict H.
           simpl in H.
           case bs2 in *.
             now contradict H.
             case (Lit.is_pos xbsres) in *.
             case (t_form .[ Lit.blit xbsres] ) in *; try now contradict H.
             case (PArray.length a == 2) in *.
             case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in *.
             specialize (IHbsres bs1 bs2 (n-1)%nat).
             simpl in H0.
             assert (length bs1 = (n-1)%nat).
             { omega. }

             cut ( (BO_BVand (N.of_nat n - 1)) = (BO_BVand (N.of_nat (n - 1)))).

             intros.
             revert H.
             rewrite H2.
             intros.
             specialize (IHbsres H H1).
             simpl. rewrite IHbsres. omega.

             simpl.
             cut ((N.of_nat n - 1)%N = (N.of_nat (n - 1))).
             intros. now rewrite H2.

            case n. now simpl.
            intros. lia.
             now contradict H.
             now contradict H.
             now contradict H.
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

Lemma check_symopp_bvor_length2: forall bs1 bs2 bsres N,
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

Lemma check_symopp_bvor_length3: forall bs1 bs2 bsres n,
  check_symopp bs1 bs2 bsres (BO_BVor (N.of_nat n)) = true ->
  (length bs1 = n)%nat ->
  (length bsres = n)%nat.
Proof. intros bs1 bs2 bsres.
       revert bs1 bs2.
       induction bsres as [ | xbsres xsbsres IHbsres ].
       - intros.
         case bs1 in *.
           simpl in H. 
           case bs2 in *.
             easy. now contradict H.
           case bs2 in *.
            simpl in H. now contradict H.
            simpl in H. now contradict H.
       - intros.
         case bs1 in *. 
         simpl in H.
         case bs2 in *.
           now contradict H.
           now contradict H.
           simpl in H.
           case bs2 in *.
             now contradict H.
             case (Lit.is_pos xbsres) in *.
             case (t_form .[ Lit.blit xbsres] ) in *; try now contradict H.
             case (PArray.length a == 2) in *.
             case ((a .[ 0] == i) && (a .[ 1] == i0) || (a .[ 0] == i0) && (a .[ 1] == i)) in *.
             specialize (IHbsres bs1 bs2 (n-1)%nat).
             simpl in H0.
             assert (length bs1 = (n-1)%nat).
             { omega. }

             cut ( (BO_BVor (N.of_nat n - 1)) = (BO_BVor (N.of_nat (n - 1)))).

             intros.
             revert H.
             rewrite H2.
             intros.
             specialize (IHbsres H H1).
             simpl. rewrite IHbsres. omega.

             simpl.
             cut ((N.of_nat n - 1)%N = (N.of_nat (n - 1))).
             intros. now rewrite H2.

            case n. now simpl.
            intros. lia.
             now contradict H.
             now contradict H.
             now contradict H.
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


Lemma check_symopp_bvxor_length2: forall bs1 bs2 bsres N,
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

Lemma check_symopp_bvxor_length3: forall bs1 bs2 bsres n,
  check_symopp bs1 bs2 bsres (BO_BVxor (N.of_nat n)) = true ->
  (length bs1 = n)%nat ->
  (length bsres = n)%nat.
Proof. intros bs1 bs2 bsres.
       revert bs1 bs2.
       induction bsres as [ | xbsres xsbsres IHbsres ].
       - intros.
         case bs1 in *.
           simpl in H. 
           case bs2 in *.
             easy. now contradict H.
           case bs2 in *.
            simpl in H. now contradict H.
            simpl in H. now contradict H.
       - intros.
         case bs1 in *. 
         simpl in H.
         case bs2 in *.
           now contradict H.
           now contradict H.
           simpl in H.
           case bs2 in *.
             now contradict H.
             case (Lit.is_pos xbsres) in *.
             case (t_form .[ Lit.blit xbsres] ) in *; try now contradict H.
             case ((i1 == i) && (i2 == i0) || (i1 == i0) && (i2 == i)) in *.
             specialize (IHbsres bs1 bs2 (n-1)%nat).
             simpl in H0.
             assert (length bs1 = (n-1)%nat).
             { omega. }

             cut ( (BO_BVxor (N.of_nat n - 1)) = (BO_BVxor (N.of_nat (n - 1)))).

             intros.
             revert H.
             rewrite H2.
             intros.
             specialize (IHbsres H H1).
             simpl. rewrite IHbsres. omega.

             simpl.
             cut ((N.of_nat n - 1)%N = (N.of_nat (n - 1))).
             intros. now rewrite H2.

            case n. now simpl.
            intros. lia.
            now contradict H.
            now contradict H.
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
      intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N|N|N|N|N| | ] a1' a2' Heq9;
        try (intros; now apply C.interp_true).
      (* BVand *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
          simpl; intros Heq10; try (now apply C.interp_true).

        case_eq (
                 check_symopp bs1 bs2 bsres (BO_BVand N) &&
                 (N.of_nat (Datatypes.length bs1) =? N)%N); 
        simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        unfold Atom.interp_form_hatom_bv at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Atom.t_interp_wf; trivial.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. } 
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop. rewrite Htia1, Htia2.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i j Hv. rewrite Hv in H0. now contradict H0.
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros n Hv. rewrite Hv in H0.

        (** n = N **)
        apply N.eqb_eq in H0.
        rewrite <- H0 in *.
        revert v_vala Htia. rewrite Hv.
        intros v_vala Htia.

        generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        revert v_vala1 Htia1 v_vala2 Htia2.
        rewrite H2, H3.
        unfold bvtrue.
        rewrite Typ.cast_refl.

        intros v_vala1 Htia1 v_vala2 Htia2.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia1 in HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2'
        = 
        interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia2 in HSp2.

        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Bval, interp_bv.

        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N).

        assert (
          H100: (N.of_nat
            (Datatypes.length
               (RAWBITVECTOR_LIST.map2 andb (map (Lit.interp rho) bs1)
                  (map (Lit.interp rho) bs2)))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          specialize (@RAWBITVECTOR_LIST.map2_and_length 
          (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
          intros. rewrite <- H6.
          now rewrite map_length.
          apply check_symopp_bvand_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite !map_length, Heq11a, Heq11b.
       }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        generalize (
          BITVECTOR_LIST.of_bits_size (RAWBITVECTOR_LIST.map2 andb 
          (map (Lit.interp rho) bs1) 
          (map (Lit.interp rho) bs2))
        ).

        rewrite H100.
        rewrite Typ.cast_refl. intros.

        unfold BITVECTOR_LIST.bv_and, RAWBITVECTOR_LIST.bv_and.
        unfold RAWBITVECTOR_LIST.size.
        unfold RAWBITVECTOR_LIST.bits.

        unfold interp_bv in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite <- Heq11a in Heq11b.
          rewrite <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }
        revert HSp2.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)
        ).

        rewrite H101. intros.

        assert (
        H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp1.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)
        ).

        rewrite H102. intros.

        rewrite Typ.cast_refl in *.
        rewrite HSp1, HSp2. simpl.
        apply eq_rec. simpl.

        rewrite H101, H102.
        rewrite N.eqb_compare, N.compare_refl. easy.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).
        exact Heq11.

        (** symmetric case*)
        rewrite Heq10a1, Heq10a2 in *.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
       }

        rewrite H4 in HSp2.
        rewrite Htia1 in HSp2.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2'
        = 
        interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp1.
        simpl in HSp1.
        rewrite Htia2 in HSp1.

        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Bval, interp_bv.

        rewrite (@check_symopp_bvand_nl bs1 bs2 bsres N).

        assert (
          H100: (N.of_nat
            (Datatypes.length
               (RAWBITVECTOR_LIST.map2 andb (map (Lit.interp rho) bs1)
                  (map (Lit.interp rho) bs2)))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          specialize (@RAWBITVECTOR_LIST.map2_and_length 
          (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
          intros. rewrite <- H6.
          apply check_symopp_bvand_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite map_length.
          apply check_symopp_bvand_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite !map_length, Heq11a, Heq11b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        generalize (
          BITVECTOR_LIST.of_bits_size (RAWBITVECTOR_LIST.map2 andb 
          (map (Lit.interp rho) bs1) 
          (map (Lit.interp rho) bs2))
        ).

        rewrite H100.
        rewrite Typ.cast_refl. intros.

        unfold BITVECTOR_LIST.bv_and, RAWBITVECTOR_LIST.bv_and.
        unfold RAWBITVECTOR_LIST.size.
        unfold RAWBITVECTOR_LIST.bits.

        unfold interp_bv in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvand_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite <- Heq11a in Heq11b.
          rewrite <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp2.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)
        ).

        rewrite H101. intros.

        assert (
        H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp1.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)
        ).

        rewrite H102. intros.
        rewrite Typ.cast_refl in *.
        rewrite HSp1, HSp2. simpl.
        apply eq_rec. simpl.
        rewrite H101, H102.
        rewrite N.eqb_compare, N.compare_refl. 
        now rewrite RAWBITVECTOR_LIST.map2_and_comm.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).
        exact Heq11.

      (* BVor *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); 
           simpl; intros Heq10; try (now apply C.interp_true).

        case_eq (
                 check_symopp bs1 bs2 bsres (BO_BVor N) &&
                 (N.of_nat (Datatypes.length bs1) =? N)%N); 
        simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        unfold Atom.interp_form_hatom_bv at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Atom.t_interp_wf; trivial.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop. rewrite Htia1, Htia2.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i j Hv. rewrite Hv in H0. now contradict H0.
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros n Hv. rewrite Hv in H0.

        (** n = N **)
        apply N.eqb_eq in H0.
        rewrite <- H0 in *.
        revert v_vala Htia. rewrite Hv.
        intros v_vala Htia.

        generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        revert v_vala1 Htia1 v_vala2 Htia2.
        rewrite H2, H3.
        unfold bvtrue.
        rewrite Typ.cast_refl.

        intros v_vala1 Htia1 v_vala2 Htia2.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        rewrite Htia1 in HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2'
        = 
        interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia2 in HSp2.

        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Bval, interp_bv.

        rewrite (@check_symopp_bvor_nl bs1 bs2 bsres N).

        assert (
          H100: (N.of_nat
            (Datatypes.length
               (RAWBITVECTOR_LIST.map2 orb (map (Lit.interp rho) bs1)
                  (map (Lit.interp rho) bs2)))) = N).
        rewrite andb_true_iff in Heq11.
        {
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          specialize (@RAWBITVECTOR_LIST.map2_or_length 
            (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
          intros. rewrite <- H6.
          now rewrite map_length.
          apply check_symopp_bvor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite !map_length, Heq11a, Heq11b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        generalize (
          BITVECTOR_LIST.of_bits_size (RAWBITVECTOR_LIST.map2 orb 
          (map (Lit.interp rho) bs1) 
          (map (Lit.interp rho) bs2))
        ).

        rewrite H100.
        rewrite Typ.cast_refl. intros.

        unfold BITVECTOR_LIST.bv_or, RAWBITVECTOR_LIST.bv_or.
        unfold RAWBITVECTOR_LIST.size.
        unfold RAWBITVECTOR_LIST.bits.

        unfold interp_bv in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite <- Heq11a in Heq11b.
          rewrite <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp2.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)
        ).

        rewrite H101. intros.

        assert (
        H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp1.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)
        ).

        rewrite H102. intros.

        rewrite Typ.cast_refl in *.
        rewrite HSp1, HSp2. simpl.
        apply eq_rec. simpl.
        rewrite H101, H102.
        rewrite N.eqb_compare, N.compare_refl. easy.
        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).
        exact Heq11.

       (** symmetric case*)
        rewrite Heq10a1, Heq10a2 in *.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp2.
        rewrite Htia1 in HSp2.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2'
        = 
        interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp1.
        simpl in HSp1.
        rewrite Htia2 in HSp1.

        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Bval, interp_bv.

        rewrite (@check_symopp_bvor_nl bs1 bs2 bsres N).

        assert (
          H100: (N.of_nat
            (Datatypes.length
               (RAWBITVECTOR_LIST.map2 orb (map (Lit.interp rho) bs1)
                  (map (Lit.interp rho) bs2)))) = N).
        rewrite andb_true_iff in Heq11.
        {
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          specialize (@RAWBITVECTOR_LIST.map2_or_length 
            (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
          intros. rewrite <- H6.
          apply check_symopp_bvor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite map_length.
          apply check_symopp_bvor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite !map_length, Heq11a, Heq11b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        generalize (
          BITVECTOR_LIST.of_bits_size (RAWBITVECTOR_LIST.map2 orb 
          (map (Lit.interp rho) bs1) 
          (map (Lit.interp rho) bs2))
        ).

        rewrite H100.
        rewrite Typ.cast_refl. intros.

        unfold BITVECTOR_LIST.bv_or, RAWBITVECTOR_LIST.bv_or.
        unfold RAWBITVECTOR_LIST.size.
        unfold RAWBITVECTOR_LIST.bits.

        unfold interp_bv in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite <- Heq11a in Heq11b.
          rewrite <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }
        revert HSp2.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)
        ).

        rewrite H101. intros.

        assert (
        H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp1.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)
        ).

        rewrite H102. intros.

        rewrite Typ.cast_refl in *.
        rewrite HSp1, HSp2. simpl.
        apply eq_rec. simpl.
        rewrite H101, H102.
        rewrite N.eqb_compare, N.compare_refl. 
        now rewrite RAWBITVECTOR_LIST.map2_or_comm.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).
        exact Heq11.

        (** BVxor **)
        - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); 
            simpl; intros Heq10; try (now apply C.interp_true).

        case_eq (
                 check_symopp bs1 bs2 bsres (BO_BVxor N) &&
                 (N.of_nat (Datatypes.length bs1) =? N)%N); 
        simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        unfold Atom.interp_form_hatom_bv at 2, Atom.interp_hatom.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Heq9. simpl.
        rewrite Atom.t_interp_wf; trivial.
        rewrite Atom.t_interp_wf; trivial.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a).
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.
        unfold get_type' in H2, H3. unfold v_type in H2, H3.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H3.
        case_eq (t_interp .[ a2']).
          intros v_typea2 v_vala2 Htia2. rewrite Htia2 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        rewrite Atom.t_interp_wf in Htia2; trivial.
        unfold apply_binop. rewrite Htia1, Htia2.
        apply Typ.eqb_spec in H2. apply Typ.eqb_spec in H3.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea).
          intros i j Hv. rewrite Hv in H0. now contradict H0.
          intros i Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros Hv. rewrite Hv in H0. now contradict H0.
          intros n Hv. rewrite Hv in H0.

        (** n = N **)
        apply N.eqb_eq in H0.
        rewrite <- H0 in *.
        revert v_vala Htia. rewrite Hv.
        intros v_vala Htia.

        generalize (Hs pos1). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        generalize (Hs pos2). intro HSp2. unfold C.valid in HSp2. rewrite Heq2 in HSp2.
        unfold C.interp in HSp2. unfold existsb in HSp2. rewrite orb_false_r in HSp2.
        unfold Lit.interp in HSp2. rewrite Heq4 in HSp2. unfold Var.interp in HSp2.
        rewrite rho_interp in HSp2. rewrite Heq7 in HSp2. simpl in HSp2.

        revert v_vala1 Htia1 v_vala2 Htia2.
        rewrite H2, H3.
        unfold bvtrue.
        rewrite Typ.cast_refl.

        intros v_vala1 Htia1 v_vala2 Htia2.

        (** case a1 = a1' and a2 = a2' **)
        rewrite orb_true_iff in Heq10.
        do 2 rewrite andb_true_iff in Heq10.
        destruct Heq10 as [Heq10 | Heq10];
          destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2.
        rewrite Heq10a1, Heq10a2 in *.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }
          rewrite H4 in HSp1.
          rewrite Htia1 in HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2'
        = 
        interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        simpl in HSp2.
        rewrite Htia2 in HSp2.

        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Bval, interp_bv.

        rewrite (@check_symopp_bvxor_nl bs1 bs2 bsres N).

        assert (
          H100: (N.of_nat
            (Datatypes.length
               (RAWBITVECTOR_LIST.map2 xorb (map (Lit.interp rho) bs1)
                  (map (Lit.interp rho) bs2)))) = N).
        rewrite andb_true_iff in Heq11.
        {
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          specialize (@RAWBITVECTOR_LIST.map2_xor_length 
            (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
          intros. rewrite <- H6.
          now rewrite map_length.
          apply check_symopp_bvxor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite !map_length, Heq11a, Heq11b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        generalize (
          BITVECTOR_LIST.of_bits_size (RAWBITVECTOR_LIST.map2 xorb 
          (map (Lit.interp rho) bs1) 
          (map (Lit.interp rho) bs2))
        ).

        rewrite H100.
        rewrite Typ.cast_refl. intros.

        unfold BITVECTOR_LIST.bv_xor, RAWBITVECTOR_LIST.bv_xor.
        unfold RAWBITVECTOR_LIST.size.
        unfold RAWBITVECTOR_LIST.bits.

        unfold interp_bv in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite <- Heq11a in Heq11b.
          rewrite <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp2.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)
        ).

        rewrite H101. intros.

        assert (
        H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp1.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)
        ).

        rewrite H102. intros.

        rewrite Typ.cast_refl in *.
        rewrite HSp1, HSp2. simpl.
        apply eq_rec. simpl.

        rewrite H101, H102.
        rewrite N.eqb_compare, N.compare_refl. easy.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).
        exact Heq11.

       (** symmetric case*)
        rewrite Heq10a1, Heq10a2 in *.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp2.
        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp2.
        rewrite Htia1 in HSp2.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2'
        = 
        interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp1.
        simpl in HSp1.
        rewrite Htia2 in HSp1.

        apply BITVECTOR_LIST.bv_eq_reflect.
        unfold Bval, interp_bv.

        rewrite (@check_symopp_bvxor_nl bs1 bs2 bsres N).

        assert (
          H100: (N.of_nat
            (Datatypes.length
               (RAWBITVECTOR_LIST.map2 xorb (map (Lit.interp rho) bs1)
                  (map (Lit.interp rho) bs2)))) = N).
        rewrite andb_true_iff in Heq11.
        {
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          specialize (@RAWBITVECTOR_LIST.map2_xor_length 
            (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)).
          intros. rewrite <- H6.
          apply check_symopp_bvxor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite map_length.
          apply check_symopp_bvxor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          now rewrite !map_length, Heq11a, Heq11b.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        generalize (
          BITVECTOR_LIST.of_bits_size (RAWBITVECTOR_LIST.map2 xorb 
          (map (Lit.interp rho) bs1) 
          (map (Lit.interp rho) bs2))
        ).

        rewrite H100.
        rewrite Typ.cast_refl. intros.

        unfold BITVECTOR_LIST.bv_xor, RAWBITVECTOR_LIST.bv_xor.
        unfold RAWBITVECTOR_LIST.size.
        unfold RAWBITVECTOR_LIST.bits.

        unfold interp_bv in HSp1, HSp2.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits in HSp1, HSp2.

        assert (
          H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_symopp_bvxor_length2 in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite <- Heq11a in Heq11b.
          rewrite <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp2.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)
        ).

        rewrite H101. intros.

        assert (
        H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        revert HSp1.

        generalize (
        BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)
        ).

        rewrite H102. intros.

        rewrite Typ.cast_refl in *.
        rewrite HSp1, HSp2. simpl.
        apply eq_rec. simpl.
        rewrite H101, H102.
        rewrite N.eqb_compare, N.compare_refl. 
        now rewrite RAWBITVECTOR_LIST.map2_xor_comm.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11, Heq11r).
        exact Heq11.
Qed.

Lemma check_symopp_eq: forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres n,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_eq (Typ.TBV n)) = true ->
      check_symopp xbs1 ybs2 zbsres (BO_eq (Typ.TBV n))  = true.
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

Lemma check_symopp_eq': forall ibs1 ibs2 xbs1 ybs2 ibsres zbsres n,
      check_symopp (ibs1 :: xbs1) (ibs2 :: ybs2) (ibsres :: zbsres) (BO_eq (Typ.TBV n)) = true ->
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

Lemma  check_symopp_bveq: forall bs1 bs2 a4 n, check_symopp bs1 bs2 (to_list a4) (BO_eq (Typ.TBV n)) = true ->
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

Lemma prop_check_eq: forall bs1 bs2 bsres,
      (length bs1) = (length bs2) ->
      check_eq bs1 bs2 bsres = true ->
      forallb2 Bool.eqb (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
      forallb (Lit.interp rho) bsres.
Proof. intro bs1.
  induction bs1 as [ | x1 bs1 IHbs1 ].
  - intros bs2 bsres Hlen Hcheck.
    case bs2 in *.
    + case bsres in *.
      * now simpl.
      * contradict Hcheck; now simpl.
    + contradict Hcheck; now simpl.
  - intros bs2 bsres Hlen Hcheck.
    symmetry.
    case bs2 in *.
    + case bsres in *; contradict Hcheck; now simpl.
    + case bsres in *.
      * contradict Hcheck; now simpl.
      * simpl.
        rename i into x2. rename i0 into r1.
        simpl in Hlen. inversion Hlen.
        rename H0 into Hlen'.

        case bsres in *.
        (*--*) simpl in Hcheck.
           case_eq (Lit.is_pos r1); intros; rewrite H in Hcheck;
           try (case bs1 in *; try (now contradict Hcheck); case bs2 in *;
                try (now contradict Hcheck));
           rename H into Hposr1;
           case_eq (t_form .[ Lit.blit r1]);intros; rewrite H in Hcheck; try (now contradict Hcheck); 
           rename H into Hform_r1;
           generalize (rho_interp (Lit.blit r1)); rewrite Hform_r1; simpl;
           intro Hi.
           (*++*) rename i into arg1; rename i0 into arg2.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi. repeat (rewrite andb_true_r).
              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
              (* ** *) intros Hif.
                 rewrite orb_true_iff in Hif.
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). now rewrite Hx1, Hx2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                     now rewrite bool_eqb_comm.
             (* ** *)intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.

           (* ++ *)
             case_eq (to_list a);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Ha, i1 into a1, l into rargs.
              case_eq (Lit.is_pos a1);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Hposa1.
              case_eq (t_form .[ Lit.blit a1]);
                intros; rewrite H in Hcheck; try (now contradict Hcheck).
              rename H into Hform_a1.
              rename i into x1', i0 into x2', i1 into arg1, i2 into arg2.
              generalize (rho_interp (Lit.blit a1)). rewrite Hform_a1. simpl.
              intro Heqx1x2.
              rewrite afold_left_and in Hi.
              rewrite Ha in Hi. simpl in Hi.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi. repeat (rewrite andb_true_r).
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposa1. rewrite Heqx1x2.

              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
              (* ** *) intros Hif.
                 rewrite Hif in Hcheck.
                 apply (@IHbs1 _ _ Hlen') in Hcheck.
                 simpl in Hcheck. rewrite Hcheck.
                 repeat (rewrite orb_true_iff in Hif).
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). now rewrite Hx1, Hx2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                     now rewrite bool_eqb_comm.
              (* ** *) intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.

       (* -- *) simpl in Hcheck.
           case_eq (Lit.is_pos r1); intros; rewrite H in Hcheck;
           try (case bs1 in *; try (now contradict Hcheck); case bs2 in *;
                try (now contradict Hcheck));
           rename H into Hposr1;
           case_eq (t_form .[ Lit.blit r1]);intros; rewrite H in Hcheck; try (now contradict Hcheck); 
           rename H into Hform_r1;
           generalize (rho_interp (Lit.blit r1)); rewrite Hform_r1; simpl;
           intro Hi.
          (* ++ *) contradict Hcheck. simpl.
              case ((i0 == x1) && (i1 == x2) || (i0 == x2) && (i1 == x1)); easy.
          (* ++ *) rename i0 into x1', i1 into x2', i2 into arg1, i3 into arg2.
              unfold Lit.interp at 1, Var.interp at 1.
              rewrite Hposr1, Hi.
              case_eq ((arg1 == x1) && (arg2 == x2) || (arg1 == x2) && (arg2 == x1)).
             (* ** *) intros Hif. rewrite Hif in Hcheck.
                 apply (@IHbs1 _ _ Hlen') in Hcheck.
                 simpl in Hcheck. rewrite Hcheck.
                 repeat (rewrite orb_true_iff in Hif).
                 repeat (rewrite andb_true_iff in Hif).
                 repeat (rewrite eqb_spec in Hif).
                 destruct Hif as [ Hif1 | Hif2 ].
                (* --- *) destruct Hif1 as (Hx1, Hx2). now rewrite Hx1, Hx2.
                (* --- *) destruct Hif2 as (Hx2, Hx1). rewrite Hx1, Hx2.
                     now rewrite bool_eqb_comm.
            (*  ** *) intros Hif. rewrite Hif in Hcheck. now contradict Hcheck.
Qed.

Lemma length_check_eq: forall bs1 bs2 bsres,
  check_eq bs1 bs2 bsres = true -> length bs1 = length bs2.
Proof.
  intro bs1.
  induction bs1.
  + intros. case bs2 in *. trivial.
    simpl in H. now contradict H.
  + intros.
    case bs2 in *.
    - simpl in H. now contradict H.
    - simpl. apply f_equal.
      simpl in H.
      revert H.
      case bsres. easy.
      intros r rl.
      case rl.
      case (Lit.is_pos r).
      case (t_form .[ Lit.blit r]); try easy.
      intro a0.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      case bs1 in *; try easy; case bs2; try easy.
      intros i1 l a0.
      case (to_list a0); try easy.
      intros i2 l0.
      case (Lit.is_pos i2); try easy.
      case (t_form .[ Lit.blit i2]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      intros _ _ i2 l0 a0.
      case (to_list a0); try easy.
      intros i1 l.
      case (Lit.is_pos i1); try easy.
      case (t_form .[ Lit.blit i1]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      intros i2 l0 a0.
      case (to_list a0); try easy.
      intros i9 l.
      case (Lit.is_pos i9); try easy.
      case (t_form .[ Lit.blit i9]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      intros _ _ i2 l0 a0.
      case (to_list a0); try easy.
      intros i9 l.
      case (Lit.is_pos i9); try easy.
      case (t_form .[ Lit.blit i9]); try easy.
      intros i3 i4.
      case ((i3 == a) && (i4 == i) || (i3 == i) && (i4 == a)).
      apply IHbs1.
      easy.
      case bs1; try easy; case bs2; easy.
      case bs1; try easy; case bs2; easy.
      case bs1; try easy; case bs2; easy.
      case bs1; try easy; case bs2.

      simpl. easy.

      intros i0 l i1 i2.
      case ((i1 == a) && (i2 == i) || (i1 == i) && (i2 == a)); easy.
      simpl.
      intros _ l i1 i2.
      case ((i1 == a) && (i2 == i) || (i1 == i) && (i2 == a)); easy.
      easy.
      case bs1 in *; try easy; case bs2; easy.
      case bs1 in *; try easy; case bs2; easy.
      case bs1 in *; try easy; case bs2; easy.
      case bs1 in *; try easy; case bs2; try easy.
      case (Lit.is_pos r); try easy.
      case (t_form .[ Lit.blit r]); try easy.
      simpl. intros x y. case ((x == a) && (y == i) || (x == i) && (y == a)); easy.
      case (Lit.is_pos r); try easy.
      case (t_form .[ Lit.blit r]); try easy.
      simpl. intros x y. case ((x == a) && (y == i) || (x == i) && (y == a)); easy.
      case (Lit.is_pos r); try easy.
      case (t_form .[ Lit.blit r]); try easy.
      intros x y. case ((x == a) && (y == i) || (x == i) && (y == a)).
      intros x2 rbs2 xr rbrs.
      apply IHbs1. easy.
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
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)); try (intros; now apply C.interp_true). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

       intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N|N|N|N|N| | ]; 
          try (intros; now apply C.interp_true).

       intros n0 a1' a2' Heq9.
       case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1')); 
         simpl; intros Heq15; try (now apply C.interp_true).

       case_eq (check_eq bs1 bs2 [bsres] &&
       (N.of_nat (Datatypes.length bs1) =? n0)%N); 
       simpl; intros Heq16; try (now apply C.interp_true).

       unfold C.valid. simpl.
       rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.

       case_eq (v_typea3); intros; rewrite H4 in H0; try (now contradict H0).
       rename H4 into Hv.

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
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1.

        (* interp_form_hatom_bv a2' =  
                 interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2.

        generalize dependent v_vala1. generalize dependent v_vala2.

        rewrite H2, H3.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (
        H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = n0
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as (Heq16, Heq16r).
          rewrite N.eqb_eq in Heq16r.
          apply length_check_eq in Heq16.
          rewrite Heq16 in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H100.
        rewrite Typ.cast_refl.

        assert (
        H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = n0
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as (Heq16, Heq16r).
          rewrite N.eqb_eq in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite !Typ.cast_refl. intros.

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
        rewrite Typ.N_cast_refl. simpl.

        rewrite Form.wf_interp_form; trivial.
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.
        simpl.

        rewrite Typ.i_eqb_t. simpl.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        unfold RAWBITVECTOR_LIST.size.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        rewrite andb_true_iff in Heq16.
        destruct Heq16 as (Heq16 & Heq16r).
        rewrite N.eqb_eq in Heq16r. simpl.
        pose proof Heq16 as Heq16p.

        apply length_check_eq in Heq16.
        rewrite !map_length, Heq16.
        rewrite N.eqb_compare, N.compare_refl.
        pose proof (Heq16) as Hleq.

        rewrite (@prop_check_eq _ _ [bsres]). simpl.
        rewrite andb_true_r. unfold Lit.interp, Var.interp.
        generalize (rho_interp (Lit.blit bsres)). simpl.
        intro Hbres. rewrite Hbres. simpl.
        rewrite Hpos.
        simpl. now unfold Atom.interp_form_hatom, interp_hatom.
        exact Hleq.

        exact Heq16p.

        intros Hpos.
        rewrite andb_true_iff in Heq16.
        destruct Heq16 as (Heq16 & Heq16r).

        contradict Heq16.
        case bs1 in *; try now simpl; case bs2 in *; now simpl.
        case bs2 in *. simpl. easy.
        simpl. rewrite Hpos. case bs1; intros; auto; case bs2; auto.

        pose proof Heq16 as Heq16'.

        rewrite andb_true_iff in Heq16.
        destruct Heq16 as (Heq16 & Heq16r).
        apply length_check_eq in Heq16; auto.

       (** case symmetry **)


        (* interp_form_hatom_bv a1' = 
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' =
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2.

        (* interp_form_hatom_bv a2' =
                 interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1.

        generalize dependent v_vala1. generalize dependent v_vala2.

        rewrite H2, H3.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (
        H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = n0
        ).
        {
          rewrite N.eqb_eq in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H100.
        rewrite !Typ.cast_refl.

        assert (
        H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = n0
        ).
        {
          rewrite N.eqb_eq in Heq16r.
          rewrite Heq16 in Heq16r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H101.
        rewrite Typ.cast_refl.

        intros.
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
        rewrite Typ.N_cast_refl. simpl.

        rewrite Form.wf_interp_form; trivial.
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.
        simpl.

        rewrite Typ.i_eqb_t. simpl.

        unfold BITVECTOR_LIST.bv_eq.
        unfold RAWBITVECTOR_LIST.bv_eq, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        unfold RAWBITVECTOR_LIST.size.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        rewrite beq_list_comm.
        rewrite !map_length, Heq16, N.eqb_compare, N.compare_refl.

        rewrite (@prop_check_eq _ _ [bsres]). simpl.
        rewrite andb_true_r. unfold Lit.interp, Var.interp.
        generalize (rho_interp (Lit.blit bsres)). simpl.
        intro Hbres. rewrite Hbres.

        rewrite andb_true_iff in Heq16'.
        destruct Heq16' as (Heq16' & Heq16'r).
        rewrite Hpos.
        now unfold Atom.interp_form_hatom, interp_hatom.
        intros. exact Heq16.

        rewrite andb_true_iff in Heq16'.
        destruct Heq16' as (Heq16' & Heq16'r).
        exact Heq16'.

        intros Hpos.
        contradict Heq16'.
        case bs1 in *; try now simpl; case bs2 in *; now simpl.
        case bs2 in *; try now simpl; case bs2 in *; now simpl.
        simpl. easy.
        simpl.
        case bs1 in *; try now simpl; case bs2 in *; now simpl.
        rewrite Hpos.
        case bs2 in *; try now simpl; case bs2 in *; now simpl.
        now rewrite andb_false_l.

        case bs2 in *; rewrite Hpos; simpl; easy.
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
    case_eq (PArray.length a == 2). intros Hl. rewrite Hl in H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.
    rewrite afold_left_and in rho_interp.
    rewrite eqb_spec in Hl.
    apply to_list_two in Hl.
    rewrite Hl in rho_interp.
    simpl in rho_interp.
    rewrite andb_true_r in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. now rewrite andb_comm. *)
    + intros. rewrite H3 in H. now contradict H.
    + intros. rewrite H2 in H. now contradict H.

  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. now rewrite xorb_comm. *)
    + intros. rewrite H2 in H. now contradict H.

  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    case_eq (PArray.length a == 2). intros Hl. rewrite Hl in H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.
    rewrite afold_left_or in rho_interp.
    rewrite eqb_spec in Hl.
    apply to_list_two in Hl.
    rewrite Hl in rho_interp.
    simpl in rho_interp.
    rewrite orb_false_r in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. now rewrite orb_comm. *)
    + intros. rewrite H3 in H. now contradict H.
    + intros. rewrite H2 in H. now contradict H.

  - intros. simpl. 
    pose proof IHc1. pose proof IHc2.
    simpl in H.
    case_eq ( Lit.is_pos i). intros Hip0.
    rewrite Hip0 in H.
    case_eq (t_form .[ Lit.blit i]); intros; rewrite H2 in H; try now contradict H.
    (* rewrite orb_true_iff in H; do 2 *) rewrite andb_true_iff in H.

    specialize (@rho_interp ( Lit.blit i)). rewrite H2 in rho_interp.
    simpl in rho_interp.

    (* destruct H. *)
    + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3.
      unfold Lit.interp at 3. unfold Var.interp.
      rewrite Hip0. now rewrite rho_interp.
    (* + destruct H. apply H0 in H. apply H1 in H3. rewrite H, H3. *)
    (*   unfold Lit.interp at 3. unfold Var.interp. *)
    (*   rewrite Hip0. rewrite rho_interp. *)
    (*   case_eq (Bool.eqb (Lit.interp rho i0) (Lit.interp rho i1)). *)
    (*   intros. apply Bool.eqb_prop in H4. rewrite H4. apply Bool.eqb_reflx. *)
    (*   intros. apply Bool.eqb_false_iff in H4. apply Bool.eqb_false_iff. unfold not in *. intro. symmetry in H5. *)
    (*   apply H4; trivial. *)
    + intros. rewrite H2 in H. now contradict H.
Qed.



Lemma map_cons T U (f: T -> U) (h: T) (l: list T): map f (h :: l) = f h :: map f l.
Proof. auto. Qed.

Lemma prop_check_ult: forall bs1 bs2, 
  length bs1 = length bs2 ->
  RAWBITVECTOR_LIST.ult_list_big_endian
    (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
  = interp_carry (ult_big_endian_lit_list bs1 bs2).
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1 ].
       - intros. simpl in *. 
         symmetry in H; rewrite empty_list_length in H.
         specialize (Lit.interp_false rho wf_rho).
         intros. unfold is_true in H0; now rewrite not_true_iff_false in H0.
       - intros.
         case_eq bs2. intros. rewrite H0 in *. now contradict H.
         intros. rewrite H0 in *.
         inversion H.
         rewrite !map_cons.
         simpl.
         case xsbs1 in *. simpl.
         case l in *. simpl. now rewrite Lit.interp_neg.
         now contradict H2.
         case l in *. simpl.
         now contradict H2. 
         rewrite !map_cons.
         unfold interp_carry.
         fold interp_carry.
         specialize (@IHbs1 (i1 :: l)).
         rewrite !map_cons in IHbs1.
         rewrite Lit.interp_neg.
         now rewrite IHbs1.
Qed.

Lemma prop_check_slt: forall bs1 bs2, 
  length bs1 = length bs2 ->
  RAWBITVECTOR_LIST.slt_list_big_endian
    (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
  = interp_carry (slt_big_endian_lit_list bs1 bs2).
Proof. intros.
       case bs1 in *. simpl.
       specialize (Lit.interp_false rho wf_rho).
         intros. unfold is_true in H0; now rewrite not_true_iff_false in H0.
       case bs2 in *.
         now contradict H.
         rewrite !map_cons.
         case bs1 in *. simpl.
         case bs2 in *. simpl. now rewrite Lit.interp_neg. 
         now contradict H.
         case bs2 in  *.
           now contradict H.
           unfold slt_big_endian_lit_list.
           unfold RAWBITVECTOR_LIST.slt_list_big_endian.
           rewrite !map_cons.
           unfold interp_carry.
           fold interp_carry.
           rewrite <- !map_cons.
           rewrite Lit.interp_neg.
           rewrite prop_check_ult.
           now apply f_equal.
           simpl.
           now inversion H.
Qed.

Lemma prop_check_ult2: forall bs1 bs2 bsres,
length bs1 = length bs2 ->
check_ult bs1 bs2 bsres = true ->
interp_carry (ult_big_endian_lit_list (rev bs1) (rev bs2)) = Lit.interp rho bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros.
         case bs2 in *.
         unfold check_ult in H0.
         simpl in *.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.
         case (Lit.is_pos bsres) in H0; rewrite eqb_spec in H0; now rewrite H0.
         intros. rewrite H1 in H0. now contradict H0.

         now contradict H.

       - intros.
         case bs2 in *.
         now contradict H.
         simpl.
         unfold check_ult,ult_lit_list in H0.
         simpl in H0.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.

         now apply prop_eq_carry_lit.

         intros. rewrite H1 in H0. now contradict H0.
Qed.

Lemma prop_check_slt2: forall bs1 bs2 bsres,
length bs1 = length bs2 ->
check_slt bs1 bs2 bsres = true ->
interp_carry (slt_big_endian_lit_list (rev bs1) (rev bs2)) = Lit.interp rho bsres.
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1].
       - intros.
         case bs2 in *.
         unfold check_slt in H0.
         simpl in *.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.
         case (Lit.is_pos bsres) in H0; rewrite eqb_spec in H0; now rewrite H0.
         intros. rewrite H1 in H0. now contradict H0.

         now contradict H.

       - intros.
         case bs2 in *.
         now contradict H.
         simpl.
         unfold check_slt, slt_lit_list in H0.
         simpl in H0.
         case_eq (Lit.is_pos bsres). intros Hbsres.
         rewrite Hbsres in H0.
         now apply prop_eq_carry_lit.

         intros. rewrite H1 in H0. now contradict H0.
Qed.

Lemma prop_lit: forall bsres, 
Lit.is_pos bsres = true ->
Lit.interp 
  (interp_state_var (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
     interp_form_hatom_bv t_form) bsres =
Form.interp (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
  interp_form_hatom_bv t_form (t_form .[ Lit.blit bsres]).
Proof. intros.
       rewrite <- rho_interp.
       simpl.
       unfold Lit.interp, Var.interp.
       rewrite H.
       simpl. easy.
Qed.

Lemma prop_lit2: forall bsres, 
Lit.is_pos bsres = false ->
Lit.interp 
  (interp_state_var (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
     interp_form_hatom_bv t_form) bsres =
negb (Form.interp (fun a0 : int => interp_bool t_i (t_interp .[ a0]))
  interp_form_hatom_bv t_form (t_form .[ Lit.blit bsres])).
Proof. intros.
       rewrite <- rho_interp.
       simpl.
       unfold Lit.interp, Var.interp.
       rewrite H.
       simpl. easy.
Qed.

Lemma valid_check_bbUlt pos1 pos2 lres : C.valid rho (check_bbUlt pos1 pos2 lres).
Proof.
      unfold check_bbUlt.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)); try (intros; now apply C.interp_true). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

       intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N|N|N|N|N| | ]; 
         try (intros; now apply C.interp_true).

       intros a1' a2' Heq9.
         case_eq ((a1 == a1') && (a2 == a2')); simpl; intros Heq15; try (now apply C.interp_true).

       case_eq (check_ult bs1 bs2 bsres &&
          (N.of_nat (Datatypes.length bs1) =? N)%N &&
          (N.of_nat (Datatypes.length bs2) =? N)%N); 
       simpl; intros Heq16; try (now apply C.interp_true).

       unfold C.valid. simpl.

       rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.
       case_eq (v_typea3);  intros; rewrite H4 in H0; try (now contradict H0).
       rename H4 into Hv.

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
       rewrite andb_true_iff in Heq15.
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.


        (* interp_form_hatom_bv a1' =
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' =
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1.

        (* interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2.

        generalize dependent v_vala1. generalize dependent v_vala2.

        rewrite H2, H3.

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (
        H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite N.eqb_eq in Heq16c.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H100.

        assert (
        H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite N.eqb_eq in Heq16b.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).       

        rewrite H101.

        rewrite Typ.cast_refl in *.

        intros.
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
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        unfold BITVECTOR_LIST.bv_ult.
        unfold RAWBITVECTOR_LIST.bv_ult, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        simpl.
        unfold RAWBITVECTOR_LIST.size.
        simpl.

        rewrite !Typ.N_cast_refl.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite N.eqb_eq in Heq16r, Heq16l.
        rewrite map_length, Heq16l.
        rewrite H100.
        rewrite N.eqb_compare. rewrite N.compare_refl.

        unfold RAWBITVECTOR_LIST.ult_list.
        specialize (@prop_check_ult (List.rev bs1) (List.rev bs2)).
        intros.

        cut ( Datatypes.length (List.rev bs1) = Datatypes.length (List.rev bs2)).
        intros. specialize (H6 H7).
        do 2 rewrite <- List.map_rev.
        rewrite H6.

        pose proof (rho_interp).
        specialize (H8 (Lit.blit a)).
        rewrite Heq10 in H8.
        simpl in H8.

        rewrite !rev_length in H7.
        specialize (@prop_check_ult2 bs1 bs2 bsres H7 Heq16).
        intros.
        rewrite H9.
        simpl.       
        unfold Atom.interp_form_hatom, interp_hatom.
        simpl.
        now rewrite prop_lit.

        rewrite !rev_length.
        apply (f_equal nat_of_N) in Heq16l.
        apply (f_equal nat_of_N) in Heq16r.
        rewrite Nat2N.id in Heq16l, Heq16r.
        now rewrite Heq16l, Heq16r.

        intros.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite N.eqb_eq in Heq16r, Heq16l.

        contradict Heq16.
        unfold check_ult.
        rewrite H6. easy.
Qed.

Lemma valid_check_bbSlt pos1 pos2 lres : C.valid rho (check_bbSlt pos1 pos2 lres).
Proof.
      unfold check_bbSlt.
       case_eq (S.get s pos1); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
       case_eq (S.get s pos2); [intros _|intros l2 [ |l] Heq2]; try now apply C.interp_true.
       case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos l2); intro Heq4; simpl; try now apply C.interp_true.
       case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
       case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
       case_eq (t_form .[ Lit.blit l2]); try (intros; now apply C.interp_true). intros a2 bs2 Heq7.
       case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true). intros a bsres Heq8.
       case_eq (Bool.eqb (Lit.is_pos a) (Lit.is_pos bsres)); try (intros; now apply C.interp_true). intros Heq12.
       case_eq (t_form .[ Lit.blit a]); try (intros; now apply C.interp_true). intros a3 Heq10.
       case_eq (t_atom .[ a3]); try (intros; now apply C.interp_true).

       intros [ | | | | | | | [ A B | A | | | | ]|N|N|N|N|N|N|N|N|N| | ] a1' a2' Heq9; 
          try (intros; now apply C.interp_true).

       case_eq ((a1 == a1') && (a2 == a2')); simpl; intros Heq15; try (now apply C.interp_true).

       case_eq (check_slt bs1 bs2 bsres &&
          (N.of_nat (Datatypes.length bs1) =? N)%N &&
          (N.of_nat (Datatypes.length bs2) =? N)%N); 
       simpl; intros Heq16; try (now apply C.interp_true).

       unfold C.valid. simpl.

       rewrite orb_false_r.
       unfold Lit.interp. rewrite Heq5.
       unfold Var.interp.
       rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

       generalize wt_t_atom. unfold Atom.wt. unfold is_true.
       rewrite PArray.forallbi_spec;intros.

       pose proof (H a3).
       assert (a3 < PArray.length t_atom).
       { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
       specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
       rewrite !andb_true_iff in H0. destruct H0. destruct H0.

       unfold get_type' in H0. unfold v_type in H0.
       case_eq (t_interp .[ a3]).
       intros v_typea3 v_vala3 Htia3. rewrite Htia3 in H0.
       case_eq (v_typea3);  intros; rewrite H4 in H0; try (now contradict H0).
       rename H4 into Hv.

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
       rewrite andb_true_iff in Heq15.
       destruct Heq15 as (Heq15a1 & Heq15a2); rewrite eqb_spec in Heq15a1, Heq15a2
       ;rewrite Heq15a1, Heq15a2 in *.


        (* interp_form_hatom_bv a1' =
                 interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' =
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia1; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite !Atom.t_interp_wf in Htia1; trivial.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1.

        (* interp_form_hatom_bv a2' =
                 interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' =
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia2; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite !Atom.t_interp_wf in Htia2; trivial.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2.

        generalize dependent v_vala1. generalize dependent v_vala2.
        rewrite H2, H3. 

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (
        H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite N.eqb_eq in Heq16c.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H100.

        assert (
        H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N
        ).
        {
          rewrite !andb_true_iff in Heq16.
          destruct Heq16 as ((Heq16a, Heq16b), Heq16c).
          rewrite N.eqb_eq in Heq16b.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).       

        rewrite H101.

        rewrite Typ.cast_refl in *.

        intros.

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
        simpl.
        apply Bool.eqb_prop in Heq12.
        rewrite Heq12.
        rewrite HSp1, HSp2.

        case_eq (Lit.is_pos bsres).
        intros Hpos.

        unfold BITVECTOR_LIST.bv_slt.
        unfold RAWBITVECTOR_LIST.bv_slt, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.bv, BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.
        simpl.
        unfold RAWBITVECTOR_LIST.size.
        simpl.

        rewrite !Typ.N_cast_refl.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite N.eqb_eq in Heq16r, Heq16l.
        rewrite map_length, Heq16l.
        rewrite H100.
        rewrite N.eqb_compare. rewrite N.compare_refl.

        unfold RAWBITVECTOR_LIST.slt_list.
        specialize (@prop_check_slt (List.rev bs1) (List.rev bs2)).
        intros.

        cut ( Datatypes.length (List.rev bs1) = Datatypes.length (List.rev bs2)).
        intros. specialize (H6 H7).
        do 2 rewrite <- List.map_rev.
        rewrite H6.

        pose proof (rho_interp).
        specialize (H8 (Lit.blit a)).
        rewrite Heq10 in H8.
        simpl in H8.

        rewrite !rev_length in H7.
        specialize (@prop_check_slt2 bs1 bs2 bsres H7 Heq16).
        intros.
        rewrite H9.
        simpl.
        unfold Atom.interp_form_hatom, interp_hatom.
        simpl.
        now rewrite prop_lit.

        rewrite !rev_length.
        apply (f_equal nat_of_N) in Heq16l.
        apply (f_equal nat_of_N) in Heq16r.
        rewrite Nat2N.id in Heq16l, Heq16r.
        now rewrite Heq16l, Heq16r.

        intros.
        rewrite !andb_true_iff in Heq16.
        destruct Heq16 as ((Heq16 & Heq16l) & Heq16r).
        rewrite N.eqb_eq in Heq16r, Heq16l.

        contradict Heq16.
        unfold check_slt.
        rewrite H6. easy.
Qed.

Lemma check_add_list:forall bs1 bs2 bsres c, 
  let n := length bsres in
  (length bs1 = n)%nat -> 
  (length bs2 = n)%nat -> 
  check_add bs1 bs2 bsres c ->
                      (RAWBITVECTOR_LIST.add_list_ingr (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2)
                        (interp_carry c))
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
        unfold is_true in H1.
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

        (** rho_interp Lit.blit i1 **)
        pose proof (rho_interp (Lit.blit i1)).
        rewrite H7 in H12. simpl in H12.

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

Lemma check_add_bvadd: forall bs1 bs2 bsres n, 
  (N.of_nat(length bs1) = n)%N -> 
  (N.of_nat(length bs2) = n)%N -> 
  (N.of_nat(length bsres) = n)%N ->  
  check_add bs1 bs2 bsres (Clit Lit._false) = true ->
  (RAWBITVECTOR_LIST.bv_add (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
   (map (Lit.interp rho) bsres)).
Proof. intros.
       pose proof H as H'. pose proof H0 as H0'. pose proof H1 as H1'.
       rewrite <- H1 in H. apply Nat2N.inj in H.
       rewrite <- H1 in H0. apply Nat2N.inj in H0.
       specialize (@check_add_list bs1 bs2 bsres ( (Clit Lit._false)) H H0 H2). intros.
       unfold RAWBITVECTOR_LIST.bv_add.
       unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits.
       unfold BITVECTOR_LIST.of_bits.
       rewrite !map_length, H, H0.
       rewrite N.eqb_refl.

       assert (  (interp_carry (Clit Lit._false)) = false).
       {
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H4.
         rewrite not_true_iff_false in H4.
         now unfold interp_carry.
       }

       rewrite H4 in H3.
       unfold RAWBITVECTOR_LIST.add_list.
       apply H3.
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
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N|N|N|N|N| | ] a1' a2' Heq9;
        try (intros; now apply C.interp_true).

      (* BVadd *)
      - case_eq ((a1 == a1') && (a2 == a2') || (a1 == a2') && (a2 == a1'));
            simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (
                 check_add bs1 bs2 bsres (Clit Lit._false) &&
                 (N.of_nat (Datatypes.length bs1) =? N)%N
        ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply BITVECTOR_LIST.bv_eq_reflect.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

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
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite N.eqb_eq in Heq11r.
          rewrite Heq11a in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.

        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }
        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. 

        revert HSp1.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }
        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. 

        revert HSp2.

        assert (H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Heq11a, <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2.

        pose proof Heq11.
        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite N.eqb_eq in Heq11r.

        apply check_add_bvadd_length in Heq11.

        unfold BITVECTOR_LIST.bv_add. simpl.
        apply eq_rec.
        simpl.

        specialize (@check_add_bvadd bs1 bs2 bsres N).

        intros. apply H8.
        exact Heq11r.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite <- Heq11b in Heq11a.
        rewrite Heq11a in Heq11r. easy.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite Heq11a in Heq11r. easy.
        rewrite andb_true_iff in H7.
        destruct H7 as (H7 & H7r).
        exact H7.

        (** symmetic case **)


        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite N.eqb_eq in Heq11r.
          rewrite Heq11a in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia1 in HSp2.
        unfold interp_bv in HSp2.

        revert HSp2.

        assert (H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          apply check_add_bvadd_length in Heq11.
          destruct Heq11 as (Heq11a, Heq11b).
          rewrite Heq11a, <- Heq11b in Heq11r.
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia2 in HSp1.
        unfold interp_bv in HSp1.

        revert HSp1.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        pose proof Heq11.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite N.eqb_eq in Heq11r.

        apply check_add_bvadd_length in Heq11.

        unfold BITVECTOR_LIST.bv_add. simpl.
        apply eq_rec.
        simpl.

        specialize (@RAWBITVECTOR_LIST.bv_add_comm N).
        intros. rewrite H8.

        specialize (@check_add_bvadd bs1 bs2 bsres N).

        intros. apply H9.
        exact Heq11r.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite <- Heq11b in Heq11a.
        rewrite Heq11a in Heq11r. easy.
        destruct Heq11 as (Heq11a & Heq11b).
        rewrite Heq11a in Heq11r. easy.

        rewrite andb_true_iff in H7.
        destruct H7 as (H7 & H7r).
        exact H7.

        unfold RAWBITVECTOR_LIST.size.
        destruct Heq11 as (Heq11a, Heq11b).
        rewrite <- Heq11a in Heq11b.
        rewrite <- Heq11b in Heq11r.
        now rewrite map_length.

        unfold RAWBITVECTOR_LIST.size.
        now rewrite map_length.
Qed.

Lemma mk_list_false_eq: forall bs, (map (fun _ : int => Lit.interp rho Lit._false) bs) =
 (RAWBITVECTOR_LIST.mk_list_false (Datatypes.length bs)).
Proof. intro bs.
       induction bs as [ | xbs xsbs IHbs ].
       - now simpl.
       - simpl. rewrite IHbs. specialize (@Lit.interp_false rho wf_rho).
        intros. unfold is_true in H. apply not_true_is_false in H.
        now rewrite H.
Qed. 

Lemma map_interp_neg: forall bs, (map (fun x : int => negb (Lit.interp rho x)) bs) =
  (map (fun x : int => Lit.interp rho (Lit.neg x)) bs).
Proof. intro bs. 
       induction bs as [ | xbs xsbs IHbs ].
       - now simpl.
       - simpl. rewrite IHbs.
         now rewrite Lit.interp_neg.
Qed.

Lemma prop_check_neg: forall bs bsres n, 
  (N.of_nat(length bs) = n)%N -> 
  (N.of_nat(length bsres) = n)%N ->  
  check_neg bs bsres = true ->
  RAWBITVECTOR_LIST.bv_neg (map (Lit.interp rho) bs) = map (Lit.interp rho) bsres.
Proof. intros.

       unfold check_neg in H1.
       specialize (@check_add_list (map (fun l : int => Lit.neg l) bs)
       (map (fun _ : int => Lit._false) bs) bsres (Clit Lit._true)).

       intros. simpl in H2.
       cut ( Datatypes.length (map (fun l : int => Lit.neg l) bs) =
       Datatypes.length bsres ). intros.
       cut (Datatypes.length (map (fun _ : int => Lit._false) bs) =
       Datatypes.length bsres). intros.
       specialize (H2 H3 H4 H1).
       unfold BITVECTOR_LIST.bv_neg, RAWBITVECTOR_LIST.bv_neg.
       unfold RAWBITVECTOR_LIST.twos_complement.

       rewrite !map_map in H2.
       rewrite !map_map.
       rewrite mk_list_false_eq in H2.
       rewrite <- map_interp_neg in H2.
       rewrite Lit.interp_true in H2.
       rewrite <- H2.
       now rewrite map_length.

       easy.

       rewrite map_length. 
       apply (f_equal (N.to_nat)) in H.
       apply (f_equal (N.to_nat)) in H0.
       rewrite Nat2N.id in H, H0.
       now rewrite H, H0.

       rewrite map_length. 
       apply (f_equal (N.to_nat)) in H.
       apply (f_equal (N.to_nat)) in H0.
       rewrite Nat2N.id in H, H0.
       now rewrite H, H0.
Qed.

Lemma check_neg_length: forall bs bsres,
  check_neg bs bsres = true -> (length bs = length bsres)%nat.
Proof. intros.
       unfold check_neg in H.
       specialize (@check_add_bvadd_length  (map (fun l : int => Lit.neg l) bs)
       (map (fun _ : int => Lit._false) bs) bsres  (Clit Lit._true)).
       intros. simpl in H0.
       specialize (H0 H).
       destruct H0. now rewrite map_length in H0.
Qed.

Lemma valid_check_bbNeg pos lres : C.valid rho (check_bbNeg pos lres).
Proof.
      unfold check_bbNeg.
      case_eq (S.get s pos); [intros _|intros l1 [ |l] Heq1]; try now apply C.interp_true.
      case_eq (Lit.is_pos l1); intro Heq3; simpl; try now apply C.interp_true.
      case_eq (Lit.is_pos lres); intro Heq5; simpl; try now apply C.interp_true.
      case_eq (t_form .[ Lit.blit l1]); try (intros; now apply C.interp_true). intros a1 bs1 Heq6.
      case_eq (t_form .[ Lit.blit lres]); try (intros; now apply C.interp_true).
      intros a bsres Heq8.
      case_eq (t_atom .[ a]); try (intros; now apply C.interp_true).
      intros [ | | | | | | | ] a1' Heq9; try now apply C.interp_true.

      case_eq ((a1 == a1') && check_neg bs1 bsres &&
      (N.of_nat (Datatypes.length bs1) =? n)%N); 
      simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl.  rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply BITVECTOR_LIST.bv_eq_reflect.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea); intros; rewrite H3 in H0; try (now contradict H0).
        rename H3 into Hv.

        generalize (Hs pos). intros HSp1. unfold C.valid in HSp1. rewrite Heq1 in HSp1.
        unfold C.interp in HSp1. unfold existsb in HSp1. rewrite orb_false_r in HSp1.
        unfold Lit.interp in HSp1. rewrite Heq3 in HSp1. unfold Var.interp in HSp1.
        rewrite rho_interp in HSp1. rewrite Heq6 in HSp1. simpl in HSp1.

        apply BITVECTOR_LIST.bv_eq_reflect in HSp1.

        unfold get_type' in H2. unfold v_type in H2.
        case_eq (t_interp .[ a1']).
          intros v_typea1 v_vala1 Htia1. rewrite Htia1 in H2.
        rewrite Atom.t_interp_wf in Htia1; trivial.
        unfold apply_binop.
        apply Typ.eqb_spec in H2.

        (** case a1 = a1' **)
        do 2 rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq10, Heq11).
        destruct Heq10 as (Heq10a1 & Heq10a2). 
        rewrite Int63Properties.eqb_spec in Heq10a1; rewrite Heq10a1 in *.

       (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H3. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H2. intros.
        rewrite Htia1.
        unfold apply_unop.
        rewrite Typ.cast_refl.
        unfold Bval.

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = n).
        {
          apply check_neg_length in Heq10a2.
          rewrite N.eqb_eq in Heq11.
          rewrite Heq10a2 in Heq11.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.

        rewrite Typ.cast_refl. 
        intros.
        unfold BITVECTOR_LIST.bv_neg.
        apply eq_rec.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H4 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1.

        revert HSp1.
        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = n).
        {
          rewrite N.eqb_eq in Heq11.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.

        rewrite Typ.cast_refl. 
        intros.
        rewrite HSp1. simpl.

        specialize(@prop_check_neg bs1 bsres).
        intros. apply H5 with n.
        now rewrite N.eqb_eq in Heq11.

        pose proof Heq10a2 as Heq10a3.
        apply check_neg_length in Heq10a3.
        rewrite <- Heq10a3.
        now rewrite N.eqb_eq in Heq11.

        easy.
Qed.

Lemma prop_forallb2: forall {A B} {f: A -> B -> bool} l1 l2, forallb2 f l1 l2 = true -> length l1 = length l2.
Proof. intros A B f l1.
       induction l1 as [ | xl1 xsl1 IHl1].
       - intros. simpl in H.
         case l2 in *. easy.
         now contradict H.
       - intros. simpl in H.
         case l2 in *.
         now contradict H.
         simpl.
         rewrite andb_true_iff in H. destruct H.
         apply IHl1 in H0. now rewrite H0.
Qed.

Lemma prop_and_with_bit: forall a b, map interp_carry (and_with_bit a b) = 
                          RAWBITVECTOR_LIST.and_with_bool (map (Lit.interp rho) a) (Lit.interp rho b).
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. now simpl in *.
       - intros. simpl in *. now rewrite IHa.
Qed.

Lemma prop_mult_step_k_h: forall a b c k, 
                          map interp_carry (mult_step_k_h a b c k) = 
                          RAWBITVECTOR_LIST.mult_bool_step_k_h
                            (map interp_carry a) (map interp_carry b)
                            (interp_carry c) k.
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. case b.
         now simpl.
         intros. now simpl.
       - intros. case b in *. simpl.
         rewrite IHa. now simpl.
         intros. simpl.
         case (k - 1 <? 0)%Z.
         simpl. apply f_equal.
         apply IHa.
         rewrite <- map_cons. simpl. apply f_equal.
         apply IHa.
Qed.

Lemma prop_interp_firstn: forall xk' a, map (Lit.interp rho) (List.firstn xk' a) = (List.firstn xk' (map (Lit.interp rho) a)).
Proof.   intro xk'0.
          induction xk'0.
           + intros. now simpl. 
           + intros. simpl.
             case a. now simpl.
             intros. simpl. apply f_equal. apply IHxk'0.
Qed.

Lemma map_firstn: forall A B n (l: list A) (f:A -> B), firstn n (map f l) = map f (firstn n l). 
Proof.
  intros A B n.
  induction n; intro l; induction l; try now simpl.
  intros. simpl. apply f_equal. apply IHn.
Qed.

Lemma prop_mult_step: forall a b res k k',
      (map interp_carry (mult_step a b res k k')) = 
      RAWBITVECTOR_LIST.mult_bool_step (map (Lit.interp rho) a) (map (Lit.interp rho) b)
                                       (map interp_carry res) k k'.
Proof. intros. revert a b res k.
       assert (false = (Lit.interp rho (Lit._false))) as Ha.
       {
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         now rewrite H.
       }

       assert (false = interp_carry (Clit Lit._false)).
       {
         unfold interp_carry.
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         now rewrite H.
       }

       assert ([] = map (interp_carry) []). { now simpl. }

       induction k' as [ | xk' xsk' IHk' ].
       - intros.
         case a. simpl. rewrite H; apply prop_mult_step_k_h.
         intros. simpl. rewrite H. rewrite prop_mult_step_k_h. simpl. now rewrite map_nth.
       - intros. simpl.
         rewrite xsk', prop_mult_step_k_h, prop_and_with_bit.
         rewrite <- map_nth, <- Ha, <- H.
         case a. now simpl. simpl. intros.
         case l. now simpl. simpl. intros.
         case xk'. now simpl. intros. now rewrite map_firstn.
Qed.

Lemma prop_bblast_bvmult: forall a b n,
                          (map interp_carry (bblast_bvmult a b n)) =
                          RAWBITVECTOR_LIST.bvmult_bool (map (Lit.interp rho) a)  
                                                        (map (Lit.interp rho) b)
                                                        n.
Proof. intros.
       revert a b.
       induction n.
       - intros. simpl. rewrite prop_and_with_bit.
         rewrite <- map_nth.
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         now rewrite H.
       - intros. simpl.
         specialize (Lit.interp_false rho wf_rho). intros.
         unfold is_true in H. rewrite not_true_iff_false in H.
         case n in *.
         rewrite prop_and_with_bit; rewrite <- map_nth; now rewrite H.
         rewrite prop_mult_step; rewrite prop_and_with_bit; rewrite <- map_nth; now rewrite H.
Qed.

Lemma prop_mult_step_k_h_len: forall a b c k,
length (mult_step_k_h a b c k) = length a .
Proof. intro a.
       induction a as [ | xa xsa IHa ].
       - intros. simpl. easy.
       - intros.
         case b in *. simpl. rewrite IHa. simpl. omega.
         simpl. case (k - 1 <? 0)%Z; simpl; now rewrite IHa.
Qed.

Lemma prop_mult_step3: forall k' a b res k, 
                         length (mult_step a b res k k') = (length res)%nat.
Proof. intro k'.
       induction k'.
       - intros. simpl. rewrite prop_mult_step_k_h_len. simpl. omega.
       - intros. simpl.
         rewrite IHk'. rewrite prop_mult_step_k_h_len. simpl; omega.
Qed.

Lemma prop_and_with_bit2: forall bs1 b, length (and_with_bit bs1 b) = length bs1.
Proof. intros bs1.
       induction bs1.
       - intros. now simpl.
       - intros. simpl. now rewrite IHbs1.
Qed.

Lemma check_bvmult_length: forall bs1 bs2,
  let bsres0 := bblast_bvmult bs1 bs2 (length bs1) in
  length bs1 = length bs2 -> length bs1 = length bsres0.
Proof. intros. unfold bblast_bvmult in bsres0.
       case_eq (length bs1). intros. unfold bsres0.
       rewrite H0.
       specialize (@prop_and_with_bit2 bs1 (nth 0 bs2 Lit._false)). intros.
       now rewrite H1.
       intros. unfold bsres0. rewrite H0.
       case n in *.
       simpl. rewrite prop_and_with_bit2. auto.
       rewrite prop_mult_step3. rewrite prop_and_with_bit2. auto.
Qed.

Lemma check_bvmult_length2: forall bs1 bs2 bsres,
  check_mult bs1 bs2 bsres = true -> length bs1 = length bs2 .
Proof. intros bs1.
       induction bs1.
       - intros. case bs2 in *.
         + easy.
         + unfold check_mult in H.
           now contradict H.
       - intros. unfold check_mult in H.
         case_eq (Nat_eqb (Datatypes.length (a :: bs1)) ((Datatypes.length bs2))).
         intros. now apply Nat_eqb_eq in H0.
         intros. rewrite H0 in H. now contradict H.
Qed.

Lemma prop_eq_carry_lit2: forall a b, forallb2 eq_carry_lit a b = true -> 
                          (map interp_carry a) = (map (Lit.interp rho) b).
Proof. intro a.
       induction a.
       - intros. simpl in H.
         case b in *. now simpl.
         now contradict H.
       - intros. 
         case b in *.
         now simpl.
         simpl in *. rewrite andb_true_iff in H; destruct H.
         apply prop_eq_carry_lit in H.
         rewrite H. apply f_equal. now apply IHa.
Qed.

Lemma prop_main: forall bs1 bs2 bsres,
                 check_mult bs1 bs2 bsres = true ->
                 map interp_carry (bblast_bvmult bs1 bs2 (Datatypes.length (map (Lit.interp rho) bs1))) =
                 map (Lit.interp rho) bsres.
Proof. intros. unfold check_mult in H.
       case_eq (Nat_eqb (Datatypes.length bs1) (Datatypes.length bs2)). intros.
       rewrite H0 in H. apply prop_eq_carry_lit2 in H.
       rewrite map_length.
       now rewrite H.
       intros. rewrite H0 in H. now contradict H.
Qed.


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
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N|N|N|N|N| | ] a1' a2' Heq9; try (intros; now apply C.interp_true).
      (* BVmult *)
      - case_eq ((a1 == a1') && (a2 == a2') (* || (a1 == a2') && (a2 == a1')*) );
            simpl; intros Heq10; try (now apply C.interp_true).

        case_eq ( 
                 check_mult bs1 bs2 bsres &&
                 (N.of_nat (Datatypes.length bs1) =? N)%N
                ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl.  rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply BITVECTOR_LIST.bv_eq_reflect.


        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

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
        rewrite andb_true_iff in Heq10.
        destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2;
        rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.
        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite Typ.cast_refl.
        unfold Bval.

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          pose proof Heq11 as Heq11'.
          apply prop_main in Heq11.
          rewrite <- Heq11. rewrite !map_length.
          specialize (@check_bvmult_length bs1 bs2).
          intros. simpl in H5. rewrite <- H5.
          now rewrite N.eqb_eq in Heq11r.
          now apply check_bvmult_length2 in Heq11'.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.

        rewrite Typ.cast_refl.
        intros.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1.

        revert HSp1.

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).
        rewrite H101.

        rewrite Typ.cast_refl.
        intros.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2.

        revert HSp2. 

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        assert (H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = N).
        {
          rewrite andb_true_iff in Heq11.
          destruct Heq11 as (Heq11, Heq11r).
          rewrite N.eqb_eq in Heq11r.
          apply check_bvmult_length2 in Heq11.
          rewrite Heq11 in Heq11r.
          now rewrite map_length.
        }

        generalize (BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H102.

        rewrite Typ.cast_refl.
        intros. rewrite HSp2.

        pose proof Heq11.

        unfold BITVECTOR_LIST.bv_mult.
        unfold RAWBITVECTOR_LIST.bv_mult.
        unfold RAWBITVECTOR_LIST.size, RAWBITVECTOR_LIST.bits.
        unfold BITVECTOR_LIST.of_bits.

        unfold BITVECTOR_LIST.bv.
        unfold RAWBITVECTOR_LIST.of_bits.
        apply eq_rec. simpl.

        rewrite andb_true_iff in Heq11.
        destruct Heq11 as (Heq11 & Heq11r).
        rewrite N.eqb_eq in Heq11r.
        rewrite map_length, Heq11r.

        apply check_bvmult_length2 in Heq11.
        rewrite Heq11 in Heq11r.
        rewrite map_length, Heq11r.
        rewrite N.eqb_compare, N.compare_refl.
        unfold RAWBITVECTOR_LIST.mult_list.
        rewrite <- prop_bblast_bvmult.

        rewrite andb_true_iff in H7. 
        destruct H7 as (H7 & H7r).

        rewrite map_length.
        apply prop_main in H7.
        rewrite map_length in H7.
        rewrite <- H7.

        easy.
Qed.

  
Lemma prop_interp_carry3: forall bs2,  map interp_carry (lit_to_carry bs2) = map (Lit.interp rho) bs2.
Proof. intro bs2.
       induction bs2 as [ | xbs2 xsbs2 IHbs2 ].
       - now simpl.
       - simpl. now rewrite IHbs2.
Qed.

Lemma check_concat_map: forall bs1 bs2,
 map (Lit.interp rho) bs1 ++ map (Lit.interp rho) bs2 = map (Lit.interp rho) (bs1 ++ bs2).
Proof. intro bs1.
       induction bs1.
       - intros. now simpl.
       - intros. simpl. now rewrite IHbs1.
Qed.

Lemma concat_nil: forall {A} (a: list A), a ++ [] = a.
Proof. intros A a.
       case a; [ easy | intros; apply app_nil_r ].
Qed.

Lemma check_concat_bvconcat: forall bs1 bs2 bsres , 
  check_concat bs1 bs2 bsres = true ->
  (RAWBITVECTOR_LIST.bv_concat (map (Lit.interp rho) bs1) (map (Lit.interp rho) bs2) =
   (map (Lit.interp rho) bsres)).
Proof. intro bs1.
       induction bs1 as [ | xbs1 xsbs1 IHbs1 ].
       - intros. simpl.
         unfold check_concat in H. simpl in H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry bs2) bsres); intros.
         rewrite concat_nil in H.
         apply prop_eq_carry_lit2 in H0.
         unfold RAWBITVECTOR_LIST.bv_concat.
         rewrite concat_nil.
         now rewrite prop_interp_carry3 in H0.
         unfold RAWBITVECTOR_LIST.bv_concat.
         rewrite concat_nil.
         rewrite concat_nil in H.
         rewrite H0 in H. now contradict H.
       - intros. unfold check_concat in H.
         case_eq (forallb2 eq_carry_lit (lit_to_carry (bs2 ++ xbs1 :: xsbs1)) bsres); intros.
         apply prop_eq_carry_lit2 in H0.
         rewrite prop_interp_carry3 in H0.
         simpl in H0. simpl.
         unfold RAWBITVECTOR_LIST.bv_concat.
         specialize (concat_map (Lit.interp rho)). intros.
         rewrite <- H0. simpl.
         rewrite <- !check_concat_map.
         apply f_equal.
         now simpl.
         rewrite H0 in H; now contradict H.
Qed.

Lemma app_length : forall (l1 l2: list bool), (length (l1 ++ l2))%nat = ((length l1) + (length l2))%nat.
Proof.
  induction l1; simpl; auto.
Qed.

Lemma concat_len: forall (bs1 bs2 bsres: list bool), bs1 ++ bs2 = bsres ->
                              ((length bs1) + (length bs2))%nat = (length bsres)%nat.
Proof. intro bs1.
       induction bs1.
       - intros. simpl. simpl in H. now rewrite H.
       - intros. simpl. simpl in H. rewrite <- H. simpl.
         now rewrite app_length.
Qed.

Lemma valid_check_bbConcat pos1 pos2 lres : C.valid rho (check_bbConcat pos1 pos2 lres).
Proof.
      unfold check_bbConcat.
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
      intros [ | | | | | | |[ A B | A| | | | ]|N|N|N|N|N|N|N|N|N| | ]  a1' a2' Heq9; try (intros; now apply C.interp_true).
      (* BVconcat *)
    - case_eq ((a1 == a1') && (a2 == a2')); simpl; intros Heq10; try (now apply C.interp_true).
        case_eq (
             check_concat bs1 bs2 bsres && (N.of_nat (Datatypes.length bs1) =? N)%N &&
             (N.of_nat (Datatypes.length bs2) =? n)%N
        ); simpl; intros Heq11; try (now apply C.interp_true).

        unfold C.valid. simpl. rewrite orb_false_r.
        unfold Lit.interp. rewrite Heq5.
        unfold Var.interp.
        rewrite wf_interp_form; trivial. rewrite Heq8. simpl.

        apply BITVECTOR_LIST.bv_eq_reflect.

        generalize wt_t_atom. unfold Atom.wt. unfold is_true.
        rewrite PArray.forallbi_spec;intros.

        pose proof (H a). 
        assert (a < PArray.length t_atom).
        { apply PArray.get_not_default_lt. rewrite def_t_atom. rewrite Heq9. easy. }
        specialize (@H0 H1). rewrite Heq9 in H0. simpl in H0.
        rewrite !andb_true_iff in H0. destruct H0. destruct H0.

        unfold get_type' in H0. unfold v_type in H0.
        case_eq (t_interp .[ a]).
        intros v_typea v_vala Htia. rewrite Htia in H0.
        case_eq (v_typea);  intros; rewrite H4 in H0; try (now contradict H0).
        rename H4 into Hv.

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
        rewrite andb_true_iff in Heq10.
        destruct Heq10 as (Heq10a1 & Heq10a2); rewrite eqb_spec in Heq10a1, Heq10a2;
        rewrite Heq10a1, Heq10a2 in *.

        (* interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a])) *)
        assert (interp_form_hatom_bv a = 
                interp_bv t_i (interp_atom (t_atom .[a]))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia. easy.
        }

        rewrite H4. rewrite Heq9. simpl.
        unfold interp_bv. unfold apply_binop.

        rewrite !Atom.t_interp_wf; trivial.

        revert v_vala1 Htia1. rewrite H3. revert v_vala2 Htia2. rewrite H2.
        intros v_vala2 Htia2 v_vala1 Htia1.
        rewrite Htia1, Htia2.
        rewrite !Typ.cast_refl.
        unfold Bval.

        assert (H100: (N.of_nat (Datatypes.length (map (Lit.interp rho) bsres))) = (N + n)%N).
        {
          rewrite !andb_true_iff in Heq11.
          destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
          apply  check_concat_bvconcat in Heq11.
          unfold RAWBITVECTOR_LIST.bv_concat in Heq11.
          apply concat_len in Heq11.
          apply N.eqb_eq in Heq11l.
          apply N.eqb_eq in Heq11r.
          rewrite !map_length in Heq11.
          rewrite <- Heq11l, <- Heq11r.
          rewrite map_length. lia.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bsres)).

        rewrite H100.
        rewrite Typ.cast_refl. intros.
        simpl.

        (* interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1'])) *)
        assert (interp_form_hatom_bv a1' = 
                interp_bv t_i (interp_atom (t_atom .[a1']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia1.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia1. easy.
        }

        rewrite H5 in HSp1.
        unfold interp_bv in HSp1.
        rewrite Htia1 in HSp1.
        unfold interp_bv in HSp1. 

        revert HSp1.

        assert (H101: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs1))) = N).
        {
          rewrite !andb_true_iff in Heq11.
          destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
          apply  check_concat_bvconcat in Heq11.
          apply N.eqb_eq in Heq11l.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs1)).

        rewrite H101.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp1.

        (* interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2'])) *)
        assert (interp_form_hatom_bv a2' = 
                interp_bv t_i (interp_atom (t_atom .[a2']))).
        {
          rewrite !Atom.t_interp_wf in Htia; trivial.
          rewrite Htia2.
          unfold Atom.interp_form_hatom_bv.
          unfold Atom.interp_hatom.
          rewrite !Atom.t_interp_wf; trivial.
          rewrite Htia2. easy.
        }

        rewrite H6 in HSp2.
        unfold interp_bv in HSp2.
        rewrite Htia2 in HSp2.
        unfold interp_bv in HSp2. 

        revert HSp2.

        assert (H102: (N.of_nat (Datatypes.length (map (Lit.interp rho) bs2))) = n).
        {
          rewrite !andb_true_iff in Heq11.
          destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
          apply  check_concat_bvconcat in Heq11.
          apply N.eqb_eq in Heq11r.
          now rewrite map_length.
        }

        unfold BITVECTOR_LIST.of_bits, RAWBITVECTOR_LIST.of_bits.

        generalize ( BITVECTOR_LIST.of_bits_size (map (Lit.interp rho) bs2)).

        rewrite H102.
        rewrite Typ.cast_refl. intros.
        simpl.

        rewrite HSp2. simpl.
        unfold BITVECTOR_LIST.bv_concat.
        apply eq_rec. simpl.
        apply check_concat_bvconcat.

        rewrite !andb_true_iff in Heq11.
        now destruct Heq11 as ((Heq11, Heq11l) & Heq11r).
Qed.

  End Proof.

End Checker.


(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

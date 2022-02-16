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


(* This file provides:
   - a generic way to inject, via tactics, types of natural numbers into
     the type Z, which is the type known by SMT solvers and, thus, by
     SMTCoq
   - an instanciation for the types nat, positive and N.
*)



Require Import ZArith.

(* This module represents the structure to be injected into Z *)
Module Type convert_type.

(* The type to be injected *)
Parameter T : Type.

(* Mapping both ways *)
Parameter Z2T : Z -> T.
Parameter T2Z : T -> Z.
(* T2Z is an injection *)
Axiom T2Z_id : forall x : T, Z2T (T2Z x) = x.

(* A property about elements of Z coming from elements of T.
   For instance, for nat, all elements are non-negative: (0 <=? z)%Z *)
Parameter inT : Z -> bool.
(* The image of the injection satisfies this property *)
Axiom T2Z_pres : forall x : T, inT (T2Z x) = true.
(* It is always possible to define inT as <fun z => Z.eqb z (T2Z (Z2T z))>.
   In this case, the proof of the axiom is simply:
    <rewrite T2Z_id, Z.eqb_eq>. *)

(* We ask this injection to be a morphism for all the following symbols *)

(* Addition *)
Parameter add : T -> T -> T.
Axiom t2z_add_morph : forall x' y', Z.add (T2Z x') (T2Z y') = T2Z (add x' y').

(* Multiplication *)
Parameter mul : T -> T -> T.
Axiom t2z_mul_morph : forall x' y', Z.mul (T2Z x') (T2Z y') = T2Z (mul x' y').

(* <= *)
Parameter leb : T -> T -> bool.
Axiom t2z_leb_morph : forall x' y', Z.leb (T2Z x') (T2Z y') = leb x' y'.

(* < *)
Parameter ltb : T -> T -> bool.
Axiom t2z_ltb_morph : forall x' y', Z.ltb (T2Z x') (T2Z y') = ltb x' y'.

(* = *)
Parameter eqb : T -> T -> bool.
Axiom t2z_eqb_morph : forall x' y', Z.eqb (T2Z x') (T2Z y') = eqb x' y'.
End convert_type.

(* This fonctor builds a conversion tactic from a module of the signature above *)
Module convert (M : convert_type).

Import M.

(* SMTCoq uses Booleans *)
Lemma implb_impl : forall a b : bool, (implb a b = true -> a = true -> b = true).
Proof.
intros a b H.
destruct a; destruct b; try reflexivity; discriminate.
Qed.

(* Get the head symbol of an application *)
Ltac get_head x := lazymatch x with ?x _ => get_head x | _ => x end.

(* [inverse_tactic tactic] succceds when [tactic] fails, and the other way round *)
Ltac inverse_tactic tactic := try (tactic; fail 1).

(* [constr_neq t u] fails if and only if [t] and [u] are convertible *)
Ltac constr_neq t u := inverse_tactic ltac:(constr_eq t u).

(* [is_not_constructor U sym] fails if and only if [sym] is a constructor of [U] *)
Ltac is_not_constructor U sym :=
let H := fresh in
assert (U -> True) as H by
       (let x := fresh in
        let y := fresh in
        intro x;
        pose x as y;
        destruct x;
        let C := eval unfold y in y in
        let c := get_head C in
        constr_neq sym c;
        exact I); clear H.

(* [is_constructor U sym] succeeds if and only if [sym] is a constructor of [U] *)
Ltac is_constructor U sym := inverse_tactic ltac:(is_not_constructor U sym).

(* Replaces the sub-terms [x] of type [T] which are not under a known
   symbol by Z2T (T2Z x) *)
Ltac converting :=
  (* The heart of the tactic *)
  repeat
    match goal with
    (* We capture each subèterm [x] together with its context, i.e. the goal is C[x] *)
    | |- context C[?x]  =>
      (* If [x] has type [T] *)
      let U := type of x in
      lazymatch eval fold T in U with
      | T =>
        lazymatch x with
        (* If x is of the shape Z2T (T2Z _) we stop since [x] is already in the expected shape *)
        | Z2T (T2Z _) => fail
        | _ =>
          (* We generate a fresh variable of type T *)
          let var := fresh in
          pose proof x as var;
          (* Otherwise, we analyze the formula obtained by replacing [x] by the fresh variable in the goal *)
          lazymatch context C[var] with
          | context [?h var] =>
            let h := get_head h in
            lazymatch h with
            (* [x] is already in the expected shape *)
            | T2Z => fail
            (* Not necessary to rewrite under symbols commuting with T2Z *)
            | add => fail | mul => fail | ltb => fail | leb => fail | eqb => fail
            (* Do not rewrite inside a constant *)
            | Zpos => fail | Zneg => fail
            | _ =>
            (* Idem: if the context contains a constructor of [T], and
               [x] starts with a constructor of [T], we are inside a
               constant *)
            let hx := get_head x in
            try (is_constructor T h; is_constructor T hx; fail 1);
            (* Otherwise, we rewrite *)
            let old_goal := context C[x] in
            let new_goal := context C[Z2T (T2Z x)] in
            replace old_goal with new_goal by (rewrite (T2Z_id x); reflexivity) end
          end;
          (* We clear the fresh variable *)
          clear var
        end
      end
    end.

Ltac rewriting :=
  repeat (try rewrite <- t2z_leb_morph;
          try rewrite <- t2z_ltb_morph;
          try rewrite <- t2z_eqb_morph;
          try rewrite <- t2z_add_morph;
          try rewrite <- t2z_mul_morph).


(* expand_type [Tn;...T2;;T1] T = T1->T2->...->Tn->T *)
Fixpoint expand_type l T : Type :=
  match l with
    | nil => T
    | cons h l => expand_type l (h -> T)
  end.
(* get_args (f t1 t2 ... tn) = [(Tn,tn);...;(T2,t2);(T1,t1)] *)
Ltac get_args X :=
  lazymatch X with
    | ?x ?y => let x_args := get_args x in let T := type of y in constr:(cons (existT (fun z => z) T y) x_args)
    | _ => constr:(@nil (sigT (fun x => x)))
  end.
(* get_args_types [(Tn,tn);...;(T2,t2);(T1,t1)] = [Tn;...;T2;T1] *)
Fixpoint get_args_types (l : list (sigT (fun x => x))) : list Type :=
  match l with
    | nil => nil
    | cons (@existT _ _ T _) l => cons T (get_args_types l)
  end.
(* apply_args [(Tn,tn);...;(T2,t2);(T1,t1)] T (f : T1->T2->...->Tn->T) = f t1 t2 ... tn *)
Ltac apply_args f args :=
  lazymatch args with
    | nil => constr:(f)
    | cons ?arg ?args => match arg with existT _ _ ?arg => let f := apply_args f args in constr:(f arg) end
  end.

(* expand_fun [Tn;...;T2;T1] T U (f : T1->T2->...->Tn->T) (g : T->U) = fun x1 x2 ... xn => g (f x1 x2 ... xn) *)
Fixpoint expand_fun (l : list Type) (T : Type) (U : Type) : expand_type l T -> (T -> U) -> expand_type l U :=
  match l with
    | nil => fun f g => g f
    | cons h l' => fun f g => expand_fun l' (h -> T) (h -> U) f (fun a x => g (a x))
  end.
(* expand (f (t1:T1) (t2:T2) ... (tn:Tn) : T) (g : T->U) = fun x1 x2 ... xn => g (f x1 x2 ... xn) *)
Ltac expand X g :=
  (* Let argsX = [(Tn,tn);...;(T2,t2);(T1,t1)] *)
  let argsX := get_args X in
  (* Let argsXtypes = [Tn;...;T2;T1] *)
  let argsXtypes := constr:(get_args_types argsX) in
  (* Let typeX = T *)
  let typeX := type of X in
  (* Let h = f *)
  let h := get_head X in
  (* Let typeg = U *)
  let typeg := match type of g with _ -> ?U => U end in
  (* We return expand_fun [Tn;...;T2;T1] T Z f T2Z = fun x1 x2 ... xn => g (f x1 x2 ... xn) *)
  constr:(expand_fun argsXtypes typeX typeg h g).

(* Replaces function symbols with return type in T, and variables in T,
   by their counterparts in Z, adding the positivity hypotheses *)
Ltac renaming :=
  repeat
    match goal with
      (* If there is a term of the shape (T2Z (f t1 ... tn)) *)
      | |- context [T2Z ?X] =>
        (* Get the head symbol *)
        let f := get_head X in
        (* Nothing to do if it is a constructor *)
        is_not_constructor T f;
        (* Otherwise, let fe = fun x1 ... xn => T2Z (f x1 ... xn) *)
        let fe := expand X T2Z in
        let fe := eval cbv in fe in
        (* Pose fe_id := fun x1 ... xn => T2Z (f x1 ... xn) *)
        let fe_id := fresh in pose (fe_id := fe);
        repeat
          match goal with
            (* For each term of the shape (T2Z (f' t'1 ... t'n)) *)
            | |- context [T2Z ?X'] =>
              (* Get the head symbol *)
              let f' := get_head X' in
              (* If f' = f *)
              constr_eq f f';
              (* Add the hypothesis inT (T2Z X') *)
              generalize (T2Z_pres X'); apply implb_impl;
              (* Let args = [t'1;...;t'n] *)
              let args := get_args X' in
              (* Let Y = fe_id t'1 ... t'n *)
              let Y := apply_args fe_id args in
              (* Replace [T2Z (f' t'1 ... t'n)] by [Y] *)
              change (T2Z X') with Y
          end;
        (* Abstract over [fe_id := fun x1 ... xn => T2Z (f x1 ... xn)] *)
        generalize fe_id;
        (* Erase the old f and the temporary fe_id *)
        clear f fe_id;
        (* Introduce the new f with the same name *)
        let f := fresh f in
        intro f
    end.

(* expand_fun' [Tn;...;T2;T1] T U (f : T1->T2->...->Tn->T) (a : T->U) = fun x1 x2 ... xn => a (f x1 x2 ... xn) *)
Fixpoint expand_fun' (l : list Type) : forall T U : Type, expand_type l T -> (T -> U) -> expand_type l U :=
  match l as l return forall T U, expand_type l T -> (T ->U) -> expand_type l U with
    | nil => fun T U f a => a f
    | cons T' l => fun T U f a => expand_fun' l (T' -> T) (T' -> U) f (fun g xn => a (g xn))
  end.
(* expand' (f (t1:T1) (t2:T2) ... (tn:Tn) : T) (g : U->Tn) = fun x1 x2 ... xn => f x1 x2 ... (g xn) *)
Ltac expand' X g :=
  (* Let argsX = [(Tn,tn);...;(T2,t2);(T1,t1)] *)
  let argsX := get_args X in
  (* Let argsXtypes = [Tn;...;T2;T1] *)
  let argsXtypes := constr:(get_args_types argsX) in
  let argsXtypes := eval cbv in argsXtypes in
  (* Let Tn = Tn *)
  let Tn := match argsXtypes with cons ?T _ => T end in
  (* Let argsXtypes = [Tn-1;...;T2;T1] *)
  let argsXtypes := match argsXtypes with cons _ ?args => args end in
  (* Let typeX = T *)
  let typeX := type of X in
  (* Let h = f *)
  let h := get_head X in
  (* Let typeg = U *)
  let typeg := match type of g with ?U -> _ => U end in
  (* Return expand_fun' [Tn-1;...;T2;T1] (Tn->T) (Z->T) f (fun b x => b (g x))) = fun x1 x2 ... xn => f x1 x2 ... (g xn) *)
  constr:(expand_fun' argsXtypes (Tn -> typeX) (typeg -> typeX) h (fun b x => b (g x))).

(* Replaces function symbols with parameters in T, with their
   counterparts with parameters in Z *)
Ltac renaming' :=
  repeat
    match goal with
      (* If there is a term of the shape (f t1 ... (Z2T tn)) *)
      | |- context [?X (Z2T ?Y)] =>
        (* Get the head symbol *)
        let f := get_head X in
        (* Nothing to do if it is a constructor *)
        is_not_constructor T f;
        (* Otherwise, let fe = fun x1 ... xn => f x1 ... (Z2T xn) *)
        let fe := expand' (X (Z2T Y)) Z2T in
        let fe := eval simpl in fe in
        repeat
          match goal with
            (* For each term of the shape (f' t'1 ... (Z2T t'n)) *)
            | |- context [?X' (Z2T ?Y')] =>
              (* Get the head symbol *)
              let f' := get_head X' in
              (* If f' = f *)
              constr_eq f f';
              (* Let args = [t'1;...;t'(n-1)] *)
              let args := get_args X' in
              (* Let Z = (fun x1 ... xn => f x1 ... (Z2T xn)) t'1 ... t'(n-1) *)
              let Z := apply_args fe args in
              (* Replace (f' t'1 ... (Z2T t'n)) with (Z t'n) *)
              change (X' (Z2T Y')) with (Z Y')
          end;
        (* Abstract over (fun x1 ... xn => (f x1 ... (Z2T xn)) *)
        generalize fe;
        (* Erase the old f *)
        clear f;
        (* Introduce the new f with the same name *)
        let f := fresh f in
        intro f
    end.

(* The whole tactic *)
Ltac convert :=
fold T add mul ltb leb eqb;
intros;
converting;
rewriting;
renaming;
renaming';
let T2Z_unfolded := eval red in T2Z in change T2Z with T2Z_unfolded;
let inT_unfolded := eval red in inT in change inT with inT_unfolded;
simpl.

End convert.

(* Instanciation for the type [positive] *)
Module pos_convert_type <: convert_type.

Definition T : Type := positive.

Definition Z2T : Z -> T := fun z =>
  match z with
    | 0%Z => 1%positive
    | Zpos p => p
    | Zneg _ => 1%positive
  end.

Definition T2Z : T -> Z := Zpos.
Lemma T2Z_id : forall x : T, Z2T (T2Z x) = x. reflexivity. Qed.

Definition inT : Z -> bool := fun z => Z.ltb 0 z.
Lemma T2Z_pres : forall x, inT (T2Z x) = true. reflexivity. Qed.

Definition add : T -> T -> T := Pos.add.
Lemma t2z_add_morph : forall x' y', Z.add (T2Z x') (T2Z y') = T2Z (add x' y').
Proof. reflexivity. Qed.

Definition mul : T -> T -> T := Pos.mul.
Lemma t2z_mul_morph : forall x' y', Z.mul (T2Z x') (T2Z y') = T2Z (mul x' y').
Proof. reflexivity. Qed.

Definition leb : T -> T -> bool := Pos.leb.
Lemma t2z_leb_morph : forall x' y', Z.leb (T2Z x') (T2Z y') = leb x' y'.
Proof. reflexivity. Qed.

Definition ltb : T -> T -> bool := Pos.ltb.
Lemma t2z_ltb_morph : forall x' y', Z.ltb (T2Z x') (T2Z y') = ltb x' y'.
Proof. reflexivity. Qed.

Definition eqb : T -> T -> bool := Pos.eqb.
Lemma t2z_eqb_morph : forall x' y', Z.eqb (T2Z x') (T2Z y') = eqb x' y'.
Proof. reflexivity. Qed.
End pos_convert_type.

Module pos_convert_mod := convert pos_convert_type.

Ltac pos_convert := pos_convert_mod.convert.


(* Instanciation for the type [N] *)
Module N_convert_type <: convert_type.

Definition T : Type := N.

Definition Z2T : Z -> T := Z.to_N.

Definition T2Z : T -> Z := Z.of_N.
Lemma T2Z_id : forall x : T, Z2T (T2Z x) = x. exact N2Z.id. Qed.

Definition inT : Z -> bool := fun z => Z.leb 0 z.
Lemma T2Z_pres : forall x, inT (T2Z x) = true. intro; unfold inT; rewrite Z.leb_le; apply N2Z.is_nonneg. Qed.

Definition add : T -> T -> T := N.add.
Lemma t2z_add_morph : forall x' y', Z.add (T2Z x') (T2Z y') = T2Z (add x' y').
Proof. intros x y; destruct x, y; reflexivity. Qed.

Definition mul : T -> T -> T := N.mul.
Lemma t2z_mul_morph : forall x' y', Z.mul (T2Z x') (T2Z y') = T2Z (mul x' y').
Proof. intros x y; destruct x, y; reflexivity. Qed.

Definition leb : T -> T -> bool := N.leb.
Lemma t2z_leb_morph : forall x' y', Z.leb (T2Z x') (T2Z y') = leb x' y'.
Proof. intros x y; destruct x, y; reflexivity. Qed.

Definition ltb : T -> T -> bool := N.ltb.
Lemma t2z_ltb_morph : forall x' y', Z.ltb (T2Z x') (T2Z y') = ltb x' y'.
Proof. intros x y; destruct x, y; reflexivity. Qed.

Definition eqb : T -> T -> bool := N.eqb.
Lemma t2z_eqb_morph : forall x' y', Z.eqb (T2Z x') (T2Z y') = eqb x' y'.
Proof. intros x y; destruct x, y; reflexivity. Qed.

End N_convert_type.

Module N_convert_mod := convert N_convert_type.

Ltac N_convert := N_convert_mod.convert.

(* Instanciation for the type [nat] *)
Require Import NPeano.
Module nat_convert_type <: convert_type.

Definition T : Type := nat.

Definition Z2T : Z -> T := Z.to_nat.

Definition T2Z : T -> Z := Z.of_nat.
Lemma T2Z_id : forall x : T, Z2T (T2Z x) = x. exact Nat2Z.id. Qed.

Definition inT : Z -> bool := fun z => Z.leb 0 z.
Lemma T2Z_pres : forall x, inT (T2Z x) = true. intro; unfold inT; rewrite Z.leb_le; apply Nat2Z.is_nonneg. Qed.

Definition add : T -> T -> T := Nat.add.
Lemma t2z_add_morph : forall x' y', Z.add (T2Z x') (T2Z y') = T2Z (add x' y').
Proof. symmetry. apply Nat2Z.inj_add. Qed.

Definition mul : T -> T -> T := Nat.mul.
Lemma t2z_mul_morph : forall x' y', Z.mul (T2Z x') (T2Z y') = T2Z (mul x' y').
Proof. symmetry. apply Nat2Z.inj_mul. Qed.

Definition leb : T -> T -> bool := Nat.leb.
Lemma t2z_leb_morph : forall x' y', Z.leb (T2Z x') (T2Z y') = leb x' y'.
Proof.
  intros x y; unfold leb.
  case_eq (Nat.leb x y); [| rewrite <- 2 Bool.not_true_iff_false];
  rewrite <- Zle_is_le_bool; rewrite Nat.leb_le; rewrite Nat2Z.inj_le; auto.
Qed.

Definition ltb : T -> T -> bool := Nat.ltb.
Lemma t2z_ltb_morph : forall x' y', Z.ltb (T2Z x') (T2Z y') = ltb x' y'.
Proof.
  intros x y; unfold ltb.
  case_eq (Nat.ltb x y); [| rewrite <- 2 Bool.not_true_iff_false];
  rewrite <- Zlt_is_lt_bool; rewrite Nat.ltb_lt; rewrite Nat2Z.inj_lt; auto.
Qed.

Definition eqb : T -> T -> bool := Nat.eqb.
Lemma t2z_eqb_morph : forall x' y', Z.eqb (T2Z x') (T2Z y') = eqb x' y'.
Proof.
  intros x y; unfold eqb.
  case_eq (Nat.eqb x y); [| rewrite <- 2 Bool.not_true_iff_false];
  rewrite Z.eqb_eq; rewrite Nat.eqb_eq; rewrite Nat2Z.inj_iff; auto.
Qed.

End nat_convert_type.

Module nat_convert_mod := convert nat_convert_type.

Ltac nat_convert := nat_convert_mod.convert.

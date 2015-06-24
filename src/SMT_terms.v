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


Require Import Bool List Int63 PArray.
Add LoadPath "." as SMTCoq.
Require Import Misc State.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Hint Unfold is_true.


(* Remark: I use Notation instead of Definition du eliminate conversion check during the type checking *)
Notation atom := int (only parsing).

Module Form.

  Notation fargs := (array _lit) (only parsing).

  Inductive form : Type :=
  | Fatom (_:atom)
  | Ftrue
  | Ffalse
  | Fnot2 (_:int) (_:_lit)
  | Fand (_:fargs)
  | For  (_:fargs)
  | Fimp (_:fargs)
  | Fxor (_:_lit) (_:_lit)
  | Fiff (_:_lit) (_:_lit)
  | Fite (_:_lit) (_:_lit) (_:_lit).

  Definition is_Ftrue h :=
    match h with Ftrue => true | _ => false end.

  Definition is_Ffalse h :=
    match h with Ffalse => true | _ => false end.

  Lemma is_Ftrue_correct : forall h, is_Ftrue h -> h = Ftrue.
  Proof. destruct h;trivial;discriminate. Qed.

  Lemma is_Ffalse_correct : forall h, is_Ffalse h -> h = Ffalse.
  Proof. destruct h;trivial;discriminate. Qed.

  Section Interp.
    Variable interp_atom : atom -> bool.

    Section Interp_form.

    (* On suppose qu'on a l'interprétation des litéraux *)
      Variable interp_var : var -> bool.

      (* Interprétation d'une formule en supposant l'interprétation
         des litéraux *)
      (* (les litéraux font office d'index de hachage) *)
      Definition interp_aux (h:form) : bool :=
        match h with
        | Fatom a => interp_atom a
        | Ftrue => true
        | Ffalse => false
        | Fnot2 i l => fold (fun b => negb (negb b)) 1 i (Lit.interp interp_var l)
        | Fand args => afold_left _ _ true andb (Lit.interp interp_var) args
        | For args => afold_left _ _ false orb (Lit.interp interp_var) args
        | Fimp args => afold_right _ _ true implb (Lit.interp interp_var) args
        | Fxor a b => xorb (Lit.interp interp_var a) (Lit.interp interp_var b)
        | Fiff a b => Bool.eqb (Lit.interp interp_var a) (Lit.interp interp_var b)
        | Fite a b c =>
          if Lit.interp interp_var a then Lit.interp interp_var b
          else Lit.interp interp_var c
        end.

    End Interp_form.

    Section Interp_get.

      Variable t_form : PArray.array form.

      Definition t_interp : PArray.array bool :=
        PArray.foldi_left (fun i t_b hf => 
            t_b.[i <- interp_aux (PArray.get t_b) hf])
        (PArray.make (PArray.length t_form) true) t_form.

      Fixpoint lt_form i h {struct h} :=
        match h with
        | Fatom _ | Ftrue | Ffalse => true
        | Fnot2 _ l => Lit.blit l < i
        | Fand args | For args | Fimp args =>
          PArray.forallb (fun l => Lit.blit l < i) args
        | Fxor a b | Fiff a b => (Lit.blit a < i) && (Lit.blit b < i) 
        | Fite a b c => (Lit.blit a < i) && (Lit.blit b < i) && (Lit.blit c < i)
        end.

      Lemma lt_form_interp_form_aux :
        forall f1 f2 i h,
          (forall j, j < i -> f1 j = f2 j) ->
          lt_form i h ->
          interp_aux f1 h = interp_aux f2 h.
      Proof.
        destruct h;simpl;intros;trivial;
          try (apply afold_left_eq;unfold is_true in H0;
            rewrite PArray.forallb_spec in H0;intros;
              auto using Lit.interp_eq_compat).
        f_equal;auto using Lit.interp_eq_compat.
        apply afold_right_eq;unfold is_true in H0;
          rewrite PArray.forallb_spec in H0;intros;
            auto using Lit.interp_eq_compat.
        unfold is_true in H0;rewrite !andb_true_iff in H0;decompose [and] H0;
          rewrite !(Lit.interp_eq_compat f1 f2);auto.
        unfold is_true in H0;rewrite !andb_true_iff in H0;decompose [and] H0;
          rewrite !(Lit.interp_eq_compat f1 f2);auto.
        unfold is_true in H0;rewrite !andb_true_iff in H0;decompose [and] H0;
          rewrite !(Lit.interp_eq_compat f1 f2);auto.
      Qed.

      Definition wf := PArray.forallbi lt_form t_form.

      Hypothesis wf_t_i : wf.

      Lemma length_t_interp : length t_interp = length t_form.
      Proof.
        unfold t_interp;apply PArray.foldi_left_Ind with (P := fun i a => length a = length t_form).
        intros;rewrite length_set;trivial.
        rewrite length_make, ltb_length;trivial.
      Qed.

      Lemma default_t_interp : default t_interp = true.
      Proof.
        unfold t_interp;apply PArray.foldi_left_Ind with
          (P := fun i a => default a = true).
        intros;rewrite default_set;trivial.
        apply default_make.
      Qed.

      Lemma t_interp_wf : forall i, i < PArray.length t_form ->
        t_interp.[i] = interp_aux (PArray.get t_interp) (t_form.[i]).
      Proof.
        set (P' i t := length t = length t_form ->
          forall j, j < i ->
            t.[j] = interp_aux (PArray.get t) (t_form.[j])).
        assert (P' (length t_form) t_interp).
        unfold is_true, wf in wf_t_i;rewrite PArray.forallbi_spec in wf_t_i.
        unfold t_interp;apply foldi_left_Ind;unfold P';intros.
        rewrite length_set in H1.
        destruct (Int63Properties.reflect_eqb j i).
        rewrite e, PArray.get_set_same.
        apply lt_form_interp_form_aux with (2:= wf_t_i i H).
        intros;rewrite get_set_other;trivial.
        intros Heq;elim (not_ltb_refl i);rewrite Heq at 1;trivial.
        rewrite H1;trivial.
        assert (j < i).
        assert ([|j|] <> [|i|]) by (intros Heq1;elim n;apply to_Z_inj;trivial).
        generalize H2;unfold is_true;rewrite !ltb_spec, (to_Z_add_1 _ _ H);
          auto with zarith.
        rewrite get_set_other, H0;auto.
        apply lt_form_interp_form_aux with
          (2:= wf_t_i j (ltb_trans _ _ _ H3 H)).
        intros;rewrite get_set_other;trivial.
        intros Heq;elim (not_ltb_refl i);apply ltb_trans with j;
          [ rewrite Heq| ];trivial.
        elim (ltb_0 _ H0).
        apply H;apply length_t_interp.
      Qed.

    End Interp_get.

    Definition interp_state_var t_form :=
      let t_interp := t_interp t_form in
      PArray.get t_interp.

    (* Register interp_aux as PrimInline. *)
    Definition interp t_form := interp_aux (interp_state_var t_form).

    Lemma wf_interp_form_lt :
      forall t_form, wf t_form ->
        forall x, x < PArray.length t_form ->
          interp_state_var t_form x = interp t_form (t_form.[x]).
    Proof.
      unfold interp_state_var;intros.
      apply t_interp_wf;trivial.
    Qed.

    Lemma wf_interp_form :
      forall t_form, PArray.default t_form = Ftrue -> wf t_form ->
        forall x, interp_state_var t_form x = interp t_form (t_form.[x]).
    Proof.
      intros t Hd Hwf x;case_eq (x < PArray.length t);intros.
      apply wf_interp_form_lt;trivial.
      unfold interp_state_var;rewrite !PArray.get_outofbound;trivial.
      rewrite default_t_interp, Hd;trivial.
      rewrite length_t_interp;trivial.
    Qed.

    Definition check_form t_form :=
      is_Ftrue (PArray.default t_form) &&
      is_Ftrue (t_form.[0]) &&
      is_Ffalse (t_form.[1]) &&
      wf t_form.

    Lemma check_form_correct : forall t_form,
       check_form t_form ->
       ((PArray.default t_form = Ftrue /\ wf t_form) /\
        Valuation.wf (interp_state_var t_form)).
    Proof.
     unfold is_true, check_form;intros t;rewrite !andb_true_iff.
     intros H;decompose [and] H;clear H;
     assert (PArray.default t = Ftrue) by (apply is_Ftrue_correct;trivial).
     repeat split;trivial.
     rewrite wf_interp_form;trivial.
     apply is_Ftrue_correct in H4;trivial;rewrite H4;reflexivity.
     rewrite wf_interp_form;trivial.
     apply is_Ffalse_correct in H3;trivial;rewrite H3;discriminate.
    Qed.

  End Interp.

End Form.

(* TODO Move this *)
Record typ_eqb : Type := Typ_eqb {
  te_carrier : Type;
  te_eqb : te_carrier -> te_carrier -> bool;
  te_reflect : forall x y, reflect (x = y) (te_eqb x y)
}.

(* Common used types into which we interpret *)

(* Unit *)

Section Unit_typ_eqb.

  Let carrier : Type := unit.

  Let eqb : carrier -> carrier -> bool :=
    fun _ _ => true.

  Lemma unit_reflect :
    forall x y, reflect (x = y) (eqb x y).
  Proof.
    unfold eqb; intros x y; case x; case y; simpl;
      constructor; reflexivity.
  Qed.

  Definition unit_typ_eqb :=
    Typ_eqb carrier eqb unit_reflect.

End Unit_typ_eqb.
(* End TODO *)

Module Typ.

  Notation index := int (only parsing).

  Inductive type :=
  | Tindex : index -> type
  | TZ : type
  | Tbool : type
  | Tpositive : type
  | Tint : type.

  Definition ftype := (list type * type)%type.

  Section Interp.

    Variable t_i : PArray.array typ_eqb.

    Definition interp t :=
      match t with
      | Tindex i => (t_i.[i]).(te_carrier)
      | TZ => Z
      | Tbool => bool
      | Tpositive => positive
      | Tint => int
      end.

    Definition interp_ftype (t:ftype) :=
      List.fold_right (fun dom codom =>interp dom -> codom)
      (interp (snd t)) (fst t).

    (* Boolean equality over interpretation of a btype *)
    Section Interp_Equality.

      Definition i_eqb (t:type) : interp t -> interp t -> bool :=
        match t with
        | Tindex i => (t_i.[i]).(te_eqb)
        | TZ => Zeq_bool
        | Tbool => Bool.eqb
        | Tpositive => Peqb
        | Tint => Int63Native.eqb
        end.

      Lemma i_eqb_spec : forall t x y, i_eqb t x y <-> x = y.
      Proof.
       destruct t;simpl;intros.
       symmetry;apply reflect_iff;apply te_reflect.
       symmetry;apply Zeq_is_eq_bool.
       apply Bool.eqb_true_iff.
       apply Peqb_eq.
       apply eqb_spec.
      Qed.

      Lemma reflect_i_eqb : forall t x y, reflect (x = y) (i_eqb t x y).
      Proof.
        intros;apply iff_reflect;symmetry;apply i_eqb_spec.
      Qed.

      Lemma i_eqb_sym : forall t x y, i_eqb t x y = i_eqb t y x.
      Proof.
        intros t x y; case_eq (i_eqb t x y); case_eq (i_eqb t y x); auto.
        change (i_eqb t x y = true) with (is_true (i_eqb t x y)); rewrite i_eqb_spec; intros H1 H2; subst y; pose (H:=reflect_i_eqb t x x); inversion H; [rewrite <- H0 in H1; discriminate|elim H2; auto].
        change (i_eqb t y x = true) with (is_true (i_eqb t y x)); rewrite i_eqb_spec; intros H1 H2; subst y; pose (H:=reflect_i_eqb t x x); inversion H; [rewrite <- H0 in H2; discriminate|elim H1; auto].
      Qed.

    End Interp_Equality.

  End Interp.

  (* Plutôt que de tester l'égalité entre deux btypes dans Prop, on
     écrit une fonction calculant:
     - si deux btype A et B sont égaux
     - si oui, une fonction permettant de passer les objets de type A en
     objets de type B
     On montre que cette fonction réfléchit l'égalité de Coq. *)

  Section Cast.

  (* L'inductif cast_result spécifie si deux btype sont égaux (Cast) ou
     non (NoCast). Dans le cas où ils sont égaux, une fonction permet de
     passer de l'un à l'autre. *)

    Inductive cast_result (A B: type) : Type :=
    | Cast (k: forall P, P A -> P B)
    | NoCast.

    Implicit Arguments Cast [A B].
    Implicit Arguments NoCast [A B].

    Notation idcast := (Cast (fun P x => x)).
    (* La fonction cast calcule cast_result *)

    Definition cast (A B: type) : cast_result A B :=
      match A as C, B as D return cast_result C D with
      | Tindex i, Tindex j =>
        match cast i j with
        | Some k => Cast (fun P => k (fun y => P (Tindex y)))
        | None => NoCast
        end
      | TZ, TZ => idcast
      | Tbool, Tbool => idcast
      | Tpositive, Tpositive => idcast
      | Tint, Tint => idcast
      | _, _ => NoCast
      end.

    Lemma cast_refl:
      forall A, cast A A = Cast (fun P (H : P A) => H).
    Proof.
      intros A0;destruct A0;simpl;trivial.
      rewrite cast_refl;trivial.
    Qed.

    (* Remark : I use this definition because eqb will not be used only in the interpretation *)
    Definition eqb (A B: type) : bool :=
      match A, B with
      | Tindex i, Tindex j => i == j
      | TZ, TZ => true
      | Tbool, Tbool => true
      | Tpositive, Tpositive => true
      | Tint, Tint => true
      | _, _ => false
      end.


    (* TODO : Move this *)
    Lemma not_false : ~ false.
    Proof. intro;discriminate. Qed.
    Hint Resolve not_false.

    Lemma is_true_true : true.
    Proof. reflexivity. Qed.
    Hint Resolve is_true_true.

    Lemma not_is_true_eq_false : forall b:bool, ~ b <-> b = false.
    Proof. exact not_true_iff_false. Qed.

    Lemma cast_diff: forall A B, eqb A B = false -> cast A B = NoCast.
    Proof.
      intros A0 B0;destruct A0; destruct B0;simpl;trivial;try discriminate.
      intros Heq;rewrite (cast_diff _ _ Heq);trivial.
    Qed.

    Lemma neq_cast : forall A B,
      cast A B = (if eqb A B then cast A B else NoCast).
    Proof.
      intros C D;case_eq (eqb C D);trivial;apply cast_diff.
    Qed.

    Lemma reflect_eqb : forall x y, reflect (x = y) (eqb x y).
    Proof.
      intros x y;destruct x;destruct y;simpl;try constructor;trivial;try discriminate.
      apply iff_reflect;rewrite eqb_spec;split;intros H;[inversion H | subst];trivial.
    Qed.

    Lemma eqb_spec : forall x y, eqb x y <-> x = y.
    Proof.
      intros;symmetry;apply reflect_iff;apply reflect_eqb.
    Qed.

    Lemma eqb_refl : forall x, eqb x x.
    Proof. intros; rewrite eqb_spec; auto. Qed.

  End Cast.

End Typ.

(* TODO move this *)
Inductive dlist (A:Type) (P:A->Type) : list A -> Type :=
| Dnil : dlist A P nil
| Dcons : forall a l, P a -> dlist A P l -> dlist A P (cons a l).

Set Implicit Arguments.
Definition list_beq := fun (A : Type) (eq_A : A -> A -> bool) =>
fix list_eqrec (X Y : list A) : bool :=
  match X with
  | nil => match Y with
           | nil => true
           | (_ :: _)%list => false
           end
  | (x :: x0)%list =>
      match Y with
      | nil => false
      | (x1 :: x2)%list => (eq_A x x1 && list_eqrec x0 x2)%bool
      end
  end.
Unset Implicit Arguments.

Lemma reflect_list_beq : forall (A:Type) (beq:A -> A -> bool),
  (forall x y, reflect (x = y) (beq x y)) ->
  forall x y, reflect (x = y) (list_beq beq x y).
Proof.
  intros A beq Hbeq;induction x;destruct y;simpl;try (constructor;trivial;discriminate).
  destruct (Hbeq a a0) as [Heq | Hd];simpl;[ | constructor;intros Heq;elim Hd;inversion Heq;trivial].
  destruct (IHx y) as [Heq0 | Hd];simpl;[ | constructor;intros Heq0;elim Hd;inversion Heq0;trivial].
  constructor;subst;trivial.
Qed.

Lemma list_beq_spec : forall (A:Type) (beq:A -> A -> bool),
  (forall x y, beq x y <-> x = y) ->
  forall x y, list_beq beq x y <-> x = y.
Proof.
  intros A beq HA x y;symmetry;apply reflect_iff;apply reflect_list_beq.
  intros;apply iff_reflect;symmetry;apply HA.
Qed.
(* End move *)

Module Atom.

  Notation func := int (only parsing).
 
  Inductive cop : Type := 
   | CO_xH
   | CO_Z0
   | CO_int : int -> cop.

  Inductive unop : Type :=
   | UO_xO
   | UO_xI
   | UO_Zpos 
   | UO_Zneg
   | UO_Zopp
   | UO_index : int -> unop.

  Inductive binop : Type :=
   | BO_Zplus
   | BO_Zminus
   | BO_Zmult
   | BO_Zlt
   | BO_Zle
   | BO_Zge
   | BO_Zgt
   | BO_int_xor
   | BO_eq (_ : Typ.type).

  Inductive nop : Type :=
   | NO_distinct (_ : Typ.type).

  Notation hatom := int (only parsing).
 
  Inductive atom : Type :=
   | Acop (_: cop)
   | Auop (_ : unop) (_:hatom)
   | Abop (_ : binop) (_:hatom) (_:hatom)
   | Anop (_ : nop) (_: list hatom)
   | Aapp (_:func) (_: list hatom).


  (* Generic predicates and operations *)

  (** Equality *)
  Definition cop_eqb o o' :=
   match o, o' with
   | CO_xH, CO_xH 
   | CO_Z0, CO_Z0 => true
   | CO_int a, CO_int a' => Int63Native.eqb a a'
   | _,_ => false
   end.

  Definition uop_eqb o o' :=
   match o, o' with
   | UO_xO, UO_xO 
   | UO_xI, UO_xI
   | UO_Zpos, UO_Zpos 
   | UO_Zneg, UO_Zneg
   | UO_Zopp, UO_Zopp => true
   | UO_index i1, UO_index i2 => Int63Native.eqb i1 i2 
   | _,_ => false
   end.

  Definition bop_eqb o o' :=
   match o, o' with
   | BO_Zplus, BO_Zplus
   | BO_Zminus, BO_Zminus
   | BO_Zmult, BO_Zmult
   | BO_Zlt, BO_Zlt
   | BO_Zle, BO_Zle
   | BO_Zge, BO_Zge
   | BO_Zgt, BO_Zgt
   | BO_int_xor, BO_int_xor => true
   | BO_eq t, BO_eq t' => Typ.eqb t t'
   | _,_ => false
   end.

  Definition nop_eqb o o' :=
    match o, o' with
      | NO_distinct t, NO_distinct t' => Typ.eqb t t'
    end.

  Definition eqb (t t':atom) :=
    match t,t' with
    | Acop o, Acop o' => cop_eqb o o'
    | Auop o t, Auop o' t' => uop_eqb o o' && (t == t')
    | Abop o t1 t2, Abop o' t1' t2' => bop_eqb o o' && (t1 == t1') && (t2 == t2')
    | Anop o t, Anop o' t' => nop_eqb o o' && list_beq Int63Native.eqb t t'
    | Aapp a la, Aapp b lb => (a == b) && list_beq Int63Native.eqb la lb
    | _, _ => false
    end.

  Ltac preflect t :=
    let Heq := fresh "Heq" in
      let Hd := fresh "Hd" in
        destruct t as [Heq | Hd];simpl;
          [ | constructor;intros Heq;elim Hd;inversion Heq;trivial].

  Lemma reflect_cop_eqb_CO_int : forall i1 i2, (i1 == i2) <-> (CO_int i1 = CO_int i2).
  Proof.
    intros;split;intro;assert (i1 = i2).
    apply eqb_spec.
    apply H.
    rewrite H0.
    trivial.
    inversion H.
    trivial.
    apply eqb_spec.
    trivial.
  Qed.
  

  Lemma reflect_cop_eqb : forall o1 o2, reflect (o1 = o2) (cop_eqb o1 o2).
  Proof.
   destruct o1;destruct o2;simpl;try (constructor;trivial;discriminate);apply iff_reflect;split;apply reflect_cop_eqb_CO_int.
  Qed.


  Lemma reflect_cop_eqb_UO_index : forall i1 i2, (i1 == i2) <-> (UO_index i1 = UO_index i2).
  Proof.
    intros;split;intro;assert (i1 = i2).
    apply eqb_spec.
    apply H.
    rewrite H0.
    trivial.
    inversion H.
    trivial.
    apply eqb_spec.
    trivial.
  Qed.

  Lemma reflect_uop_eqb : forall o1 o2, reflect (o1 = o2) (uop_eqb o1 o2).
  Proof.
   destruct o1;destruct o2;simpl;try (constructor;trivial;discriminate);apply iff_reflect;split;apply reflect_cop_eqb_UO_index.
  Qed.
 
  Lemma reflect_bop_eqb : forall o1 o2, reflect (o1 = o2) (bop_eqb o1 o2).
  Proof.
   destruct o1;destruct o2;simpl;try (constructor;trivial;discriminate).
   preflect (Typ.reflect_eqb t t0).
   constructor;subst;trivial.
  Qed.

  Lemma reflect_nop_eqb : forall o1 o2, reflect (o1 = o2) (nop_eqb o1 o2).
  Proof.
    intros [t1] [t2]; simpl; preflect (Typ.reflect_eqb t1 t2); constructor; subst; reflexivity.
  Qed.

  Lemma reflect_eqb : forall t1 t2, reflect (t1 = t2) (eqb t1 t2).
  Proof.
    destruct t1;destruct t2;simpl; try (constructor;trivial;discriminate).
    (* Constants *)
    preflect (reflect_cop_eqb c c0);constructor;subst;trivial.
    (* Unary operators *)
    preflect (reflect_uop_eqb u u0); preflect (Int63Properties.reflect_eqb i i0);
      constructor;subst;trivial.
    (* Binary operators *)
    preflect (reflect_bop_eqb b b0); 
    preflect (Int63Properties.reflect_eqb i i1);
    preflect (Int63Properties.reflect_eqb i0 i2);
    constructor;subst;trivial.
    (* N-ary operators *)
    preflect (reflect_nop_eqb n n0); preflect (reflect_list_beq _ _ Int63Properties.reflect_eqb l l0); constructor; subst; reflexivity.
    (* Application *)
    preflect (Int63Properties.reflect_eqb i i0);
    preflect (reflect_list_beq _ _ Int63Properties.reflect_eqb l l0);
    constructor;subst;trivial.
  Qed.
  
  Lemma eqb_spec : forall t1 t2, eqb t1 t2 <-> t1 = t2.
  Proof.
    intros;symmetry;apply reflect_iff;apply reflect_eqb.
  Qed.
  
  (** Typing and interpretation *)
  
  Record val (t:Type) (I:t -> Type) := Val {
    v_type : t;
    v_val : I v_type
  }.

  Section Typing_Interp.
    Variable t_i : PArray.array typ_eqb.

    Local Notation interp_t := (Typ.interp t_i).
    Local Notation interp_ft := (Typ.interp_ftype t_i).

    Definition bval := val Typ.type interp_t.
    Definition Bval := Val Typ.type interp_t.
    Definition tval := val Typ.ftype interp_ft.
    Definition Tval := Val Typ.ftype interp_ft.

    Definition bvtrue : bval := Bval Typ.Tbool true.
    Definition bvfalse : bval := Bval Typ.Tbool false.

    Lemma Bval_inj1 : forall T U t u, Bval T t = Bval U u -> T = U.
    Proof. intros T U t u H; inversion H; auto. Qed.

    Lemma Bval_inj2 : forall T t u, Bval T t = Bval T u -> t = u.
    Proof.
      intros T t u H; assert (H1: (fun (x:bval) =>
      match Typ.cast (v_type _ _ x) T with
        | Typ.Cast k => k _ (v_val _ _ x) = v_val _ _ (Bval T u)
        | Typ.NoCast => True
      end) (Bval T t)).
      rewrite H, Typ.cast_refl; reflexivity.
      simpl in H1; rewrite Typ.cast_refl in H1; auto.
    Qed.

    (* Interprétation d'une fonction*)
    Variable t_func : PArray.array tval.

    (** Type checking of atom assuming an type for hatom *)
    Section Typ_Aux.
      Variable get_type : hatom -> Typ.type.

      Definition typ_cop o := 
        match o with
        | CO_xH => Typ.Tpositive 
        | CO_Z0 => Typ.TZ
        | CO_int a => Typ.Tint
        end.

      Definition typ_uop o :=
        match o with
        | UO_xO => (Typ.Tpositive,Typ.Tpositive) 
        | UO_xI => (Typ.Tpositive,Typ.Tpositive) 
        | UO_Zpos => (Typ.Tpositive, Typ.TZ)
        | UO_Zneg => (Typ.Tpositive, Typ.TZ)
        | UO_Zopp => (Typ.TZ, Typ.TZ)
        | UO_index i => (Typ.Tint, Typ.Tbool)
        end.

      Definition typ_bop o := 
        match o with
        | BO_Zplus  => ((Typ.TZ,Typ.TZ), Typ.TZ) 
        | BO_Zminus => ((Typ.TZ,Typ.TZ), Typ.TZ) 
        | BO_Zmult  => ((Typ.TZ,Typ.TZ), Typ.TZ) 
        | BO_Zlt    => ((Typ.TZ,Typ.TZ), Typ.Tbool) 
        | BO_Zle    => ((Typ.TZ,Typ.TZ), Typ.Tbool) 
        | BO_Zge    => ((Typ.TZ,Typ.TZ), Typ.Tbool) 
        | BO_Zgt    => ((Typ.TZ,Typ.TZ), Typ.Tbool)
        | BO_int_xor => ((Typ.Tint,Typ.Tint),Typ.Tint)
        | BO_eq t   => ((t,t),Typ.Tbool)
        end.

      Definition typ_nop o :=
        match o with
          | NO_distinct t => (t,Typ.Tbool)
        end.

      Fixpoint check_args (args:list hatom) (targs:list Typ.type) :=
        match args, targs with
        | nil, nil => true
        | a::args, t::targs => Typ.eqb (get_type a) t && check_args args targs
        | _, _ => false
        end.

      Definition check_aux (a:atom) (t:Typ.type) : bool := 
        match a with
        | Acop o => Typ.eqb (typ_cop o) t 
        | Auop o a =>
          let (ta,t') := typ_uop o in
          Typ.eqb t' t && Typ.eqb (get_type a) ta
        | Abop o a1 a2 =>
          let (ta,t') := typ_bop o in
          let (ta1,ta2) := ta in
          Typ.eqb t' t && Typ.eqb (get_type a1) ta1 && Typ.eqb (get_type a2) ta2 
        | Anop o a =>
          let (ta,t') := typ_nop o in
          (Typ.eqb t' t) && (List.forallb (fun t1 => Typ.eqb (get_type t1) ta) a)
        | Aapp f args =>
          let (targs,tr) := v_type _ _ (t_func.[f]) in
          check_args args targs && Typ.eqb tr t
        end.

      (* Typing is unique *)

      Lemma unicity : forall a t1 t2,
        check_aux a t1 -> check_aux a t2 -> t1 = t2.
      Proof.
        destruct a;simpl. 
        (* Constants *)
        intros t1 t2;rewrite !Typ.eqb_spec;intros;subst;trivial.
        (* Unary operators *)
        unfold is_true; intros t1 t2;rewrite (surjective_pairing (typ_uop u)),!andb_true_iff.
        intros [H1 _] [H2 _]; change (is_true (Typ.eqb (snd (typ_uop u)) t1)) in H1.
        change (is_true (Typ.eqb (snd (typ_uop u)) t2)) in H2.
        rewrite Typ.eqb_spec in H1, H2;subst;trivial.
        (* Binary operators *)
        unfold is_true; intros t1 t2;rewrite (surjective_pairing (typ_bop b)),
           (surjective_pairing (fst (typ_bop b))) ,!andb_true_iff.
        intros [[H1 _] _] [[H2 _] _]; change (is_true (Typ.eqb (snd (typ_bop b)) t1)) in H1.
        change (is_true (Typ.eqb (snd (typ_bop b)) t2)) in H2.
        rewrite Typ.eqb_spec in H1, H2;subst;trivial.
        (* N-ary operators *)
        intros t1 t2; destruct (typ_nop n) as [ta t']; unfold is_true; rewrite !andb_true_iff; change (is_true (Typ.eqb t' t1) /\ is_true (List.forallb (fun t3 : int => Typ.eqb (get_type t3) ta) l) -> is_true (Typ.eqb t' t2) /\ is_true (List.forallb (fun t3 : int => Typ.eqb (get_type t3) ta) l) -> t1 = t2); rewrite !Typ.eqb_spec; intros [H1 _] [H2 _]; subst; auto.
        (* Application *)
        intros t1 t2;destruct (v_type Typ.ftype interp_ft (t_func.[ i])).
        unfold is_true;rewrite !andb_true_iff;intros [_ H1] [_ H2].
        transitivity t;[ symmetry| ];rewrite <-Typ.eqb_spec;trivial.
      Qed.

      (* Typing is decidable *)

      Lemma check_args_dec : forall tr args targs,
        {exists T : Typ.type,
          check_args args targs && Typ.eqb tr T} +
        {forall T : Typ.type,
          check_args args targs && Typ.eqb tr T = false}.
      Proof.
        intro A; induction args as [ |h l IHl]; simpl.
        (* Base case *)
        intros [ | ]; simpl.
        left; exists A; apply Typ.eqb_refl.
        intros; right; reflexivity.
        (* Inductive case *)
        intros [ |B targs]; simpl.
        right; reflexivity.
        case (Typ.eqb (get_type h) B); simpl; auto.
      Qed.

      Lemma check_aux_dec : forall a,
        {exists T, check_aux a T} + {forall T, check_aux a T = false}.
      Proof.
        intros [op|op h|op h1 h2|op ha|f args]; simpl.
        (* Constants *)
        left; destruct op; simpl.
        exists Typ.Tpositive; auto.
        exists Typ.TZ; auto.
        exists Typ.Tint; auto.
        (* Unary operators *)
        destruct op; simpl; try (case (Typ.eqb (get_type h) Typ.Tpositive); [left; exists Typ.Tpositive|right; intro; rewrite andb_false_r]; reflexivity); try (case (Typ.eqb (get_type h) Typ.Tpositive); [left; exists Typ.TZ|right; intro; rewrite andb_false_r]; reflexivity);try (case (Typ.eqb (get_type h) Typ.TZ); [left; exists Typ.TZ|right; intro; rewrite andb_false_r]; reflexivity);case (Typ.eqb (get_type h) Typ.Tint); [left; exists Typ.Tbool|right; intro; rewrite andb_false_r]; reflexivity.
        (* Binary operators *)
        destruct op; simpl; try (case (Typ.eqb (get_type h1) Typ.TZ); [case (Typ.eqb (get_type h2) Typ.TZ); [left; exists Typ.TZ|right; intro; rewrite andb_false_r]|right; intro; rewrite andb_false_r]; reflexivity); try (case (Typ.eqb (get_type h1) Typ.TZ); [case (Typ.eqb (get_type h2) Typ.TZ); [left; exists Typ.Tbool|right; intro; rewrite andb_false_r]|right; intro; rewrite andb_false_r]; reflexivity); try (case (Typ.eqb (get_type h1) t); [case (Typ.eqb (get_type h2) t); [left; exists Typ.Tbool|right; intro; rewrite andb_false_r]|right; intro; rewrite andb_false_r]; reflexivity); case (Typ.eqb (get_type h1) Typ.Tint); [case (Typ.eqb (get_type h2) Typ.Tint); [left; exists Typ.Tint|right; intro; rewrite andb_false_r]|right; intro; rewrite andb_false_r]; reflexivity.
        (* N-ary operators *)
        destruct op as [ty]; simpl; case (List.forallb (fun t1 : int => Typ.eqb (get_type t1) ty) ha).
        left; exists Typ.Tbool; auto.
        right; intro T; rewrite andb_false_r; auto.
        (* Application *)
        case (v_type Typ.ftype interp_ft (t_func .[ f])); intros; apply check_args_dec.
      Qed.

    End Typ_Aux.
    (** Interpretation of hatom assuming an interpretation for atom *)
    Section Interp_Aux.

      Variable interp_hatom : hatom -> bval.

      Definition apply_unop (t  r : Typ.type)
            (op : interp_t t -> interp_t r) (tv:bval) :=
        let (t', v) := tv in
        match Typ.cast t' t with
        | Typ.Cast k => Bval r (op (k _ v))
        | _ => bvtrue
        end.

      Definition apply_binop (t1 t2 r : Typ.type)
            (op : interp_t t1 -> interp_t t2 -> interp_t r) (tv1 tv2:bval) :=
        let (t1', v1) := tv1 in
        let (t2', v2) := tv2 in
        match Typ.cast t1' t1, Typ.cast t2' t2 with
        | Typ.Cast k1, Typ.Cast k2 => Bval r (op (k1 _ v1) (k2 _ v2))
        | _, _ => bvtrue
        end.

      Fixpoint apply_func
           targs tr (f:interp_ft (targs,tr)) (lv:list bval) : bval :=
        match targs as targs0 return interp_ft (targs0,tr) -> bval with
        | nil => fun v =>
          match lv with
          | nil => Bval tr v
          | _ => bvtrue
          end
        | t::targs => fun f =>
          match lv with
          | v::lv =>
            let (tv,v) := v in
            match Typ.cast tv t with
            | Typ.Cast k =>
              let f := f (k _ v) in apply_func targs tr f lv
            | _ => bvtrue
            end
          | _ => bvtrue
          end
        end f.

      Definition interp_cop o :=
        match o with
        | CO_xH => Bval Typ.Tpositive xH
        | CO_Z0 => Bval Typ.TZ Z0
        | CO_int a => Bval Typ.Tint a
        end.

      Definition interp_uop o :=    
        match o with
        | UO_xO   => apply_unop Typ.Tpositive Typ.Tpositive xO
        | UO_xI   => apply_unop Typ.Tpositive Typ.Tpositive xI
        | UO_Zpos => apply_unop Typ.Tpositive Typ.TZ Zpos
        | UO_Zneg => apply_unop Typ.Tpositive Typ.TZ Zneg
        | UO_Zopp => apply_unop Typ.TZ Typ.TZ Zopp
        | UO_index a => apply_unop Typ.Tint Typ.Tbool (Int63Op.get_digit a)
        end.

      Definition interp_bop o :=
         match o with
         | BO_Zplus => apply_binop Typ.TZ Typ.TZ Typ.TZ Zplus
         | BO_Zminus => apply_binop Typ.TZ Typ.TZ Typ.TZ Zminus
         | BO_Zmult => apply_binop Typ.TZ Typ.TZ Typ.TZ Zmult
         | BO_Zlt => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zlt_bool
         | BO_Zle => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zle_bool
         | BO_Zge => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zge_bool
         | BO_Zgt => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zgt_bool
         | BO_int_xor => apply_binop Typ.Tint Typ.Tint Typ.Tint Int63Native.lxor
         | BO_eq t => apply_binop t t Typ.Tbool (Typ.i_eqb t_i t)
         end.

      Fixpoint compute_interp ty acc l :=
        match l with
          | nil => Some acc
          | a::q =>
            let (ta,va) := interp_hatom a in
            match Typ.cast ta ty with
              | Typ.Cast ka => compute_interp ty ((ka _ va)::acc) q
              | _ => None
            end
        end.

      (* Lemma compute_interp_spec : forall ty l acc, *)
      (*   match compute_interp ty acc l with *)
      (*     | Some l' => forall i, In i l' <-> (In i acc \/ (exists a, In a l /\ interp_hatom a = Bval ty i)) *)
      (*     | None => exists a, In a l /\ let (ta,_) := interp_hatom a in ta <> ty *)
      (*   end. *)
      (* Proof. *)
      (*   intro ty; induction l as [ |a q IHq]; simpl. *)
      (*   intros acc i; split. *)
      (*   intro H; left; auto. *)
      (*   intros [H|[a [H _]]]; auto; elim H. *)
      (*   intro acc; case_eq (interp_hatom a); intros ta va Heq; rewrite Typ.neq_cast; case_eq (Typ.eqb ta ty). *)
      (*   change (Typ.eqb ta ty = true) with (is_true (Typ.eqb ta ty)); rewrite Typ.eqb_spec; intro; subst ta; rewrite Typ.cast_refl; generalize (IHq (va :: acc)); clear IHq; case (compute_interp ty (va :: acc) q). *)
      (*   intros l IH i; rewrite (IH i); clear IH; split; intros [H|[a1 [H1 H2]]]. *)
      (*   inversion H; auto. *)
      (*   subst va; clear H; right; exists a; split; auto. *)
      (*   right; exists a1; split; auto. *)
      (*   left; constructor 2; auto. *)
      (*   destruct H1 as [H1|H1]. *)
      (*   subst a1; left; constructor 1; rewrite Heq in H2; apply (Bval_inj2 ty); auto. *)
      (*   right; exists a1; auto. *)
      (*   intros [a1 [H1 H2]]; exists a1; split; auto. *)
      (*   intro H; exists a; split; auto; rewrite Heq; intro H1; subst ta; rewrite Typ.eqb_refl in H; discriminate. *)
      (* Qed. *)

      Lemma compute_interp_spec : forall ty l acc,
        match compute_interp ty acc l with
          | Some l' => forall i j, In2 i j l' <-> (In2 i j acc \/ (In j acc /\ exists a, In a l /\ interp_hatom a = Bval ty i) \/ (exists a b, In2 b a l /\ interp_hatom a = Bval ty i /\ interp_hatom b = Bval ty j))
          | None => exists a, In a l /\ let (ta,_) := interp_hatom a in ta <> ty
        end.
      Proof.
        intro ty; induction l as [ |a q IHq]; simpl.
        intros acc i; split.
        intro H; left; auto.
        intros [H|[[_ [a [H _]]]|[a [b [H _]]]]]; auto.
        elim H.
        inversion H.
        intro acc; case_eq (interp_hatom a); intros ta va Heq; rewrite Typ.neq_cast; case_eq (Typ.eqb ta ty).
        change (Typ.eqb ta ty = true) with (is_true (Typ.eqb ta ty)); rewrite Typ.eqb_spec; intro; subst ta; rewrite Typ.cast_refl; generalize (IHq (va :: acc)); clear IHq; case (compute_interp ty (va :: acc) q).
        intros l IH i j; rewrite (IH i j); clear IH; split.
        intros [H|[[H [b [H1 H2]]]|[b [c [H [H1 H2]]]]]].
        inversion H; clear H.
        subst i l0; right; left; split; auto; exists a; split; auto.
        subst k l0; left; auto.
        inversion H; clear H.
        subst va; right; right; exists b; exists a; repeat split; auto; constructor 1; auto.
        right; left; split; auto; exists b; auto.
        right; right; exists b; exists c; repeat split; auto; constructor 2; auto.
        intros [H|[[H [b [[H1|H1] H2]]]|[b [c [H [H1 H2]]]]]].
        left; constructor 2; auto.
        subst b; rewrite Heq in H2; generalize (Bval_inj2 _ _ _ H2); intro; subst va; left; constructor; auto.
        right; left; split.
        constructor 2; auto.
        exists b; auto.
        inversion H; clear H.
        subst c l0; rewrite Heq in H2; generalize (Bval_inj2 _ _ _ H2); intro; subst va; right; left; split.
        constructor 1; auto.
        exists b; auto.
        subst k l0; right; right; exists b; exists c; auto.
        intros [a1 [H1 H2]]; exists a1; split; auto.
        intro H; exists a; split; auto; rewrite Heq; intro H1; subst ta; rewrite Typ.eqb_refl in H; discriminate.
      Qed.

      (* Lemma compute_interp_spec_rev : forall ty l, *)
      (*   match compute_interp ty nil l with *)
      (*     | Some l' => forall i, In i (rev l') <-> (exists a, In a l /\ interp_hatom a = Bval ty i) *)
      (*     | None => exists a, In a l /\ let (ta,_) := interp_hatom a in ta <> ty *)
      (*   end. *)
      (* Proof. (* ICI *) *)
      (*   intros ty l; generalize (compute_interp_spec ty l nil); case (compute_interp ty nil l); auto; intros l' H i; rewrite <- In_rev, (H i); split; auto; intros [H1|H1]; auto; inversion H1. *)
      (* Qed. *)

      Lemma compute_interp_spec_rev : forall ty l,
        match compute_interp ty nil l with
          | Some l' => forall i j, In2 j i (rev l') <-> (exists a b, In2 b a l /\ interp_hatom a = Bval ty i /\ interp_hatom b = Bval ty j)
          | None => exists a, In a l /\ let (ta,_) := interp_hatom a in ta <> ty
        end.
      Proof.
        intros ty l; generalize (compute_interp_spec ty l nil); case (compute_interp ty nil l); auto; intros l' H i j; rewrite In2_rev, (H i j); split; auto; intros [H1|[[H1 _]|H1]]; auto; inversion H1.
      Qed.

      Definition interp_aux (a:atom) : bval :=
        match a with
        | Acop o => interp_cop o
        | Auop o a => interp_uop o (interp_hatom a)
        | Abop o a1 a2 => interp_bop o (interp_hatom a1) (interp_hatom a2)
        | Anop (NO_distinct t) a =>
          match compute_interp t nil a with
            | Some l => Bval Typ.Tbool (distinct (Typ.i_eqb t_i t) (rev l))
            | None => bvtrue
          end
        | Aapp f args =>
          let (tf,f) := t_func.[f] in
          let lv := List.map interp_hatom args in
          apply_func (fst tf) (snd tf) f lv
        end.

      Definition interp_bool (v:bval) : bool :=
        let (t,v) := v in
        match Typ.cast t Typ.Tbool with
        | Typ.Cast k => k _ v
        | _ => true
        end.


      (* If an atom is well-typed, it has an interpretation *)

      Variable get_type : hatom -> Typ.type.
      Hypothesis check_aux_interp_hatom : forall h,
        exists v, interp_hatom h = (Bval (get_type h) v).

      Lemma check_args_interp_aux : forall t l f,
        (let (targs, tr) := v_type Typ.ftype interp_ft f in
          check_args get_type l targs && Typ.eqb tr t) ->
        exists v : interp_t t,
          (let (tf, f0) := f in
            apply_func (fst tf) (snd tf) f0 (List.map interp_hatom l)) =
          Bval t v.
      Proof.
        intro A; induction l as [ |h l IHl]; simpl; intros [tf f]; simpl.
        (* Base case *)
        destruct tf as [[ | ] tr]; try discriminate; simpl; rewrite Typ.eqb_spec; intro; subst tr; exists f; auto.
        (* Inductive case *)
        destruct tf as [[ |B targs] tr]; try discriminate; simpl; rewrite <- andb_assoc; unfold is_true; rewrite andb_true_iff; change (Typ.eqb (get_type h) B = true /\ check_args get_type l targs && Typ.eqb tr A = true) with (is_true (Typ.eqb (get_type h) B) /\ is_true (check_args get_type l targs && Typ.eqb tr A)); rewrite Typ.eqb_spec; intros [H1 H2]; destruct (check_aux_interp_hatom h) as [v0 Heq0]; rewrite Heq0; generalize v0 Heq0; rewrite H1; intros v1 Heq1; simpl; generalize (IHl (Tval (targs,tr) (f v1))); simpl; intro IH; destruct (IH H2) as [v2 Heq2]; exists v2; rewrite Typ.cast_refl; auto.
      Qed.

      Lemma check_aux_interp_aux_aux : forall a t,
         check_aux get_type a t ->
         exists v, interp_aux a = (Bval t v).
      Proof.
        intros [op|op h|op h1 h2|op ha|f l]; simpl.
        (* Constants *)
        destruct op; intros [j| | | | ]; simpl; try discriminate; intros _.
        exists 1%positive; auto.
        exists 0%Z; auto.
        exists i%int63; auto.
        (* Unary operators *)
        destruct op; intros [j| | | | ]; simpl; try discriminate; rewrite Typ.eqb_spec; intro H1; destruct (check_aux_interp_hatom h) as [x Hx]; rewrite Hx; simpl; generalize x Hx; rewrite H1; intros y Hy; rewrite Typ.cast_refl.
        exists (y~0)%positive; auto.
        exists (y~1)%positive; auto.
        exists (Zpos y); auto.
        exists (Zneg y); auto.
        exists (- y)%Z; auto.
        exists (get_digit i y); auto.
        (* Binary operators *)
        destruct op as [ | | | | | | | |A]; intros [i| | | | ]; simpl; try discriminate; unfold is_true; rewrite andb_true_iff; try (change (Typ.eqb (get_type h1) Typ.TZ = true /\ Typ.eqb (get_type h2) Typ.TZ = true) with (is_true (Typ.eqb (get_type h1) Typ.TZ) /\ is_true (Typ.eqb (get_type h2) Typ.TZ)); rewrite !Typ.eqb_spec; intros [H1 H2]; destruct (check_aux_interp_hatom h1) as [x1 Hx1]; rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl; generalize x1 Hx1 x2 Hx2; rewrite H1, H2; intros y1 Hy1 y2 Hy2; rewrite !Typ.cast_refl).
        exists (y1 + y2)%Z; auto.
        exists (y1 - y2)%Z; auto.
        exists (y1 * y2)%Z; auto.
        exists (y1 <? y2)%Z; auto.
        exists (y1 <=? y2)%Z; auto.
        exists (y1 >=? y2)%Z; auto.
        exists (y1 >? y2)%Z; auto.
        change (Typ.eqb (get_type h1) Typ.Tint = true /\ Typ.eqb (get_type h2) Typ.Tint = true) with (is_true (Typ.eqb (get_type h1) Typ.Tint) /\ is_true (Typ.eqb (get_type h2) Typ.Tint)).
        rewrite !Typ.eqb_spec; intros [H1 H2]; destruct (check_aux_interp_hatom h1) as [x1 Hx1]; rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl; generalize x1 Hx1 x2 Hx2; rewrite H1, H2; intros y1 Hy1 y2 Hy2; rewrite !Typ.cast_refl.
        exists (y1 lxor y2)%int63; auto.
        change (Typ.eqb (get_type h1) A = true /\ Typ.eqb (get_type h2) A = true) with (is_true (Typ.eqb (get_type h1) A) /\ is_true (Typ.eqb (get_type h2) A)); rewrite !Typ.eqb_spec; intros [H1 H2]; destruct (check_aux_interp_hatom h1) as [x1 Hx1]; rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl; generalize x1 Hx1 x2 Hx2; rewrite H1, H2; intros y1 Hy1 y2 Hy2; rewrite !Typ.cast_refl; exists (Typ.i_eqb t_i A y1 y2); auto.
        (* N-ary operators *)
        destruct op as [A]; simpl; intros [ | | | | ]; try discriminate; simpl; intros _; case (compute_interp A nil ha).
        intro l; exists (distinct (Typ.i_eqb t_i A) (rev l)); auto.
        exists true; auto.
        (* Application *)
        intro t; apply check_args_interp_aux.
      Qed.


      (* If an atom is not well-typed, its interpretation is bvtrue *)

      Lemma check_args_interp_aux_contr : forall l f,
        (forall T : Typ.type,
          (let (targs, tr) := v_type Typ.ftype interp_ft f in
            check_args get_type l targs && Typ.eqb tr T) = false) ->
        (let (tf, f0) := f in
          apply_func (fst tf) (snd tf) f0 (List.map interp_hatom l)) = bvtrue.
        induction l as [ |h l IHl]; simpl; intros [tf f]; simpl.
        (* Base case *)
        destruct tf as [[ | ] tr]; simpl; auto; intro H; generalize (H tr); rewrite Typ.eqb_refl; discriminate.
        (* Inductive case *)
        destruct tf as [[ |B targs] tr]; simpl; auto. intro H. destruct (check_aux_interp_hatom h) as [v Hv]. rewrite Hv. simpl. assert (H2: (Typ.eqb (get_type h) B = false) \/ (forall T : Typ.type, check_args get_type l targs && Typ.eqb tr T = false)) by (case_eq (Typ.eqb (get_type h) B); try (intros; left; reflexivity); intro Heq; right; intro T; generalize (H T); rewrite Heq; auto). destruct H2 as [H2|H2]; rewrite Typ.neq_cast.
        rewrite H2. auto.
        case_eq (Typ.eqb (get_type h) B); auto. change (Typ.eqb (get_type h) B = true) with (is_true (Typ.eqb (get_type h) B)). rewrite Typ.eqb_spec. intro; subst B. rewrite Typ.cast_refl. apply (IHl (Tval (targs,tr) (f v))). auto.
      Qed.

      Lemma check_aux_interp_aux_contr_aux : forall a,
        (forall T, check_aux get_type a T = false) ->
        interp_aux a = bvtrue.
      Proof.
        intros [op|op h|op h1 h2|op ha|f l]; simpl.
        (* Constants *)
        destruct op; simpl; intro H.
        discriminate (H Typ.Tpositive).
        discriminate (H Typ.TZ).
        discriminate (H Typ.Tint).
        (* Unary operators *)
        destruct op; simpl; intro H; destruct (check_aux_interp_hatom h) as [v Hv]; rewrite Hv; simpl; rewrite Typ.neq_cast; try (pose (H2 := H Typ.Tpositive); simpl in H2; rewrite H2; auto); try (pose (H2 := H Typ.TZ); simpl in H2; rewrite H2; auto); pose (H2 := H Typ.Tbool);simpl in H2; rewrite H2;auto.
        (* Binary operators *)
        destruct op; simpl; intro H; destruct (check_aux_interp_hatom h1) as [v1 Hv1]; destruct (check_aux_interp_hatom h2) as [v2 Hv2]; rewrite Hv1, Hv2; simpl; try (pose (H2 := H Typ.TZ); simpl in H2; rewrite andb_false_iff in H2; destruct H2 as [H2|H2]; [rewrite (Typ.neq_cast (get_type h1)), H2|rewrite (Typ.neq_cast (get_type h2)), H2; case (Typ.cast (get_type h1) Typ.TZ)]; auto); try (pose (H2 := H Typ.Tint); simpl in H2; rewrite andb_false_iff in H2; destruct H2 as [H2|H2]; [rewrite (Typ.neq_cast (get_type h1)), H2|rewrite (Typ.neq_cast (get_type h2)), H2; case (Typ.cast (get_type h1) Typ.Tint)]; auto); try (pose (H2 := H Typ.Tbool); simpl in H2; rewrite andb_false_iff in H2; destruct H2 as [H2|H2]; [rewrite (Typ.neq_cast (get_type h1)), H2|rewrite (Typ.neq_cast (get_type h2)), H2; case (Typ.cast (get_type h1) Typ.TZ)]; auto); case (Typ.cast (get_type h1) t); auto.
        (* N-ary operators *)
        destruct op as [A]; simpl; intro H; generalize (H Typ.Tbool); simpl; clear H; assert (H: forall l1, List.forallb (fun t1 : int => Typ.eqb (get_type t1) A) ha = false -> match compute_interp A l1 ha with | Some l => Bval Typ.Tbool (distinct (Typ.i_eqb t_i A) (rev l)) | None => bvtrue end = bvtrue).
        induction ha as [ |h ha Iha]; simpl.
        intros; discriminate.
        intro l1; destruct (check_aux_interp_hatom h) as [vh Hh]; case_eq (Typ.eqb (get_type h) A); simpl.
        change (Typ.eqb (get_type h) A = true) with (is_true (Typ.eqb (get_type h) A)); rewrite Typ.eqb_spec; intro; subst A; intro H; rewrite Hh; simpl; rewrite Typ.cast_refl; apply Iha; auto.
        intros H _; rewrite Hh; simpl; rewrite (Typ.cast_diff _ _ H); auto.
        apply H.
        (* Application *)
        apply check_args_interp_aux_contr.
      Qed.

    End Interp_Aux.

    Section Interp_get.

      Variable t_atom : PArray.array atom.

      Definition t_interp : PArray.array bval :=
        PArray.foldi_left (fun i t_a a => t_a.[i <- interp_aux (PArray.get t_a) a])
          (PArray.make (PArray.length t_atom) (interp_cop CO_xH)) t_atom.

      Definition lt_atom i a :=
        match a with
        | Acop _ => true
        | Auop _ h => h < i
        | Abop _ h1 h2 => (h1 < i) && (h2 < i)
        | Anop _ ha => List.forallb (fun h => h < i) ha
        | Aapp f args => List.forallb (fun h => h < i) args
        end.

      Lemma lt_interp_aux :
         forall f1 f2 i, (forall j, j < i -> f1 j = f2 j) ->
         forall a, lt_atom i a ->
             interp_aux f1 a = interp_aux f2 a.
      Proof.
        intros f1 f2 i Hf; destruct a;simpl;intros;auto.
        (* Unary operators *)
        rewrite Hf;trivial.
        (* Binary operators *)
        unfold is_true in H;rewrite andb_true_iff in H;destruct H;rewrite !Hf;trivial.
        (* N-ary operators *)
        destruct n as [A]; replace (compute_interp f1 A nil l) with (compute_interp f2 A nil l); trivial; assert (H1: forall acc, compute_interp f2 A acc l = compute_interp f1 A acc l); auto; induction l as [ |k l IHl]; simpl; auto; intro acc; simpl in H; unfold is_true in H; rewrite andb_true_iff in H; destruct H as [H1 H2]; rewrite (Hf _ H1); destruct (f2 k) as [ta va]; destruct (Typ.cast ta A) as [ka| ]; auto.
        (* Application *)
        replace (List.map f1 l) with (List.map f2 l); trivial.
        induction l;simpl in H |- *;trivial.
        unfold is_true in H;rewrite andb_true_iff in H;destruct H;rewrite Hf, IHl;trivial.
      Qed.

      Definition wf := PArray.forallbi lt_atom t_atom.

      Hypothesis wf_t_i : wf.

      Lemma length_t_interp : length t_interp = length t_atom.
      Proof.
        unfold t_interp;apply PArray.foldi_left_Ind with
          (P := fun i a => length a = length t_atom).
        intros;rewrite length_set;trivial.
        rewrite length_make, ltb_length;trivial.
      Qed.

      Lemma default_t_interp : default t_interp = interp_cop CO_xH.
      Proof.
        unfold t_interp;apply PArray.foldi_left_Ind with
          (P := fun i a => default a = interp_cop CO_xH).
        intros;rewrite default_set;trivial.
        apply default_make.
      Qed.

      Lemma t_interp_wf_lt : forall i, i < PArray.length t_atom ->
         t_interp.[i] = interp_aux (PArray.get t_interp) (t_atom.[i]).
      Proof.
        set (P' i t := length t = length t_atom ->
               forall j, j < i ->
               t.[j] = interp_aux (PArray.get t) (t_atom.[j])).
        assert (P' (length t_atom) t_interp).
         unfold is_true, wf in wf_t_i;rewrite PArray.forallbi_spec in wf_t_i.
         unfold t_interp;apply foldi_left_Ind;unfold P';intros.
         rewrite length_set in H1.
         destruct (Int63Properties.reflect_eqb j i).
          rewrite e, PArray.get_set_same.
          apply lt_interp_aux with (2:= wf_t_i i H).
          intros;rewrite get_set_other;trivial.
          intros Heq;elim (not_ltb_refl i);rewrite Heq at 1;trivial.
          rewrite H1;trivial.
         assert (j < i).
          assert ([|j|] <> [|i|]) by(intros Heq1;elim n;apply to_Z_inj;trivial).
          generalize H2;unfold is_true;rewrite !ltb_spec,
            (to_Z_add_1 _ _ H);auto with zarith.
         rewrite get_set_other, H0;auto.
         apply lt_interp_aux with (2:= wf_t_i j (ltb_trans _ _ _ H3 H)).
         intros;rewrite get_set_other;trivial.
         intros Heq;elim (not_ltb_refl i);apply ltb_trans with j;
           [ rewrite Heq| ];trivial.
         elim (ltb_0 _ H0).
        apply H;apply length_t_interp.
      Qed.

      Hypothesis default_t_atom : default t_atom = Acop CO_xH.

      Lemma t_interp_wf : forall i,
         t_interp.[i] = interp_aux (PArray.get t_interp) (t_atom.[i]).
      Proof.
        intros i;case_eq (i< PArray.length t_atom);intros.
        apply t_interp_wf_lt;trivial.
        rewrite !PArray.get_outofbound;trivial.
        rewrite default_t_atom, default_t_interp;trivial.
        rewrite length_t_interp;trivial.
      Qed.

      Definition get_type' (t_interp':array bval) i := v_type _ _ (t_interp'.[i]).

      Local Notation get_type := (get_type' t_interp).

      (* If an atom is well-typed, it has an interpretation *)

      Lemma check_aux_interp_aux_lt_aux : forall a h,
        (forall j : int,
          j < h ->
          exists v : interp_t (v_type Typ.type interp_t (a .[ j])),
            a .[ j] = Bval (v_type Typ.type interp_t (a .[ j])) v) ->
        forall l, List.forallb (fun h0 : int => h0 < h) l = true ->
          forall (f0: tval),
            exists
              v : interp_t
              (v_type Typ.type interp_t
                (let (tf, f) := f0 in
                  apply_func (fst tf) (snd tf) f (List.map (get a) l))),
              (let (tf, f) := f0 in
                apply_func (fst tf) (snd tf) f (List.map (get a) l)) =
              Bval
              (v_type Typ.type interp_t
                (let (tf, f) := f0 in
                  apply_func (fst tf) (snd tf) f (List.map (get a) l))) v.
      Proof.
        intros a h IH; induction l as [ |j l IHl]; simpl.
        intros _ [[[ | ] tr] f]; simpl.
        exists f; auto.
        exists true; auto.
        rewrite andb_true_iff; intros [H1 H2] [[[ |A targs] tr] f]; simpl.
        exists true; auto.
        destruct (IH j H1) as [x Hx]; rewrite Hx; simpl; case (Typ.cast (v_type Typ.type interp_t (a .[ j])) A); simpl.
        intro k; destruct (IHl H2 (Tval (targs,tr) (f (k interp_t x)))) as [y Hy]; simpl in Hy; rewrite Hy; simpl; exists y; auto.
        exists true; auto.
      Qed.

      Lemma check_aux_interp_aux_lt : forall h, h < length t_atom ->
        forall a,
          (forall j, j < h ->
            exists v, a.[j] = Bval (v_type _ _ (a.[j])) v) ->
          exists v, interp_aux (get a) (t_atom.[h]) =
            Bval (v_type _ _ (interp_aux (get a) (t_atom.[h]))) v.
      Proof.
        unfold wf, is_true in wf_t_i; rewrite forallbi_spec in wf_t_i.
        intros h Hh a IH; generalize (wf_t_i h Hh).
        case (t_atom.[h]); simpl.
        (* Constants *)
        intros [ | | ] _; simpl.
        exists 1%positive; auto.
        exists 0%Z; auto.
        exists i%int63; auto.
        (* Unary operators *)
        intros [ | | | | | ] i H; simpl; destruct (IH i H) as [x Hx]; rewrite Hx; simpl.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists ((k interp_t x)~0)%positive; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists ((k interp_t x)~1)%positive; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists (Zpos (k interp_t x)); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists (Zneg (k interp_t x)); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.TZ); simpl; try (exists true; auto); intro k; exists (- k interp_t x)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tint); simpl; try (intro k; exists (get_digit i0 (k interp_t x)); auto); try (exists true; auto).
        (* Binary operators *)
        intros [ | | | | | | | |A] h1 h2; simpl; rewrite andb_true_iff; intros [H1 H2]; destruct (IH h1 H1) as [x Hx]; destruct (IH h2 H2) as [y Hy]; rewrite Hx, Hy; simpl.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ); simpl; try (exists true; auto); intro k2; exists (k1 interp_t x + k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ); simpl; try (exists true; auto); intro k2; exists (k1 interp_t x - k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ); simpl; try (exists true; auto); intro k2; exists (k1 interp_t x * k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x <? k2 interp_t y); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x <=? k2 interp_t y); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x >=? k2 interp_t y); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x >? k2 interp_t y); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.Tint); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.Tint); simpl; try (intro k2; exists (k1 interp_t x lxor k2 interp_t y)%int63; auto); exists true;auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) A); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) A) as [k2| ]; simpl; try (exists true; reflexivity); exists (Typ.i_eqb t_i A (k1 interp_t x) (k2 interp_t y)); auto.
        (* N-ary operators *)
        intros [A] l; assert (forall acc, List.forallb (fun h0 : int => h0 < h) l = true -> exists v, match compute_interp (get a) A acc l with | Some l0 => Bval Typ.Tbool (distinct (Typ.i_eqb t_i A) (rev l0)) | None => bvtrue end = Bval (v_type Typ.type interp_t match compute_interp (get a) A acc l with | Some l0 => Bval Typ.Tbool (distinct (Typ.i_eqb t_i A) (rev l0)) | None => bvtrue end) v); auto; induction l as [ |i l IHl]; simpl.
        intros acc _; exists (distinct (Typ.i_eqb t_i A) (rev acc)); auto.
        intro acc; rewrite andb_true_iff; intros [H1 H2]; destruct (IH _ H1) as [va Hva]; rewrite Hva; simpl; case (Typ.cast (v_type Typ.type interp_t (a .[ i])) A); simpl; try (exists true; auto); intro k; destruct (IHl (k interp_t va :: acc) H2) as [vb Hvb]; exists vb; auto.
        (* Application *)
        intros i l H; apply (check_aux_interp_aux_lt_aux a h IH l H (t_func.[i])).
      Qed.

      Lemma check_aux_interp_hatom_lt : forall h, h < length t_atom ->
        exists v, t_interp.[h] = Bval (get_type h) v.
      Proof.
        set (P' i t := length t = length t_atom ->
          forall j, j < i ->
            exists v, t.[j] = Bval (v_type Typ.type interp_t (t.[j])) v).
        assert (P' (length t_atom) t_interp).
        unfold t_interp;apply foldi_left_Ind;unfold P';intros.
        rewrite length_set in H1.
        destruct (Int63Properties.reflect_eqb j i).
        rewrite e, PArray.get_set_same.
        apply check_aux_interp_aux_lt; auto.
        rewrite H1; auto.
        assert (j < i).
        assert ([|j|] <> [|i|]) by(intros Heq1;elim n;apply to_Z_inj;trivial).
        generalize H2;unfold is_true;rewrite !ltb_spec,
          (to_Z_add_1 _ _ H);auto with zarith.
        rewrite get_set_other;auto.
        elim (ltb_0 _ H0).
        apply H;apply length_t_interp.
      Qed.

      Lemma check_aux_interp_hatom : forall h,
        exists v, t_interp.[h] = Bval (get_type h) v.
      Proof.
        intros i;case_eq (i< PArray.length t_atom);intros.
        apply check_aux_interp_hatom_lt;trivial.
        unfold get_type'; rewrite !PArray.get_outofbound;trivial.
        rewrite default_t_interp; simpl; exists (1%positive); auto.
        rewrite length_t_interp;trivial.
      Qed.

      Lemma check_aux_interp_aux : forall a t,
         check_aux get_type a t ->
         exists v, interp_aux (get t_interp) a = (Bval t v).
      Proof.
        intros a t; apply check_aux_interp_aux_aux; apply check_aux_interp_hatom.
      Qed.

      (* If an atom is not well-typed, its interpretation if bvtrue *)

      Lemma check_aux_interp_aux_contr : forall a,
        (forall T, check_aux get_type a T = false) ->
        interp_aux (get t_interp) a = bvtrue.
      Proof.
        intros; eapply check_aux_interp_aux_contr_aux; eauto; apply check_aux_interp_hatom.
      Qed.

    End Interp_get.


    Definition get_type t_atom :=
      get_type' (t_interp t_atom).

    Definition wt t_atom :=
      let t_interp := t_interp t_atom in
      let get_type := get_type' t_interp in
        PArray.forallbi (fun i h => check_aux get_type h (get_type i)) t_atom.


    Definition interp_hatom (t_atom : PArray.array atom) :=
      let t_a := t_interp t_atom in
      PArray.get t_a.

    Definition interp t_atom := interp_aux (interp_hatom t_atom).

    Definition interp_form_hatom t_atom : hatom -> bool :=
      let interp := interp_hatom t_atom in
      fun a => interp_bool (interp a).

  End Typing_Interp.

  Definition check_atom t_atom :=
    match default t_atom with
      | Acop CO_xH => wf t_atom
      | _ => false
    end.

  Lemma check_atom_correct : forall t_atom, check_atom t_atom ->
    wf t_atom /\ default t_atom = Acop CO_xH.
  Proof.
    intro t_atom; unfold check_atom; case (default t_atom); try discriminate; intro c; case c; auto; discriminate.
  Qed.

End Atom.

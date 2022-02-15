(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool Int63 Psatz PArray BinNat BinPos ZArith SMT_classes_instances.
Require Import Misc State BVList. (* FArray Equalities DecidableTypeEx. *)
Require FArray.
Require List .
Local Open Scope list_scope.
Local Open Scope array_scope.
Local Open Scope int63_scope.

Hint Unfold is_true : smtcoq_core.


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
  | Fite (_:_lit) (_:_lit) (_:_lit)
   (* Bit-blasting predicate (theory of bit vectors):
        bbT a [l1;...;ln] means [l1;...;ln] is the bitwise representation of a
      (in little endian)
      WARNING: this is a slight infringement of stratification
      *)
  | FbbT (_:atom) (_:list _lit)
  (* TODO: replace [list _lit] with [fargs] *)
  .


  Definition is_Ftrue h :=
    match h with Ftrue => true | _ => false end.

  Definition is_Ffalse h :=
    match h with Ffalse => true | _ => false end.

  Lemma is_Ftrue_correct : forall h, is_Ftrue h -> h = Ftrue.
  Proof. destruct h; trivial;discriminate. Qed.

  Lemma is_Ffalse_correct : forall h, is_Ffalse h -> h = Ffalse.
  Proof. destruct h;trivial;discriminate. Qed.


  Section Interp.
    Variable interp_atom : atom -> bool.
    Variable interp_bvatom : atom -> forall s, BITVECTOR_LIST.bitvector s.

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
        | Fnot2 i l => foldi (fun _ b => negb (negb b)) 0 i (Lit.interp interp_var l)
        | Fand args => afold_left _ true andb (amap (Lit.interp interp_var) args)
        | For args => afold_left _ false orb (amap (Lit.interp interp_var) args)
        | Fimp args => afold_right _ true implb (amap (Lit.interp interp_var) args)
        | Fxor a b => xorb (Lit.interp interp_var a) (Lit.interp interp_var b)
        | Fiff a b => Bool.eqb (Lit.interp interp_var a) (Lit.interp interp_var b)
        | Fite a b c =>
          if Lit.interp interp_var a then Lit.interp interp_var b
          else Lit.interp interp_var c
        | FbbT a ls =>
          let ils := List.map (Lit.interp interp_var) ls in
          let n := N.of_nat (List.length ils) in
          BITVECTOR_LIST.bv_eq (interp_bvatom a n) (BITVECTOR_LIST.of_bits ils)
        end.

    End Interp_form.

    Section Interp_get.

      Variable t_form : array form.

      Definition t_interp : array bool :=
        foldi (fun i t_b =>
            t_b.[i <- interp_aux (get t_b) (t_form.[i])]) 0 (length t_form)
        (make (length t_form) true).

      Fixpoint lt_form i h {struct h} :=
        match h with
        | Fatom _ | Ftrue | Ffalse => true
        | Fnot2 _ l => Lit.blit l < i
        | Fand args | For args | Fimp args =>
          aforallbi (fun _ l => Lit.blit l < i) args
        | Fxor a b | Fiff a b => (Lit.blit a < i) && (Lit.blit b < i)
        | Fite a b c => (Lit.blit a < i) && (Lit.blit b < i) && (Lit.blit c < i)
        | FbbT _ ls => List.forallb (fun l => Lit.blit l < i) ls
        end.

      Lemma lt_form_interp_form_aux :
        forall f1 f2 i h,
          (forall j, j < i -> f1 j = f2 j) ->
          lt_form i h ->
          interp_aux f1 h = interp_aux f2 h.
      Proof.
        destruct h;simpl;intros;trivial;
          try (try apply afold_left_eq; try apply afold_right_eq;unfold is_true in H0;
            rewrite ?forallb_spec, ?aforallbi_spec, ?andb_true_iff in H0;intros;
            rewrite ?length_amap; try rewrite length_amap in H1;
            rewrite ?get_amap by assumption;
              auto using Lit.interp_eq_compat with smtcoq_core).
        - f_equal;auto using Lit.interp_eq_compat.
        - decompose [and] H0; rewrite !(Lit.interp_eq_compat f1 f2);auto.
        - decompose [and] H0; rewrite !(Lit.interp_eq_compat f1 f2);auto.
        - decompose [and] H0; rewrite !(Lit.interp_eq_compat f1 f2);auto.
        - replace (List.map (Lit.interp f2) l) with (List.map (Lit.interp f1) l); auto.
          unfold is_true in H0. rewrite List.forallb_forall in H0.
          apply List.map_ext_in. intros x Hx. apply Lit.interp_eq_compat; auto with smtcoq_core.
      Qed.

      Definition wf := aforallbi lt_form t_form.

      Hypothesis wf_t_i : wf.

      Lemma length_t_interp : length t_interp = length t_form.
      Proof.
        unfold t_interp.
        assert (Bt := to_Z_bounded (length t_form)).
        apply (foldi_ind _ (fun i a => length a = length t_form)).
        rewrite leb_spec, to_Z_0; lia.
        rewrite length_make, leb_length; reflexivity.
        intros;rewrite length_set;trivial.
      Qed.

      Lemma default_t_interp : default t_interp = true.
      Proof.
        unfold t_interp.
        assert (Bt := to_Z_bounded (length t_form)).
        apply (foldi_ind _ (fun i a => default a = true)).
        rewrite leb_spec, to_Z_0; lia.
        apply default_make.
        intros;rewrite default_set;trivial.
      Qed.

      Lemma t_interp_wf : forall i, i < PArray.length t_form ->
        t_interp.[i] = interp_aux (PArray.get t_interp) (t_form.[i]).
      Proof.
        set (P' i t := length t = length t_form ->
          forall j, j < i ->
            t.[j] = interp_aux (PArray.get t) (t_form.[j])).
        assert (P' (length t_form) t_interp).
        unfold is_true, wf in wf_t_i;rewrite aforallbi_spec in wf_t_i.
        unfold t_interp;apply foldi_ind;unfold P';intros.
        apply leb_0.
        elim (ltb_0 _ H0).
        rewrite length_set in H2.
        destruct (reflect_eqb j i).
        rewrite e, get_set_same.
        apply lt_form_interp_form_aux with (2:= wf_t_i i H0).
        intros;rewrite get_set_other;trivial.
        intros Heq;elim (not_ltb_refl i);rewrite Heq at 1;trivial.
        rewrite H2;trivial.
        assert (j < i).
        assert ([|j|] <> [|i|]) by (intros Heq1;elim n;apply to_Z_inj;trivial).
        generalize H3;unfold is_true;rewrite !ltb_spec, (to_Z_add_1 _ _ H0);
          auto with zarith.
        rewrite get_set_other, H1;auto.
        apply lt_form_interp_form_aux with
          (2:= wf_t_i j (ltb_trans _ _ _ H4 H0)).
        intros;rewrite get_set_other;trivial.
        intros Heq;elim (not_ltb_refl i);apply ltb_trans with j;
          [ rewrite Heq| ];trivial.
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


Require OrderedTypeEx.


Module Typ.

  Import FArray.

  Notation index := N (only parsing).

  Inductive type :=
  | TFArray : type -> type -> type
  | Tindex : index -> type
  | TZ : type
  | Tbool : type
  | Tpositive : type
  | TBV : N -> type.

  Definition ftype := (list type * type)%type.

  Section Interp.

    Import OrderedTypeEx.

    Variable t_i : PArray.array typ_compdec.

    Fixpoint interp_compdec_aux (t:type) : {ty: Type & CompDec ty} :=
      match t with
      | TFArray ti te =>
        let iti := interp_compdec_aux ti in
        let ite := interp_compdec_aux te in
        let cti := projT2 iti in
        let cte := projT2 ite in
        let tti := type_compdec cti in
        let tte := type_compdec cte in
        existT (fun ty : Type => CompDec ty)
               (@farray tti
                        tte
                        (@ord_of_compdec tti cti)
                        (@inh_of_compdec tte cte))
               (FArray_compdec tti tte)
      | Tindex i =>
        existT (fun ty : Type => CompDec ty)
               (te_carrier (t_i .[of_Z (Z.of_N i)])) (te_compdec (t_i .[of_Z (Z.of_N i)]))
      | TZ => existT (fun ty : Type => CompDec ty) Z Z_compdec
      | Tbool => existT (fun ty : Type => CompDec ty) bool bool_compdec
      | Tpositive => existT (fun ty : Type => CompDec ty) positive Positive_compdec
      | TBV n => existT (fun ty : Type => CompDec ty) (BITVECTOR_LIST.bitvector n) (BV_compdec n)
      end.

    Definition interp (t:type) : Type := type_compdec (projT2 (interp_compdec_aux t)).

    Definition interp_compdec (t:type) : CompDec (interp t) :=
      projT2 (interp_compdec_aux t).


    Definition interp_ftype (t:ftype) :=
      List.fold_right (fun dom codom => interp dom -> codom)
      (interp (snd t)) (fst t).


    Global Instance dec_interp (t:type) : DecType (interp t) :=
      (@EqbToDecType _ (@eqbtype_of_compdec (interp t) (interp_compdec t))).

    Global Instance ord_interp (t:type) : OrdType (interp t) :=
      @ord_of_compdec (interp t) (interp_compdec t).

    Global Instance comp_interp (t:type) : Comparable (interp t) :=
      @comp_of_compdec (interp t) (interp_compdec t).

    Global Instance inh_interp (t:type) : Inhabited (interp t) :=
      @inh_of_compdec (interp t) (interp_compdec t).


    (* Boolean equality over interpretation of a btype *)
    Section Interp_Equality.


      Definition i_eqb (t:type) : interp t -> interp t -> bool :=
        eqb_of_compdec (interp_compdec t).


      Lemma eqb_compdec_spec {t} (c : CompDec t) : forall x y,
          eqb_of_compdec c x y = true <-> x = y.
      Proof.
        intros x y.
        destruct c as [TY [E HE] O C I].
        unfold eqb_of_compdec.
        simpl. now rewrite HE.
      Qed.

      Lemma eqb_compdec_spec_false {t} (c : CompDec t) : forall x y,
          eqb_of_compdec c x y = false <-> x <> y.
      Proof.
        intros x y.
        apply eqb_spec_false.
      Qed.

      Lemma i_eqb_spec : forall t x y, i_eqb t x y <-> x = y.
      Proof.
        intros.
        unfold i_eqb.
        apply eqb_compdec_spec.
      Qed.

      Lemma i_eqb_spec_false : forall t x y, i_eqb t x y = false <-> x <> y.
      Proof.
        intros.
        unfold i_eqb.
        apply eqb_compdec_spec_false.
      Qed.

      Lemma reflect_eqb_compdec {t} (c : CompDec t) : forall x y,
          reflect (x = y) (eqb_of_compdec c x y).
      Proof.
        intros x y.
        apply SMT_classes.reflect_eqb.
      Qed.


      Lemma reflect_i_eqb : forall t x y, reflect (x = y) (i_eqb t x y).
      Proof.
        intros.
        unfold i_eqb.
        apply reflect_eqb_compdec.
      Qed.

     Lemma i_eqb_sym : forall t x y, i_eqb t x y = i_eqb t y x.
     Proof. intros. apply eqb_sym2. Qed.


      Definition i_eqb_eqb (t:type) : interp t -> interp t -> bool :=
        match t with
        | Tindex i => eqb_of_compdec (t_i.[of_Z (Z.of_N i)]).(te_compdec)
        | TZ => Z.eqb (* Zeq_bool *)
        | Tbool => Bool.eqb
        | Tpositive => Pos.eqb
        | TBV n => (@BITVECTOR_LIST.bv_eq n)
        | TFArray ti te => i_eqb (TFArray ti te)
        end.


      Lemma eqb_compdec_refl {t} (c : CompDec t) : forall x,
          eqb_of_compdec c x x = true.
      Proof.
        intro x.
        apply eqb_refl.
      Qed.

      Lemma i_eqb_refl : forall t x, i_eqb t x x.
      Proof.
        intros.
        unfold i_eqb.
        apply eqb_compdec_refl.
      Qed.


      Lemma eqb_compdec_trans {t} (c : CompDec t) : forall x y z,
          eqb_of_compdec c x y = true ->
          eqb_of_compdec c y z = true ->
          eqb_of_compdec c x z = true.
      Proof.
        intros x y z.
        apply eqb_trans.
      Qed.

      Lemma i_eqb_trans : forall t x y z, i_eqb t x y -> i_eqb t y z -> i_eqb t x z.
      Proof.
        intros.
        unfold i_eqb.
        apply (eqb_compdec_trans _ x y z); auto.
      Qed.


      Lemma i_eqb_t : forall t x y, i_eqb t x y = i_eqb_eqb t x y.
      Proof.
        intros.
        unfold i_eqb_eqb.
        destruct t; simpl; auto; unfold i_eqb; simpl.
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

    Arguments Cast {A B} k.
    Arguments NoCast {A B}.

    Notation idcast := (Cast (fun P x => x)).
    (* La fonction cast calcule cast_result *)

    Fixpoint positive_cast (n m : positive) {struct n} :
      option (forall P, P n -> P m) :=
      match n, m return option (forall P, P n -> P m) with
      | xH, xH => Some (fun P x => x)
      | xO p, xO q =>
        match positive_cast p q with
        | Some k => Some (fun P => k (fun y => P (xO y)))
        | None => None
        end
      | xI p, xI q =>
        match positive_cast p q with
        | Some k => Some (fun P => k (fun y => P (xI y)))
        | None => None
        end
      | _, _ => None
      end.

    Definition N_cast (n m : N) : option (forall P, P n -> P m) :=
      match n, m return option (forall P, P n -> P m) with
      | N0, N0 => Some (fun P x => x)
      | Npos p, Npos q =>
        match positive_cast p q with
        | Some k => Some (fun P => k (fun y => P (Npos y)))
        | None => None
        end
      | _, _ => None
      end.


    (* TODO *)

    Fixpoint cast (A B: type) : cast_result A B :=
      match A as C, B as D return cast_result C D with
      | Tindex i, Tindex j =>
        match N_cast i j with
        | Some k => Cast (fun P => k (fun y => P (Tindex y)))
        | None => NoCast
        end
      | TZ, TZ => idcast
      | Tbool, Tbool => idcast
      | Tpositive, Tpositive => idcast
      | TBV n, TBV m =>
        match N_cast n m with
        | Some k => Cast (fun P => k (fun y => P (TBV y)))
        | None => NoCast
        end
      | TFArray k1 e1, TFArray k2 e2 =>
        match cast k1 k2, cast e1 e2 with
        | Cast kk, Cast ke =>
          let ka P :=
              let Pb d := P (TFArray d e1) in
              let Pc d := P (TFArray k2 d) in
              fun x => ke Pc (kk Pb x)
          in Cast ka
        | _, _ => NoCast
        end
      | _, _ => NoCast
      end.

    Lemma positive_cast_refl:
      forall p, positive_cast p p = Some (fun P (H : P p) => H).
    Proof. induction p as [p IHp|p IHp| ]; simpl; try rewrite IHp; auto. Qed.

    Lemma N_cast_refl:
      forall n, N_cast n n = Some (fun P (H : P n) => H).
    Proof. intros [ |p]; simpl; try rewrite positive_cast_refl; auto. Qed.

    Fixpoint cast_refl A:
      cast A A = Cast (fun P (H : P A) => H).
    Proof.
      destruct A;simpl;trivial.
      do 2 rewrite cast_refl. easy.
      rewrite N_cast_refl;trivial.
      rewrite N_cast_refl;trivial.
    Qed.


    (* Remark : I use this definition because eqb will not be used only in the interpretation *)
    Fixpoint eqb (A B: type) : bool :=
      match A, B with
      | Tindex i, Tindex j => N.eqb i j
      | TZ, TZ => true
      | Tbool, Tbool => true
      | Tpositive, Tpositive => true
      | TBV n, TBV m => N.eqb n m
      | TFArray k1 e1, TFArray k2 e2 =>
        eqb k1 k2 && eqb e1 e2
      | _,_ => false
      end.


    (* TODO : Move this *)
    Lemma not_false : ~ false.
    Proof. intro;discriminate. Qed.
    Hint Resolve not_false : smtcoq_core.

    Lemma is_true_true : true.
    Proof. reflexivity. Qed.
    Hint Resolve is_true_true : smtcoq_core.

    Lemma not_is_true_eq_false : forall b:bool, ~ b <-> b = false.
    Proof. exact not_true_iff_false. Qed.

    Lemma positive_cast_diff: forall p q, p <> q -> positive_cast p q = None.
    Proof.
      induction p as [p IHp|p IHp| ]; intros [q|q| ]; auto; intro Heq.
      - simpl. rewrite IHp; auto.
        intro H. apply Heq. rewrite H. reflexivity.
      - simpl. rewrite IHp; auto.
        intro H. apply Heq. rewrite H. reflexivity.
      - elim Heq. reflexivity.
    Qed.

    Lemma N_cast_diff: forall n m, n <> m -> N_cast n m = None.
    Proof.
      intros [ |n] [ |m]; auto; intro Heq.
      - elim Heq; reflexivity.
      - simpl. rewrite positive_cast_diff; auto.
        intro H. apply Heq. rewrite H. reflexivity.
    Qed.

    Fixpoint cast_diff A B: eqb A B = false -> cast A B = NoCast.
    Proof.
      destruct A; destruct B;simpl;trivial;try discriminate.
      intros.
      rewrite andb_false_iff in H.
      destruct H; apply cast_diff in H; rewrite H; auto.
      case (cast A1 B1); auto.
      rewrite N.eqb_neq. intro Heq. now rewrite N_cast_diff.
      rewrite N.eqb_neq. intro Heq. now rewrite N_cast_diff.
    Qed.

    Lemma cast_eqb A B k: cast A B = Cast k -> eqb A B = true.
    Proof.
      intros.
      apply not_false_iff_true.
      unfold not.
      intro.
      apply cast_diff in H0.
      rewrite H in H0. inversion H0.
    Qed.

    Lemma neq_cast : forall A B,
      cast A B = (if eqb A B then cast A B else NoCast).
    Proof.
      intros C D;case_eq (eqb C D);trivial;apply cast_diff.
    Qed.

    Fixpoint reflect_eqb x y: reflect (x = y) (eqb x y).
    Proof.
      destruct x;destruct y;simpl;try constructor;trivial;try discriminate.
      apply iff_reflect.
      split.
      intro H. inversion H. subst.
      rewrite andb_true_iff.
      split;
      [specialize (reflect_eqb y1 y1) | specialize (reflect_eqb y2 y2)];
      apply reflect_iff in reflect_eqb; apply reflect_eqb; auto.
      intros.
      rewrite andb_true_iff in H; destruct H.
      apply (reflect_iff _ _ (reflect_eqb x1 y1)) in H.
      apply (reflect_iff _ _ (reflect_eqb x2 y2)) in H0.
      subst; auto.
      apply iff_reflect. rewrite N.eqb_eq. split;intros H;[inversion H | subst]; trivial.
      apply iff_reflect. rewrite N.eqb_eq. split;intros H;[inversion H | subst]; trivial.
    Qed.

    Lemma eqb_spec : forall x y, eqb x y <-> x = y.
    Proof.
      intros.
      symmetry.
      apply reflect_iff.
      apply reflect_eqb.
    Qed.

    Lemma eqb_refl : forall x, eqb x x.
    Proof. intros; rewrite eqb_spec; auto. Qed.


    Lemma cast_eq A B k: cast A B = Cast k -> A = B.
    Proof.
      intros. apply eqb_spec. apply (cast_eqb _ _ k). auto.
    Qed.

    Lemma nocast_refl A B: cast A B = NoCast -> cast B A = NoCast.
    Proof.
      intros.
      apply cast_diff.
      rewrite neq_cast in H.
      case_eq (eqb A B). intro.
      rewrite H0 in H.
      apply eqb_spec in H0.
      rewrite H0 in H.
      rewrite cast_refl in H.
      now contradict H.
      intro.
      apply not_true_iff_false.
      unfold not.
      intro.
      apply eqb_spec in H1.
      rewrite H1 in H0. rewrite eqb_refl in H0. now contradict H0.
    Qed.


  End Cast.


End Typ.

Arguments Typ.Cast {_} {_} _.
Arguments Typ.NoCast {_} {_}.

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
   | CO_BV (_: list bool) (_ :N).

  Inductive unop : Type :=
   | UO_xO
   | UO_xI
   | UO_Zpos
   | UO_Zneg
   | UO_Zopp
   | UO_BVbitOf (_: N) (_: nat)
   | UO_BVnot   (_: N)
   | UO_BVneg   (_: N)
   | UO_BVextr  (i: N) (n0: N) (n1: N) (* TODO n1 first arg *)
   | UO_BVzextn (n: N) (i: N)
   | UO_BVsextn (n: N) (i: N).

  Inductive binop : Type :=
   | BO_Zplus
   | BO_Zminus
   | BO_Zmult
   | BO_Zlt
   | BO_Zle
   | BO_Zge
   | BO_Zgt
   | BO_eq (_ : Typ.type)
   | BO_BVand (_: N)
   | BO_BVor (_: N)
   | BO_BVxor (_: N)
   | BO_BVadd (_: N)
   | BO_BVmult (_: N)
   | BO_BVult (_: N)
   | BO_BVslt (_: N)
   | BO_BVconcat (_: N) (_: N)
   | BO_BVshl (_: N)
   | BO_BVshr (_: N)
   | BO_select (_ : Typ.type) (_ : Typ.type)
   | BO_diffarray (_ : Typ.type) (_ : Typ.type)
  .

  Inductive nop : Type :=
   | NO_distinct (_ : Typ.type).

  Inductive terop : Type :=
   | TO_store (_ : Typ.type) (_ : Typ.type).

  Notation hatom := int (only parsing).

  Inductive atom : Type :=
   | Acop (_: cop)
   | Auop (_ : unop) (_:hatom)
   | Abop (_ : binop) (_:hatom) (_:hatom)
   | Atop (_ : terop) (_:hatom) (_:hatom) (_:hatom)
   | Anop (_ : nop) (_: list hatom)
   | Aapp (_:func) (_: list hatom).


  (* Generic predicates and operations *)

  (** Equality *)
  Definition cop_eqb o o' :=
   match o, o' with
   | CO_xH, CO_xH
   | CO_Z0, CO_Z0 => true
   | CO_BV bv s, CO_BV bv' s' => N.eqb s s' && RAWBITVECTOR_LIST.beq_list bv bv'
   | _,_ => false
   end.

  Definition uop_eqb o o' :=
   match o, o' with
   | UO_xO, UO_xO
   | UO_xI, UO_xI
   | UO_Zpos, UO_Zpos
   | UO_Zneg, UO_Zneg
   | UO_Zopp, UO_Zopp => true
   | UO_BVbitOf s1 n, UO_BVbitOf s2 m => Nat.eqb n m && N.eqb s1 s2
   | UO_BVnot s1, UO_BVnot s2 => N.eqb s1 s2
   | UO_BVneg s1, UO_BVneg s2 => N.eqb s1 s2
   | UO_BVextr i0 n00 n01, UO_BVextr i1 n10 n11 => N.eqb i0 i1 && N.eqb n00 n10 && N.eqb n01 n11
   | UO_BVzextn s1 i1, UO_BVzextn s2 i2 => N.eqb s1 s2 && N.eqb i1 i2
   | UO_BVsextn s1 i1, UO_BVsextn s2 i2 => N.eqb s1 s2 && N.eqb i1 i2
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
   | BO_Zgt, BO_Zgt => true
   | BO_eq t, BO_eq t' => Typ.eqb t t'
   | BO_BVand s1, BO_BVand s2 => N.eqb s1 s2
   | BO_BVor s1, BO_BVor s2
   | BO_BVxor s1, BO_BVxor s2
   | BO_BVadd s1, BO_BVadd s2
   | BO_BVmult s1, BO_BVmult s2 => N.eqb s1 s2
   | BO_BVult s1, BO_BVult s2 => N.eqb s1 s2
   | BO_BVslt s1, BO_BVslt s2 => N.eqb s1 s2
   | BO_BVconcat s1 s2, BO_BVconcat s3 s4 => N.eqb s1 s3 && N.eqb s2 s4
   | BO_BVshl s1, BO_BVshl s2 => N.eqb s1 s2
   | BO_BVshr s1, BO_BVshr s2 => N.eqb s1 s2
   | BO_select ti te, BO_select ti' te'
   | BO_diffarray ti te, BO_diffarray ti' te' => Typ.eqb ti ti' && Typ.eqb te te'
   | _,_ => false
   end.

  Definition top_eqb o o' :=
   match o, o' with
   | TO_store ti te, TO_store ti' te' => Typ.eqb ti ti' && Typ.eqb te te'
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
    | Anop o t, Anop o' t' => nop_eqb o o' && list_beq Int63.eqb t t'
    | Atop o t1 t2 t3, Atop o' t1' t2' t3' =>
      top_eqb o o' && (t1 == t1') && (t2 == t2') && (t3 == t3')
    | Aapp a la, Aapp b lb => (a == b) && list_beq Int63.eqb la lb
    | _, _ => false
    end.

  Ltac preflect t :=
    let Heq := fresh "Heq" in
      let Hd := fresh "Hd" in
        destruct t as [Heq | Hd];simpl;
          [ | constructor;intros Heq;elim Hd;inversion Heq;trivial].

  Lemma reflect_cop_eqb : forall o1 o2, reflect (o1 = o2) (cop_eqb o1 o2).
  Proof.
    destruct o1; destruct o2; simpl; try (constructor; trivial; discriminate).
    apply iff_reflect. split. intro.
    inversion H. rewrite andb_true_iff. split.
      rewrite N.eqb_refl; auto. apply RAWBITVECTOR_LIST.List_eq_refl; auto.
      intros. rewrite andb_true_iff in H. destruct H as (Ha, Hb).
        apply N.eqb_eq in Ha. rewrite RAWBITVECTOR_LIST.List_eq in Hb.
        now rewrite Ha, Hb.
  Qed.

  Lemma reflect_uop_eqb : forall o1 o2, reflect (o1 = o2) (uop_eqb o1 o2).
  Proof.
    intros [ | | | | | s1 n1 | s1 | s1 | s1 | s1 | s1 ] [ | | | | |s2 n2 | s2 | s2 | s2 | s2 | s2 ];simpl; try constructor;trivial; try discriminate.
    - apply iff_reflect. case_eq (Nat.eqb n1 n2).
      + case_eq ((s1 =? s2)%N).
        * rewrite N.eqb_eq, beq_nat_true_iff.
          intros -> ->. split; reflexivity.
        * rewrite N.eqb_neq, beq_nat_true_iff.
          intros H1 ->; split; try discriminate.
          intro H. inversion H. elim H1. auto.
      + split; auto.
        * rewrite beq_nat_false_iff in H. intros. contradict H0.
          intro H'. apply H. inversion H'. reflexivity.
        *  intros. contradict H0. easy.
    - apply iff_reflect. rewrite N.eqb_eq. split; intro H.
      + now inversion H.
      + now rewrite H.
    - apply iff_reflect. rewrite N.eqb_eq. split; intro H.
      + now inversion H.
      + now rewrite H.
    - intros. apply iff_reflect. split. intro H.
      inversion H.
      rewrite !andb_true_iff; split.
      split; now rewrite N.eqb_eq.
      now rewrite N.eqb_eq.
      intros. rewrite !andb_true_iff in H.
      destruct H as ((Ha, Hb), Hc).
      rewrite N.eqb_eq in Ha, Hb, Hc.
      subst.
      reflexivity.
    - intros. apply iff_reflect. split; intros.
      + rewrite !andb_true_iff. inversion H.
        split; try split; try now rewrite N.eqb_eq.
      + rewrite !andb_true_iff in H.
        destruct H as (Ha, Hb).
        rewrite N.eqb_eq in Ha, Hb.
        now subst.
    - intros. apply iff_reflect. split; intros.
      + rewrite !andb_true_iff. inversion H.
        split; try split; try now rewrite N.eqb_eq.
      + rewrite !andb_true_iff in H.
        destruct H as (Ha, Hb).
        rewrite N.eqb_eq in Ha, Hb.
        now subst.
  Qed.


  Lemma reflect_bop_eqb : forall o1 o2, reflect (o1 = o2) (bop_eqb o1 o2).
  Proof.
    intros [ | | | | | | | A1|s1|s1 |s1 | s1 | s1 | s1 | s1 | s1 | s1 | s1 | I1 E1 | I1 E1 ]
           [ | | | | | | | A2|s2|s2| s2 | s2 | s2 | s2 | s2 | s2 | s2 | s2 |I2 E2 | I2 E2 ];
      simpl;try (constructor;trivial;discriminate).
   - preflect (Typ.reflect_eqb A1 A2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - intros.
     preflect (N.eqb_spec s1 s2).
     preflect (N.eqb_spec n n0).
     constructor;subst;trivial.

   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.
   - preflect (N.eqb_spec s1 s2).
     constructor;subst;trivial.

   - preflect (Typ.reflect_eqb I1 I2).
     preflect (Typ.reflect_eqb E1 E2).
     constructor;subst;trivial.
   - preflect (Typ.reflect_eqb I1 I2).
     preflect (Typ.reflect_eqb E1 E2).
     constructor;subst;trivial.
Qed.

  Lemma reflect_top_eqb : forall o1 o2, reflect (o1 = o2) (top_eqb o1 o2).
  Proof.
    intros [ I1 E1 ] [ I2 E2 ]. simpl.
    preflect (Typ.reflect_eqb I1 I2).
    preflect (Typ.reflect_eqb E1 E2).
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
    preflect (reflect_uop_eqb u u0); preflect (Misc.reflect_eqb i i0);
      constructor;subst;trivial.
    (* Binary operators *)
    preflect (reflect_bop_eqb b b0);
    preflect (Misc.reflect_eqb i i1);
    preflect (Misc.reflect_eqb i0 i2);
    constructor;subst;trivial.
    (* Ternary operators *)
    preflect (reflect_top_eqb t t0).
    preflect (Misc.reflect_eqb i i2).
    preflect (Misc.reflect_eqb i0 i3).
    preflect (Misc.reflect_eqb i1 i4).
    constructor;subst;trivial.
    (* N-ary operators *)
    preflect (reflect_nop_eqb n n0);
    preflect (reflect_list_beq _ _ Misc.reflect_eqb l l0);
    constructor; subst; reflexivity.
    (* Application *)
    preflect (Misc.reflect_eqb i i0);
    preflect (reflect_list_beq _ _ Misc.reflect_eqb l l0);
    constructor;subst;trivial.
  Qed.

  Lemma eqb_spec : forall t1 t2, eqb t1 t2 <-> t1 = t2.
  Proof.
    intros;symmetry; apply reflect_iff; apply reflect_eqb.
  Qed.

  (** Typing and interpretation *)

  Record val (t:Type) (I:t -> Type) := Val {
    v_type : t;
    v_val : I v_type
  }.

  Section Typing_Interp.
    Variable t_i : PArray.array typ_compdec.

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

    (* Interpretation of a function*)
    Variable t_func : PArray.array tval.

    (** Type checking of atom assuming an type for hatom *)
    Section Typ_Aux.
      Variable get_type : hatom -> Typ.type.

      Definition typ_cop o :=
        match o with
        | CO_xH => Typ.Tpositive
        | CO_Z0 => Typ.TZ
        | CO_BV _ s => Typ.TBV s
        end.

      Definition typ_uop o :=
        match o with
        | UO_xO => (Typ.Tpositive,Typ.Tpositive)
        | UO_xI => (Typ.Tpositive,Typ.Tpositive)
        | UO_Zpos => (Typ.Tpositive, Typ.TZ)
        | UO_Zneg => (Typ.Tpositive, Typ.TZ)
        | UO_Zopp => (Typ.TZ, Typ.TZ)
        | UO_BVbitOf s _ => (Typ.TBV s, Typ.Tbool)
        | UO_BVnot s => (Typ.TBV s, Typ.TBV s)
        | UO_BVneg s => (Typ.TBV s, Typ.TBV s)
        | UO_BVextr i n0 n1 => (Typ.TBV n1, Typ.TBV n0)
        | UO_BVzextn s i => (Typ.TBV s, Typ.TBV (i + s))
        | UO_BVsextn s i => (Typ.TBV s, Typ.TBV (i + s))
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
        | BO_eq t   => ((t,t),Typ.Tbool)
        | BO_BVand s  => ((Typ.TBV s,Typ.TBV s), (Typ.TBV s))
        | BO_BVor s   => ((Typ.TBV s,Typ.TBV s), Typ.TBV s)
        | BO_BVxor s   => ((Typ.TBV s,Typ.TBV s), Typ.TBV s)
        | BO_BVadd s   => ((Typ.TBV s,Typ.TBV s), Typ.TBV s)
        | BO_BVmult s   => ((Typ.TBV s,Typ.TBV s), Typ.TBV s)
        | BO_BVult s   => ((Typ.TBV s,Typ.TBV s), Typ.Tbool)
        | BO_BVconcat s1 s2   => ((Typ.TBV s1,Typ.TBV s2), (Typ.TBV (s1 + s2)))
        | BO_BVslt s   => ((Typ.TBV s,Typ.TBV s), Typ.Tbool)
        | BO_BVshl s   => ((Typ.TBV s,Typ.TBV s), Typ.TBV s)
        | BO_BVshr s   => ((Typ.TBV s,Typ.TBV s), Typ.TBV s)
        | BO_select ti te => ((Typ.TFArray ti te, ti), te)
        | BO_diffarray ti te => ((Typ.TFArray ti te, Typ.TFArray ti te), ti)
        end.

      Definition typ_top o :=
        match o with
        | TO_store ti te => ((Typ.TFArray ti te, ti, te), Typ.TFArray ti te)
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
        | Atop o a1 a2 a3 =>
          let (ta, t') := typ_top o in
          let '(ta1, ta2, ta3) := ta in
          Typ.eqb t' t && Typ.eqb (get_type a1) ta1 &&
                  Typ.eqb (get_type a2) ta2 && Typ.eqb (get_type a3) ta3
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
        (* Ternary operators *)
        unfold is_true. intros.
        destruct typ_top. destruct p. destruct p.
        rewrite !andb_true_iff in H, H0.
        destruct H as (((Ha, Hb), Hc), Hd).
        destruct H0 as (((H0a, H0b), H0c), H0d).
        apply Typ.eqb_spec in Ha.
        apply Typ.eqb_spec in H0a. now subst.
        (* N-ary operators *)
        intros t1 t2; destruct (typ_nop n) as [ta t'];
        unfold is_true; rewrite !andb_true_iff;
        change (is_true (Typ.eqb t' t1) /\ is_true
        (List.forallb (fun t3 : int => Typ.eqb (get_type t3) ta) l) -> is_true (Typ.eqb t' t2) /\ is_true (List.forallb
        (fun t3 : int => Typ.eqb (get_type t3) ta) l) -> t1 = t2); rewrite !Typ.eqb_spec; intros [H1 _] [H2 _]; subst; auto.
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
        intros [op|op h|op h1 h2|op ha i i0|f args | i e ]; simpl.
        (* Constants *)
        left; destruct op; simpl.
        exists Typ.Tpositive; auto with smtcoq_core.
        exists Typ.TZ; auto with smtcoq_core.
        exists (Typ.TBV n); now rewrite N.eqb_refl.
        (* Unary operators *)
        destruct op; simpl;
        (case (Typ.eqb (get_type h) Typ.Tpositive)).
           left; exists Typ.Tpositive; easy.
            right; intros; rewrite andb_false_r; easy.
            left; exists Typ.Tpositive; easy.
            right; intros; rewrite andb_false_r; easy.

            left; exists Typ.TZ; easy.
            right; intros; rewrite andb_false_r; easy.
            left; exists Typ.TZ; easy.
            right; intros; rewrite andb_false_r; easy.


         (case (Typ.eqb (get_type h) Typ.TZ)).
          left. exists Typ.TZ. easy.
          right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) Typ.TZ)).
          left. exists Typ.TZ. easy.
          right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n1))).
           left. exists (Typ.TBV n0). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n1))).
           left. exists (Typ.TBV n0). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV (i + n)). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV (i + n)). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV (i + n)). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

         (case (Typ.eqb (get_type h) (Typ.TBV n))).
           left. exists (Typ.TBV (i + n)). now rewrite N.eqb_refl; easy.
           right. intros. rewrite andb_false_r. easy.

        (* Binary operators *)
        destruct op; simpl.
        (case (Typ.eqb (get_type h1) Typ.TZ)); (case (Typ.eqb (get_type h2) Typ.TZ)).
          left. exists Typ.TZ. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) Typ.TZ)); (case (Typ.eqb (get_type h2) Typ.TZ)).
          left. exists Typ.TZ. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _ )).
          left. exists Typ.TZ. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists Typ.Tbool. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVor*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVxor*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVadd*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVmult*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVult*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.Tbool). easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVslt*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.Tbool). easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVconcat*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV (n + n0)). rewrite N.eqb_refl. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVshl*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (*additional case for BO_BVshr*)
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists (Typ.TBV n). now rewrite N.eqb_refl; easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.


       (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists t0. rewrite Typ.eqb_refl. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.


       (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _)).
          left. exists t. rewrite Typ.eqb_refl. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.

          (* Ternary operators *)
        revert i i0; destruct op; simpl. intros h1 h2.
        (case (Typ.eqb (get_type h1) _)); (case (Typ.eqb (get_type h2) _));
        (case (Typ.eqb (get_type ha) _)).
          left. exists (Typ.TFArray t t0). rewrite !Typ.eqb_refl. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
          right. intros. rewrite andb_false_r. easy.
        (* N-ary operators *)
        destruct f as [ty]; simpl; case (List.forallb (fun t1 : int => Typ.eqb (get_type t1) ty) args).
        left; exists Typ.Tbool; auto with smtcoq_core.
        right; intro T; rewrite andb_false_r; auto.
        (* Application *)
        case (v_type Typ.ftype interp_ft (t_func .[ i])); intros; apply check_args_dec.
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

      Definition apply_terop (t1 t2 t3 r : Typ.type)
            (op : interp_t t1 -> interp_t t2 -> interp_t t3 -> interp_t r) (tv1 tv2 tv3: bval) :=
        let (t1', v1) := tv1 in
        let (t2', v2) := tv2 in
        let (t3', v3) := tv3 in
        match Typ.cast t1' t1, Typ.cast t2' t2, Typ.cast t3' t3 with
        | Typ.Cast k1, Typ.Cast k2, Typ.Cast k3  => Bval r (op (k1 _ v1) (k2 _ v2) (k3 _ v3))
        | _, _, _ => bvtrue
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
        | CO_BV bv s => Bval (Typ.TBV s) (BITVECTOR_LIST._of_bits bv s)
        end.

      Definition interp_uop o :=
        match o with
        | UO_xO   => apply_unop Typ.Tpositive Typ.Tpositive xO
        | UO_xI   => apply_unop Typ.Tpositive Typ.Tpositive xI
        | UO_Zpos => apply_unop Typ.Tpositive Typ.TZ Zpos
        | UO_Zneg => apply_unop Typ.Tpositive Typ.TZ Zneg
        | UO_Zopp => apply_unop Typ.TZ Typ.TZ Z.opp
        | UO_BVbitOf s n => apply_unop (Typ.TBV s) Typ.Tbool (BITVECTOR_LIST.bitOf n)
        | UO_BVnot s => apply_unop (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_not s)
        | UO_BVneg s => apply_unop (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_neg s)
        | UO_BVextr i n0 n1 =>
          apply_unop (Typ.TBV n1) (Typ.TBV n0) (@BITVECTOR_LIST.bv_extr i n0 n1)
        | UO_BVzextn s i =>
          apply_unop (Typ.TBV s) (Typ.TBV (i + s)) (@BITVECTOR_LIST.bv_zextn s i)
        | UO_BVsextn s i =>
          apply_unop (Typ.TBV s) (Typ.TBV (i + s)) (@BITVECTOR_LIST.bv_sextn s i)
        end.


      Definition interp_bop o :=
         match o  with
         | BO_Zplus => apply_binop Typ.TZ Typ.TZ Typ.TZ Zplus
         | BO_Zminus => apply_binop Typ.TZ Typ.TZ Typ.TZ Zminus
         | BO_Zmult => apply_binop Typ.TZ Typ.TZ Typ.TZ Zmult
         | BO_Zlt => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zlt_bool
         | BO_Zle => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zle_bool
         | BO_Zge => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zge_bool
         | BO_Zgt => apply_binop Typ.TZ Typ.TZ Typ.Tbool Zgt_bool
         | BO_eq t => apply_binop t t Typ.Tbool (Typ.i_eqb t_i t)
         | BO_BVand s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_and s)
         | BO_BVor s  =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_or s)
         | BO_BVxor s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_xor s)
         | BO_BVadd s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_add s)
         | BO_BVmult s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_mult s)
         | BO_BVult s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) Typ.Tbool (@BITVECTOR_LIST.bv_ult s)
         | BO_BVslt s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) Typ.Tbool (@BITVECTOR_LIST.bv_slt s)
         | BO_BVconcat s1 s2 =>
           apply_binop (Typ.TBV s1) (Typ.TBV s2) (Typ.TBV (s1 + s2)) (@BITVECTOR_LIST.bv_concat s1 s2)
         | BO_BVshl s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_shl s)
         | BO_BVshr s =>
           apply_binop (Typ.TBV s) (Typ.TBV s) (Typ.TBV s) (@BITVECTOR_LIST.bv_shr s)
         | BO_select ti te => apply_binop (Typ.TFArray ti te) ti te FArray.select
         | BO_diffarray ti te =>
           let iti := Typ.interp_compdec_aux t_i ti in
           let ite := Typ.interp_compdec_aux t_i te in
           let cti := projT2 iti in
           let cte := projT2 ite in
           let tti := type_compdec cti in
           let tte := type_compdec cte in
           apply_binop (Typ.TFArray ti te) (Typ.TFArray ti te) ti (@FArray.diff tti tte (@EqbToDecType _ (@eqbtype_of_compdec tti cti)) (@ord_of_compdec tti cti) (@comp_of_compdec tti cti) (@EqbToDecType _ (@eqbtype_of_compdec tte cte)) (@ord_of_compdec tte cte) (@comp_of_compdec tte cte) (@inh_of_compdec tti cti) (@inh_of_compdec tte cte))
         end.

      Definition interp_top o :=
         match o with
         | TO_store ti te =>
           let iti := Typ.interp_compdec_aux t_i ti in
           let ite := Typ.interp_compdec_aux t_i te in
           let cti := projT2 iti in
           let cte := projT2 ite in
           let tti := type_compdec cti in
           let tte := type_compdec cte in
           apply_terop (Typ.TFArray ti te) ti te (Typ.TFArray ti te) (@FArray.store tti tte (@EqbToDecType _ (@eqbtype_of_compdec tti cti)) (@ord_of_compdec tti cti) (@comp_of_compdec tti cti) (@ord_of_compdec tte cte) (@comp_of_compdec tte cte) (@inh_of_compdec tte cte))
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
          | Some l' => forall i j, In2 i j l' <-> (In2 i j acc \/ (List.In j acc /\ exists a, List.In a l /\ interp_hatom a = Bval ty i) \/ (exists a b, In2 b a l /\ interp_hatom a = Bval ty i /\ interp_hatom b = Bval ty j))
          | None => exists a, List.In a l /\ let (ta,_) := interp_hatom a in ta <> ty
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
          | None => exists a, List.In a l /\ let (ta,_) := interp_hatom a in ta <> ty
        end.
      Proof.
        intros ty l; generalize (compute_interp_spec ty l nil); case (compute_interp ty nil l); auto; intros l' H i j; rewrite In2_rev, (H i j); split; auto; intros [H1|[[H1 _]|H1]]; auto; inversion H1.
      Qed.

      Definition interp_aux (a:atom) : bval :=
        match a with
        | Acop o => interp_cop o
        | Auop o a => interp_uop o (interp_hatom a)
        | Abop o a1 a2 => interp_bop o (interp_hatom a1) (interp_hatom a2)
        | Atop o a1 a2 a3 => interp_top o (interp_hatom a1) (interp_hatom a2) (interp_hatom a3)
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

      Definition interp_bv (v:bval) (s:N) : BITVECTOR_LIST.bitvector s :=
        let (t,v) := v in
        match Typ.cast t (Typ.TBV s) with
        | Typ.Cast k => k _ v
        | _ => BITVECTOR_LIST.zeros s
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
        intros [op|op h|op h1 h2|op h1 h2 h3|op ha|f l]; simpl.
        (* Constants *)
        destruct op as [ | |l n]; intros [ | i | | | |size]; simpl; try discriminate.
        exists 1%positive; auto.
        exists 0%Z; auto.
        intros H. exists (BITVECTOR_LIST._of_bits l size). unfold is_true in H. rewrite N.eqb_eq in H. now rewrite H.
        (* Unary operators *)
        destruct op as [ | | | | |n n0|n|n|n n0 n1|n n0|n n0]; intros [ | ind| | | |size];
        simpl; try discriminate; try rewrite Typ.eqb_spec;
        intros H1a; destruct (check_aux_interp_hatom h)
        as [x Hx]; rewrite Hx; simpl; generalize x Hx;
        try rewrite H1a; intros y Hy; try rewrite Typ.cast_refl.
        exists (y~0)%positive; auto.
        exists (y~1)%positive; auto.
        exists (Zpos y); auto.
        exists (Zneg y); auto.
        exists (- y)%Z; auto.
        (* bitOf *)
        exists (BITVECTOR_LIST.bitOf n0 y); auto.
        (* bv_not *)
        intros.
        apply andb_true_iff in H1a. destruct H1a as (Ha, Hb).
        rewrite N.eqb_eq in Ha.
        revert x y Hx Hy Hb.
        rewrite <- Ha in *. intros.
        apply Typ.eqb_spec in Hb.
        revert x y Hx Hy.
        rewrite Hb. intros.
        exists (@BITVECTOR_LIST.bv_not n y); auto. rewrite Typ.cast_refl; auto.
        (* bv_neg *)
        intros.
        apply andb_true_iff in H1a. destruct H1a as (Ha, Hb).
        rewrite N.eqb_eq in Ha.
        revert x y Hx Hy Hb.
        rewrite <- Ha in *. intros.
        apply Typ.eqb_spec in Hb.
        revert x y Hx Hy.
        rewrite Hb. intros.
        exists (@BITVECTOR_LIST.bv_neg n y); auto. rewrite Typ.cast_refl; auto.
        (* bv_extr *)
        intros.
        apply andb_true_iff in H1a. destruct H1a as (Ha, Hb).
        rewrite N.eqb_eq in Ha.
        revert x y Hx Hy Hb.
        rewrite <- Ha in *. intros.
        apply Typ.eqb_spec in Hb.
        revert x y Hx Hy.
        rewrite Hb. intros.
        exists (@BITVECTOR_LIST.bv_extr n n0 n1 y); auto. rewrite Typ.cast_refl; auto.
        (* bv_zextn *)
        intros.
        apply andb_true_iff in H1a. destruct H1a as (Ha, Hb).
        rewrite N.eqb_eq in Ha.
        revert x y Hx Hy Hb.
        rewrite <- Ha in *. intros.
        apply Typ.eqb_spec in Hb.
        revert x y Hx Hy.
        rewrite Hb. intros.
        exists (@BITVECTOR_LIST.bv_zextn n n0 y); auto. rewrite Typ.cast_refl; auto.
        (* bv_sextn *)
        intros.
        apply andb_true_iff in H1a. destruct H1a as (Ha, Hb).
        rewrite N.eqb_eq in Ha.
        revert x y Hx Hy Hb.
        rewrite <- Ha in *. intros.
        apply Typ.eqb_spec in Hb.
        revert x y Hx Hy.
        rewrite Hb. intros.
        exists (@BITVECTOR_LIST.bv_sextn n n0 y); auto. rewrite Typ.cast_refl; auto.
  (* Binary operators *)
        destruct op as [ | | | | | | | A |s1|s2| s3 | s4 | s6 | s7 | s8 | s9 | s10 | n m | ti te | ti te];
          [ intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] |
            intros [ ti' te' | i | | | |s ] | |
            ];
        simpl; try discriminate; unfold is_true;
        try (rewrite andb_true_iff ;change (Typ.eqb (get_type h1) Typ.TZ = true /\ Typ.eqb (get_type h2) Typ.TZ = true) with
        (is_true (Typ.eqb (get_type h1) Typ.TZ) /\ is_true (Typ.eqb (get_type h2) Typ.TZ));
        rewrite !Typ.eqb_spec; intros [H1 H2];
        destruct (check_aux_interp_hatom h1) as [x1 Hx1];
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2];
        rewrite Hx2; simpl; generalize x1 Hx1 x2 Hx2;
        rewrite H1, H2; intros y1 Hy1 y2 Hy2; rewrite !Typ.cast_refl);

        try (change (Typ.eqb (get_type h1) Typ.TBV = true /\ Typ.eqb (get_type h2) Typ.TBV = true) with
        (is_true (Typ.eqb (get_type h1) Typ.TBV) /\ is_true (Typ.eqb (get_type h2) Typ.TBV));
        rewrite !Typ.eqb_spec; intros [H1 H2];
        destruct (check_aux_interp_hatom h1) as [x1 Hx1];
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2];
        rewrite Hx2; simpl; generalize x1 Hx1 x2 Hx2; rewrite H1, H2;
        intros y1 Hy1 y2 Hy2; rewrite !Typ.cast_refl).

        exists (y1 + y2)%Z; auto.
        exists (y1 - y2)%Z; auto.
        exists (y1 * y2)%Z; auto.
        exists (y1 <? y2)%Z; auto.
        exists (y1 <=? y2)%Z; auto.
        exists (y1 >=? y2)%Z; auto.
        exists (y1 >? y2)%Z; auto.
        rewrite andb_true_iff ; change (Typ.eqb (get_type h1) A = true /\ Typ.eqb (get_type h2) A = true) with
        (is_true (Typ.eqb (get_type h1) A) /\ is_true (Typ.eqb (get_type h2) A));
        rewrite !Typ.eqb_spec; intros [H1 H2]; destruct (check_aux_interp_hatom h1) as [x1 Hx1];
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl;
        generalize x1 Hx1 x2 Hx2; rewrite H1, H2; intros y1 Hy1 y2 Hy2; rewrite !Typ.cast_refl;
        exists (Typ.i_eqb t_i A y1 y2); auto.
        (*BO_BVand*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_and y1 y2); auto.
        (*BO_BVor*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_or y1 y2); auto.
        (*BO_BVxor*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_xor y1 y2); auto.
        (*BO_BVadd*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_add y1 y2); auto.
        (*BO_BVmult*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_mult y1 y2); auto.
        (*BO_BVult*)
        intros. rewrite !andb_true_iff in H. destruct H as (Hb, Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_ult y1 y2); auto.
        (*BO_BVslt*)
        intros. rewrite !andb_true_iff in H. destruct H as (Hb, Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_slt y1 y2); auto.
        (*BO_BVconcat*)
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply N.eqb_eq in Ha.
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite !Typ.cast_refl.
        rewrite <- Ha.
        exists (BITVECTOR_LIST.bv_concat y1 y2); auto.
        (*BO_BVshl*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_shl y1 y2); auto.
        (*BO_BVshr*)
        simpl in s.
        intros. rewrite !andb_true_iff in H. destruct H as ((Ha, Hb), Hc).
        apply Typ.eqb_spec in Hb.
        apply Typ.eqb_spec in Hc.
        rewrite N.eqb_eq in Ha.
        revert Hb Hc. rewrite Ha in *. intros.

        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        revert x1 Hx1 x2 Hx2.
        rewrite Hb, Hc. intros y1 Hy1 y2 Hy2.
        rewrite Typ.cast_refl.
        exists (BITVECTOR_LIST.bv_shr y1 y2); auto.

        (* BO_select *)
        intros t' H.
        rewrite !andb_true_iff in H.
        destruct H as ((H1, H2), H3).
        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        apply Typ.eqb_spec in H1.
        apply Typ.eqb_spec in H2.
        apply Typ.eqb_spec in H3.
        revert x1 Hx1 x2 Hx2.
        rewrite H2, H3, H1.
        rewrite !Typ.cast_refl.
        intros.
        exists (FArray.select x1 x2); auto.

        (* BO_diffarray *)
        intros t' H.
        rewrite !andb_true_iff in H.
        destruct H as ((H1, H2), H3).
        destruct (check_aux_interp_hatom h1) as [x1 Hx1].
        rewrite Hx1; destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2; simpl.
        apply Typ.eqb_spec in H1.
        apply Typ.eqb_spec in H2.
        apply Typ.eqb_spec in H3.
        revert x1 Hx1 x2 Hx2.
        rewrite H2, H3, H1.
        rewrite !Typ.cast_refl.
        intros.
        exists ((@FArray.diff (Typ.interp t_i t') (Typ.interp t_i te)
             (Typ.dec_interp t_i t')
             (Typ.ord_interp t_i t')
             (Typ.comp_interp t_i t') (Typ.dec_interp t_i te) (Typ.ord_interp t_i te)
             (Typ.comp_interp t_i te) (Typ.inh_interp t_i t') (Typ.inh_interp t_i te) x1 x2)); auto.

        (* Ternary operatores *)
        destruct op as [ti te]; intros [ ti' te' | | | | | ];
          simpl; try discriminate; unfold is_true.
        intros H.
        rewrite !andb_true_iff in H.
        destruct H as ((((H1, H2), H3), H4), H5).
        apply Typ.eqb_spec in H1.
        apply Typ.eqb_spec in H2.
        apply Typ.eqb_spec in H3.
        apply Typ.eqb_spec in H4.
        apply Typ.eqb_spec in H5.
        destruct (check_aux_interp_hatom h1) as [x1 Hx1]. rewrite Hx1;
        destruct (check_aux_interp_hatom h2) as [x2 Hx2]; rewrite Hx2;
        destruct (check_aux_interp_hatom h3) as [x3 Hx3]; rewrite Hx3; simpl.
        revert x1 Hx1 x2 Hx2 x3 Hx3.
        rewrite H3, H4, H5, H1, H2.
        intros.
        rewrite !Typ.cast_refl.
        intros.
        exists (@FArray.store (Typ.interp t_i ti') (Typ.interp t_i te') (Typ.dec_interp t_i ti') (Typ.ord_interp t_i ti') (Typ.comp_interp t_i ti') (Typ.ord_interp t_i te') (Typ.comp_interp t_i te') (Typ.inh_interp t_i te') x1 x2 x3); auto.

        (* N-ary operators *)
        destruct op as [A]; simpl; intros [ | | | | | ]; try discriminate; simpl; intros _; case (compute_interp A nil ha).
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
        intros [op | op h | op h1 h2 | op h1 h2 h3 | op ha | f l]; simpl.
        (* Constants *)
        destruct op; simpl; intro H.
        discriminate (H Typ.Tpositive).
        discriminate (H Typ.TZ).
        specialize (H (Typ.TBV n)). simpl in H. rewrite N.eqb_refl in H. now contradict H.
        (* Unary operators *)
        destruct op; simpl; intro H; destruct (check_aux_interp_hatom h) as [v Hv];
          rewrite Hv; simpl; rewrite Typ.neq_cast;
            try (pose (H2 := H Typ.Tpositive); simpl in H2; rewrite H2; auto);
            try (pose (H2 := H Typ.TZ); simpl in H2; rewrite H2; auto);
            try (pose (H2 := H Typ.Tbool); simpl in H2; rewrite H2; auto);
            try (pose (H2 := H Typ.TBV); simpl in H2; rewrite H2; auto).
            (* bv_not *)
            specialize (H (Typ.TBV n)). simpl in H. rewrite andb_false_iff in H.
            destruct H as [ H | H].
              rewrite N.eqb_refl in H. now contradict H.
              now rewrite H.
            (* bv_neg *)
            specialize (H (Typ.TBV n)). simpl in H. rewrite andb_false_iff in H.
            destruct H as [ H | H].
              rewrite N.eqb_refl in H. now contradict H.
              now rewrite H.
            (* bv_extr *)
            specialize (H (Typ.TBV n0)). simpl in H. rewrite andb_false_iff in H.
            destruct H as [ H | H].
              rewrite N.eqb_refl in H. now contradict H.
              now rewrite H.
            (* bv_zextn *)
            specialize (H (Typ.TBV (i + n))). simpl in H. rewrite andb_false_iff in H.
            destruct H as [ H | H].
              rewrite N.eqb_refl in H. now contradict H.
              now rewrite H.
            (* bv_sextn *)
            specialize (H (Typ.TBV (i + n))). simpl in H. rewrite andb_false_iff in H.
            destruct H as [ H | H].
              rewrite N.eqb_refl in H. now contradict H.
              now rewrite H.
        (* Binary operators *)
        destruct op; simpl; intro H; destruct (check_aux_interp_hatom h1) as [v1 Hv1];
        destruct (check_aux_interp_hatom h2) as [v2 Hv2]; rewrite Hv1, Hv2; simpl;
        try (pose (H2 := H Typ.TZ); simpl in H2; rewrite andb_false_iff in H2;
        destruct H2 as [H2|H2]; [rewrite (Typ.neq_cast (get_type h1)),
          H2|rewrite (Typ.neq_cast (get_type h2)), H2; case (Typ.cast (get_type h1) Typ.TZ)]; auto);
        try (pose (H2 := H Typ.Tbool); simpl in H2; rewrite andb_false_iff in H2; destruct H2 as [H2|H2];
        [rewrite (Typ.neq_cast (get_type h1)), H2|rewrite (Typ.neq_cast (get_type h2)), H2; case (Typ.cast (get_type h1) Typ.TZ)]; auto);
        try (pose (H2 := H Typ.TBV); simpl in H2; rewrite !andb_false_iff in H2; destruct H2 as [[H2|H2]|H2];
        [rewrite N.eqb_refl in H2; discriminate | rewrite (Typ.neq_cast (get_type h1)), H2|rewrite (Typ.neq_cast (get_type h2)), H2;
        case (Typ.cast (get_type h1) Typ.TBV); case (Typ.cast (get_type h1) Typ.TBV)]; auto).
        intros. simpl in H.
        case_eq (Typ.cast (get_type h1) t). easy. easy.
        case_eq (Typ.cast (get_type h1) t). easy. easy.
        (*BVand*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVor*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVxor*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVadd*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVmult*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVult*)
        specialize (H Typ.Tbool). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        specialize (H0 H). now rewrite H0.

        case_eq (Typ.cast (get_type h1) (Typ.TBV n)). intros.
        specialize (@Typ.cast_diff (get_type h2) (Typ.TBV n)). intros.
        specialize (H1 H). easy.
        easy.

        case_eq (Typ.cast (get_type h1) (Typ.TBV n)). intros.
        specialize (@Typ.cast_diff (get_type h2) (Typ.TBV n)). intros.
        specialize (H1 H2). easy.
        easy.

        (*BVslt*)
        specialize (H Typ.Tbool). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        specialize (H0 H). now rewrite H0.

        case_eq (Typ.cast (get_type h1) (Typ.TBV n)). intros.
        specialize (@Typ.cast_diff (get_type h2) (Typ.TBV n)). intros.
        specialize (H1 H). easy.
        easy.

        case_eq (Typ.cast (get_type h1) (Typ.TBV n)). intros.
        specialize (@Typ.cast_diff (get_type h2) (Typ.TBV n)). intros.
        specialize (H1 H2). easy.
        easy.
        (*BVconcat*)
        specialize (H (Typ.TBV (n+n0))). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVshl*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.
        (*BVshr*)
        specialize (H (Typ.TBV n)). simpl in H.
        apply andb_false_iff in H. destruct H.
        specialize (@Typ.cast_diff (get_type h1) (Typ.TBV n)). intros.
        rewrite andb_false_iff in H. destruct H as [ H | H ].
          rewrite N.eqb_refl in H. now contradict H.
          apply Typ.cast_diff in H. now rewrite H.
          apply Typ.cast_diff in H. rewrite H.
          case (Typ.cast (get_type h1) (Typ.TBV n)); auto.

        (* BO_select *)
        specialize (H t0). simpl in H.
        rewrite !andb_false_iff in H. destruct H. destruct H.
        rewrite Typ.eqb_refl in H. now contradict H.
        rewrite (Typ.cast_diff _ _ H); auto.
        rewrite (Typ.cast_diff _ _ H); auto.
        case (Typ.cast (get_type h1) (Typ.TFArray t t0)); auto.

        (* BO_diffarray *)
        specialize (H t). simpl in H.
        rewrite !andb_false_iff in H. destruct H. destruct H.
        rewrite Typ.eqb_refl in H. now contradict H.
        rewrite (Typ.cast_diff _ _ H); auto.
        rewrite (Typ.cast_diff _ _ H); auto.
        case (Typ.cast (get_type h1) (Typ.TFArray t t0)); auto.

        (* Ternary operators *)
        destruct op; simpl; intro H;
          destruct (check_aux_interp_hatom h1) as [v1 Hv1];
          destruct (check_aux_interp_hatom h2) as [v2 Hv2];
          destruct (check_aux_interp_hatom h3) as [v3 Hv3];
          rewrite Hv1, Hv2, Hv3; simpl.
        specialize (H (Typ.TFArray t t0)). simpl in H.
        rewrite !andb_false_iff in H.
        destruct H as [[ [ [ H | H] | H] | H] | H];
          try (rewrite (Typ.cast_diff _ _ H); auto);
          try (case (Typ.cast (get_type h1) (Typ.TFArray t t0)); auto);
          try (rewrite !Typ.eqb_refl in H; now contradict H).
        intros. case (Typ.cast (get_type h2) t); auto.

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

      Definition t_interp : array bval :=
        foldi (fun i t_a => t_a.[i <- interp_aux (get t_a) (t_atom.[i])]) 0 (length t_atom)
          (make (length t_atom) (interp_cop CO_xH)).

      Definition lt_atom i a :=
        match a with
        | Acop _ => true
        | Auop _ h => h < i
        | Abop _ h1 h2 => (h1 < i) && (h2 < i)
        | Atop _ h1 h2 h3 => (h1 < i) && (h2 < i) && (h3 < i)
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
        (* Ternary operators *)
        unfold is_true in H;rewrite !andb_true_iff in H;do 2 destruct H;rewrite !Hf;trivial.
        (* N-ary operators *)
        destruct n as [A]; replace (compute_interp f1 A nil l) with (compute_interp f2 A nil l); trivial; assert (H1: forall acc, compute_interp f2 A acc l = compute_interp f1 A acc l); auto; induction l as [ |k l IHl]; simpl; auto; intro acc; simpl in H; unfold is_true in H; rewrite andb_true_iff in H; destruct H as [H1 H2]; rewrite (Hf _ H1); destruct (f2 k) as [ta va]; destruct (Typ.cast ta A) as [ka| ]; auto.
        (* Application *)
        replace (List.map f1 l) with (List.map f2 l); trivial.
        induction l;simpl in H |- *;trivial.
        unfold is_true in H;rewrite andb_true_iff in H;destruct H;rewrite Hf, IHl;trivial.
      Qed.

      Definition wf := aforallbi lt_atom t_atom.

      Hypothesis wf_t_i : wf.

      Lemma length_t_interp : length t_interp = length t_atom.
      Proof.
        unfold t_interp.
        assert (Bt := to_Z_bounded (length t_atom)).
        apply (foldi_ind _ (fun i a => length a = length t_atom)).
        rewrite leb_spec, to_Z_0; lia.
        rewrite length_make, leb_length;trivial.
        intros;rewrite length_set;trivial.
      Qed.

      Lemma default_t_interp : default t_interp = interp_cop CO_xH.
      Proof.
        unfold t_interp.
        assert (Bt := to_Z_bounded (length t_atom)).
        apply (foldi_ind _ (fun i a => default a = interp_cop CO_xH)).
        rewrite leb_spec, to_Z_0; lia.
        apply default_make.
        intros;rewrite default_set;trivial.
      Qed.

      Lemma t_interp_wf_lt : forall i, i < PArray.length t_atom ->
         t_interp.[i] = interp_aux (PArray.get t_interp) (t_atom.[i]).
      Proof.
        assert (Bt := to_Z_bounded (length t_atom)).
        set (P' i t := length t = length t_atom ->
               forall j, j < i ->
               t.[j] = interp_aux (PArray.get t) (t_atom.[j])).
        assert (P' (length t_atom) t_interp).
         unfold is_true, wf in wf_t_i;rewrite aforallbi_spec in wf_t_i.
         unfold t_interp;apply foldi_ind;unfold P';intros.
         rewrite leb_spec, to_Z_0; lia.
         elim (ltb_0 _ H0).
         rewrite length_set in H2.
         destruct (Misc.reflect_eqb j i).
          rewrite e, PArray.get_set_same.
          apply lt_interp_aux with (2:= wf_t_i i H0).
          intros;rewrite get_set_other;trivial.
          intros Heq;elim (not_ltb_refl i);rewrite Heq at 1;trivial.
          rewrite H2;trivial.
         assert (j < i).
          assert ([|j|] <> [|i|]) by(intros Heq1;elim n;apply to_Z_inj;trivial).
          generalize H3;unfold is_true;rewrite !ltb_spec,
            (to_Z_add_1 _ _ H0);auto with zarith.
         rewrite get_set_other, H1;auto.
         apply lt_interp_aux with (2:= wf_t_i j (ltb_trans _ _ _ H4 H0)).
         intros;rewrite get_set_other;trivial.
         intros Heq;elim (not_ltb_refl i);apply ltb_trans with j;
           [ rewrite Heq| ];trivial.
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
        unfold wf, is_true in wf_t_i; rewrite aforallbi_spec in wf_t_i.
        intros h Hh a IH; generalize (wf_t_i h Hh).
        case (t_atom.[h]); simpl.
        (* Constants *)
        intros [ | | ] _; simpl.
        exists 1%positive; auto.
        exists 0%Z; auto.
        exists (BITVECTOR_LIST._of_bits l n); auto.
        (* Unary operators *)

        intros [ | | | | | | | | i0 n0 n1| n i0| n i0] i H;
          simpl; destruct (IH i H) as [x Hx]; rewrite Hx; simpl.

        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists ((k interp_t x)~0)%positive; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists ((k interp_t x)~1)%positive; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists (Zpos (k interp_t x)); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.Tpositive); simpl; try (exists true; auto); intro k; exists (Zneg (k interp_t x)); auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) Typ.TZ); simpl; try (exists true; auto); intro k; exists (- k interp_t x)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) (Typ.TBV n)); simpl; [ | exists true; auto]. intro k; exists (BITVECTOR_LIST.bitOf n0 (k interp_t x)) ; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) (Typ.TBV n)); simpl; [ | exists true; auto]. intro k; exists (BITVECTOR_LIST.bv_not (k interp_t x)) ; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) (Typ.TBV n)); simpl; [ | exists true; auto]. intro k; exists (BITVECTOR_LIST.bv_neg (k interp_t x)) ; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) (Typ.TBV n1));
        simpl; [ | exists true; auto]. intro k; exists (BITVECTOR_LIST.bv_extr i0 n0 (k interp_t x)) ; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) (Typ.TBV n));
        simpl; [ | exists true; auto]. intro k. exists (BITVECTOR_LIST.bv_zextn i0 (k interp_t x)) ; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ i])) (Typ.TBV n));
        simpl; [ | exists true; auto]. intro k. exists (BITVECTOR_LIST.bv_sextn i0 (k interp_t x)) ; auto.

       (* Binary operators *)
        intros [ | | | | | | |A | | | | | | | | | | | ti te| ti te] h1 h2; simpl; rewrite andb_true_iff; intros [H1 H2]; destruct (IH h1 H1) as [x Hx]; destruct (IH h2 H2) as [y Hy]; rewrite Hx, Hy; simpl.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ); simpl; try (exists true; auto); intro k2; exists (k1 interp_t x + k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ); simpl; try (exists true; auto); intro k2; exists (k1 interp_t x - k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ); simpl; try (exists true; auto); intro k2; exists (k1 interp_t x * k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x <? k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x <=? k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x >=? k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) Typ.TZ); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) Typ.TZ) as [k2| ]; simpl; try (exists true; reflexivity); exists (k1 interp_t x >? k2 interp_t y)%Z; auto.
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) A); simpl; try (exists true; auto); intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) A) as [k2| ]; simpl; try (exists true; reflexivity); exists (Typ.i_eqb t_i A (k1 interp_t x) (k2 interp_t y)); auto.

        (*BO_BVand*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_and (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVor*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_or (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVxor*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_xor (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVadd*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_add (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVmult*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_mult (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVult*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_ult (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVslt*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_slt (k1 interp_t x) (k2 interp_t y));
          auto.
        (*BO_BVconcat*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV (n))); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV (n0))) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_concat (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVshl*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_shl (k1 interp_t x) (k2 interp_t y));
        auto.
        (*BO_BVshr*)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TBV n)); simpl; try (exists true; auto);
        intro k1; case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TBV n)) as [k2| ];
        simpl; try (exists true; reflexivity); exists (BITVECTOR_LIST.bv_shr (k1 interp_t x) (k2 interp_t y));
        auto.
        (* BO_select *)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TFArray ti te) );
          simpl; try (exists true; auto); intro k1;
            case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) ti) as [k2| ];
            simpl; try (exists true; reflexivity).
        exists (FArray.select (k1 interp_t x) (k2 interp_t y)); auto.

        (* BO_diffarray *)
        case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TFArray ti te) );
          simpl; try (exists true; auto); intro k1;
            case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) (Typ.TFArray ti te)) as [k2| ];
            simpl; try (exists true; reflexivity).
        exists ((@FArray.diff (Typ.interp t_i ti) (Typ.interp t_i te) (Typ.dec_interp t_i ti) (Typ.ord_interp t_i ti) (Typ.comp_interp t_i ti) (Typ.dec_interp t_i te) (Typ.ord_interp t_i te) (Typ.comp_interp t_i te) (Typ.inh_interp t_i ti) (Typ.inh_interp t_i te) (k1 (Typ.interp t_i) x) (k2 (Typ.interp t_i) y))); auto.

        (* Ternary operators *)
        intros [ti te] h1 h2 h3; simpl; rewrite !andb_true_iff; intros [[H1 H2] H3];
          destruct (IH h1 H1) as [x Hx];
          destruct (IH h2 H2) as [y Hy];
          destruct (IH h3 H3) as [z Hz]; rewrite Hx, Hy, Hz; simpl.
         case (Typ.cast (v_type Typ.type interp_t (a .[ h1])) (Typ.TFArray ti te) );
          simpl; try (exists true; auto); intro k1;
         case (Typ.cast (v_type Typ.type interp_t (a .[ h2])) ti );
          simpl; try (exists true; auto); intro k2;
            case (Typ.cast (v_type Typ.type interp_t (a .[ h3])) te) as [k3| ];
            simpl; try (exists true; reflexivity).
         exists (@FArray.store (Typ.interp t_i ti) (Typ.interp t_i te)
             (Typ.dec_interp t_i ti)
             (Typ.ord_interp t_i ti)
             (Typ.comp_interp t_i ti) (Typ.ord_interp t_i te) (Typ.comp_interp t_i te)
             (Typ.inh_interp t_i te) (k1 (Typ.interp t_i) x) (k2 (Typ.interp t_i) y)
             (k3 (Typ.interp t_i) z)); auto.

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
        assert (Bt := to_Z_bounded (length t_atom)).
        set (P' i t := length t = length t_atom ->
          forall j, j < i ->
            exists v, t.[j] = Bval (v_type Typ.type interp_t (t.[j])) v).
        assert (P' (length t_atom) t_interp).
        unfold t_interp;apply foldi_ind;unfold P';intros.
        rewrite leb_spec, to_Z_0; lia.
        elim (ltb_0 _ H0).
        rewrite length_set in H2.
        destruct (Misc.reflect_eqb j i).
        rewrite e, PArray.get_set_same.
        apply check_aux_interp_aux_lt; auto.
        rewrite H2; auto.
        assert (j < i).
        assert ([|j|] <> [|i|]) by(intros Heq1;elim n;apply to_Z_inj;trivial).
        generalize H3;unfold is_true;rewrite !ltb_spec,
          (to_Z_add_1 _ _ H0);auto with zarith.
        rewrite get_set_other;auto.
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
        aforallbi (fun i h => check_aux get_type h (get_type i)) t_atom.

    Definition interp_hatom (t_atom : PArray.array atom) :=
      let t_a := t_interp t_atom in
      PArray.get t_a.

    Definition interp t_atom := interp_aux (interp_hatom t_atom).

    Definition interp_form_hatom t_atom : hatom -> bool :=
      let interp := interp_hatom t_atom in
      fun a => interp_bool (interp a).

    Definition interp_form_hatom_bv t_atom :
      hatom -> forall s, BITVECTOR_LIST.bitvector s :=
      let interp := interp_hatom t_atom in
      fun a s => interp_bv (interp a) s.

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

Arguments Atom.Val {_} {_} _ _.

(* These definitions are not used. This is just a hack, Coq refuses to
   construct PArrays from OCaml if these are not here for some silly reason *)
(*
Section PredefinedArrays.
  Variable t_i : PArray.array typ_compdec.

  Definition mkarray_typ_compdec := @PArray.make typ_compdec.
  Definition arrayset_typ_compdec := @PArray.set typ_compdec.

  Definition mkarray_func := @PArray.make (Atom.tval t_i).
  Definition arrayset_func := @PArray.set (Atom.tval t_i).

  Definition mkarray_form := @PArray.make Form.form.
  Definition arrayset_form := @PArray.set Form.form.

  Definition mkarray_atom := @PArray.make Atom.atom.
  Definition arrayset_atom := @PArray.set Atom.atom.

End PredefinedArrays.
*)


(* Register constants for OCaml access *)
Register Typ.type as SMTCoq.SMT_terms.Typ.type.
Register Typ.TFArray as SMTCoq.SMT_terms.Typ.TFArray.
Register Typ.Tindex as SMTCoq.SMT_terms.Typ.Tindex.
Register Typ.TZ as SMTCoq.SMT_terms.Typ.TZ.
Register Typ.Tbool as SMTCoq.SMT_terms.Typ.Tbool.
Register Typ.Tpositive as SMTCoq.SMT_terms.Typ.Tpositive.
Register Typ.TBV as SMTCoq.SMT_terms.Typ.TBV.
Register Typ.interp as SMTCoq.SMT_terms.Typ.interp.
Register Typ.dec_interp as SMTCoq.SMT_terms.Typ.dec_interp.
Register Typ.ord_interp as SMTCoq.SMT_terms.Typ.ord_interp.
Register Typ.comp_interp as SMTCoq.SMT_terms.Typ.comp_interp.
Register Typ.inh_interp as SMTCoq.SMT_terms.Typ.inh_interp.
Register Typ.i_eqb as SMTCoq.SMT_terms.Typ.i_eqb.
Register Atom.tval as SMTCoq.SMT_terms.Atom.tval.
Register Atom.Tval as SMTCoq.SMT_terms.Atom.Tval.
Register Atom.CO_xH as SMTCoq.SMT_terms.Atom.CO_xH.
Register Atom.CO_Z0 as SMTCoq.SMT_terms.Atom.CO_Z0.
Register Atom.CO_BV as SMTCoq.SMT_terms.Atom.CO_BV.
Register Atom.UO_xO as SMTCoq.SMT_terms.Atom.UO_xO.
Register Atom.UO_xI as SMTCoq.SMT_terms.Atom.UO_xI.
Register Atom.UO_Zpos as SMTCoq.SMT_terms.Atom.UO_Zpos.
Register Atom.UO_Zneg as SMTCoq.SMT_terms.Atom.UO_Zneg.
Register Atom.UO_Zopp as SMTCoq.SMT_terms.Atom.UO_Zopp.
Register Atom.UO_BVbitOf as SMTCoq.SMT_terms.Atom.UO_BVbitOf.
Register Atom.UO_BVnot as SMTCoq.SMT_terms.Atom.UO_BVnot.
Register Atom.UO_BVneg as SMTCoq.SMT_terms.Atom.UO_BVneg.
Register Atom.UO_BVextr as SMTCoq.SMT_terms.Atom.UO_BVextr.
Register Atom.UO_BVzextn as SMTCoq.SMT_terms.Atom.UO_BVzextn.
Register Atom.UO_BVsextn as SMTCoq.SMT_terms.Atom.UO_BVsextn.
Register Atom.BO_Zplus as SMTCoq.SMT_terms.Atom.BO_Zplus.
Register Atom.BO_Zminus as SMTCoq.SMT_terms.Atom.BO_Zminus.
Register Atom.BO_Zmult as SMTCoq.SMT_terms.Atom.BO_Zmult.
Register Atom.BO_Zlt as SMTCoq.SMT_terms.Atom.BO_Zlt.
Register Atom.BO_Zle as SMTCoq.SMT_terms.Atom.BO_Zle.
Register Atom.BO_Zge as SMTCoq.SMT_terms.Atom.BO_Zge.
Register Atom.BO_Zgt as SMTCoq.SMT_terms.Atom.BO_Zgt.
Register Atom.BO_eq as SMTCoq.SMT_terms.Atom.BO_eq.
Register Atom.BO_BVand as SMTCoq.SMT_terms.Atom.BO_BVand.
Register Atom.BO_BVor as SMTCoq.SMT_terms.Atom.BO_BVor.
Register Atom.BO_BVxor as SMTCoq.SMT_terms.Atom.BO_BVxor.
Register Atom.BO_BVadd as SMTCoq.SMT_terms.Atom.BO_BVadd.
Register Atom.BO_BVmult as SMTCoq.SMT_terms.Atom.BO_BVmult.
Register Atom.BO_BVult as SMTCoq.SMT_terms.Atom.BO_BVult.
Register Atom.BO_BVslt as SMTCoq.SMT_terms.Atom.BO_BVslt.
Register Atom.BO_BVconcat as SMTCoq.SMT_terms.Atom.BO_BVconcat.
Register Atom.BO_BVshl as SMTCoq.SMT_terms.Atom.BO_BVshl.
Register Atom.BO_BVshr as SMTCoq.SMT_terms.Atom.BO_BVshr.
Register Atom.BO_select as SMTCoq.SMT_terms.Atom.BO_select.
Register Atom.BO_diffarray as SMTCoq.SMT_terms.Atom.BO_diffarray.
Register Atom.TO_store as SMTCoq.SMT_terms.Atom.TO_store.
Register Atom.NO_distinct as SMTCoq.SMT_terms.Atom.NO_distinct.
Register Atom.atom as SMTCoq.SMT_terms.Atom.atom.
Register Atom.Acop as SMTCoq.SMT_terms.Atom.Acop.
Register Atom.Auop as SMTCoq.SMT_terms.Atom.Auop.
Register Atom.Abop as SMTCoq.SMT_terms.Atom.Abop.
Register Atom.Atop as SMTCoq.SMT_terms.Atom.Atop.
Register Atom.Anop as SMTCoq.SMT_terms.Atom.Anop.
Register Atom.Aapp as SMTCoq.SMT_terms.Atom.Aapp.
Register Form.form as SMTCoq.SMT_terms.Form.form.
Register Form.Fatom as SMTCoq.SMT_terms.Form.Fatom.
Register Form.Ftrue as SMTCoq.SMT_terms.Form.Ftrue.
Register Form.Ffalse as SMTCoq.SMT_terms.Form.Ffalse.
Register Form.Fnot2 as SMTCoq.SMT_terms.Form.Fnot2.
Register Form.Fand as SMTCoq.SMT_terms.Form.Fand.
Register Form.For as SMTCoq.SMT_terms.Form.For.
Register Form.Fxor as SMTCoq.SMT_terms.Form.Fxor.
Register Form.Fimp as SMTCoq.SMT_terms.Form.Fimp.
Register Form.Fiff as SMTCoq.SMT_terms.Form.Fiff.
Register Form.Fite as SMTCoq.SMT_terms.Form.Fite.
Register Form.FbbT as SMTCoq.SMT_terms.Form.FbbT.


(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

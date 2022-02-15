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


Require Import List Bool Int63 Psatz Ring63 PArray Omega Misc Ring.

(* Require Import AxiomesInt. *)

Local Open Scope int63_scope.
Local Open Scope array_scope.

Coercion is_true : bool >-> Sortclass.

Set Vm Optimize.

Notation var := int (only parsing).

(* Variables interpretation *)
Module Valuation.
(* TODO : Should be var -> Prop *)
  Definition t := var -> bool.
  Definition wf (rho : t) : Prop := rho 0 /\ ~ rho 1.

End Valuation.


Module Var.

  Definition _true : var := 0. (* true *)
  (* Register _true as PrimInline. *)

  Definition _false : var := 1. (* false *)

  Definition interp (rho:Valuation.t) (x:var) : bool := rho x.

  Lemma interp_true : forall rho, Valuation.wf rho -> interp rho _true.
  Proof. intros rho [H _];exact H. Qed.

  Lemma interp_false : forall rho, Valuation.wf rho -> ~ interp rho _false.
  Proof. intros rho [_ H];exact H. Qed.

End Var.

Notation _lit := int (only parsing).

Module Lit.

  Definition is_pos (l:_lit) := is_even l.
  (* Register is_pos as PrimInline. *)

  Definition blit (l:_lit) : var := l >> 1.
  (* Register blit as PrimInline. *)

  Definition lit (x:var) : _lit := x << 1.
  (* Register lit as PrimInline. *)

  Definition neg (l:_lit) : _lit := l lxor 1.
  (* Register neg as PrimInline. *)

  Definition nlit (x:var) : _lit := neg (lit x).
  (* Register nlit as PrimInline. *)

  Definition _true : _lit := Eval compute in lit Var._true.
  (* Register _true as PrimInline. *)

  Lemma lit_true : _true = lit Var._true.
  Proof. reflexivity. Qed.

  Definition _false : _lit := Eval compute in lit Var._false.
  (* Register _false as PrimInline. *)

  Lemma lit_false : _false = lit Var._false.
  Proof. reflexivity. Qed.

  Definition eqb (l l' : _lit) := l == l'.
  (* Register eqb as PrimInline. *)

  Lemma eqb_spec : forall l l', eqb l l' = true <-> l = l'.
  Proof eqb_spec.

  Lemma neg_involutive : forall l,  neg (neg l) = l.
  Proof.
    unfold neg;intros; rewrite <- lxorA;change (1 lxor 1) with 0;rewrite lxor0_r;trivial.
  Qed.

  Lemma blit_neg : forall l, blit (neg l) = blit l.
  Proof.
    unfold blit, neg;intros l.
    rewrite lxor_lsr, lxor0_r;trivial.
  Qed.

  Lemma lit_blit: forall l,
    is_pos l = true -> lit (blit l) = l.
  Proof.
    unfold is_pos, lit, blit;intros.
    rewrite (bit_xor_split l) at 2.
    rewrite is_even_bit, negb_true_iff in H;rewrite H.
    symmetry;apply lxor0_r.
  Qed.

  Lemma lit_blit_neg: forall l,
    is_pos l = false -> lit (blit l) = neg l.
  Proof.
    unfold is_pos, lit, blit;intros.
    rewrite (bit_xor_split l) at 2.
    rewrite is_even_bit, negb_false_iff in H;rewrite H.
    rewrite <- (neg_involutive ((l >> 1) << 1)) at 1;trivial.
  Qed.

  Lemma nlit_blit: forall l,
    is_pos l = false -> nlit (blit l) = l.
  Proof.
    unfold nlit;intros;rewrite lit_blit_neg;auto using neg_involutive.
  Qed.

  Lemma nlit_blit_neg: forall l,
    is_pos l = true -> nlit (blit l) = neg l.
  Proof.
    unfold nlit;intros;rewrite lit_blit;auto using neg_involutive.
  Qed.

  Lemma is_pos_lit : forall l,
    is_pos (lit l) = true.
  Proof.
    unfold is_pos, lit;apply is_even_lsl_1.
  Qed.

  Lemma is_pos_neg : forall l,
    is_pos (neg l) = negb (is_pos l).
  Proof.
    unfold neg, is_pos;intros l.
    rewrite is_even_xor, xorb_false_r;trivial.
  Qed.

  Lemma is_pos_nlit : forall l,
    is_pos (nlit l) = false.
  Proof.
    unfold nlit;intros l;rewrite is_pos_neg, is_pos_lit;trivial.
  Qed.

  Lemma is_pos_true : is_pos _true.
  Proof. reflexivity. Qed.

  Lemma is_pos_false : is_pos _false.
  Proof. reflexivity. Qed.

  Lemma blit_pos :forall a b,
    Lit.blit a = Lit.blit b -> Lit.is_pos a = Lit.is_pos b ->
    a = b.
  Proof lsr_is_even_eq.

  Lemma blit_lit : forall l, blit (lit (blit l)) = blit l.
  Proof.
    intros l;case_eq (is_pos l);intros.
    rewrite lit_blit;trivial.
    rewrite lit_blit_neg, blit_neg;trivial.
  Qed.

  Lemma blit_nlit : forall l, blit (nlit (blit l)) = blit l.
  Proof.
    intros l;case_eq (is_pos l);intros.
    rewrite nlit_blit_neg, blit_neg;trivial.
    rewrite nlit_blit;trivial.
  Qed.

  Lemma blit_true : blit _true = Var._true.
  Proof. reflexivity. Qed.

  Lemma blit_false : blit _false = Var._false.
  Proof. reflexivity. Qed.

                        (* Interpretation of a literal *)
  Definition interp rho (l:_lit) :=
    if is_pos l then Var.interp rho (blit l)
      else negb (Var.interp rho (blit l)).

  Lemma interp_true : forall rho, Valuation.wf rho -> interp rho _true.
  Proof.
    intros rho Hwf;unfold interp;rewrite is_pos_true, blit_true.
    apply Var.interp_true;trivial.
  Qed.

  Lemma interp_false : forall rho, Valuation.wf rho -> ~interp rho _false.
  Proof.
    intros rho Hwf;unfold interp;rewrite is_pos_false, blit_false.
    apply Var.interp_false;trivial.
  Qed.

  Lemma interp_neg : forall rho l, interp rho (neg l) = negb (interp rho l).
  Proof.
    intros rho l;unfold interp;rewrite is_pos_neg, blit_neg.
    destruct (is_pos l);simpl;auto using negb_involutive.
  Qed.

  Lemma interp_lit : forall rho l, interp rho (lit (blit l)) = Var.interp rho (blit l).
  Proof.
    intros;unfold interp;rewrite is_pos_lit, blit_lit;trivial.
  Qed.

  Lemma interp_nlit : forall rho l, interp rho (nlit (blit l)) = negb (Var.interp rho (blit l)).
  Proof.
    unfold nlit;intros rho l;rewrite interp_neg, interp_lit;trivial.
  Qed.

  Lemma interp_eq_compat : forall rho1 rho2 l,
    rho1 (blit l) = rho2 (blit l) ->
    interp rho1 l = interp rho2 l.
  Proof.
    unfold interp, Var.interp;intros rho1 rho2 l Heq;rewrite Heq;trivial.
  Qed.

  Lemma lxor_neg : forall l1 l2, (l1 lxor l2 == 1) = true -> l1 = Lit.neg l2.
  Proof.
    unfold Lit.neg; intros l1 l2;rewrite eqb_spec;intros Heq;rewrite <- Heq.
    rewrite lxorC, <- lxorA, lxor_nilpotent, lxor0_r;trivial.
  Qed.

End Lit.


Lemma compare_spec' : forall x y,
    match x ?= y with
    | Lt => x < y
    | Eq => x = y
    | Gt => y < x
    end.
Proof.
  intros x y;rewrite compare_def_spec;unfold compare_def.
  case_eq (x < y);intros;[reflexivity | ].
  case_eq (x == y);intros.
  rewrite <- eqb_spec;trivial.
  rewrite <- not_true_iff_false in H, H0.
  unfold is_true in *;rewrite ltb_spec in H |- *;rewrite eqb_spec in H0.
  assert ([|x|] <> [|y|]) by (intros Heq;apply H0, to_Z_inj;trivial);omega.
Qed.


Module C.

  Definition t := list _lit.

  Definition interp (rho:Valuation.t) (l:t) :=
    List.existsb (Lit.interp rho) l.

  Definition valid rho c :=
    interp rho c = true.

  Definition _true : t := Lit._true :: nil.

  Definition is_false (c:t) :=
    match c with
      | nil => true
      | _ => false
    end.

  Fixpoint has_true (c:t) :=
    match c with
      | nil => false
      | l :: c => (l == Lit._true) || has_true c
    end.
  

  Section OR.

    Variable or : t -> t -> t.
    Variable l1 : _lit.
    Variable c1 : t.

    Fixpoint or_aux (c2:t) :=
      match c2 with
      | nil => l1 :: c1
      | l2::c2' =>
        match l1 ?= l2 with
        | Eq => l1 :: or c1 c2'
        | Lt => l1 :: or c1 c2
        | Gt => l2 :: or_aux c2'
        end
      end.

    Variable rho : Valuation.t.
    Hypothesis or_correct : forall c2,
        interp rho (or c1 c2) = interp rho c1 || interp rho c2.

    Lemma or_aux_correct : forall c2,
      interp rho (or_aux c2) = interp rho (l1::c1) || interp rho c2.
    Proof.
      induction c2;simpl.
      rewrite orb_false_r;trivial.
      generalize (compare_spec' l1 a);destruct (l1 ?= a);intros H;simpl.
      rewrite H;destruct (Lit.interp rho a);trivial.
      rewrite !orb_false_l, or_correct;trivial.
      rewrite or_correct;simpl;rewrite orb_assoc;trivial.
      rewrite IHc2;simpl.
      destruct (Lit.interp rho a);simpl;trivial.
      rewrite orb_true_r;trivial.
    Qed.

  End OR.

  Fixpoint or (c1 c2:t) {struct c1} : t :=
    match c1, c2 with
    | nil, _ => c2
    | _, nil => c1
    | l1::c1, l2::c2' =>
      match compare l1 l2 with
      | Eq => l1 :: or c1 c2'
      | Lt => l1 :: or c1 c2
      | Gt => l2 :: or_aux or l1 c1 c2'
      end
    end.

  Lemma or_correct : forall rho c1 c2,
    interp rho (or c1 c2) = interp rho c1 || interp rho c2.
  Proof.
    induction c1;simpl;trivial.
    destruct c2;simpl.
    rewrite orb_false_r;trivial.
    generalize (compare_spec' a i);destruct (a ?= i);intros H;simpl.
    rewrite H, IHc1;simpl;destruct (Lit.interp rho i);simpl;trivial.
    rewrite IHc1, orb_assoc;trivial.
    rewrite or_aux_correct;simpl;trivial.
    destruct (Lit.interp rho i);trivial.
    simpl;rewrite !orb_true_r;trivial.
  Qed.

  Section RESOLVE.

    Variable resolve : t -> t -> t.
    Variable l1 : _lit.
    Variable c1 : t.

    Fixpoint resolve_aux (c2:t) : t :=
      match c2 with
      | nil => _true
      | l2::c2' =>
        match compare l1 l2 with
        | Eq => l1 :: resolve c1 c2'
        | Lt => if l1 lxor l2 == 1 then or c1 c2' else l1 :: resolve c1 c2
        | Gt =>
          if l1 lxor l2 == 1 then or c1 c2' else l2 :: resolve_aux c2'
        end
      end.

    Lemma resolve_aux_correct : forall rho,
      (forall c2, interp rho c1 -> interp rho c2 -> interp rho (resolve c1 c2)) ->
      interp rho (l1 :: c1) ->
      forall c2, interp rho c2 ->
      interp rho (resolve_aux c2).
    Proof.
      intros rho resolve_correct Hc1;simpl in Hc1.
      induction c2;simpl;try discriminate.
      generalize (compare_spec' l1 a);destruct (l1 ?= a);intros;subst;simpl.
      simpl in Hc1;destruct (Lit.interp rho a);simpl in *;auto.
      generalize (Lit.lxor_neg l1 a);destruct (l1 lxor a == 1);intros.
      rewrite or_correct.
      rewrite H1, Lit.interp_neg in Hc1;trivial;destruct (Lit.interp rho a).
      simpl in Hc1;rewrite Hc1;trivial.
      simpl in H0;rewrite H0, orb_true_r;trivial.
      simpl;destruct (Lit.interp rho l1);simpl;auto.
      generalize (Lit.lxor_neg l1 a);destruct (l1 lxor a == 1);intros.
      rewrite or_correct.
      rewrite H1, Lit.interp_neg in Hc1;trivial;destruct (Lit.interp rho a).
      simpl in Hc1;rewrite Hc1;trivial.
      simpl in H0;rewrite H0, orb_true_r;trivial.
      simpl;destruct (Lit.interp rho a);simpl;auto.
    Qed.

  End RESOLVE.

  Fixpoint resolve (c1 c2:t) {struct c1} : t :=
    match c1, c2 with
    | nil, _ => _true
    | _, nil => _true
    | l1::c1, l2::c2' =>
      match compare l1 l2 with
      | Eq => l1 :: resolve c1 c2'
      | Lt => if l1 lxor l2 == 1 then or c1 c2' else l1 :: resolve c1 c2
      | Gt =>
        if l1 lxor l2 == 1 then or c1 c2' else l2 :: resolve_aux resolve l1 c1 c2'
      end
    end.

  Lemma resolve_correct : forall rho c1 c2,
    interp rho c1 -> interp rho c2 ->
    interp rho (resolve c1 c2).
  Proof.
    induction c1;simpl;try discriminate.
    destruct c2;simpl;try discriminate.
    intros Hc1 Hc2.
    generalize (compare_spec' a i);destruct (a ?= i);intros;subst;simpl.
    destruct (Lit.interp rho i);simpl in *;auto.
    generalize (Lit.lxor_neg a i);destruct (a lxor i == 1);intros.
    rewrite or_correct.
    rewrite H0, Lit.interp_neg in Hc1;trivial;destruct (Lit.interp rho i).
    simpl in Hc1;rewrite Hc1;trivial.
    simpl in Hc2;rewrite Hc2, orb_true_r;trivial.
    simpl;destruct (Lit.interp rho a);simpl;auto.
    generalize (Lit.lxor_neg a i);destruct (a lxor i == 1);intros.
    rewrite or_correct.
    rewrite H0, Lit.interp_neg in Hc1;trivial;destruct (Lit.interp rho i).
    simpl in Hc1;rewrite Hc1;trivial.
    simpl in Hc2;rewrite Hc2, orb_true_r;trivial.
    simpl;destruct (Lit.interp rho i);simpl;auto using resolve_aux_correct.
  Qed.

  Lemma interp_true : forall rho, Valuation.wf rho -> interp rho _true = true.
  Proof.
    unfold _true, interp;intros rho Hwf;simpl.
    rewrite Lit.interp_true;trivial.
  Qed.

  Lemma is_false_correct :
    forall c, is_false c = true ->
      forall rho, ~valid rho c.
  Proof.
    unfold valid, interp;destruct c;simpl; auto;discriminate.
  Qed.

  Lemma Cinterp_neg rho cl :
    interp rho (List.map Lit.neg cl) = negb (List.forallb (Lit.interp rho) cl).
  Proof.
    induction cl as [ |l cl IHcl]; auto.
    simpl. now rewrite negb_andb, IHcl, Lit.interp_neg.
  Qed.

End C.


Notation clause_id := int (only parsing).

Notation resolution := (array clause_id) (only parsing).

Module S.

  Definition t := array C.t.

  Definition get (s:t) (cid:clause_id) := s.[cid].
  (* Register get as PrimInline. *)

  (* Do not use this function outside this module *)
  (* expect if you are sure that [c = sort_uniq c] *)
  Definition internal_set (s:t) (cid:clause_id) (c:C.t) : t := s.[cid <- c].
  (* Register internal_set as PrimInline. *)

  Definition make (nclauses : int) : t :=
    PArray.make nclauses C._true.

  Definition valid rho s :=
    forall id, C.valid rho (get s id).


  (* Specification of make *)

  Lemma valid_make : forall rho nclauses,
    Valuation.wf rho ->
    valid rho (make nclauses).
  Proof.
    unfold valid, make, get;intros.
    rewrite PArray.get_make; apply C.interp_true;trivial.
  Qed.


  (* Specification of get *)

  Lemma valid_get : forall rho s, valid rho s ->
    forall id, C.valid rho (get s id).
  Proof. intros rho s H id. unfold valid in H. unfold Valuation.t in rho. apply H. Qed.
  (** Proof. auto. Qed. **)


  (* Specification of internal_set *)

  Lemma valid_internal_set :
    forall rho s, valid rho s ->
      forall c, C.valid rho c ->
        forall id, valid rho (set s id c).
  Proof.
    unfold valid, get;simpl;intros.
    destruct (reflect_eqb id id0);subst.
    case_eq (id0 < length s);intros.
    rewrite PArray.get_set_same;trivial.
    rewrite PArray.get_outofbound.
    rewrite PArray.default_set.
    rewrite <- (PArray.get_outofbound _ _ (length s)); trivial.
    rewrite <- not_true_iff_false, ltb_spec;auto with zarith.
    rewrite PArray.length_set;trivial.
    rewrite get_set_other;trivial.
  Qed.

  (* Building clause *)
  (* Same as set but without precondition *)

  (* TODO: It can be a good idea to change the insertion sort algorithm *)

  Fixpoint insert l1 c :=
   match c with
   | nil => l1:: nil
   | l2 :: c' =>
     match l1 ?= l2 with
     | Lt => if l1 lxor l2 == 1 then C._true else l1 :: c
     | Eq => c
     | Gt => if l1 lxor l2 == 1 then C._true else l2 :: insert l1 c'
     end
   end.

  Fixpoint insert_no_simpl l1 c :=
   match c with
   | nil => l1:: nil
   | l2 :: c' =>
     match l1 ?= l2 with
     | Lt => l1 :: c
     | Eq => c
     | Gt => l2 :: insert_no_simpl l1 c'
     end
   end.

  Fixpoint insert_keep l1 c :=
   match c with
   | nil => l1:: nil
   | l2 :: c' =>
     match l1 ?= l2 with
     | Lt | Eq => l1 :: c
     | Gt => l2 :: insert_keep l1 c'
     end
   end.

  Fixpoint sort c :=
    match c with
    | nil => nil
    | l1 :: c => insert_no_simpl l1 (sort c)
    end.

  
  Fixpoint sort_uniq c :=
    match c with
    | nil => nil
    | l1 :: c => insert l1 (sort_uniq c)
    end.

  Fixpoint sort_keep c :=
    match c with
    | nil => nil
    | l1 :: c => insert_keep l1 (sort_keep c)
    end.

  
  Lemma insert_correct : forall rho (Hwf:Valuation.wf rho) l1 c,
    C.interp rho (insert l1 c) = C.interp rho (l1 :: c).
  Proof.
    intros rho Hwf l1;induction c;simpl;trivial.
    generalize (compare_spec' l1 a);destruct (l1 ?= a);intros;subst;simpl.
    destruct (Lit.interp rho a);simpl in *;auto.
    generalize (Lit.lxor_neg l1 a);destruct (l1 lxor a == 1);intros;trivial.
    rewrite C.interp_true;trivial.
    rewrite H0, Lit.interp_neg;trivial;destruct (Lit.interp rho a);trivial.
    generalize (Lit.lxor_neg l1 a);destruct (l1 lxor a == 1);intros.
    rewrite C.interp_true;trivial.
    rewrite H0, Lit.interp_neg;trivial;destruct (Lit.interp rho a);trivial.
    simpl;rewrite orb_assoc,(orb_comm (Lit.interp rho l1)),<-orb_assoc,IHc;trivial.
  Qed.

  
  Lemma insert_no_simpl_correct : forall rho (Hwf:Valuation.wf rho) l1 c,
    C.interp rho (insert_no_simpl l1 c) = C.interp rho (l1 :: c).
  Proof.
    intros rho Hwf l1;induction c;simpl;trivial.
    generalize (compare_spec' l1 a);destruct (l1 ?= a);intros;subst;simpl;auto.
    destruct (Lit.interp rho a);simpl in *;auto.
    simpl;rewrite orb_assoc,(orb_comm (Lit.interp rho l1)),<-orb_assoc,IHc;trivial.
  Qed.

  Lemma insert_keep_correct : forall rho (Hwf:Valuation.wf rho) l1 c,
      C.interp rho (insert_keep l1 c) = C.interp rho (l1 :: c).
  Proof.
    intros rho Hwf l1;induction c;simpl;trivial.
    generalize (compare_spec' l1 a);destruct (l1 ?= a);intros;subst;simpl;auto.
    destruct (Lit.interp rho a);simpl in *;auto. rewrite orb_true_r; auto.
  Qed.

    
  Lemma sort_uniq_correct : forall rho (Hwf:Valuation.wf rho) c,
    C.interp rho (sort_uniq c) = C.interp rho c.
  Proof.
    intros rho Hwf;induction c;simpl;trivial.
    rewrite insert_correct;trivial;simpl;rewrite IHc;trivial.
  Qed.

      
  Lemma sort_correct : forall rho (Hwf:Valuation.wf rho) c,
    C.interp rho (sort c) = C.interp rho c.
  Proof.
    intros rho Hwf;induction c;simpl;trivial.
    rewrite insert_no_simpl_correct;trivial;simpl;rewrite IHc;trivial.
  Qed.

        
  Lemma sort_keep_correct : forall rho (Hwf:Valuation.wf rho) c,
    C.interp rho (sort_keep c) = C.interp rho c.
  Proof.
    intros rho Hwf;induction c;simpl;trivial.
    rewrite insert_keep_correct;trivial;simpl;rewrite IHc;trivial.
  Qed.

  
  (* Definition set_clause (s:t) pos (c:C.t) : t := *)
  (*   set s pos (sort_uniq c). *)
  
  (* Version that does not simplify ~a \/ a *)
  Definition set_clause (s:t) pos (c:C.t) : t :=
    set s pos (sort c).

  Lemma valid_set_clause :
    forall rho s, Valuation.wf rho -> valid rho s -> forall pos c,
                 C.valid rho c -> valid rho (set_clause s pos c).
  Proof.
    unfold valid, get, set_clause. intros rho s Hrho Hs pos c Hc id.
    destruct (reflect_eqb pos id);subst.
    case_eq (id < length s); intro H.
    unfold get;rewrite PArray.get_set_same; trivial.
    unfold C.valid;rewrite sort_correct;trivial.
    generalize (Hs id);rewrite !PArray.get_outofbound, PArray.default_set;trivial.
    rewrite length_set;trivial.
    rewrite get_set_other;trivial.
  Qed.

  Definition set_clause_keep (s:t) pos (c:C.t) : t :=
    set s pos (sort_keep c).


  Lemma valid_set_clause_keep :
    forall rho s, Valuation.wf rho -> valid rho s -> forall pos c,
                 C.valid rho c -> valid rho (set_clause_keep s pos c).
  Proof.
    unfold valid, get, set_clause_keep. intros rho s Hrho Hs pos c Hc id.
    destruct (reflect_eqb pos id);subst.
    case_eq (id < length s); intro H.
    unfold get;rewrite PArray.get_set_same; trivial.
    unfold C.valid;rewrite sort_keep_correct;trivial.
    generalize (Hs id);rewrite !PArray.get_outofbound, PArray.default_set;trivial.
    rewrite length_set;trivial.
    rewrite get_set_other;trivial.
  Qed.

  (* Resolution *)

  Open Scope int63_scope.

  Definition set_resolve (s:t) pos (r:resolution) : t :=
    let len := PArray.length r in
    if len == 0 then s
    else
      let c := foldi (fun i c' => (C.resolve (get s (r.[i])) c')) 1 len (get s (r.[0])) in
      (* S.set_clause *) internal_set s pos c.

  Lemma valid_set_resolve :
    forall rho s, Valuation.wf rho -> valid rho s ->
      forall pos r, valid rho (set_resolve s pos r).
  Proof.
    unfold set_resolve; intros rho s Hrho Hv pos r.
    destruct (reflect_eqb (length r) 0);[trivial | ].
    apply valid_internal_set;trivial.
    pattern (length r); apply (int_ind_bounded _ 1).
    generalize (to_Z_bounded (length r)); rewrite <- to_Z_eq, to_Z_0 in n; rewrite leb_spec, to_Z_1; lia.
    rewrite foldi_ge; [ apply Hv | reflexivity ].
    intros i Hi1 Hi2 Hc.
    rewrite foldi_lt_r.
    apply C.resolve_correct; [ apply Hv | ring_simplify (i + 1 - 1); exact Hc ].
    rewrite ltb_spec, to_Z_add_1_wB, to_Z_1.
    rewrite leb_spec, to_Z_1 in Hi1; generalize (to_Z_bounded i); omega.
    rewrite ltb_spec in Hi2; generalize (to_Z_bounded (length r)); omega.
 Qed.

  (* Weakening *)


  Definition subclause (cl1 cl2 : list _lit) :=
    List.forallb (fun l1 =>
                    (l1 == Lit._false) || (l1 == Lit.neg Lit._true) ||
                    List.existsb (fun l2 => l1 == l2) cl2) cl1.
  
  Definition check_weaken (s:t) (cid:clause_id) (cl:list _lit) : C.t :=
    if subclause (get s cid) cl then cl else C._true.


  Lemma check_weaken_valid : forall rho s (cid:clause_id) (cl:list _lit),
      Valuation.wf rho ->
      valid rho s ->
      C.valid rho (check_weaken s cid cl).
  Proof.
    intros rho s cid cl Hw Hs.
    unfold check_weaken, C.valid.
    case_eq (subclause (get s cid) cl); try (intros; now apply C.interp_true).
    specialize (Hs cid).
    unfold C.valid, C.interp in Hs.
    apply existsb_exists in Hs.
    intro.
    unfold subclause in H.
    rewrite forallb_forall in H.
    unfold C.valid, C.interp.
    apply existsb_exists.
    destruct Hs as (x, (Hi, Hax)).
    specialize (H x Hi).
    rewrite !orb_true_iff in H.
    rewrite !eqb_spec in H.
    destruct H as [[H | H] | H].
    - contradict Hax. subst. apply Lit.interp_false; trivial.
    - contradict Hax. subst. rewrite Lit.interp_neg.
      rewrite not_true_iff_false, negb_false_iff, Lit.interp_true; trivial.
    - apply existsb_exists in H.
      destruct H as (x', (Hcl, Hxx')).
      rewrite eqb_spec in Hxx'.
      subst x'.
      exists x. auto.
  Qed.
  
  Definition set_weaken (s:t) pos (cid:clause_id) (cl:list _lit) : t :=
      S.set_clause_keep s pos (check_weaken s cid cl).

  
      
  Lemma valid_set_weaken :
    forall rho s, Valuation.wf rho -> valid rho s ->
      forall pos cid w, valid rho (set_weaken s pos cid w).
  Proof.
    intros.
    apply S.valid_set_clause_keep; auto.
    apply check_weaken_valid; auto.
  Qed.

  
End S.


(* Register constants for OCaml access *)
Register C.t as SMTCoq.State.C.t.
Register S.t as SMTCoq.State.S.t.

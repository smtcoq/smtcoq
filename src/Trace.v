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

Add LoadPath "." as SMTCoq.
Add LoadPath "cnf" as SMTCoq.cnf.
Add LoadPath "euf" as SMTCoq.euf.
Add LoadPath "lia" as SMTCoq.lia.
Add LoadPath "spl" as SMTCoq.spl.
Add LoadPath "int63" as SMTCoq.int63.

Require Import Bool Int63 PArray.
Require Import Misc State SMT_terms Cnf Euf Lia Syntactic Arithmetic Operators CnfInt63.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Set Vm Optimize.
Section trace.

  (* We are given a certificate, a checker for it (that modifies a
     state), and a proof that the checker is correct: the state it
     returns must be valid and well-formed. *)

  Variable step : Type.

  Variable check_step : S.t -> step -> S.t.

  Variable rho : Valuation.t.

  (* We use [array array step] to allow bigger trace *)
  Definition _trace_ := array (array step).

  (* A checker for such a trace *)

  Variable is_false : C.t -> bool.
  Hypothesis is_false_correct : forall c, is_false c -> ~ C.interp rho c.

  Definition _checker_ (s: S.t) (t: _trace_) (confl:clause_id) : bool :=
    let s' := PArray.fold_left (fun s a => PArray.fold_left check_step s a) s t in
    is_false (S.get s' confl).
  (* Register _checker_ as PrimInline. *)

  (* For debugging *)
  (*

  Variable check_step_debug : S.t -> step -> option S.t.

  Definition _checker_debug_ (s: S.t) (t: _trace_) : sum S.t ((int*int)*S.t) :=
    let s' := PArray.foldi_left (fun i s a => PArray.foldi_left (fun j s' a' =>
      match s' with
        | inl s'' =>
          match check_step_debug s'' a' with
            | Some s''' => inl s'''
            | None => inr ((i,j),s'')
          end
        | u => u
      end) s a) (inl s) t in
    s'.

  Definition _checker_partial_ (s: S.t) (t: _trace_) (max:int) : S.t :=
    PArray.fold_left (fun s a => PArray.foldi_left (fun i s' a' => if i < max then check_step s' a' else s') s a) s t.
  *)

  (* Proof of its partial correction: if it returns true, then the
     initial state is not valid *)

  Hypothesis valid_check_step :
    forall s, S.valid rho s -> forall c, S.valid rho (check_step s c).

  Lemma _checker__correct :
    forall s, forall t confl, _checker_ s t confl-> ~ (S.valid rho s).
  Proof.
    unfold _checker_.
    intros s t' cid Hf Hv.
    apply (is_false_correct Hf).
    apply S.valid_get.
    apply PArray.fold_left_ind; auto.
    intros a i _ Ha;apply PArray.fold_left_ind;trivial.
    intros a0 i0 _ H1;auto.
  Qed.
 
End trace.


(* Application to resolution *)

Module Sat_Checker.

 Inductive step :=
   | Res (_:int) (_:resolution).

 Definition resolution_checker s t :=
    _checker_ (fun s (st:step) => let (pos, r) := st in S.set_resolve s pos r) s t.

 Lemma resolution_checker_correct :
    forall rho, Valuation.wf rho ->
    forall s t cid, resolution_checker C.is_false s t cid->
     ~S.valid rho s.
 Proof.
   intros rho Hwr;apply _checker__correct.
   intros; apply C.is_false_correct; trivial.
   intros s Hv (pos, r);apply S.valid_set_resolve;trivial. 
 Qed.
   
 (** Application to Zchaff *)
 Definition dimacs := PArray.array (PArray.array _lit).

 Definition C_interp_or rho c := 
   afold_left _ _ false orb (Lit.interp rho) c.

 Lemma C_interp_or_spec : forall rho c,
   C_interp_or rho c = C.interp rho (to_list c).
 Proof.
   intros rho c; unfold C_interp_or; case_eq (C.interp rho (to_list c)).
   unfold C.interp; rewrite List.existsb_exists; intros [x [H1 H2]]; destruct (In_to_list _ _ H1) as [i [H3 H4]]; subst x; apply (afold_left_orb_true _ i); auto.
   unfold C.interp; intro H; apply afold_left_orb_false; intros i H1; case_eq (Lit.interp rho (c .[ i])); auto; intro Heq; assert (H2: exists x, List.In x (to_list c) /\ Lit.interp rho x = true).
   exists (c.[i]); split; auto; apply to_list_In; auto.
   rewrite <- List.existsb_exists in H2; rewrite H2 in H; auto.
Qed.

 Definition valid rho (d:dimacs) :=
   afold_left _ _ true andb (C_interp_or rho) d.

 Lemma valid_spec : forall rho d,
   valid rho d <->
   (forall i : int, i < length d -> C.interp rho (PArray.to_list (d.[i]))).
 Proof.
   unfold valid; intros rho d; split; intro H.
   intros i Hi; case_eq (C.interp rho (to_list (d .[ i]))); try reflexivity.
   intro Heq; erewrite afold_left_andb_false in H; try eassumption.
   rewrite C_interp_or_spec; auto.
   apply afold_left_andb_true; try assumption; intros i Hi; rewrite C_interp_or_spec; apply H; auto.
 Qed.

 Inductive certif :=
   | Certif : int -> _trace_ step -> clause_id -> certif.

 Definition add_roots s (d:dimacs) := 
   PArray.foldi_right (fun i c s => S.set_clause s i (PArray.to_list c)) d s.

 Definition checker (d:dimacs) (c:certif) :=
   let (nclauses, t, confl_id) := c in
   resolution_checker C.is_false (add_roots (S.make nclauses) d) t confl_id.

 Lemma valid_add_roots : forall rho, Valuation.wf rho ->
    forall d s, valid rho d -> S.valid rho s ->
    S.valid rho (add_roots s d).
 Proof.
   intros rho Hwr d s Hd Hs; unfold add_roots; apply (PArray.foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i Hlt Hv; apply S.valid_set_clause; auto; rewrite valid_spec in Hd; apply Hd; auto.
 Qed.

 Lemma checker_correct : forall d c,
    checker d c = true ->
    forall rho, Valuation.wf rho -> ~valid rho d.
 Proof.
   unfold checker; intros d (nclauses, t, confl_id) Hc rho Hwf Hv.
   apply (resolution_checker_correct Hwf Hc).
   apply valid_add_roots; auto.
   apply S.valid_make; auto.
 Qed.

 Definition interp_var rho x := 
   match compare x 1 with
   | Lt => true
   | Eq => false
   | Gt => rho (x - 1) 
     (* This allows to have variable starting at 1 in the interpretation as in dimacs files *)
   end.

 Lemma theorem_checker : 
   forall d c,
     checker d c = true ->
     forall rho, ~valid (interp_var rho) d.
 Proof.
  intros d c H rho;apply checker_correct with c;trivial.
  split;compute;trivial;discriminate.
 Qed.

End Sat_Checker.

Module Cnf_Checker.
  
  Inductive step :=
  | Res (pos:int) (res:resolution)
  | ImmFlatten (pos:int) (cid:clause_id) (lf:_lit) 
  | CTrue (pos:int)       
  | CFalse (pos:int)
  | BuildDef (pos:int) (l:_lit)
  | BuildDef2 (pos:int) (l:_lit)
  | BuildProj (pos:int) (l:_lit) (i:int)
  | ImmBuildDef (pos:int) (cid:clause_id)
  | ImmBuildDef2 (pos:int) (cid:clause_id)
  | ImmBuildProj (pos:int) (cid:clause_id) (i:int).

  Local Open Scope list_scope.

  Local Notation check_flatten t_form := (check_flatten t_form (fun i1 i2 => i1 == i2) (fun _ _ => false)) (only parsing).

  Definition step_checker t_form s (st:step) :=
    match st with
    | Res pos res => S.set_resolve s pos res
    | ImmFlatten pos cid lf => S.set_clause s pos (check_flatten t_form s cid lf) 
    | CTrue pos => S.set_clause s pos Cnf.check_True
    | CFalse pos => S.set_clause s pos Cnf.check_False
    | BuildDef pos l => S.set_clause s pos (check_BuildDef t_form l)
    | BuildDef2 pos l => S.set_clause s pos (check_BuildDef2 t_form l)
    | BuildProj pos l i => S.set_clause s pos (check_BuildProj t_form l i)
    | ImmBuildDef pos cid => S.set_clause s pos (check_ImmBuildDef t_form s cid) 
    | ImmBuildDef2 pos cid => S.set_clause s pos (check_ImmBuildDef2 t_form s cid)
    | ImmBuildProj pos cid i => S.set_clause s pos (check_ImmBuildProj t_form s cid i)
    end.

  Lemma step_checker_correct : forall rho t_form,
    Form.check_form t_form ->
    forall s, S.valid (Form.interp_state_var rho t_form) s ->
      forall st : step, S.valid (Form.interp_state_var rho t_form)
        (step_checker t_form s st).
  Proof.
    intros rho t_form Ht s H; destruct (Form.check_form_correct rho _ Ht) as [[Ht1 Ht2] Ht3]; intros [pos res|pos cid lf|pos|pos|pos l|pos l|pos l i|pos cid|pos cid|pos cid i]; simpl; try apply S.valid_set_clause; auto.
    apply S.valid_set_resolve; auto.
    apply valid_check_flatten; auto; try discriminate; intros a1 a2; unfold is_true; rewrite Int63Properties.eqb_spec; intro; subst a1; auto.
    apply valid_check_True; auto.
    apply valid_check_False; auto.
    apply valid_check_BuildDef; auto.
    apply valid_check_BuildDef2; auto.
    apply valid_check_BuildProj; auto.
    apply valid_check_ImmBuildDef; auto.
    apply valid_check_ImmBuildDef2; auto.
    apply valid_check_ImmBuildProj; auto.
  Qed.

  Definition cnf_checker t_form s t :=
    _checker_ (step_checker t_form) s t.

  Lemma cnf_checker_correct : forall rho t_form,
    Form.check_form t_form -> forall s t confl,
      cnf_checker t_form C.is_false s t confl ->
      ~ (S.valid (Form.interp_state_var rho t_form) s).
  Proof.
    unfold cnf_checker; intros rho t_form Ht; apply _checker__correct.
    intros c H; apply C.is_false_correct; auto.
    apply step_checker_correct; auto.
  Qed.


 Inductive certif :=
   | Certif : int -> _trace_ step -> int -> certif.

 Definition checker t_form l (c:certif) :=
   let (nclauses, t, confl) := c in   
   Form.check_form t_form &&
   cnf_checker t_form C.is_false (S.set_clause (S.make nclauses) 0 (l::nil)) t confl.

 Lemma checker_correct : forall t_form l c,
    checker t_form l c = true ->
    forall rho, ~ (Lit.interp (Form.interp_state_var rho t_form) l).
 Proof.
   unfold checker; intros t_form l (nclauses, t, confl); unfold is_true; rewrite andb_true_iff; intros [H1 H2] rho H; apply (cnf_checker_correct (rho:=rho) H1 H2); destruct (Form.check_form_correct rho _ H1) as [[Ht1 Ht2] Ht3]; apply S.valid_set_clause; auto.
   apply S.valid_make; auto.
   unfold C.valid; simpl; rewrite H; auto.
 Qed.

 Definition checker_b t_form l (b:bool) (c:certif) :=
   let l := if b then Lit.neg l else l in
   checker t_form l c.

 Lemma checker_b_correct : forall t_var t_form l b c,
    checker_b t_form l b c = true ->
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l = b.
 Proof.
   unfold checker_b; intros t_var t_form l b c; case b; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l); auto; intros H1 H2; elim (checker_correct H2 (rho:=get t_var)); auto; rewrite Lit.interp_neg, H1; auto.
 Qed.

 Definition checker_eq t_form l1 l2 l (c:certif) :=
   negb (Lit.is_pos l) && 
   match t_form.[Lit.blit l] with
   | Form.Fiff l1' l2' => (l1 == l1') && (l2 == l2')
   | _ => false
   end && 
   checker t_form l c.

 Lemma checker_eq_correct : forall t_var t_form l1 l2 l c,
   checker_eq t_form l1 l2 l c = true ->
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l1 =
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l2.
 Proof.
   unfold checker_eq; intros t_var t_form l1 l2 l c; rewrite !andb_true_iff; case_eq (t_form .[ Lit.blit l]); [intros _ _|intros _|intros _|intros _ _ _|intros _ _|intros _ _|intros _ _|intros _ _ _|intros l1' l2' Heq|intros _ _ _ _]; intros [[H1 H2] H3]; try discriminate; rewrite andb_true_iff in H2; rewrite !Int63Properties.eqb_spec in H2; destruct H2 as [H2 H4]; subst l1' l2'; case_eq (Lit.is_pos l); intro Heq'; rewrite Heq' in H1; try discriminate; clear H1; assert (H:PArray.default t_form = Form.Ftrue /\ Form.wf t_form).
   unfold checker in H3; destruct c as (nclauses, t, confl); rewrite andb_true_iff in H3; destruct H3 as [H3 _]; destruct (Form.check_form_correct (get t_var) _ H3) as [[Ht1 Ht2] Ht3]; split; auto.
   destruct H as [H1 H2]; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l1); intro Heq1; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l2); intro Heq2; auto; elim (checker_correct H3 (rho:=get t_var)); unfold Lit.interp; rewrite Heq'; unfold Var.interp; rewrite Form.wf_interp_form; auto; rewrite Heq; simpl; rewrite Heq1, Heq2; auto.
 Qed.

End Cnf_Checker.

Module Cnf_CheckerInt.
  
  Inductive step :=
  | Res (pos:int) (res:resolution)
  | ImmFlatten (pos:int) (cid:clause_id) (lf:_lit) 
  | CTrue (pos:int)       
  | CFalse (pos:int)
  | BuildDef (pos:int) (l:_lit)
  | BuildDef2 (pos:int) (l:_lit)
  | BuildProj (pos:int) (l:_lit) (i:int)
  | ImmBuildDef (pos:int) (cid:clause_id)
  | ImmBuildDef2 (pos:int) (cid:clause_id)
  | ImmBuildProj (pos:int) (cid:clause_id) (i:int)
  | BuildDefInt (pos:int) (l:array _lit)
  | BuildProjInt (pos:int) (l:array _lit) (i:int).

  Local Open Scope list_scope.

  Local Notation check_flatten t_form := (check_flatten t_form (fun i1 i2 => i1 == i2) (fun _ _ => false)) (only parsing).

  Definition step_checker t_form t_atom s (st:step) :=
    match st with
    | Res pos res => S.set_resolve s pos res
    | ImmFlatten pos cid lf => S.set_clause s pos (check_flatten t_form s cid lf) 
    | CTrue pos => S.set_clause s pos Cnf.check_True
    | CFalse pos => S.set_clause s pos Cnf.check_False
    | BuildDef pos l => S.set_clause s pos (check_BuildDef t_form l)
    | BuildDef2 pos l => S.set_clause s pos (check_BuildDef2 t_form l)
    | BuildProj pos l i => S.set_clause s pos (check_BuildProj t_form l i)
    | ImmBuildDef pos cid => S.set_clause s pos (check_ImmBuildDef t_form s cid) 
    | ImmBuildDef2 pos cid => S.set_clause s pos (check_ImmBuildDef2 t_form s cid)
    | ImmBuildProj pos cid i => S.set_clause s pos (check_ImmBuildProj t_form s cid i) 
    | BuildDefInt pos l => S.set_clause s pos (check_BuildDefInt t_form t_atom l)
    | BuildProjInt pos l i => S.set_clause s pos (check_BuildProjInt t_form t_atom l i)
    end.

Lemma step_checker_correct : forall rho t_form t_atom,
    Form.check_form t_form -> Atom.check_atom t_atom ->
    forall s, S.valid (Form.interp_state_var rho t_form) s ->
      forall st : step, S.valid (Form.interp_state_var rho t_form)
        (step_checker t_form t_atom s st).
  Proof.
    intros rho t_form t_atom Ht s H; destruct (Form.check_form_correct rho _ Ht) as [[Ht1 Ht2] Ht3];intro;intros [pos res|pos cid lf|pos|pos|pos l|pos l|pos l i|pos cid|pos cid|pos cid i|pos l|pos l i]; simpl; try apply S.valid_set_clause; auto.
    apply S.valid_set_resolve; auto.
    apply valid_check_flatten; auto; try discriminate; intros a1 a2; unfold is_true; rewrite Int63Properties.eqb_spec; intro; subst a1; auto.
    apply valid_check_True; auto.
    apply valid_check_False; auto.
    apply valid_check_BuildDef; auto.
    apply valid_check_BuildDef2; auto.
    apply valid_check_BuildProj; auto.
    apply valid_check_ImmBuildDef; auto.
    apply valid_check_ImmBuildDef2; auto.
    apply valid_check_ImmBuildProj; auto.
    (*apply valid_check_BuildDefInt; auto.*)
    (*apply valid_check_BuildProjInt; auto.*)
    admit.
    admit.
  Qed.


  Definition cnf_checker t_form t_atom s t :=
    _checker_ (step_checker t_form t_atom) s t.


  Lemma cnf_checker_correct : forall rho t_form t_atom,
    Form.check_form t_form -> Atom.check_atom t_atom ->
    forall s t confl,
      cnf_checker t_form t_atom C.is_false s t confl ->
      ~ (S.valid (Form.interp_state_var rho t_form) s).
  Proof.
    unfold cnf_checker; intros rho t_form t_atom Ht Ht1; apply _checker__correct.
    intros c H; apply C.is_false_correct; auto.
    apply step_checker_correct; auto.
  Qed.


 Inductive certif :=
   | Certif : int -> _trace_ step -> int -> certif.

 Definition checker t_form t_atom l (c:certif) :=
   let (nclauses, t, confl) := c in   
   Form.check_form t_form && Atom.check_atom t_atom &&
   cnf_checker t_form t_atom C.is_false (S.set_clause (S.make nclauses) 0 (l::nil)) t confl.


 Lemma checker_correct : forall t_form t_atom l c,
    checker t_form t_atom l c = true ->
    forall rho, ~ (Lit.interp (Form.interp_state_var rho t_form) l).
 Proof.
   unfold checker. intros t_form t_atom l (nclauses, t, confl); unfold is_true; rewrite andb_true_iff; intros [H1 H2] rho H. apply andb_true_iff in H1. destruct H1. apply (cnf_checker_correct (rho:=rho) H0 H1 H2). destruct (Form.check_form_correct rho _ H0) as [[Ht1 Ht2] Ht3]; apply S.valid_set_clause; auto.
   apply S.valid_make; auto.
   unfold C.valid; simpl; rewrite H; auto.
 Qed.

 Definition checker_b t_form t_atom l (b:bool) (c:certif) :=
   let l := if b then Lit.neg l else l in
   checker t_form t_atom l c.

 Lemma checker_b_correct : forall t_var t_form t_atom l b c,
    checker_b t_form t_atom l b c = true ->
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l = b.
 Proof.
   unfold checker_b; intros t_var t_form t_atom l b c. case b; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l); auto; intros H1 H2; elim (checker_correct H2 (rho:=get t_var)); auto; rewrite Lit.interp_neg, H1; auto.
 Qed.

 Definition checker_eq t_form t_atom l1 l2 l (c:certif) :=
   negb (Lit.is_pos l) && 
   match t_form.[Lit.blit l] with
   | Form.Fiff l1' l2' => (l1 == l1') && (l2 == l2')
   | _ => false
   end && 
   checker t_form t_atom l c.

 Lemma checker_eq_correct : forall t_var t_form t_atom l1 l2 l c,
   checker_eq t_form t_atom l1 l2 l c = true ->
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l1 =
    Lit.interp (Form.interp_state_var (PArray.get t_var) t_form) l2.
 Proof.
   unfold checker_eq; intros t_var t_form t_atom l1 l2 l c; rewrite !andb_true_iff; case_eq (t_form .[ Lit.blit l]); [intros _ _|intros _|intros _|intros _ _ _|intros _ _|intros _ _|intros _ _|intros _ _ _|intros l1' l2' Heq|intros _ _ _ _]; intros [[H1 H2] H3]; try discriminate; rewrite andb_true_iff in H2; rewrite !Int63Properties.eqb_spec in H2; destruct H2 as [H2 H4]; subst l1' l2'; case_eq (Lit.is_pos l); intro Heq'; rewrite Heq' in H1; try discriminate; clear H1; assert (H:PArray.default t_form = Form.Ftrue /\ Form.wf t_form).
   unfold checker in H3; destruct c as (nclauses, t, confl); rewrite andb_true_iff in H3; destruct H3 as [H3 _]; apply andb_true_iff in H3. destruct H3. destruct (Form.check_form_correct (get t_var) _ H) as [[Ht1 Ht2] Ht3]; split; auto.
   destruct H as [H1 H2]; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l1); intro Heq1; case_eq (Lit.interp (Form.interp_state_var (get t_var) t_form) l2); intro Heq2; auto; elim (checker_correct H3 (rho:=get t_var)); unfold Lit.interp; rewrite Heq'; unfold Var.interp; rewrite Form.wf_interp_form; auto; rewrite Heq; simpl; rewrite Heq1, Heq2; auto.
 Qed.

End Cnf_CheckerInt.


(* Application to resolution + cnf justification + euf + lia *)

(* Require Cnf.Cnf. *)
(* Require Euf.Euf. *)
(* Require Lia.Lia. *)

Module Euf_Checker.

  Inductive step :=
  | Res (pos:int) (res:resolution)
  | ImmFlatten (pos:int) (cid:clause_id) (lf:_lit)
  | CTrue (pos:int)
  | CFalse (pos:int)
  | BuildDef (pos:int) (l:_lit)
  | BuildDef2 (pos:int) (l:_lit)
  | BuildProj (pos:int) (l:_lit) (i:int)
  | ImmBuildDef (pos:int) (cid:clause_id)
  | ImmBuildDef2 (pos:int) (cid:clause_id)
  | ImmBuildProj (pos:int) (cid:clause_id) (i:int)
  | EqTr (pos:int) (l:_lit) (fl: list _lit)
  | EqCgr (pos:int) (l:_lit) (fl: list (option _lit))
  | EqCgrP (pos:int) (l1:_lit) (l2:_lit) (fl: list (option _lit))
  | LiaMicromega (pos:int) (cl:list _lit) (c:list ZMicromega.ZArithProof)
  | LiaDiseq (pos:int) (l:_lit)
  | SplArith (pos:int) (orig:clause_id) (res:_lit) (l:list ZMicromega.ZArithProof)
  | SplDistinctElim (pos:int) (orig:clause_id) (res:_lit).

  Local Open Scope list_scope.

  Local Notation check_flatten t_atom t_form := (check_flatten t_form (check_hatom t_atom) (check_neg_hatom t_atom)) (only parsing).

  Definition step_checker t_atom t_form s (st:step) :=
    match st with
      | Res pos res => S.set_resolve s pos res
      | ImmFlatten pos cid lf => S.set_clause s pos (check_flatten t_atom t_form s cid lf)
      | CTrue pos => S.set_clause s pos Cnf.check_True
      | CFalse pos => S.set_clause s pos Cnf.check_False
      | BuildDef pos l => S.set_clause s pos (check_BuildDef t_form l)
      | BuildDef2 pos l => S.set_clause s pos (check_BuildDef2 t_form l)
      | BuildProj pos l i => S.set_clause s pos (check_BuildProj t_form l i)
      | ImmBuildDef pos cid => S.set_clause s pos (check_ImmBuildDef t_form s cid)
      | ImmBuildDef2 pos cid => S.set_clause s pos (check_ImmBuildDef2 t_form s cid)
      | ImmBuildProj pos cid i => S.set_clause s pos (check_ImmBuildProj t_form s cid i)
      | EqTr pos l fl => S.set_clause s pos (check_trans t_form t_atom l fl)
      | EqCgr pos l fl => S.set_clause s pos (check_congr t_form t_atom l fl)
      | EqCgrP pos l1 l2 fl => S.set_clause s pos (check_congr_pred t_form t_atom l1 l2 fl)
      | LiaMicromega pos cl c => S.set_clause s pos (check_micromega t_form t_atom cl c)
      | LiaDiseq pos l => S.set_clause s pos (check_diseq t_form t_atom l)
      | SplArith pos orig res l => S.set_clause s pos (check_spl_arith t_form t_atom (S.get s orig) res l)
      | SplDistinctElim pos orig res => S.set_clause s pos (check_distinct_elim t_form t_atom (S.get s orig) res)
    end.

  Lemma step_checker_correct : forall t_i t_func t_atom t_form,
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
      Form.check_form t_form -> Atom.check_atom t_atom ->
      Atom.wt t_i t_func t_atom ->
      forall s, S.valid rho s ->
        forall st : step, S.valid rho (step_checker t_atom t_form s st).
  Proof.
    intros t_i t_func t_atom t_form rho H1 H2 H10 s Hs. destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [[Ht1 Ht2] Ht3]. destruct (Atom.check_atom_correct _ H2) as [Ha1 Ha2]. intros [pos res|pos cid lf|pos|pos|pos l|pos l|pos l i|pos cid|pos cid|pos cid i|pos l fl|pos l fl|pos l1 l2 fl|pos cl c|pos l|pos orig res l|pos orig res]; simpl; try apply S.valid_set_clause; auto.
    apply S.valid_set_resolve; auto.
    apply valid_check_flatten; auto; intros h1 h2 H.
    rewrite (Syntactic.check_hatom_correct_bool _ _ _ Ha1 Ha2 _ _ H); auto.
    rewrite (Syntactic.check_neg_hatom_correct_bool _ _ _ H10 Ha1 Ha2 _ _ H); auto.
    apply valid_check_True; auto.
    apply valid_check_False; auto.
    apply valid_check_BuildDef; auto.
    apply valid_check_BuildDef2; auto.
    apply valid_check_BuildProj; auto.
    apply valid_check_ImmBuildDef; auto.
    apply valid_check_ImmBuildDef2; auto.
    apply valid_check_ImmBuildProj; auto.
    apply valid_check_trans; auto.
    apply valid_check_congr; auto.
    apply valid_check_congr_pred; auto.
    apply valid_check_micromega; auto.
    apply valid_check_diseq; auto.
    apply valid_check_spl_arith; auto.
    apply valid_check_distinct_elim; auto.
  Qed.

  Definition euf_checker t_atom t_form s t :=
    _checker_ (step_checker t_atom t_form) s t.

  Lemma euf_checker_correct : forall t_i t_func t_atom t_form,
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
      Form.check_form t_form -> Atom.check_atom t_atom ->
      Atom.wt t_i t_func t_atom ->
      forall s t confl,
        euf_checker t_atom t_form C.is_false s t confl ->
        ~ (S.valid rho s).
  Proof.
    unfold euf_checker; intros t_i t_func t_atom t_form rho H1 H2 H10; apply _checker__correct.
    intros c H; apply C.is_false_correct; auto.
    apply step_checker_correct; auto.
  Qed.

  Inductive certif :=
  | Certif : int -> _trace_ step -> int -> certif.

  Definition add_roots s d used_roots :=
    match used_roots with
      | Some ur => PArray.foldi_right (fun i c_index s =>
        let c := if c_index < length d then (d.[c_index])::nil else C._true in
          S.set_clause s i c) ur s
      | None => PArray.foldi_right (fun i c s => S.set_clause s i (c::nil)) d s
    end.

  Definition valid t_i t_func t_atom t_form d :=
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
    afold_left _ _ true andb (Lit.interp rho) d.

  Lemma add_roots_correct : forall t_i t_func t_atom t_form,
    let rho := Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form in
      Form.check_form t_form -> Atom.check_atom t_atom ->
      Atom.wt t_i t_func t_atom ->
      forall s d used_roots, S.valid rho s -> valid t_func t_atom t_form d ->
        S.valid rho (add_roots s d used_roots).
  Proof.
    intros t_i t_func t_atom t_form rho H1 H2 H10 s d used_roots H3; unfold valid; intro H4; pose (H5 := (afold_left_andb_true_inv _ _ _ H4)); unfold add_roots; assert (Valuation.wf rho) by (destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [_ H]; auto); case used_roots.
    intro ur; apply (foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i H6 Ha; apply S.valid_set_clause; auto; case_eq (ur .[ i] < length d).
    intro; unfold C.valid; simpl; rewrite H5; auto.
    intros; apply C.interp_true; auto.
    apply (foldi_right_Ind _ _ (fun _ a => S.valid rho a)); auto; intros a i H6 Ha; apply S.valid_set_clause; auto; unfold C.valid; simpl; rewrite H5; auto.
  Qed.

  Definition checker t_i t_func t_atom t_form d used_roots (c:certif) :=
    let (nclauses, t, confl) := c in
    Form.check_form t_form && Atom.check_atom t_atom &&
    Atom.wt t_i t_func t_atom &&
    euf_checker t_atom t_form C.is_false (add_roots (S.make nclauses) d used_roots) t confl.
  Implicit Arguments checker [].

  Lemma checker_correct : forall t_i t_func t_atom t_form d used_roots c,
    checker t_i t_func t_atom t_form d used_roots c = true ->
    ~ valid t_func t_atom t_form d.
  Proof.
    unfold checker; intros t_i t_func t_atom t_form d used_roots (nclauses, t, confl); rewrite !andb_true_iff; intros [[[H1 H2] H10] H3] H; eelim euf_checker_correct; try eassumption; apply add_roots_correct; try eassumption; apply S.valid_make; destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [_ H4]; auto.
  Qed.

  Definition checker_b t_i t_func t_atom t_form l (b:bool) (c:certif) :=
    let l := if b then Lit.neg l else l in
    let (nclauses,_,_) := c in
    checker t_i t_func t_atom t_form (PArray.make nclauses l) None c.

  Lemma checker_b_correct : forall t_i t_func t_atom t_form l b c,
    checker_b t_func t_atom t_form l b c = true ->
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l = b.
  Proof.
   unfold checker_b; intros t_i t_func t_atom t_form l b (nclauses, t, confl); case b; intros H2; case_eq (Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l); auto; intros H1; elim (checker_correct H2 (t_func:=t_func)); auto; unfold valid; apply afold_left_andb_true; intros i Hi; rewrite get_make; auto; rewrite Lit.interp_neg, H1; auto.
 Qed.

  Definition checker_eq t_i t_func t_atom t_form l1 l2 l (c:certif) :=
    negb (Lit.is_pos l) &&
    match t_form.[Lit.blit l] with
      | Form.Fiff l1' l2' => (l1 == l1') && (l2 == l2')
      | _ => false
    end &&
    let (nclauses,_,_) := c in
    checker t_i t_func t_atom t_form (PArray.make nclauses l) None c.

  Lemma checker_eq_correct : forall t_i t_func t_atom t_form l1 l2 l c,
    checker_eq t_func t_atom t_form l1 l2 l c = true ->
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l1 =
    Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l2.
  Proof.
   unfold checker_eq; intros t_i t_func t_atom t_form l1 l2 l (nclauses, t, confl); rewrite !andb_true_iff; case_eq (t_form .[ Lit.blit l]); [intros _ _|intros _|intros _|intros _ _ _|intros _ _|intros _ _|intros _ _|intros _ _ _|intros l1' l2' Heq|intros _ _ _ _]; intros [[H1 H2] H3]; try discriminate; rewrite andb_true_iff in H2; rewrite !Int63Properties.eqb_spec in H2; destruct H2 as [H2 H4]; subst l1' l2'; case_eq (Lit.is_pos l); intro Heq'; rewrite Heq' in H1; try discriminate; clear H1; assert (H:PArray.default t_form = Form.Ftrue /\ Form.wf t_form).
   unfold checker in H3; rewrite !andb_true_iff in H3; destruct H3 as [[[H3 _] _] _]; destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H3) as [[Ht1 Ht2] Ht3]; split; auto.
   destruct H as [H1 H2]; case_eq (Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l1); intro Heq1; case_eq (Lit.interp (Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form) l2); intro Heq2; auto; elim (checker_correct H3 (t_func:=t_func)); unfold valid; apply afold_left_andb_true; intros i Hi; rewrite get_make; unfold Lit.interp; rewrite Heq'; unfold Var.interp; rewrite Form.wf_interp_form; auto; rewrite Heq; simpl; rewrite Heq1, Heq2; auto.
 Qed.


  (* Checker for extraction, that does not know the evaluation contexts.
     TODO: show that there always exists a well-typed evaluation
     context. *)

  Definition checker_ext t_atom t_form d used_roots (c:certif) :=
    let (nclauses, t, confl) := c in
    Form.check_form t_form && Atom.check_atom t_atom &&
    euf_checker t_atom t_form C.is_false (add_roots (S.make nclauses) d used_roots) t confl.
  Implicit Arguments checker_ext [].

  Lemma checker_ext_correct : forall t_atom t_form d used_roots c,
    checker_ext t_atom t_form d used_roots c = true ->
    forall t_i t_func, Atom.wt t_i t_func t_atom ->
                       ~ valid t_func t_atom t_form d.
  Proof.
    unfold checker_ext; intros t_atom t_form d used_roots (nclauses, t, confl); rewrite !andb_true_iff; intros [[H1 H2] H3]; intros t_i t_func H10 H; eelim euf_checker_correct; try eassumption; apply add_roots_correct; try eassumption; apply S.valid_make; destruct (Form.check_form_correct (Atom.interp_form_hatom t_i t_func t_atom) _ H1) as [_ H4]; auto.
  Qed.

  (* For debugging *)
  (*
  Fixpoint is__true (c:C.t) :=
    match c with
      | cons l q => if (l == 0) then true else is__true q
      | _ => false
    end.

  Definition step_checker_debug t_atom t_form s (st:step) :=
    match st with
      | Res pos res =>
        let s' := S.set_resolve s pos res in
          if is__true (s'.[pos]) then None else Some s'
      | ImmFlatten pos cid lf =>
        let c := check_flatten t_atom t_form s cid lf in
          if is__true c then None else Some (S.set_clause s pos c)
      | CTrue pos => Some (S.set_clause s pos Cnf.check_True)
      | CFalse pos => Some (S.set_clause s pos Cnf.check_False)
      | BuildDef pos l =>
        let c := check_BuildDef t_form l in
          if is__true c then None else Some (S.set_clause s pos c)
      | BuildDef2 pos l =>
        let c := check_BuildDef2 t_form l in
          if is__true c then None else Some (S.set_clause s pos c)
      | BuildProj pos l i =>
        let c := check_BuildProj t_form l i in
          if is__true c then None else Some (S.set_clause s pos c)
      | ImmBuildDef pos cid =>
        let c := check_ImmBuildDef t_form s cid in
          if is__true c then None else Some (S.set_clause s pos c)
      | ImmBuildDef2 pos cid =>
        let c := check_ImmBuildDef2 t_form s cid in
          if is__true c then None else Some (S.set_clause s pos c)
      | ImmBuildProj pos cid i =>
        let c := check_ImmBuildProj t_form s cid i in
          if is__true c then None else Some (S.set_clause s pos c)
      | EqTr pos l fl =>
        let c := check_trans t_form t_atom l fl in
          if is__true c then None else Some (S.set_clause s pos c)
      | EqCgr pos l fl =>
        let c := check_congr t_form t_atom l fl in
          if is__true c then None else Some (S.set_clause s pos c)
      | EqCgrP pos l1 l2 fl =>
        let c := check_congr_pred t_form t_atom l1 l2 fl in
          if is__true c then None else Some (S.set_clause s pos c)
      | LiaMicromega pos cl c =>
        let c := check_micromega t_form t_atom cl c in
          if is__true c then None else Some (S.set_clause s pos c)
      | LiaDiseq pos l =>
        let c := check_diseq t_form t_atom l in
          if is__true c then None else Some (S.set_clause s pos c)
      | SplArith pos orig res l =>
        let c := check_spl_arith t_form t_atom (S.get s orig) res l in
          if is__true c then None else Some (S.set_clause s pos c)
      | SplDistinctElim pos input res =>
        let c := check_distinct_elim t_form t_atom (S.get s input) res in
          if is__true c then None else Some (S.set_clause s pos c)
    end.

  Definition euf_checker_debug t_atom t_form s t :=
    _checker_debug_ (step_checker_debug t_atom t_form) s t.

  Definition euf_checker_partial t_atom t_form s t :=
    _checker_partial_ (step_checker t_atom t_form) s t.
  *)

End Euf_Checker.


Unset Implicit Arguments.

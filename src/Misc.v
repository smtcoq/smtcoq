(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bool List PArray Int63.
Local Open Scope int63_scope.
Local Open Scope array_scope.


(** Lemmas about Bool *)

Lemma implb_true_r : forall a, implb a true = true.
Proof. intros [ | ]; reflexivity. Qed.


(** Lemmas about Int63 *)

Lemma le_eq : forall i j,
  (j <= i) = true -> (j + 1 <= i) = false -> i = j.
Proof.
  intros i j; rewrite leb_spec; destruct (dec_Zle [|j+1|] [|i|]) as [H|H].
  rewrite <- leb_spec in H; rewrite H; discriminate.
  intros H1 _; apply to_Z_inj; rewrite add_spec, to_Z_1 in H.
  assert (H2: (([|j|] + 1)%Z < wB)%Z \/ ([|j|] + 1)%Z = wB).
  pose (H3 := to_Z_bounded j); omega.
  destruct H2 as [H2|H2].
  rewrite Zmod_small in H.
  omega.
  split.
  pose (H3 := to_Z_bounded j); omega.
  assumption.
  rewrite H2, Z_mod_same_full in H; elim H; destruct (to_Z_bounded i) as [H3 _]; assumption.
Qed.


Lemma lt_eq : forall i j,
  (i < j + 1) = true -> (i < j) = false -> i = j.
Proof.
  intros i j. rewrite ltb_spec. destruct (dec_Zlt [|i|] [|j|]) as [H|H].
  rewrite <- ltb_spec in H; rewrite H; discriminate.
  intros H1 _; apply to_Z_inj. rewrite add_spec in H1. rewrite to_Z_1 in H1.
  assert (H2: (([|j|] + 1)%Z < wB)%Z \/ ([|j|] + 1)%Z = wB).
  pose (H3 := to_Z_bounded j); omega.
  destruct H2 as [H2|H2].
  rewrite Zmod_small in H1.
  omega.
  split.
  pose (H3 := to_Z_bounded j); omega.
  assumption.
  rewrite H2, Z_mod_same_full in H1; elimtype False. destruct (to_Z_bounded i) as [H3 _]. omega.
Qed.


Lemma foldi_down_ZInd2 :
   forall A (P: Z -> A -> Prop) (f:int -> A -> A) max min a,
   (max < min = true -> P ([|min|])%Z a) ->
   (P ([|max|]+1)%Z a) ->
   (forall i a, min <= i = true -> i <= max = true -> P ([|i|]+1)%Z a -> P [|i|] (f i a)) ->
   P [|min|] (foldi_down f max min a).
Proof.
 unfold foldi_down;intros A P f max min a Hlt;intros.
 set (P' z cont :=
       if Zlt_bool z ([|min|]+1)%Z then cont = (fun a0 : A => a0)
       else forall a, P z a -> P [|min|] (cont a)).
 assert (H1: P' ([|max|]+1)%Z (foldi_down_cont (fun (i : int) (cont : A -> A) (a0 : A) => cont (f i a0)) max
                       min (fun a0 : A => a0))).
 apply foldi_down_cont_ZInd;intros;red.
 assert (H20: (z+1 < [|min|]+1)%Z).
 omega.
 rewrite Zlt_is_lt_bool in H20; rewrite H20;trivial.
 case_eq (Zlt_bool ([|i|]+1) ([|min|]+1));intros.
  rewrite <- Zlt_is_lt_bool in H4;rewrite leb_spec in H1;elimtype False;omega.
 clear H4;revert H3;unfold P'.
 case_eq (Zlt_bool ([|i|] - 1 + 1) ([|min|]+1));intros;auto.
  rewrite <- Zlt_is_lt_bool in H3; assert ([|i|] = [|min|]) by (rewrite leb_spec in H1;omega).
  rewrite H4, <- H6. apply H0;trivial.
  apply H4. replace ([|i|] - 1 + 1)%Z with [|i|] by omega. auto.
 revert H1;unfold P'.
 case_eq (Zlt_bool ([|max|]+1)%Z ([|min|]+1)%Z);auto.
 rewrite <- Zlt_is_lt_bool.
 intro H22; assert (H21: ([|max|] < [|min|])%Z). omega.
 rewrite <- ltb_spec in H21. intros;rewrite foldi_down_cont_lt;auto.
Qed.


Lemma foldi_down_Ind2 : forall A (P : int -> A -> Prop) f max min a,
  (max < max_int = true) ->
  (max < min = true -> P min a) ->
  P (max+1) a ->
  (forall i a, min <= i = true -> i <= max = true ->
    P (i+1) a -> P i (f i a)) ->
  P min (foldi_down f max min a).
Proof.
  intros A P f max min a H H0 H1 H2.
  set (P' z a := (0 <= z < wB)%Z -> P (of_Z z) a).
  assert (W:= to_Z_add_1 _ _ H).
  assert (P' ([|min|])%Z (foldi_down f max min a)).
  apply foldi_down_ZInd2;unfold P';intros.
  rewrite of_to_Z;auto.
  rewrite <- W, of_to_Z;auto.
  rewrite of_to_Z. apply H2; trivial.
  assert (i < max_int = true).
  apply leb_ltb_trans with max; trivial.
  rewrite <- (to_Z_add_1 _ _ H7) in H5. rewrite of_to_Z in H5. apply H5. apply to_Z_bounded.
  unfold P' in H3; rewrite of_to_Z in H3;apply H3;apply to_Z_bounded.
Qed.


(** Lemmas about PArray.to_list *)

Lemma to_list_In : forall {A} (t: array A) i,
  i < length t = true -> In (t.[i]) (to_list t).
Proof.
  intros A t i H; unfold to_list; case_eq (0 == length t); intro Heq.
  unfold is_true in H; rewrite ltb_spec in H; rewrite eqb_spec in Heq; rewrite <- Heq in H; rewrite to_Z_0 in H; pose (H1 := to_Z_bounded i); elimtype False; omega.
  pose (P := fun j a => i < j = true \/ In (t .[ i]) a).
  pose (H1:= foldi_down_Ind2 _ P); unfold P in H1.
  assert (H2: i < 0 = true \/ In (t .[ i]) (foldi_down (fun (i0 : int) (l : list A) => t .[ i0] :: l) (length t - 1) 0 nil)).
  apply H1.
  rewrite ltb_spec; erewrite to_Z_sub_1; try eassumption.
  pose (H2 := to_Z_bounded (length t)); change [|max_int|] with (wB-1)%Z; omega.
  intro H2; elimtype False; rewrite ltb_spec, to_Z_0 in H2; pose (H3 := to_Z_bounded (length t - 1)); omega.
  left; unfold is_true; rewrite ltb_spec; rewrite (to_Z_add_1 _ max_int).
  erewrite to_Z_sub_1; try eassumption.
  unfold is_true in H; rewrite ltb_spec in H; omega.
  rewrite ltb_spec; erewrite to_Z_sub_1; try eassumption.
  pose (H2 := to_Z_bounded (length t)); change [|max_int|] with (wB-1)%Z; omega.
  intros j a H2 H3 [H4|H4].
  case_eq (i < j); intro Heq2.
  left; reflexivity.
  right; rewrite (lt_eq _ _ H4 Heq2); constructor; reflexivity.
  right; constructor 2; assumption.
  destruct H2 as [H2|H2]; try assumption.
  unfold is_true in H2; rewrite ltb_spec, to_Z_0 in H2; pose (H3 := to_Z_bounded i); elimtype False; omega.
Qed.

Lemma In_to_list : forall {A} (t: array A) x,
  In x (to_list t) -> exists i, i < length t = true /\ x = t.[i].
Proof.
  intros A t x; unfold to_list; case_eq (0 == length t); intro Heq.
  intro H; inversion H.
  rewrite eqb_false_spec in Heq.
  pose (P (_:int) l := In x l ->
   exists i : int, (i < length t) = true /\ x = t .[ i]).
  pose (H1 := foldi_down_Ind2 _ P (fun (i : int) (l : list A) => t .[ i] :: l) (length t - 1) 0); unfold P in H1; apply H1.
  rewrite ltb_spec, to_Z_sub_1_diff; auto; change [|max_int|] with (wB-1)%Z; pose (H2 := to_Z_bounded (length t)); omega.
  intros _ H; inversion H.
  intro H; inversion H.
  simpl; intros i a _ H2 IH [H3|H3].
  exists i; split; auto; rewrite ltb_spec; rewrite leb_spec, to_Z_sub_1_diff in H2; auto; omega.
  destruct (IH H3) as [j [H4 H5]]; exists j; auto.
Qed.


(** Lemmas about PArray.mapi *)

Lemma length_mapi : forall {A B} (f:int -> A -> B) t,
  length (mapi f t) = length t.
Proof.
  unfold mapi; intros A B f t; case_eq (length t == 0).
  rewrite Int63Properties.eqb_spec; intro Heq; rewrite Heq, length_make; auto.
  rewrite eqb_false_spec; intro Heq; apply foldi_ind.
  rewrite length_make, ltb_length; auto.
  intros i a _ H1 H2; rewrite length_set; auto.
Qed.


Lemma default_mapi : forall {A B} (f:int -> A -> B) t,
  default (mapi f t) = f (length t) (default t).
Proof.
  unfold mapi; intros A B f t; case (length t == 0).
  rewrite default_make; auto.
  apply foldi_ind.
  rewrite default_make; auto.
  intros; rewrite default_set; auto.
Qed.

Lemma get_mapi : forall {A B} (f:int -> A -> B) t i,
  i < length t = true -> (mapi f t).[i] = f i (t.[i]).
Proof.
  intros A B f t i Hi; generalize (length_mapi f t); unfold mapi; case_eq (length t == 0).
  rewrite Int63Properties.eqb_spec; intro Heq; rewrite Heq in Hi; eelim ltb_0; eassumption.
  rewrite eqb_false_spec; intro Heq; pose (Hi':=Hi); replace (length t) with ((length t - 1) + 1) in Hi'.
  generalize Hi'; apply (foldi_Ind _ (fun j a => (i < j) = true -> length a = length t -> a.[i] = f i (t.[i]))).
  rewrite ltb_spec, (to_Z_sub_1 _ i); auto; destruct (to_Z_bounded (length t)) as [_ H]; change [|max_int|] with (wB-1)%Z; omega.
  intros H _; eelim ltb_0; eassumption.
  intros H; eelim ltb_0; eassumption.
  intros j a _ H1 IH H2 H3; rewrite length_set in H3; case_eq (j == i).
  rewrite Int63Properties.eqb_spec; intro Heq2; subst i; rewrite get_set_same; auto; rewrite H3; auto.
  rewrite eqb_false_spec; intro Heq2; rewrite get_set_other; auto; apply IH; auto; rewrite ltb_spec; rewrite ltb_spec, (to_Z_add_1 _ (length t)) in H2.
  assert (H4: [|i|] <> [|j|]) by (intro H4; apply Heq2, to_Z_inj; auto); omega.
  rewrite ltb_spec; rewrite leb_spec, (to_Z_sub_1 _ _ Hi) in H1; omega.
  apply to_Z_inj; rewrite (to_Z_add_1 _ max_int).
  rewrite to_Z_sub_1_diff; auto; omega.
  rewrite ltb_spec, to_Z_sub_1_diff; auto; destruct (to_Z_bounded (length t)) as [_ H]; change [|max_int|] with (wB-1)%Z; omega.
Qed.


Lemma get_mapi_outofbound : forall {A B} (f:int -> A -> B) t i,
  i < length t = false -> (mapi f t).[i] = f (length t) (default t).
Proof.
  intros A B f t i H1; rewrite get_outofbound.
  apply default_mapi.
  rewrite length_mapi; auto.
Qed.


(** Custom fold_left and fold_right *)

Definition afold_left A B default (OP : A -> A -> A) (F : B -> A) (V : array B) :=
  let n := PArray.length V in
  if n == 0 then default
  else foldi (fun i a => OP a (F (V.[i]))) 1 (n-1) (F (V.[0])).


Definition afold_right A B default (OP : A -> A -> A) (F : B -> A) (V : array B) :=
  let n := PArray.length V in
  if n == 0 then default else
    if n <= 1 then F (V.[0])
    else foldi_down (fun i b => OP (F (V.[i])) b) (n-2) 0 (F (V.[n-1])).


(** Some properties about afold_left *)

Lemma afold_left_eq :
  forall A B OP def (F1 F2 : A -> B) V1 V2,
    length V1 = length V2 ->
    (forall i, i < length V1 = true -> F1 (V1.[i]) = F2 (V2.[i])) ->
    afold_left _ _ def OP F1 V1 = afold_left _ _ def OP F2 V2.
Proof.
  unfold afold_left;intros. rewrite <- H.
  destruct (Int63Properties.reflect_eqb (length V1) 0);trivial.
  rewrite (H0 0); [ |  unfold is_true;rewrite <- not_0_ltb;trivial].
  apply foldi_eq_compat;intros;rewrite H0;trivial.
  unfold is_true;rewrite ltb_leb_sub1;trivial.
Qed.


Definition afoldi_left {A B:Type} default (OP : int -> A -> A -> A) (F : B -> A) (V : array B) :=
  let n := PArray.length V in
    if n == 0 then default
      else foldi (fun i a => OP i a (F (V.[i]))) 1 (n-1) (F (V.[0])).


Lemma afoldi_left_Ind :
  forall {A B: Type} (P : int -> A -> Prop) default (OP : int -> A -> A -> A) (F : B -> A) (t:array B),
    if length t == 0 then
      True
    else
      (forall a i, i < length t = true -> P i a -> P (i+1) (OP i a (F (t.[i])))) ->
      P 1 (F (t.[0])) ->
      P (length t) (afoldi_left default OP F t).
Proof.
  intros A B P default OP F t; case_eq (length t == 0).
  intros; exact I.
  intros Heq H1 H2; unfold afoldi_left; rewrite Heq;
    assert (H: (length t - 1) + 1 = length t) by ring.
  rewrite <- H at 1; apply foldi_Ind; auto.
  assert (W:= leb_max_int (length t)); rewrite leb_spec in W.
  rewrite ltb_spec, to_Z_sub_1_diff; auto with zarith.
  intro H3; rewrite H3 in Heq; discriminate.
  intro Hlt; assert (H3: length t - 1 = 0).
  rewrite ltb_spec, to_Z_1 in Hlt; apply to_Z_inj; rewrite to_Z_0; pose (H3 := to_Z_bounded (length t - 1)); omega.
  rewrite H3; assumption.
  intros i a H3 H4; apply H1; trivial.
  rewrite ltb_leb_sub1; auto.
  intro H5; rewrite H5 in Heq; discriminate.
Qed.


Lemma afold_left_Ind :
  forall A B (P : int -> A -> Prop) default (OP : A -> A -> A) (F : B -> A) (t:array B),
    if length t == 0 then
      True
    else
      (forall a i, i < length t = true -> P i a -> P (i+1) (OP a (F (t.[i])))) ->
      P 1 (F (t.[0])) ->
      P (length t) (afold_left A B default OP F t).
Proof.
  intros A B P default OP F t;
    apply (afoldi_left_Ind P default (fun _ => OP)); trivial.
Qed.


Lemma afold_left_ind :
  forall A B (P : A -> Prop) default (OP : A -> A -> A) (F : B -> A) (t:array B),
    (forall a i, i < length t = true -> P a -> P (OP a (F (t.[i])))) ->
    P default -> P (F (t.[0])) ->
    P (afold_left _ _ default OP F t).
Proof.
  intros A B P default OP F t H1 H2 H4.
  pose (H3 := afold_left_Ind A B (fun _ => P) default OP F t).
  case_eq (length t == 0); intro Heq.
  unfold afold_left; rewrite Heq; assumption.
  rewrite Heq in H3; apply H3; trivial.
Qed.


Lemma afold_left_spec : forall A B (f:B -> A) args op e,
  (forall a, op e a = a) ->
  afold_left _ _ e op f args =
  fold_left (fun a v  => op a (f v)) e args.
  Proof.
    unfold afold_left, fold_left;intros A B f args op neu H10.
    destruct (reflect_eqb (length args) 0) as [e|n].
    rewrite e, eqb_refl;trivial.
    apply not_eq_sym in n;rewrite (eqb_false_complete _ _ n).
    case_eq (0 < (length args - 1));intros H.
    rewrite foldi_lt with (from := 0);trivial.
    rewrite H10; auto.
    assert (H0: (0 <> [|length args|])%Z).
    intros Heq;apply n;apply to_Z_inj;trivial.
    assert (H1: length args = 1).
    generalize (to_Z_bounded (length args)).
    rewrite <- not_true_iff_false, ltb_spec, to_Z_0, to_Z_sub_1_diff in H;auto.
    intros;apply to_Z_inj;rewrite to_Z_1;omega.
    rewrite H1; change (1 - 1) with 0; rewrite (foldi_eq _ _ 0 0); auto.
  Qed.


(** Some properties about afold_right *)

Lemma afold_right_eq :
  forall A B OP def (F1 F2 : A -> B) V1 V2,
    length V1 = length V2 ->
    (forall i, i < length V1 = true -> F1 (V1.[i]) = F2 (V2.[i])) ->
    afold_right _ _ def OP F1 V1 = afold_right _ _ def OP F2 V2.
Proof.
  unfold afold_right;intros.
  rewrite <- H.
  destruct (Int63Properties.reflect_eqb (length V1) 0);trivial.
  destruct (reflect_leb (length V1) 1);intros.
  apply H0;unfold is_true;rewrite ltb_leb_sub1;trivial. apply leb_0.
  assert (length V1 - 1 < length V1 = true).
  rewrite ltb_leb_sub1;auto using leb_refl.
  rewrite (H0 (length V1 - 1));trivial.
  apply foldi_down_eq_compat;intros;rewrite H0;trivial.
  unfold is_true;rewrite ltb_leb_sub1;[ | trivial].
  apply ltb_leb_sub1;trivial.
  revert n0 H3;rewrite ltb_spec, leb_spec, to_Z_1, sub_spec.
  change [|2|] with 2%Z.
  intros HH;assert (W:= to_Z_bounded (length V1));rewrite Zmod_small;omega.
Qed.


Definition afoldi_right {A B:Type} default (OP : int -> A -> A -> A) (F : B -> A) (V : array B) :=
  let n := PArray.length V in
    if n == 0 then default
      else if n <= 1 then F (V .[ 0])
        else foldi_down (fun i a => OP i (F (V.[i])) a) (n-2) 0 (F (V.[n-1])).


Lemma afoldi_right_Ind :
  forall {A B: Type} (P : int -> A -> Prop) default (OP : int -> A -> A -> A) (F : B -> A) (t:array B),
    if length t <= 1 then
      True
    else
      (forall a i, i < length t - 1 = true -> P (i+1) a -> P i (OP i (F (t.[i])) a)) ->
      P ((length t)-1) (F (t.[(length t)-1])) ->
      P 0 (afoldi_right default OP F t).
Proof.
  intros A B P default OP F t; case_eq (length t <= 1).
  intros; exact I.
  intros Heq H1 H2; unfold afoldi_right. replace (length t == 0) with false.
  rewrite Heq.
  set (P' z a := P (of_Z (z + 1)) a).
  change (P' ([|0|] - 1)%Z (foldi_down (fun (i : int) (a : A) => OP i (F (t .[ i])) a) (length t - 2) 0 (F (t .[ length t - 1])))).
  apply foldi_down_ZInd;unfold P'.
  intros Hlt;elim (ltb_0 _ Hlt).
  replace (length t - 2) with (length t - 1 - 1) by ring.
  rewrite to_Z_sub_1_diff.
  ring_simplify ([|length t - 1|] - 1 + 1)%Z;rewrite of_to_Z;trivial.
  assert (H10: (1 < length t) = true) by (rewrite ltb_negb_geb, Heq; auto).
  intro H11. rewrite ltb_spec in H10. assert (H12: [|length t - 1|] = 0%Z) by (rewrite H11; auto). change [|1|] with (1%Z) in H10. rewrite to_Z_sub_1_diff in H12; [omega| ]. intro H13. assert (H14: [|length t|] = 0%Z) by (rewrite H13; auto). omega.
  intros;ring_simplify ([|i|] - 1 + 1)%Z;rewrite of_to_Z;auto.
  assert (i < length t - 1 = true).
    rewrite ltb_spec. rewrite leb_spec in H0. replace (length t - 2) with (length t - 1 - 1) in H0 by ring. rewrite to_Z_sub_1_diff in H0; [omega| ]. intro H4. assert (H5: [|length t - 1|] = 0%Z) by (rewrite H4; auto). assert (H6: 1 < length t = true) by (rewrite ltb_negb_geb, Heq; auto). rewrite ltb_spec in H6. change ([|1|]) with (1%Z) in H6. rewrite to_Z_sub_1_diff in H5; [omega| ]. intro H7. assert (H8: [|length t|] = 0%Z) by (rewrite H7; auto). omega.
  apply H1;trivial.
  rewrite <-(to_Z_add_1 _ _ H4), of_to_Z in H3;auto.
  symmetry. rewrite eqb_false_spec. intro H. rewrite H in Heq. discriminate.
Qed.


Lemma afold_right_Ind :
  forall A B (P : int -> A -> Prop) default (OP : A -> A -> A) (F : B -> A) (t:array B),
    if length t <= 1 then
      True
    else
      (forall a i, i < length t - 1 = true -> P (i+1) a -> P i (OP (F (t.[i])) a)) ->
      P ((length t)-1) (F (t.[(length t)-1])) ->
      P 0 (afold_right A B default OP F t).
Proof.
  intros A B P default OP F t;
    apply (afoldi_right_Ind P default (fun _ => OP) F).
Qed.


Lemma afold_right_ind :
  forall A B (P : A -> Prop) default (OP : A -> A -> A) (F : B -> A) (t:array B),
    (forall a i, i < length t - 1 = true -> P a -> P (OP (F (t.[i])) a)) ->
    P default -> P (F (t.[length t - 1])) ->
    P (afold_right _ _ default OP F t).
Proof.
  intros A B P default OP F t H1 H2 H4.
  pose (H3 := afold_right_Ind A B (fun _ => P) default OP F t).
  unfold afold_right. case_eq (length t == 0); auto. intro H10. assert (H := H10). rewrite eqb_false_spec in H. case_eq (length t <= 1); intro Heq.
  replace 0 with (length t - 1); auto. apply to_Z_inj. rewrite to_Z_sub_1_diff; auto. rewrite leb_spec in Heq. assert (H5 := leb_0 (length t)). rewrite leb_spec in H5. change [|0|] with 0%Z in *. change [|1|] with 1%Z in Heq. assert (H6 : [|length t|] <> 0%Z) by (intro H6; elim H; apply to_Z_inj; auto). omega. rewrite Heq in H3. unfold afold_right in H3. rewrite H10, Heq in H3. apply H3; auto.
Qed.


Lemma afold_right_ind_nonempty :
  forall A B (P : A -> Prop) default (OP : A -> A -> A) (F : B -> A) (t:array B),
    (forall a i, i < length t - 1 = true -> P a -> P (OP (F (t.[i])) a)) ->
    0 < length t = true -> P (F (t.[length t - 1])) ->
    P (afold_right _ _ default OP F t).
Proof.
  intros A B P default OP F t H1 H2 H4.
  pose (H3 := afold_right_Ind A B (fun _ => P) default OP F t).
  unfold afold_right. assert (H10 : length t == 0 = false) by (rewrite eqb_false_spec; intro H; rewrite H in H2; discriminate). rewrite H10. assert (H := H10). rewrite eqb_false_spec in H. case_eq (length t <= 1); intro Heq.
  replace 0 with (length t - 1); auto. apply to_Z_inj. rewrite to_Z_sub_1_diff; auto. rewrite leb_spec in Heq. assert (H5 := leb_0 (length t)). rewrite leb_spec in H5. change [|0|] with 0%Z in *. change [|1|] with 1%Z in Heq. assert (H6 : [|length t|] <> 0%Z) by (intro H6; elim H; apply to_Z_inj; auto). omega. rewrite Heq in H3. unfold afold_right in H3. rewrite H10, Heq in H3. apply H3; auto.
Qed.


Lemma afold_right_spec : forall A B (f:B -> A) args op e,
  (forall a, op a e = a) ->
  afold_right _ _ e op f args =
  fold_right (fun v a => op (f v) a) args e.
  Proof.
    unfold afold_right, fold_right;intros A B f args op neu H10.
    destruct (reflect_eqb (length args) 0) as [e|n].
    rewrite e, eqb_refl;trivial.
    apply not_eq_sym in n;rewrite (eqb_false_complete _ _ n).
    case_eq (length args <= 1); intro Heq.
    assert (H11: length args = 1).
    apply to_Z_inj. rewrite leb_spec in Heq. assert (H11: 0%Z <> [|length args|]) by (intro H; elim n; apply to_Z_inj; auto). change [|1|] with (1%Z) in *. assert (H12 := leb_0 (length args)). rewrite leb_spec in H12. change [|0|] with 0%Z in H12. omega.
    rewrite H11, foldi_down_eq; auto.
    assert (H11: 1 < length args = true) by (rewrite ltb_negb_geb, Heq; auto). replace (foldi_down (fun (i : int) (b : A) => op (f (args .[ i])) b) (length args - 1) 0 neu) with (foldi_down (fun (i : int) (b : A) => op (f (args .[ i])) b) (length args - 1 - 1) 0 (op (f (args .[ length args - 1])) neu)).
    replace (length args - 1 - 1) with (length args - 2) by ring. rewrite H10. auto.
    symmetry. apply foldi_down_gt. rewrite ltb_spec. change [|0|] with 0%Z. rewrite to_Z_sub_1_diff; auto. rewrite ltb_spec in H11. change [|1|] with 1%Z in H11. omega.
  Qed.


(** Application to our uses of afold_left and afold_right *)
(* Case andb *)

Lemma afold_left_andb_false : forall A i a f,
  i < length a = true ->
  f (a .[ i]) = false ->
  afold_left bool A true andb f a = false.
Proof.
  intros A i a f; rewrite afold_left_spec; auto; apply (fold_left_Ind _ _ (fun j t => (i < j) = true -> f (a .[ i]) = false -> t = false)).
  intros b j H1 H2 H3 H4; case_eq (i == j).
  rewrite Int63Properties.eqb_spec; intro; subst i; rewrite H4, andb_false_r; auto.
  rewrite eqb_false_spec; intro Heq; rewrite H2; auto; rewrite ltb_spec; rewrite ltb_spec in H3; rewrite (to_Z_add_1 _ (length a)) in H3; auto; assert (H5: [|i|] <> [|j|]) by (intro H5; apply Heq, to_Z_inj; auto); omega.
  intro H; eelim ltb_0; eassumption.
Qed.


Lemma afold_left_andb_false_inv : forall A a f,
  afold_left bool A true andb f a = false ->
  exists i, (i < length a = true) /\ (f (a .[ i]) = false).
Proof.
  intros A a f; rewrite afold_left_spec; auto; apply fold_left_ind; try discriminate.
  intros b i H1; case b; simpl.
  intros _ H2; exists i; auto.
  intros H2 _; destruct (H2 (refl_equal false)) as [j [H3 H4]]; exists j; auto.
Qed.


Lemma afold_left_andb_true : forall A a f,
  (forall i, i < length a = true -> f (a.[i]) = true) ->
  afold_left bool A true andb f a = true.
Proof.
  intros A a f H; rewrite afold_left_spec; auto; apply fold_left_ind; trivial; intros b j H1 H2; rewrite H2; simpl; rewrite H; trivial.
Qed.


Lemma afold_left_andb_true_inv : forall A a f,
  afold_left bool A true andb f a = true ->
  forall i, i < length a = true -> f (a.[i]) = true.
Proof.
  intros A a f; rewrite afold_left_spec; auto; apply (fold_left_Ind _ _ (fun j t => t = true -> forall i, (i < j) = true -> f (a .[ i]) = true)).
  intros b i H1; case b; simpl; try discriminate; intros H2 H3 j Hj; case_eq (j == i); intro Heq.
  rewrite Int63Properties.eqb_spec in Heq; subst j; auto.
  apply H2; auto; rewrite eqb_false_spec in Heq; rewrite ltb_spec; rewrite ltb_spec in Hj; assert (H4: [|j|] <> [|i|]) by (intro H; apply Heq, to_Z_inj; auto); rewrite (to_Z_add_1 _ (length a)) in Hj; auto; omega.
  intros _ i H; eelim ltb_0; eassumption.
Qed.


(* Case orb *)

Lemma afold_left_orb_true : forall A i a f,
  i < length a = true ->
  f (a .[ i]) = true ->
  afold_left bool A false orb f a = true.
Proof.
  intros A i a f; rewrite afold_left_spec; auto; apply (fold_left_Ind _ _ (fun j t => (i < j) = true -> f (a .[ i]) = true -> t = true)).
  intros b j H1 H2 H3 H4; case_eq (i == j).
  rewrite Int63Properties.eqb_spec; intro; subst i; rewrite H4, orb_true_r; auto.
  rewrite eqb_false_spec; intro Heq; rewrite H2; auto; rewrite ltb_spec; rewrite ltb_spec in H3; rewrite (to_Z_add_1 _ (length a)) in H3; auto; assert (H5: [|i|] <> [|j|]) by (intro H5; apply Heq, to_Z_inj; auto); omega.
  intro H; eelim ltb_0; eassumption.
Qed.


Lemma afold_left_orb_true_inv : forall A a f,
  afold_left bool A false orb f a = true ->
  exists i, (i < length a = true) /\ (f (a .[ i]) = true).
Proof.
  intros A a f; rewrite afold_left_spec; auto; apply fold_left_ind; try discriminate.
  intros b i H1; case b; simpl.
  intros H2 _; destruct (H2 (refl_equal true)) as [j [H3 H4]]; exists j; auto.
  intros _ H2; exists i; auto.
Qed.


Lemma afold_left_orb_false : forall A a f,
  (forall i, i < length a = true -> f (a.[i]) = false) ->
  afold_left bool A false orb f a = false.
Proof.
  intros A a f H; rewrite afold_left_spec; auto; apply fold_left_ind; trivial; intros b j H1 H2; rewrite H2; simpl; rewrite H; trivial.
Qed.


Lemma afold_left_orb_false_inv : forall A a f,
  afold_left bool A false orb f a = false ->
  forall i, i < length a = true -> f (a.[i]) = false.
Proof.
  intros A a f; rewrite afold_left_spec; auto; apply (fold_left_Ind _ _ (fun j t => t = false -> forall i, (i < j) = true -> f (a .[ i]) = false)).
  intros b i H1; case b; simpl; try discriminate; intros H2 H3 j Hj; case_eq (j == i); intro Heq.
  rewrite Int63Properties.eqb_spec in Heq; subst j; auto.
  apply H2; auto; rewrite eqb_false_spec in Heq; rewrite ltb_spec; rewrite ltb_spec in Hj; assert (H4: [|j|] <> [|i|]) by (intro H; apply Heq, to_Z_inj; auto); rewrite (to_Z_add_1 _ (length a)) in Hj; auto; omega.
  intros _ i H; eelim ltb_0; eassumption.
Qed.


(* Case implb *)

Lemma afold_right_implb_false : forall A a f,
  0 < length a = true /\
  (forall i, i < length a - 1 = true -> f (a .[ i]) = true) /\
  f (a.[length a - 1]) = false ->
  afold_right bool A true implb f a = false.
Proof.
  intros A a f; intros [H1 [H2 H3]]; apply afold_right_ind_nonempty; auto; intros b i H4 H5; rewrite H5, H2; auto.
Qed.


Lemma afold_right_implb_false_inv : forall A a f,
  afold_right bool A true implb f a = false ->
  0 < length a = true /\
  (forall i, i < length a - 1 = true -> f (a .[ i]) = true) /\
  f (a.[length a - 1]) = false.
Proof.
  intros A a f; case_eq (length a == 0); intro Heq1.
  unfold afold_right; rewrite Heq1; discriminate.
  intro H; split.
  rewrite eqb_false_spec in Heq1; rewrite <- not_0_ltb; auto.
  generalize H; clear H; case_eq (length a <= 1); intro Heq2.
  unfold afold_right; rewrite Heq1, Heq2; intro H; replace (length a - 1) with 0.
  split; auto; intros i Hi; elim (ltb_0 i); auto.
  rewrite eqb_false_spec in Heq1; apply to_Z_inj; rewrite to_Z_sub_1_diff; auto; rewrite leb_spec in Heq2; change [|1|] with 1%Z in Heq2; assert ([|length a|] <> 0%Z) by (intro H1; apply Heq1, to_Z_inj; auto); generalize (leb_0 (length a)); rewrite leb_spec; change [|0|] with 0%Z; omega.
  pose (P j k := k = false -> (forall i : int, (j <= i) = true -> (i < length a - 1) = true -> f (a .[ i]) = true) /\ f (a .[ length a - 1]) = false); assert (H: P 0 (afold_right bool A true implb f a)).
  generalize (afold_right_Ind _ _ P true implb f a); rewrite Heq2; intro IH; apply IH; clear IH; unfold P.
  intros b i H1 H2 H3; case_eq b; intro Heq3.
  rewrite Heq3 in H3; generalize H3; case (f (a .[ i])); discriminate.
  destruct (H2 Heq3) as [H4 H5]; split; auto; intros j H6 H7; case_eq (i == j); intro Heq4.
  rewrite eqb_spec in Heq4; subst j b; generalize H3; case (f (a .[ i])); auto; discriminate.
  apply H4; auto; rewrite leb_spec in *; rewrite (to_Z_add_1 _ _ H1); rewrite eqb_false_spec in Heq4; assert ([|i|] <> [|j|]) by (intro H; apply Heq4, to_Z_inj; auto); omega.
  intro H; split; auto; intros i H1 H2; elimtype False; rewrite leb_spec in H1; rewrite ltb_spec in H2; omega.
  unfold P in H; intro H1; destruct (H H1) as [H2 H3]; split; auto; intro i; apply H2, leb_0.
Qed.


Lemma afold_right_implb_true_aux : forall A a f,
  (exists i, i < length a - 1 = true /\ f (a.[i]) = false) ->
  afold_right bool A true implb f a = true.
Proof.
  intros A a f; case_eq (length a == 0); intro Heq1.
  intros _; unfold afold_right; rewrite Heq1; auto.
  case_eq (length a <= 1); intro Heq2.
  intros [i [Hi _]]; elim (ltb_0 i); replace 0 with (length a - 1); auto; rewrite eqb_false_spec in Heq1; apply to_Z_inj; rewrite to_Z_sub_1_diff; auto; assert (H1: [|length a|] <> 0%Z) by (intro H; apply Heq1, to_Z_inj; auto); rewrite leb_spec in Heq2; generalize (leb_0 (length a)); rewrite leb_spec; change [|0|] with 0%Z; change [|1|] with 1%Z in Heq2; omega.
  pose (P j k := (exists i : int, (j <= i) = true /\ (i < length a - 1) = true /\ f (a .[ i]) = false) -> k = true); assert (H: P 0 (afold_right bool A true implb f a)).
  generalize (afold_right_Ind _ _ P true implb f a); rewrite Heq2; intro IH; apply IH; clear IH; unfold P.
  intros b i H1 H2 [j [H3 [H4 H5]]]; case_eq (i == j); intro Heq3.
  rewrite eqb_spec in Heq3; subst i; rewrite H5; case b; auto.
  rewrite H2.
  case (f (a .[ i])); auto.
  exists j; repeat split; auto; assert (H: i < j = true).
  rewrite ltb_spec; rewrite leb_spec in H3; rewrite eqb_false_spec in Heq3; assert (H: [|i|] <> [|j|]) by (intro H; apply Heq3, to_Z_inj; auto); omega.
  rewrite leb_spec, (to_Z_add_1 _ _ H); rewrite ltb_spec in H; omega.
  intros [i [H1 [H2 _]]]; elimtype False; rewrite leb_spec in H1; rewrite ltb_spec in H2; omega.
  unfold P in H; intros [i Hi]; apply H; exists i; split; auto; apply leb_0.
Qed.


Lemma afold_right_implb_true : forall A a f,
  length a = 0 \/ (exists i, i < length a - 1 = true /\ f (a.[i]) = false) \/
  (forall i, i < length a = true -> f (a.[i]) = true) ->
  afold_right bool A true implb f a = true.
Proof.
  intros A a f; case_eq (length a == 0).
  intros H _; unfold afold_right; rewrite H; auto.
  intros Heq [H1|[H1|H1]].
  rewrite H1 in Heq; discriminate.
  apply afold_right_implb_true_aux; auto.
  apply afold_right_ind_nonempty.
  intros b i H2 H3; subst b; case (f (a .[ i])); auto.
  apply not_0_ltb; intro H; rewrite H in Heq; discriminate.
  apply H1; rewrite ltb_spec, to_Z_sub_1_diff; [omega| ]; intro H; rewrite H in Heq; discriminate.
Qed.


Lemma afold_right_implb_true_inv : forall A a f,
  afold_right bool A true implb f a = true ->
  length a = 0 \/ (exists i, i < length a - 1 = true /\ f (a.[i]) = false) \/
  (forall i, i < length a = true -> f (a.[i]) = true).
Proof.
  intros A a f; case_eq (length a == 0); intro Heq1.
  intros _; left; rewrite eqb_spec in Heq1; auto.
  case_eq (length a <= 1); intro Heq2.
  unfold afold_right; rewrite Heq1, Heq2; intro H; right; right; intros i Hi; replace i with 0; auto; apply to_Z_inj; rewrite ltb_spec in Hi; rewrite eqb_false_spec in Heq1; assert (H1: [|length a|] <> 0%Z) by (intro H1; apply Heq1, to_Z_inj; auto); rewrite leb_spec in Heq2; change [|1|] with 1%Z in Heq2; generalize (leb_0 (length a)) (leb_0 i); rewrite !leb_spec; change [|0|] with 0%Z;  omega.
  pose (P j k := k = true -> (exists i : int, (j <= i) = true /\ (i < length a - 1) = true /\ f (a .[ i]) = false) \/ (forall i : int, (j <= i) = true -> (i < length a) = true -> f (a .[ i]) = true)); assert (H: P 0 (afold_right bool A true implb f a)).
  generalize (afold_right_Ind _ _ P true implb f a); rewrite Heq2; intro IH; apply IH; clear IH; unfold P.
  intros b i H1 H2 H3; case_eq b; intro Heq3.
  destruct (H2 Heq3) as [[j [H4 [H5 H6]]]|H4].
  left; exists j; repeat split; auto; rewrite leb_spec in *; rewrite (to_Z_add_1 _ _ H1) in H4; omega.
  case_eq (f (a.[i])); intro Heq4.
  right; intros j H5 H6; case_eq (i == j); intro Heq5.
  rewrite eqb_spec in Heq5; subst j; auto.
  apply H4; auto; rewrite leb_spec in *; rewrite (to_Z_add_1 _ _ H1); rewrite eqb_false_spec in Heq5; assert ([|i|] <> [|j|]) by (intro H; apply Heq5, to_Z_inj; auto); omega.
  left; exists i; repeat split; auto; apply leb_refl.
  rewrite Heq3 in H3; case_eq (f (a .[ i])); intro Heq4; rewrite Heq4 in H3; try discriminate; left; exists i; repeat split; auto; apply leb_refl.
  intros H1; right; intros i H2 H3; replace i with (length a - 1); auto; apply to_Z_inj; rewrite leb_spec in H2; rewrite (to_Z_sub_1 _ _ H3) in *; rewrite ltb_spec in H3; omega.
  unfold P in H; intro H1; right; destruct (H H1) as [[i [_ H2]]|H2].
  left; exists i; auto.
  right; intro i; apply H2, leb_0.
Qed.


(* Other cases *)

Lemma afold_left_length_2 : forall A B default OP F t,
  (length t == 2) = true ->
  afold_left A B default OP F t = OP (F (t.[0])) (F (t.[1])).
Proof.
  intros A B default OP F t H; unfold afold_left; rewrite eqb_spec in H; rewrite H; change (2 == 0) with false; simpl; change (2-1) with 1; rewrite foldi_eq; trivial.
Qed.


Lemma afold_right_length_2 : forall A B default OP F t,
  (length t == 2) = true ->
  afold_right A B default OP F t = OP (F (t.[0])) (F (t.[1])).
Proof.
  intros A B default OP F t H; unfold afold_right; rewrite eqb_spec in H; rewrite H; change (2 == 0) with false; simpl; change (2<=1) with false; simpl; change (2-2) with 0; rewrite foldi_down_eq; trivial.
Qed.


Ltac tac_left :=
  intros t f H H1 H2; rewrite afold_left_length_2;
    [rewrite H1, H2| ]; trivial.


Ltac tac_right :=
  try (intros t f H H1 H2; rewrite afold_right_length_2;
    [rewrite H1, H2| ]; trivial);
  try (intros t f H H1; rewrite afold_right_length_2;
    [rewrite H1| ]; trivial);
  try (rewrite implb_true_r; trivial).


Lemma afold_left_xorb_false1 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = false -> f (t .[ 1]) = false ->
  afold_left bool int false xorb f t = false.
Proof. tac_left. Qed.


Lemma afold_left_xorb_false2 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = true -> f (t .[ 1]) = true ->
  afold_left bool int false xorb f t = false.
Proof. tac_left. Qed.


Lemma afold_left_xorb_true1 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = false -> f (t .[ 1]) = true ->
  afold_left bool int false xorb f t = true.
Proof. tac_left. Qed.


Lemma afold_left_xorb_true2 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = true -> f (t .[ 1]) = false ->
  afold_left bool int false xorb f t = true.
Proof. tac_left. Qed.


(* Lemma afold_right_implb_false : forall t f, *)
(*   (PArray.length t == 2) = true -> *)
(*   f (t .[ 0]) = true -> f (t .[ 1]) = false -> *)
(*   afold_right bool int true implb f t = false. *)
(* Proof. tac_right. Qed. *)


(* Lemma afold_right_implb_true1 : forall t f, *)
(*   (PArray.length t == 2) = true -> *)
(*   f (t .[ 0]) = false -> *)
(*   afold_right bool int true implb f t = true. *)
(* Proof. tac_right. Qed. *)


(* Lemma afold_right_implb_true2 : forall t f, *)
(*   (PArray.length t == 2) = true -> *)
(*   f (t.[1]) = true -> *)
(*   afold_right bool int true implb f t = true. *)
(* Proof. tac_right. Qed. *)


Lemma afold_left_eqb_false1 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = false -> f (t .[ 1]) = true ->
  afold_left bool int true eqb f t = false.
Proof. tac_left. Qed.


Lemma afold_left_eqb_false2 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = true -> f (t .[ 1]) = false ->
  afold_left bool int true eqb f t = false.
Proof. tac_left. Qed.


Lemma afold_left_eqb_true1 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = true -> f (t .[ 1]) = true ->
  afold_left bool int true eqb f t = true.
Proof. tac_left. Qed.


Lemma afold_left_eqb_true2 : forall t f,
  (PArray.length t == 2) = true ->
  f (t .[ 0]) = false -> f (t .[ 1]) = false ->
  afold_left bool int true eqb f t = true.
Proof. tac_left. Qed.


(** Two elements in a list *)

Section List2.

  Variable A : Type.

  Inductive In2 (i j : A) : list A -> Prop :=
  | In2_hd : forall l, In j l -> In2 i j (i::l)
  | In2_tl : forall k l, In2 i j l -> In2 i j (k::l).

  Local Hint Constructors In2.


  Lemma In2_app : forall i j l m, In2 i j (l ++ m) <->
    In2 i j l \/ (In i l /\ In j m) \/ In2 i j m.
  Proof.
    intros i j; induction l as [ |t l IHl]; simpl; intro m; split; auto.
    intros [H|[[H _]|H]]; auto.
    inversion H.
    elim H.
    intro H; inversion H; clear H.
    subst i l0; rewrite in_app_iff in H1; destruct H1 as [H1|H1]; auto.
    subst k l0; rewrite IHl in H1; destruct H1 as [H1|[[H1 H2]|H1]]; auto.
    intros [H|[[[H|H] H1]|H]].
    inversion H; clear H.
    subst i l0; constructor 1; rewrite in_app_iff; auto.
    subst k l0; constructor 2; rewrite IHl; left; auto.
    subst t; constructor 1; rewrite in_app_iff; auto.
    constructor 2; rewrite IHl; right; left; auto.
    constructor 2; rewrite IHl; right; right; auto.
  Qed.


  Fixpoint rev_aux acc (l:list A) :=
    match l with
      | nil => acc
      | t::q => rev_aux (t::acc) q
    end.


  Lemma In2_rev_aux : forall i j l acc, In2 i j (rev_aux acc l) <->
    In2 i j acc \/ (In i l /\ In j acc) \/ In2 j i l.
  Proof.
    intros i j; induction l as [ |t q IHq]; simpl; intro acc; split; auto.
    intros [H|[[H _]|H]]; auto.
    elim H.
    inversion H.
    rewrite IHq; clear IHq; intros [H|[[H1 H2]|H]]; auto.
    inversion H; auto.
    inversion H2; auto; clear H2; subst t; right; right; auto.
    intros [H|[[[H1|H1] H2]|H]]; rewrite IHq; clear IHq; auto.
    subst t; auto.
    right; left; split; auto; constructor 2; auto.
    inversion H; clear H; auto; subst j l; right; left; split; auto; constructor 1; auto.
  Qed.


  Definition rev := rev_aux nil.


  Lemma In2_rev : forall i j l, In2 i j (rev l) <-> In2 j i l.
  Proof.
    intros i j l; unfold rev; rewrite In2_rev_aux; split; auto; intros [H|[[_ H]|H]]; auto; inversion H.
  Qed.


  Lemma In2_In : forall i j, i <> j -> forall l, (In i l /\ In j l) <-> (In2 i j l \/ In2 j i l).
  Proof.
    intros i j H l; split.
    intros [H1 H2]; generalize H1 H2; clear H1 H2; induction l as [ |t q IHq].
    intro H1; inversion H1.
    intros H1 H2; inversion H1; clear H1.
    subst t; inversion H2; auto; elim H; auto.
    inversion H2; clear H2.
    subst t; auto.
    destruct (IHq H0 H1) as [H2|H2]; auto.
    intros [H1|H1]; induction H1 as [H1|t q H1 [IH1 IH2]].
    split; [constructor 1|constructor 2]; auto.
    split; constructor 2; auto.
    split; [constructor 2|constructor 1]; auto.
    split; constructor 2; auto.
  Qed.

End List2.

Arguments In2 [A] i j _.
Arguments rev [A] l.
Arguments In2_In [A i j] _ l.


(** List of distinct elements *)

Section Distinct.

  Variable A : Type.
  Variable eq : A -> A -> bool.

  Fixpoint distinct_aux2 acc ref l :=
    match l with
      | nil => acc
      | t::q => distinct_aux2 (acc && (negb (eq ref t))) ref q
    end.

  Lemma distinct_aux2_spec : forall ref l acc, distinct_aux2 acc ref l = true
    <->
    acc = true /\ (forall i, In i l -> eq ref i = false).
  Proof.
    intro ref; induction l as [ |t q IHq]; simpl.
    intro acc; split.
    intro H; split; auto; intros i H1; elim H1.
    intros [H _]; auto.
    intro acc; rewrite (IHq (acc && negb (eq ref t))); split.
    rewrite andb_true_iff; intros [[H1 H2] H3]; split; auto; intros i [Hi|Hi]; auto; subst i; generalize H2; case (eq ref t); auto; discriminate.
    intros [H1 H2]; rewrite andb_true_iff; repeat split; auto; rewrite (H2 t); auto.
  Qed.

  Lemma distinct_aux2_spec_neg : forall ref l acc,
    distinct_aux2 acc ref l = false <->
    acc = false \/ (exists i, In i l /\ eq ref i = true).
  Proof.
    intro ref; induction l as [ |t q IHq]; simpl.
    intro acc; split; auto; intros [H|[i [H _]]]; auto; elim H.
    intro acc; rewrite (IHq (acc && negb (eq ref t))); rewrite andb_false_iff;split.
    intros [[H|H]|[i [H1 H2]]]; auto.
    right; exists t; split; auto; generalize H; case (eq ref t); auto.
    right; exists i; split; auto.
    intros [H|[i [[H1|H1] H2]]]; auto.
    subst t; left; right; generalize H2; case (eq ref i); auto.
    right; exists i; auto.
  Qed.

  Fixpoint distinct_aux acc l :=
    match l with
      | nil => acc
      | t::q =>
        let acc' := distinct_aux2 acc t q in
        distinct_aux acc' q
    end.

  Local Hint Constructors In2.

  Lemma distinct_aux_spec : forall l acc, distinct_aux acc l = true <->
    acc = true /\ (forall i j, In2 i j l -> eq i j = false).
  Proof.
    induction l as [ |t q IHq]; simpl.
    intro acc; split.
    intro H; split; auto; intros i j H1; inversion H1.
    intros [H _]; auto.
    intro acc; rewrite (IHq (distinct_aux2 acc t q)), distinct_aux2_spec; split.
    intros [[H1 H2] H3]; split; auto; intros i j H; inversion H; auto.
    intros [H1 H2]; repeat split; auto.
  Qed.

  Lemma distinct_aux_spec_neg : forall l acc, distinct_aux acc l = false <->
    acc = false \/ (exists i j, In2 i j l /\ eq i j = true).
  Proof.
    induction l as [ |t q IHq]; simpl.
    intro acc; split; auto; intros [H|[i [j [H _]]]]; auto; inversion H.
    intro acc; rewrite (IHq (distinct_aux2 acc t q)), distinct_aux2_spec_neg; split.
    intros [[H|[i [H1 H2]]]|[i [j [H1 H2]]]]; auto.
    right; exists t; exists i; auto.
    right; exists i; exists j; auto.
    intros [H|[i [j [H1 H2]]]]; auto; inversion H1; clear H1.
    subst i l; left; right; exists j; auto.
    subst k l; right; exists i; exists j; auto.
  Qed.

  Definition distinct := distinct_aux true.

  Lemma distinct_spec : forall l, distinct l = true <->
    (forall i j, In2 i j l -> eq i j = false).
  Proof.
    unfold distinct; intro l; rewrite distinct_aux_spec; split; auto; intros [_ H]; auto.
  Qed.

  Lemma distinct_false_spec : forall l, distinct l = false <->
    (exists i j, In2 i j l /\ eq i j = true).
  Proof.
    unfold distinct; intro l; rewrite distinct_aux_spec_neg; split; auto; intros [H|H]; auto; discriminate.
  Qed.

End Distinct.

Arguments distinct [A] eq l.


(** Specification of existsb *)

Lemma existsb_false_spec : forall f from to,
  existsb f from to = false <->
  forall i, ((from <= i) = true /\ (i <= to) = true) -> f i = false.
Proof.
  unfold existsb;intros; setoid_rewrite leb_spec; apply foldi_cont_ZInd.
  intros z Hz; split; auto; intros _ i [H1 H2]; assert (H3 := Z.le_trans _ _ _ H1 H2); elimtype False; omega.
  intros i cont H1 H2 H3; case_eq (f i); intro Heq.
  split; try discriminate; intro H; rewrite <- Heq; apply H; split; try omega; rewrite leb_spec in H2; auto.
  rewrite H3; split; intros H j [Hj1 Hj2].
  case_eq (i == j); intro Heq2.
  rewrite eqb_spec in Heq2; subst j; auto.
  apply H; split; auto; rewrite eqb_false_spec in Heq2; assert ([|i|] <> [|j|]) by (intro; apply Heq2, to_Z_inj; auto); omega.
  apply H; omega.
Qed.


Lemma array_existsbi_false_spec : forall A (f : int -> A -> bool) t,
  existsbi f t = false <->
  forall i, i < length t = true -> f i (t.[i]) = false.
Proof.
  unfold existsbi;intros A f t; destruct (reflect_eqb 0 (length t)).
  split; auto. intros _ i Hi. elim (ltb_0 i). rewrite e. auto.
  rewrite existsb_false_spec. split.
  intros H i Hi. apply H. split; [apply leb_0| ]. rewrite leb_spec. rewrite (to_Z_sub_1 _ _ Hi). rewrite ltb_spec in Hi. omega.
  intros H i [_ Hi]. apply H. rewrite ltb_spec. rewrite leb_spec in Hi. rewrite to_Z_sub_1_diff in Hi; auto; omega.
Qed.


Lemma array_existsb_false_spec : forall A (f : A -> bool) t,
  PArray.existsb f t = false <->
  forall i, i < length t = true -> f (t.[i]) = false.
Proof.
  intros A f t; unfold PArray.existsb; case_eq (0 == length t).
  rewrite eqb_spec; intro H; split; auto; intros _ i Hi; elim (ltb_0 i); rewrite H; auto.
  intro H; rewrite existsb_false_spec; split.
  intros H1 i Hi; apply H1; split; [apply leb_0| ]; rewrite leb_spec, (to_Z_sub_1 _ _ Hi); rewrite ltb_spec in Hi; omega.
  intros H1 i [_ H2]; apply H1; rewrite ltb_spec; rewrite leb_spec in H2; rewrite to_Z_sub_1_diff in H2; [omega| ]; intro H3; rewrite H3 in H; discriminate.
Qed.


(** Forall of two lists at the same time *)

Section Forall2.

  Variables (A B:Type) (f:A->B->bool).

  Fixpoint forallb2 l1 l2 :=
    match l1, l2 with
      | nil, nil => true
      | a::l1, b::l2 => f a b && forallb2 l1 l2
      | _, _ => false
    end.

End Forall2.

Implicit Arguments forallb2 [A B].


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


Require Import Bool List PArray Int63 Ring63 ZArith Psatz.
Local Open Scope int63_scope.
Local Open Scope array_scope.

Global Notation "[| x |]" := (φ x).


(** Lemmas about Bool *)

Lemma implb_true_r : forall a, implb a true = true.
Proof. intros [ | ]; reflexivity. Qed.


(** Lemmas about Int63 *)

Lemma reflect_eqb : forall i j, reflect (i = j)%Z (i == j).
Proof.
 intros; apply iff_reflect.
 symmetry;apply eqb_spec.
Qed.

Lemma to_Z_eq : forall x y, [|x|] = [|y|] <-> x = y.
Proof.
 split;intros;subst;trivial.
 apply to_Z_inj;trivial.
Qed.

Lemma max_int_wB : [|max_int|] = (wB - 1)%Z.
Proof.
 reflexivity.
Qed.

Lemma le_eq : forall i j,
  (j <= i) = true -> (j + 1 <= i) = false -> i = j.
Proof.
  intros i j; rewrite leb_spec; destruct (dec_Zle [|j+1|] [|i|]) as [H|H].
  rewrite <- leb_spec in H; rewrite H; discriminate.
  intros H1 _; apply to_Z_inj; rewrite add_spec, to_Z_1 in H.
  assert (H2: (([|j|] + 1)%Z < wB)%Z \/ ([|j|] + 1)%Z = wB).
  pose (H3 := to_Z_bounded j); lia.
  destruct H2 as [H2|H2].
  rewrite Z.mod_small in H.
  lia.
  split.
  pose (H3 := to_Z_bounded j); lia.
  assumption.
  rewrite H2, Z_mod_same_full in H; elim H; destruct (to_Z_bounded i) as [H3 _]; assumption.
Qed.

Lemma leb_0 : forall x, 0 <= x = true.
Proof.
 intros x;rewrite leb_spec;destruct (to_Z_bounded x);trivial.
Qed.

Lemma leb_refl : forall n, n <= n = true.
Proof.
 intros n;rewrite leb_spec;apply Z.le_refl.
Qed.

Lemma lt_eq : forall i j,
  (i < j + 1) = true -> (i < j) = false -> i = j.
Proof.
  intros i j. rewrite ltb_spec. destruct (dec_Zlt [|i|] [|j|]) as [H|H].
  rewrite <- ltb_spec in H; rewrite H; discriminate.
  intros H1 _; apply to_Z_inj. rewrite add_spec in H1. rewrite to_Z_1 in H1.
  assert (H2: (([|j|] + 1)%Z < wB)%Z \/ ([|j|] + 1)%Z = wB).
  pose (H3 := to_Z_bounded j); lia.
  destruct H2 as [H2|H2].
  rewrite Z.mod_small in H1.
  lia.
  split.
  pose (H3 := to_Z_bounded j); lia.
  assumption.
  rewrite H2, Z_mod_same_full in H1; elimtype False. destruct (to_Z_bounded i) as [H3 _]. lia.
Qed.

Lemma not_0_ltb : forall x, x <> 0 <-> 0 < x = true.
Proof.
 intros x;rewrite ltb_spec, to_Z_0;assert (W:=to_Z_bounded x);split.
 intros Hd;assert ([|x|] <> 0)%Z;[ | omega].
   intros Heq;elim Hd;apply to_Z_inj;trivial.
 intros Hlt Heq;elimtype False.
 assert ([|x|] = 0)%Z;[ rewrite Heq, to_Z_0;trivial | omega].
Qed.

Lemma ltb_0 : forall x, ~ (x < 0 = true).
Proof.
 intros x;rewrite ltb_spec, to_Z_0;destruct (to_Z_bounded x);omega.
Qed.

Lemma not_ltb_refl : forall i, ~(i < i = true).
Proof.
 intros;rewrite ltb_spec;omega.
Qed.

Lemma ltb_trans : forall x y z, x < y = true ->  y < z = true -> x < z = true.
Proof.
 intros x y z;rewrite !ltb_spec;apply Z.lt_trans.
Qed.

Lemma leb_ltb_eqb : forall x y, ((x <= y) = (x < y) || (x == y)).
Proof.
 intros.
 apply eq_true_iff_eq.
 rewrite leb_spec, orb_true_iff, ltb_spec, eqb_spec, <- to_Z_eq;omega.
Qed.

Lemma leb_ltb_trans : forall x y z, x <= y = true ->  y < z = true -> x < z = true.
Proof.
 intros x y z;rewrite leb_spec, !ltb_spec;apply Z.le_lt_trans.
Qed.

Lemma to_Z_add_1 : forall x y, x < y = true -> [|x+1|] = ([|x|] + 1)%Z.
Proof.
  intros x y;assert (W:= to_Z_bounded x);assert (W0:= to_Z_bounded y);
   rewrite ltb_spec;intros;rewrite add_spec, to_Z_1, Z.mod_small;omega.
Qed.

Lemma to_Z_add_1_wB : forall x, ([|x|] < wB - 1)%Z -> [|x + 1|] = ([|x|] + 1)%Z.
Proof.
  intros; assert (Bx := to_Z_bounded x); rewrite add_spec, to_Z_1, Z.mod_small; lia.
Qed.

Lemma leb_not_gtb : forall n m, m <= n = true -> ~(n < m = true).
Proof.
 intros n m; rewrite ltb_spec, leb_spec;omega.
Qed.

Lemma leb_negb_gtb : forall x y, x <= y = negb (y < x).
Proof.
 intros x y;apply Bool.eq_true_iff_eq;split;intros.
 apply Bool.eq_true_not_negb;apply leb_not_gtb;trivial.
 rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false in H.
 rewrite leb_spec; rewrite ltb_spec in H;omega.
Qed.

Lemma ltb_negb_geb : forall x y, x < y = negb (y <= x).
Proof.
 intros;rewrite leb_negb_gtb, Bool.negb_involutive;trivial.
Qed.

Lemma to_Z_sub_gt : forall x y, y <= x = true -> [|x - y|] = ([|x|] - [|y|])%Z.
Proof.
 intros x y;assert (W:= to_Z_bounded x);assert (W0:= to_Z_bounded y);
   rewrite leb_spec;intros;rewrite sub_spec, Zmod_small;omega.
Qed.

Lemma to_Z_sub_1 : forall x y, y < x = true -> ([| x - 1|] = [|x|] - 1)%Z.
Proof.
 intros;apply to_Z_sub_gt.
 generalize (leb_ltb_trans _ _ _ (leb_0 y) H).
 rewrite ltb_spec, leb_spec, to_Z_0, to_Z_1;auto with zarith.
Qed.

Lemma to_Z_sub_1_diff : forall x, x <> 0 -> ([| x - 1|] = [|x|] - 1)%Z.
Proof.
  intros x;rewrite not_0_ltb;apply to_Z_sub_1.
Qed.

Lemma to_Z_sub_1_0 : forall x, (0 < [|x|])%Z -> [|x - 1|] = ([|x|] - 1)%Z.
Proof.
 intros; apply (to_Z_sub_1 _ 0); rewrite ltb_spec; assumption.
Qed.

Lemma ltb_leb_sub1 : forall x i,  x <> 0 -> (i < x = true <-> i <= x - 1 = true).
Proof.
 intros x i Hdiff.
 rewrite ltb_spec, leb_spec, to_Z_sub_1_diff;trivial.
 split;auto with zarith.
Qed.

Lemma minus_1_lt i : (i == 0) = false -> i - 1 < i = true.
Proof.
  intro Hl. rewrite ltb_spec, (to_Z_sub_1 _ 0).
  - lia.
  - rewrite ltb_spec. rewrite eqb_false_spec in Hl.
    assert (0%Z <> [|i|])
      by (change 0%Z with [|0|]; intro H; apply to_Z_inj in H; auto).
    destruct (to_Z_bounded i) as [H1 _].
    clear -H H1. change [|0|] with 0%Z. lia.
Qed.

Lemma lsr0_l i: 0 >> i = 0.
Proof.
 apply to_Z_inj.
 generalize (lsr_spec 0 i).
 rewrite to_Z_0, Zdiv_0_l; auto.
Qed.

Lemma lxor_lsr i1 i2 i: (i1 lxor i2) >> i = (i1 >> i) lxor (i2 >> i).
Proof.
 apply bit_ext; intros n.
 rewrite lxor_spec, !bit_lsr, lxor_spec.
 case (_ <= _); auto.
Qed.

Lemma bit_or_split i : i = (i>>1)<<1 lor bit i 0.
Proof.
 apply bit_ext.
 intros n; rewrite lor_spec.
 rewrite bit_lsl, bit_lsr, bit_b2i.
 case (to_Z_bounded n); intros Hi _.
 case (Zle_lt_or_eq _ _ Hi).
 2: replace 0%Z with [|0|]; auto; rewrite to_Z_eq.
 2: intros H; rewrite <-H.
 2: replace (0 < 1) with true; auto.
 intros H; clear Hi.
 case_eq (n == 0).
 rewrite eqb_spec; intros H1; generalize H; rewrite H1; discriminate.
 intros _; rewrite orb_false_r.
 case_eq (n < 1).
 rewrite ltb_spec, to_Z_1; intros HH; contradict HH; auto with zarith.
 intros _.
 generalize (@bit_M i n); case (_ <= _).
 intros H1; rewrite H1; auto.
 intros _.
 case (to_Z_bounded n); intros H1n H2n.
 assert (F1: [|n - 1|] = ([|n|] - 1)%Z).
 rewrite sub_spec, Zmod_small; rewrite to_Z_1; auto with zarith.
 generalize (add_le_r 1 (n - 1)); case (_ <= _); rewrite F1, to_Z_1; intros HH.
 replace (1 + (n -1)) with n. change (bit i n = bit i n). reflexivity.
 apply to_Z_inj; rewrite add_spec, F1, Zmod_small; rewrite to_Z_1;
  auto with zarith.
 rewrite bit_M; auto; rewrite leb_spec.
 replace [|n|] with wB; try discriminate; auto with zarith.
Qed.

Lemma lsr_is_even_eq : forall i j,
  i >> 1 = j >> 1 ->
  is_even i = is_even j ->
  i = j.
Proof.
 intros;apply bit_ext.
 intros n;destruct (reflect_eqb n 0).
 rewrite <- (negb_involutive (bit i n)), <- (negb_involutive (bit j n)).
 rewrite e, <- !is_even_bit, H0;trivial.
 assert (W1 : [|n|] <> 0%Z) by (intros Heq;apply n0;apply to_Z_inj;trivial).
 assert (W2 := to_Z_bounded n);clear n0.
 assert (W3 : [|n-1|] = ([|n|] - 1)%Z).
   rewrite sub_spec, to_Z_1, Zmod_small;trivial;omega.
 assert (H1 : n = (n-1)+1).
   apply to_Z_inj;rewrite add_spec, W3.
   rewrite Zmod_small;rewrite to_Z_1; omega.
 case_eq ((n-1) < digits); intro l.
  rewrite ltb_spec in l.
  rewrite H1, <- !bit_half, H; trivial; rewrite ltb_spec; trivial.
 assert ((digits <= n) = true).
  rewrite <- Bool.not_true_iff_false, ltb_spec in l; rewrite leb_spec;omega.
 rewrite !bit_M;trivial.
Qed.

Lemma lsr1_bit : forall i k, bit i k >> 1 = 0.
Proof.
 intros;destruct (bit i k);trivial.
Qed.

Lemma is_even_or i j : is_even (i lor j) = is_even i && is_even j.
Proof.
 rewrite !is_even_bit, lor_spec; case bit; auto.
Qed.

Lemma is_even_xor i j : is_even (i lxor j) = negb (xorb (is_even i) (is_even j)).
Proof.
 rewrite !is_even_bit, lxor_spec; do 2 case bit; auto.
Qed.

Lemma bit_xor_split: forall i : int, i = (i >> 1) << 1 lxor bit i 0.
Proof.
 intros.
 rewrite bit_or_split at 1.
 apply lsr_is_even_eq.
 rewrite lxor_lsr, lor_lsr, lsr1_bit, lxor0_r, lor0_r;trivial.
 rewrite is_even_or, is_even_xor.
 rewrite is_even_lsl_1;trivial.
 rewrite (xorb_true_l (is_even (bit i 0))), negb_involutive;trivial.
Qed.

Lemma lxor_nilpotent: forall i, i lxor i = 0.
Proof.
 intros;apply bit_ext;intros.
 rewrite lxor_spec, xorb_nilpotent, bit_0;trivial.
Qed.

Lemma int_ind : forall (P : int -> Prop),
  P 0 ->
  (forall i, (i < max_int) = true -> P i -> P (i + 1)) ->
  forall i, P i.
Proof.
 intros P HP0 Hrec i.
 assert (Bi := to_Z_bounded i).
 destruct Bi as [ Bi0 Bi ].
 rewrite <- of_to_Z.
 rewrite Z2Nat.inj_lt in Bi; [ | exact Bi0 | lia ]; clear Bi0.
 rewrite <- (Z2Nat.id (to_Z i)); [ | apply to_Z_bounded ].
 revert Bi.
 induction (Z.to_nat (to_Z i)); clear i.
 intro; apply HP0.
 rewrite Nat2Z.inj_lt.
 rewrite Z2Nat.id; [ | generalize wB_pos; clear IHn; lia ].
 rewrite Nat2Z.inj_succ.
 rewrite <- Z.add_1_r.
 rewrite <- (Nat2Z.id n) in IHn at 1.
 rewrite <- Z2Nat.inj_lt in IHn; [ | clear IHn; lia | clear IHn; generalize wB_pos; lia ].
 generalize (Z.of_nat n) IHn (Nat2Z.is_nonneg n); clear n IHn; intros z IHz Hz1 Hz2.
 replace (of_Z (z + 1)) with (of_Z z + 1).
 apply Hrec.
 apply ltb_spec.
 rewrite of_Z_spec, Z.mod_small, max_int_wB; lia.
 apply IHz; lia.
 apply to_Z_inj.
 rewrite of_Z_spec, Z.mod_small by lia.
 rewrite to_Z_add_1_wB, of_Z_spec.
 rewrite Z.mod_small; lia.
 rewrite of_Z_spec, Z.mod_small; lia.
Qed.

Lemma int_ind_bounded : forall (P : int -> Prop) min max,
  min <= max = true ->
  P min ->
  (forall i, min <= i = true -> i < max = true -> P i -> P (i + 1)) ->
  P max.
Proof.
 intros P min max Hle Hmin Hrec.
 rewrite leb_spec in Hle.
 assert (Bmin := to_Z_bounded min);assert (Bmax := to_Z_bounded max).
 replace max with (min + (max - min)) by ring.
 generalize (leb_refl (max - min)).
 pattern (max - min) at 1 3.
 apply int_ind.
 intros _; replace (min + 0) with min by ring; exact Hmin.
 intros i Hi1 IH; revert Hi1.
 rewrite ltb_spec, leb_spec.
 assert (Bi := to_Z_bounded i).
 rewrite max_int_wB; intro Hi1.
 replace (min + (i + 1)) with (min + i + 1) by ring.
 rewrite to_Z_add_1_wB, sub_spec, Z.mod_small by lia.
 intro Hi2; apply Hrec.
 rewrite leb_spec, add_spec, Z.mod_small; lia.
 rewrite ltb_spec, add_spec, Z.mod_small; lia.
 apply IH.
 rewrite leb_spec, sub_spec, Z.mod_small; lia.
Qed.

Definition foldi {A : Type} (f : int -> A -> A) (from to : int) (a : A) : A :=
  let fix foldi_rec (n : nat) (a : A) : A :=
    match n with
      | O => a
      | S m => foldi_rec m (f (to - of_Z (Z.of_nat n)) a)
    end in
  foldi_rec (Z.to_nat (to_Z to) - Z.to_nat (to_Z from))%nat a.

Lemma foldi_ge : forall A f from to (a:A),
  to <= from = true -> foldi f from to a = a.
Proof.
 intros A f from to a; unfold foldi.
 assert (Bfrom := to_Z_bounded from); assert (Bto := to_Z_bounded to).
 rewrite leb_spec, Z2Nat.inj_le by lia; intro Hle.
 replace (_ - _)%nat with O by lia; tauto.
Qed.

Lemma foldi_lt_l : forall A f from to (a:A),
  from < to = true -> foldi f from to a = foldi f (from + 1) to (f from a).
Proof.
 intros A f from to a; rewrite ltb_spec; intro Hlt; unfold foldi.
 assert (Bfrom := to_Z_bounded from); assert (Bto := to_Z_bounded to).
 rewrite <- Nat.sub_succ.
 rewrite Nat.sub_succ_l by (rewrite Nat.le_succ_l, <- Z2Nat.inj_lt; lia); f_equal.
 rewrite to_Z_add_1_wB, Z.add_1_r, Z2Nat.inj_succ by lia; reflexivity.
 f_equal.
 rewrite <- Nat.sub_succ_l by (rewrite Nat.le_succ_l, <- Z2Nat.inj_lt; lia).
 rewrite Nat.sub_succ, <- Z2Nat.inj_sub, Z2Nat.id by lia.
 apply to_Z_inj; rewrite sub_spec, of_Z_spec, <- 2!sub_spec; f_equal; ring.
Qed.

Lemma foldi_lt_r : forall A f from to (a:A),
  from < to = true -> foldi f from to a = f (to - 1) (foldi f from (to - 1) a).
Proof.
 intros A f from to a; rewrite ltb_spec; intro Hlt.
 assert (Bfrom := to_Z_bounded from); assert (Bto := to_Z_bounded to).
 replace from with (max_int - (max_int - from)) by ring.
 revert a; pattern (max_int - from).
 apply (int_ind_bounded _ (max_int - (to - 1))).
 rewrite leb_spec, sub_spec, to_Z_sub_1_0, sub_spec, max_int_wB, 2!Z.mod_small by lia; lia.
 intro a; replace (max_int - (max_int - (to - 1))) with (to - 1) by ring.
 rewrite foldi_lt_l by (rewrite ltb_spec, to_Z_sub_1_0; lia).
 ring_simplify (to - 1 + 1).
 rewrite 2!foldi_ge by (rewrite leb_spec; lia); reflexivity.
 intro i; rewrite leb_spec, ltb_spec, sub_spec, to_Z_sub_1_0, sub_spec, max_int_wB, 2!Z.mod_small by lia.
 intros Hi1 Hi2 IH a.
 rewrite foldi_lt_l by (rewrite ltb_spec, sub_spec, to_Z_add_1_wB, max_int_wB, Z.mod_small by lia; lia).
 rewrite (foldi_lt_l _ _ (max_int - (i + 1))) by (rewrite ltb_spec, sub_spec, to_Z_add_1_wB, to_Z_sub_1_0, max_int_wB, Z.mod_small by lia; lia).
 replace (max_int - (i + 1) + 1) with (max_int - i) by ring.
 apply IH.
Qed.

Lemma foldi_ind : forall A (P : int -> A -> Prop) f from to a,
  from <= to = true -> P from a ->
  (forall i a, from <= i = true -> i < to = true -> P i a -> P (i + 1) (f i a)) ->
  P to (foldi f from to a).
Proof.
  intros A P f from to a Hle Hfrom IH.
  assert (Bfrom := to_Z_bounded from); assert (Bto := to_Z_bounded to).
  pattern to; apply (int_ind_bounded _ from).
  exact Hle.
  rewrite foldi_ge by (rewrite leb_spec; lia).
  exact Hfrom.
  intro i; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, ltb_spec; intros Hi1 Hi2; rewrite (foldi_lt_r _ _ _ (i + 1)) by (rewrite ltb_spec, to_Z_add_1_wB; lia).
  ring_simplify (i + 1 - 1); apply IH; [ rewrite leb_spec; exact Hi1 | rewrite ltb_spec; exact Hi2 ].
Qed.

Lemma foldi_ind2 : forall A B (P : int -> A -> B -> Prop) f1 f2 from to a1 a2,
  from <= to = true -> P from a1 a2 ->
  (forall i a1 a2, from <= i = true -> i < to = true -> P i a1 a2 -> P (i + 1) (f1 i a1) (f2 i a2)) ->
  P to (foldi f1 from to a1) (foldi f2 from to a2).
Proof.
  intros A B P f1 f2 from to a1 a2 Hle Hfrom IH.
  assert (Bfrom := to_Z_bounded from); assert (Bto := to_Z_bounded to).
  pattern to; apply (int_ind_bounded _ from).
  exact Hle.
  rewrite 2!foldi_ge by (rewrite leb_spec; lia).
  exact Hfrom.
  intro i; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, ltb_spec; intros Hi1 Hi2; rewrite 2!(foldi_lt_r _ _ _ (i + 1)) by (rewrite ltb_spec, to_Z_add_1_wB; lia).
  ring_simplify (i + 1 - 1); apply IH; [ rewrite leb_spec; exact Hi1 | rewrite ltb_spec; exact Hi2 ].
Qed.

Lemma foldi_eq_compat : forall A (f1 f2:int -> A -> A) min max a,
  (forall i a, min <= i = true -> i < max = true -> f1 i a = f2 i a) ->
  foldi f1 min max a = foldi f2 min max a.
Proof.
 intros A f1 f2 min max a Hf.
 assert (Bmin := to_Z_bounded min); assert (Bmax := to_Z_bounded max).
 case (Z.lt_ge_cases [|min|] [|max|]); [ intro Hlt | intro Hle ].
 apply (foldi_ind2 _ _ (fun _ a b => a = b)); [ rewrite leb_spec; lia | reflexivity | ].
 intros i a1 a2 Hi1 Hi2 Heq; rewrite Heq; apply Hf; assumption.
 rewrite 2!foldi_ge by (rewrite leb_spec; lia); reflexivity.
Qed.

(** Lemmas about to_list *)

Definition to_list {A : Type} (t : array A) :=
  List.rev (foldi (fun i l => t.[i] :: l)%list 0 (length t) nil).

Lemma foldi_to_list : forall A B (f : A -> B -> A) a e,
 foldi (fun i x => f x (a.[i])) 0 (length a) e = fold_left f (to_list a) e.
Proof.
  intros A B f a e; unfold to_list.
  rewrite <- fold_left_rev_right, rev_involutive.
  apply (foldi_ind2 _ _ (fun _ a b => a = fold_right (fun y x => f x y) e b)).
  apply leb_0.
  reflexivity.
  intros i x l _ Hi IH.
  simpl; f_equal; exact IH.
Qed.

Lemma to_list_In : forall {A} (t: array A) i,
  i < length t = true -> In (t.[i]) (to_list t).
  intros A t i; assert (Bt := to_Z_bounded (length t)); assert (Bi := to_Z_bounded i); rewrite ltb_spec; unfold to_list.
  rewrite <- in_rev.
  apply foldi_ind.
  rewrite leb_spec, to_Z_0; lia.
  rewrite to_Z_0; lia.
  intros j l _; assert (Bj := to_Z_bounded j).
  rewrite ltb_spec; intros Hj IH.
  rewrite to_Z_add_1_wB by lia; intro Hij.
  case (reflect_eqb j i); [ intro Heq; rewrite Heq; clear Heq | rewrite <- to_Z_eq; intro Hneq ].
  apply in_eq.
  apply in_cons.
  apply IH.
  lia.
Qed.

Lemma to_list_In_eq : forall {A} (t: array A) i x,
  i < length t = true -> x = t.[i] -> In x (to_list t).
Proof.
  intros A t i x Hi ->. now apply to_list_In.
Qed.

Lemma In_to_list : forall {A} (t: array A) x,
  In x (to_list t) -> exists i, i < length t = true /\ x = t.[i].
Proof.
  intros A t x; assert (Bt := to_Z_bounded (length t)); unfold to_list.
  rewrite <- in_rev.
  set (a := foldi _ _ _ _); pattern (length t) at 0, a; subst a; apply foldi_ind.
  rewrite leb_spec, to_Z_0; lia.
  intro H; elim (in_nil H).
  intros i a _; assert (Bi := to_Z_bounded i); rewrite ltb_spec; intros Hi IH.
  intro Hin; case (in_inv Hin); clear Hin; [ | exact IH ].
  intro H; rewrite <- H; clear H.
  exists i.
  split; [ rewrite ltb_spec; lia | reflexivity ].
Qed.

(** Lemmas about amapi/amap *)

Definition amapi {A B:Type} (f:int->A->B) (t:array A) :=
  let l := length t in
  foldi (fun i tb => tb.[i <- f i (t.[i])]) 0 l (make l (f l (default t))).

Definition amap {A B:Type} (f:A->B) := amapi (fun _ => f).

Lemma length_amapi : forall {A B} (f:int -> A -> B) t,
  length (amapi f t) = length t.
Proof.
  unfold amapi; intros A B f t.
  assert (Bt := to_Z_bounded (length t)).
  apply (foldi_ind _ (fun _ a => length a = length t)).
  apply leb_0.
  rewrite length_make, leb_length by reflexivity; reflexivity.
  intros i a _; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec; intros Hi IH.
  rewrite length_set; exact IH.
Qed.

Lemma length_amap : forall {A B} (f:A -> B) t,
  length (amap f t) = length t.
Proof.
  intros; unfold amap; apply length_amapi.
Qed.

Lemma default_amapi : forall {A B} (f:int -> A -> B) t,
  default (amapi f t) = f (length t) (default t).
Proof.
  unfold amapi; intros A B f t.
  assert (Bt := to_Z_bounded (length t)).
  apply (foldi_ind _ (fun i a => default a = f (length t) (default t))).
  apply leb_0.
  rewrite default_make by reflexivity; reflexivity.
  intros i a _; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec; intros Hi IH.
  rewrite default_set; exact IH.
Qed.

Lemma default_amap : forall {A B} (f:A -> B) t,
  default (amap f t) = f (default t).
Proof.
  intros; unfold amap; apply default_amapi.
Qed.

Lemma get_amapi : forall {A B} (f:int -> A -> B) t i,
  i < length t = true -> (amapi f t).[i] = f i (t.[i]).
Proof.
  intros A B f t.
  assert (Bt := to_Z_bounded (length t)).
  intro i; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec; intro Hi.
  generalize (length_amapi f t); unfold amapi; revert Hi.
  set (a := foldi _ _ _ _); pattern (length t) at 1, a; subst a; apply foldi_ind.
  rewrite leb_spec, to_Z_0; lia.
  rewrite to_Z_0; lia.
  intros j a _; assert (Bj := to_Z_bounded j).
  rewrite ltb_spec; intros Hj IH.
  rewrite to_Z_add_1_wB by lia; intro Hij.
  rewrite length_set; case (reflect_eqb j i); [ intro Heq; rewrite Heq | intro Hneq ]; intro Hlength.
  rewrite get_set_same by (rewrite Hlength, ltb_spec; lia); reflexivity.
  rewrite get_set_other by exact Hneq.
  apply IH; [ rewrite <- to_Z_eq in Hneq; lia | exact Hlength ].
Qed.

Lemma get_amap : forall {A B} (f:A -> B) t i,
  i < length t = true -> (amap f t).[i] = f (t.[i]).
Proof.
  intros; unfold amap; apply get_amapi; assumption.
Qed.

Lemma get_amapi_outofbound : forall {A B} (f:int -> A -> B) t i,
  i < length t = false -> (amapi f t).[i] = f (length t) (default t).
Proof.
  intros A B f t i H1; rewrite get_outofbound.
  apply default_amapi.
  rewrite length_amapi; auto.
Qed.

Lemma get_amap_outofbound : forall {A B} (f:A -> B) t i,
  i < length t = false -> (amap f t).[i] = f (default t).
Proof.
  intros; unfold amap; apply get_amapi_outofbound; assumption.
Qed.

Lemma to_list_amap : forall A B (f : A -> B) t, to_list (amap f t) = List.map f (to_list t).
Proof.
  intros A B f t.
  assert (Bt := to_Z_bounded (length t)).
  unfold to_list; rewrite length_amap.
  rewrite map_rev; f_equal.
  apply (foldi_ind2 _ _ (fun i a b  => a = map f b)).
  apply leb_0.
  reflexivity.
  intros i a1 a2 _; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec; intros Hi IH.
  simpl; f_equal.
  apply get_amap.
  rewrite ltb_spec; lia.
  apply IH.
Qed.

(** Some properties about afold_left *)

Definition afold_left A default (OP : A -> A -> A) (V : array A) :=
  if length V == 0 then default
  else foldi (fun i a => OP a (V.[i])) 1 (length V) (V.[0]).

Lemma afold_left_spec : forall A args op (e : A),
  (forall a, op e a = a) ->
  afold_left _ e op args =
  foldi (fun i a => op a (args.[i])) 0 (length args) e.
  Proof.
    unfold afold_left;intros A args op neu H10.
    destruct (reflect_eqb (length args) 0) as [e|n].
    rewrite e, foldi_ge by reflexivity;trivial.
    rewrite (foldi_lt_l _ _ 0) by (apply not_0_ltb; assumption).
    f_equal; rewrite H10; reflexivity.
  Qed.

Lemma afold_left_eq :
  forall A OP (def : A) V1 V2,
    length V1 = length V2 ->
    (forall i, i < length V1 = true -> V1.[i] = V2.[i]) ->
    afold_left _ def OP V1 = afold_left _ def OP V2.
Proof.
  intros A OP def V1 V2 Heqlength HeqV.
  assert (BV1 := to_Z_bounded (length V1)).
  unfold afold_left.
  rewrite <- Heqlength.
  case (reflect_eqb (length V1) 0).
  reflexivity.
  rewrite <- to_Z_eq, to_Z_0; intro Hneq.
  rewrite <- HeqV by (rewrite ltb_spec, to_Z_0; lia).
  apply (foldi_ind2 _ _ (fun i a b => a = b)).
  rewrite leb_spec, to_Z_1; lia.
  reflexivity.
  intros i a1 a2; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_1; intro Hi1.
  rewrite ltb_spec by lia; intros Hi2 IH.
  f_equal;[ exact IH | apply HeqV; rewrite ltb_spec; lia ].
Qed.

Lemma afold_left_ind : forall A OP def V (P : int -> A -> Prop),
  (length V = 0 -> P 0 def) ->
  (0 < length V = true -> P 1 (V.[0])) ->
  (forall a i, 0 < i = true -> i < length V = true -> P i a -> P (i + 1) (OP a (V.[i]))) ->
  P (length V) (afold_left A def OP V).
Proof.
  intros A OP def V P HP0 HP1 HPOP.
  assert (BV := to_Z_bounded (length V)).
  unfold afold_left.
  case (reflect_eqb (length V) 0); [ intro Heq; rewrite Heq; tauto | intro Hneq ].
  rewrite <- to_Z_eq, to_Z_0 in Hneq.
  apply foldi_ind.
  rewrite leb_spec, to_Z_1; lia.
  apply HP1; rewrite ltb_spec, to_Z_0; lia.
  intros i a; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_1, ltb_spec; intros Hi1 Hi2 IH.
  apply HPOP; [ rewrite ltb_spec, to_Z_0; lia | rewrite ltb_spec; lia | exact IH ].
Qed.

(** Some properties about afold_right *)

Definition afold_right A default (OP : A -> A -> A) (V : array A) :=
  if length V == 0 then default
  else foldi (fun i => OP (V.[length V - 1 - i])) 1 (length V) (V.[length V - 1]).

Lemma afold_right_spec : forall A args op (e : A),
  (forall a, op a e = a) ->
  afold_right _ e op args =
  foldi (fun i a => op (args.[length args - 1 - i]) a) 0 (length args) e.
  Proof.
    unfold afold_right;intros A args op neu H10.
    assert (Bargs := to_Z_bounded (length args)).
    destruct (reflect_eqb (length args) 0) as [e|n].
    rewrite e, foldi_ge by reflexivity;trivial.
    change 1 with (0 + 1) at 2.
    replace (length args - 1) with (length args - 1 - 0) at 1 by ring.
    rewrite <- (H10 (args.[length args - 1 - 0])).
    rewrite <- (foldi_lt_l _ (fun i => op (args.[length args - 1 - i]))) by (apply not_0_ltb; assumption).
    apply foldi_eq_compat; intros; reflexivity.
  Qed.

Lemma afold_right_eq :
  forall A OP (def : A) V1 V2,
    length V1 = length V2 ->
    (forall i, i < length V1 = true -> V1.[i] = V2.[i]) ->
    afold_right _ def OP V1 = afold_right _ def OP V2.
Proof.
  intros A OP def V1 V2 Heqlength HeqV.
  assert (BV1 := to_Z_bounded (length V1)).
  unfold afold_right.
  rewrite <- Heqlength.
  case (reflect_eqb (length V1) 0); [ reflexivity | intro Hneq ].
  rewrite <- to_Z_eq, to_Z_0 in Hneq.
  rewrite <- HeqV by (rewrite ltb_spec, to_Z_sub_1_0; lia).
  apply (foldi_ind2 _ _ (fun i a b => a = b)).
  rewrite leb_spec, to_Z_1; lia.
  reflexivity.
  intros i a1 a2; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_1; intro Hi1.
  rewrite ltb_spec by lia; intros Hi2 IH.
  f_equal;[ apply HeqV; rewrite ltb_spec, sub_spec, to_Z_sub_1_0, Z.mod_small; lia | exact IH ].
Qed.

Lemma afold_right_ind : forall A OP def V (P : int -> A -> Prop),
  (length V = 0 -> P 0 def) ->
  (0 < length V = true -> P (length V - 1) (V.[length V - 1])) ->
  (forall a i, 0 < i = true -> i < length V = true -> P i a -> P (i - 1) (OP (V.[i - 1]) a)) ->
  P 0 (afold_right A def OP V).
Proof.
  intros A OP def V P HP0 HP1 HPOP.
  assert (BV := to_Z_bounded (length V)).
  unfold afold_right.
  case (reflect_eqb (length V) 0); [ intro Heq; apply HP0; exact Heq | intro Hneq ].
  rewrite <- to_Z_eq, to_Z_0 in Hneq.
  replace 0 with (length V - length V) at 1 by ring.
  apply (foldi_ind _ (fun i a => P (length V - i) a)).
  rewrite leb_spec, to_Z_1; lia.
  apply HP1; rewrite ltb_spec, to_Z_0; lia.
  intros i a; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_1, ltb_spec; intros Hi1 Hi2 IH.
  replace (length V - (i + 1)) with (length V - i - 1) by ring.
  replace (length V - 1 - i) with (length V - i - 1) by ring.
  apply HPOP; [ rewrite ltb_spec, to_Z_0, sub_spec, Z.mod_small; lia | rewrite ltb_spec, sub_spec, Z.mod_small; lia | exact IH ].
Qed.

(** Application to our uses of afold_left and afold_right *)
(* Case andb *)

Lemma afold_left_andb_false : forall i a,
  i < length a = true ->
  a .[ i] = false ->
  afold_left bool true andb a = false.
Proof.
  intros i a; assert (Ba := to_Z_bounded (length a)); assert (Bi := to_Z_bounded i).
  rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  rewrite ltb_spec, to_Z_0; lia.
  intros j b _; assert (Bj := to_Z_bounded j).
  rewrite 2!ltb_spec; intros Hj IH.
  rewrite ltb_spec, to_Z_add_1_wB by lia; intro Hij.
  case (reflect_eqb i j).
  intros Heq Hai; rewrite <- Heq, Hai; apply andb_false_r.
  rewrite <- to_Z_eq; intros Hneq Hai.
  rewrite IH; [ apply andb_false_l | lia | exact Hai ].
Qed.

Lemma afold_left_andb_false_inv : forall a,
  afold_left bool true andb a = false ->
  exists i, (i < length a = true) /\ (a .[ i] = false).
Proof.
  intro a; assert (Ba := to_Z_bounded (length a)).
  rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  discriminate.
  intros i b _; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec; intros Hj IH.
  destruct b.
  rewrite andb_true_l; intro H; exists i; rewrite H.
  split; [ rewrite ltb_spec, to_Z_add_1_wB; lia | reflexivity ].
  generalize (IH eq_refl); clear IH; intros [ j [ Hji Haj ] ] _.
  rewrite ltb_spec in Hji; exists j.
  split; [ rewrite ltb_spec, to_Z_add_1_wB; lia | exact Haj ].
Qed.

Lemma afold_left_andb_true : forall a,
  (forall i, i < length a = true -> a.[i] = true) ->
  afold_left bool true andb a = true.
Proof.
  intros a H.
  rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  reflexivity.
  intros b j _ H1 H2; rewrite H2; simpl; rewrite H; trivial.
Qed.

Lemma afold_left_andb_true_inv : forall a,
  afold_left bool true andb a = true ->
  forall i, i < length a = true -> a.[i] = true.
Proof.
  intros a H i; assert (Ba := to_Z_bounded (length a)); assert (Bi := to_Z_bounded i).
  revert H; rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  rewrite ltb_spec, to_Z_0; lia.
  intros j b _; assert (Bj := to_Z_bounded j).
  rewrite 2!ltb_spec; intros Hj IH.
  rewrite ltb_spec, to_Z_add_1_wB by lia.
  rewrite andb_true_iff.
  case (reflect_eqb i j).
  intro Heq; rewrite <- Heq; tauto.
  rewrite <- to_Z_eq; intros Hneq [ Hb Haj ] Hij.
  apply IH; [ exact Hb | lia ].
Qed.

Lemma afold_left_and A (p : A -> bool) a :
  afold_left bool true andb (amap p a) =
  List.forallb p (to_list a).
Proof.
  rewrite afold_left_spec, foldi_to_list, to_list_amap by exact andb_true_l.
  rewrite <- andb_true_r.
  generalize true.
  induction (to_list a) as [ | x l ]; clear a; intro b.
  reflexivity.
  simpl; rewrite IHl.
  rewrite (andb_comm b (p x)), (andb_comm (p x) (forallb p l)); apply andb_assoc.
Qed.

(* Case orb *)

Lemma afold_left_orb_true : forall i a,
  i < length a = true ->
  a .[ i] = true ->
  afold_left bool false orb a = true.
Proof.
  intros i a; assert (Ba := to_Z_bounded (length a)); assert (Bi := to_Z_bounded i).
  rewrite afold_left_spec by apply orb_false_l; apply foldi_ind.
  apply leb_0.
  rewrite ltb_spec, to_Z_0; lia.
  intros j b _; assert (Bj := to_Z_bounded j).
  rewrite 2!ltb_spec; intros Hj IH.
  rewrite ltb_spec, to_Z_add_1_wB by lia; intro Hij.
  case (reflect_eqb i j).
  intros Heq Hai; rewrite <- Heq, Hai; apply orb_true_r.
  rewrite <- to_Z_eq; intros Hneq Hai.
  rewrite IH; [ apply orb_true_l | lia | exact Hai ].
Qed.

Lemma afold_left_orb_true_inv : forall a,
  afold_left bool false orb a = true ->
  exists i, i < length a = true /\ a .[ i] = true.
Proof.
  intro a; assert (Ba := to_Z_bounded (length a)).
  rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  discriminate.
  intros i b _; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec; intros Hj IH.
  destruct b.
  generalize (IH eq_refl); clear IH; intros [ j [ Hji Haj ] ] _.
  rewrite ltb_spec in Hji; exists j.
  split; [ rewrite ltb_spec, to_Z_add_1_wB; lia | exact Haj ].
  rewrite orb_false_l; intro H; exists i; rewrite H.
  split; [ rewrite ltb_spec, to_Z_add_1_wB; lia | reflexivity ].
Qed.

Lemma afold_left_orb_false : forall a,
  (forall i, i < length a = true -> a.[i] = false) ->
  afold_left bool false orb a = false.
Proof.
  intros a H.
  rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  reflexivity.
  intros b j _ H1 H2; rewrite H2; simpl; rewrite H; trivial.
Qed.

Lemma afold_left_orb_false_inv : forall a,
  afold_left bool false orb a = false ->
  forall i, i < length a = true -> a.[i] = false.
Proof.
  intros a H i; assert (Ba := to_Z_bounded (length a)); assert (Bi := to_Z_bounded i).
  revert H; rewrite afold_left_spec by apply andb_true_l; apply foldi_ind.
  apply leb_0.
  rewrite ltb_spec, to_Z_0; lia.
  intros j b _; assert (Bj := to_Z_bounded j).
  rewrite 2!ltb_spec; intros Hj IH.
  rewrite ltb_spec, to_Z_add_1_wB by lia.
  rewrite orb_false_iff.
  case (reflect_eqb i j).
  intro Heq; rewrite <- Heq; tauto.
  rewrite <- to_Z_eq; intros Hneq [ Hb Haj ] Hij.
  apply IH; [ exact Hb | lia ].
Qed.

Lemma afold_left_or A (p : A -> bool) a :
  afold_left bool false orb (amap p a) =
  List.existsb p (to_list a).
Proof.
  rewrite afold_left_spec, foldi_to_list, to_list_amap by exact andb_true_l.
  rewrite <- orb_false_r.
  generalize false.
  induction (to_list a) as [ | x l ]; clear a; intro b.
  reflexivity.
  simpl; rewrite IHl.
  rewrite (orb_comm b (p x)), (orb_comm (p x) (existsb p l)); apply orb_assoc.
Qed.

(* Case implb *)

Lemma afold_right_implb_false : forall a,
  0 < length a = true /\
  (forall i, i < length a - 1 = true -> a .[ i] = true) /\
  a.[length a - 1] = false ->
  afold_right bool true implb a = false.
Proof.
  intros a; intros [H1 [H2 H3]].
  pattern 0; apply afold_right_ind.
  intro H; rewrite H in H1; discriminate.
  intros _; exact H3.
  intros b i H4 H5 H6; rewrite H6; clear H6.
  rewrite H2; [ reflexivity | ].
  assert (Ba := to_Z_bounded (length a)); assert (Bi := to_Z_bounded i).
  revert H1 H4 H5; rewrite 4!ltb_spec, to_Z_0; intros H1 H4 H5.
  rewrite 2!to_Z_sub_1_0; lia.
Qed.

Lemma afold_right_implb_false_inv : forall a,
  afold_right bool true implb a = false ->
  0 < length a = true /\
  (forall i, i < length a - 1 = true -> a .[ i] = true) /\
  a.[length a - 1] = false.
Proof.
  intros a H; assert (Ba := to_Z_bounded (length a)); split; [ | split ].
  revert H; unfold afold_right.
  case (reflect_eqb (length a) 0).
  intro Heq; rewrite Heq; discriminate.
  rewrite <- to_Z_eq, to_Z_0; intros Hlength _.
  rewrite ltb_spec, to_Z_0; lia.
  intro i; generalize (leb_0 i); revert H i; apply afold_right_ind.
  discriminate.
  intros _ _ i; rewrite leb_spec, ltb_spec; lia.
  intros b j; assert (Bj := to_Z_bounded j).
  rewrite 2!ltb_spec, to_Z_0; intros Hj1 Hj2 IH.
  unfold implb; case_eq (a.[j - 1]); [ | discriminate ]; intros Ha H; subst b; intro i.
  case (reflect_eqb i (j - 1)).
  intro Heq; subst i; intros; exact Ha.
  rewrite <- to_Z_eq, to_Z_sub_1_0 by lia; intro Hneq.
  rewrite leb_spec, to_Z_sub_1_0 by lia; intro Hji.
  apply IH; [ reflexivity | rewrite leb_spec; lia ].
  revert H; unfold afold_right.
  case (reflect_eqb (length a) 0).
  discriminate.
  rewrite <- to_Z_eq, to_Z_0; intro Hlength.
  apply (foldi_ind _ (fun i b => b = false -> a.[length a - 1] = false)).
  rewrite leb_spec, to_Z_1; lia.
  tauto.
  intros i b; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_1; intro Hi1.
  rewrite ltb_spec; intros Hi2 IH.
  unfold implb at 1; case (a.[length a - 1 - i]); [ exact IH | discriminate ].
Qed.

Lemma afold_right_implb_true_aux : forall a,
  (exists i, i < length a - 1 = true /\ a.[i] = false) ->
  afold_right bool true implb a = true.
Proof.
  intros a [ i [ Hi Hai ] ].
  assert (Bi := to_Z_bounded i).
  generalize (leb_0 i); apply afold_right_ind.
  reflexivity.
  intros _; revert Hi; rewrite ltb_spec, leb_spec; lia.
  intros b j.
  assert (Bj := to_Z_bounded j).
  rewrite ltb_spec, to_Z_0; intro Hj1.
  rewrite ltb_spec; intro Hj2.
  rewrite leb_spec; intro IH.
  rewrite leb_spec, to_Z_sub_1_0 by lia; intro Hji.
  case (reflect_eqb i (j - 1)).
  intro Heq; rewrite Heq in Hai; rewrite Hai; reflexivity.
  rewrite <- to_Z_eq, to_Z_sub_1_0 by lia; intro Hneq.
  rewrite IH by lia; case (a.[j - 1]); reflexivity.
Qed.

Lemma afold_right_implb_true : forall a,
  length a = 0 \/ (exists i, i < length a - 1 = true /\ a.[i] = false) \/
  (forall i, i < length a = true -> a.[i] = true) ->
  afold_right bool true implb a = true.
Proof.
  intro a; assert (Ba := to_Z_bounded (length a)); case (reflect_eqb (length a) 0).
  intros H _; unfold afold_right; rewrite H; reflexivity.
  intro Hneq.
  intros [H1|[H1|H1]].
  elim (Hneq H1).
  apply afold_right_implb_true_aux; auto.
  assert (Heq : length a == 0 = false) by (rewrite <- not_true_iff_false, eqb_spec; exact Hneq).
  unfold afold_right; rewrite Heq.
  revert Hneq; rewrite <- to_Z_eq, to_Z_0; intro Hneq.
  apply (foldi_ind _ (fun i a => a = true)).
  rewrite leb_spec, to_Z_1; lia.
  apply H1; rewrite ltb_spec, to_Z_sub_1_0; lia.
  intros i b; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_1; intro Hi1.
  rewrite ltb_spec; intros Hi2 IH.
  rewrite IH; case (a.[length a - 1 - i]); reflexivity.
Qed.

Lemma afold_right_implb_true_inv : forall a,
  afold_right bool true implb a = true ->
  length a = 0 \/ (exists i, i < length a - 1 = true /\ a.[i] = false) \/
  (forall i, i < length a = true -> a.[i] = true).
Proof.
  intros a H; cut (length a = 0
    \/ (exists i, 0 <= i = true /\ i < length a - 1 = true /\ a.[i] = false)
    \/ (forall i, 0 <= i = true -> i < length a = true -> a.[i] = true)).
  clear H; intro H; destruct H as [ H | H ].
  left; tauto.
  destruct H as [ H | H ].
  destruct H as [ i [ Hi1 Hi2 ] ].
  right; left; exists i; tauto.
  right; right; intro i; apply H; apply leb_0.
  assert (Ba := to_Z_bounded (length a)).
  revert H; apply afold_right_ind.
  left; tauto.
  rewrite ltb_spec, to_Z_0; intro Hlength.
  intro Ha; right; right.
  intro i; assert (Bi := to_Z_bounded i).
  rewrite leb_spec, to_Z_sub_1_0 by lia; intro Hi1.
  rewrite ltb_spec; intro Hi2.
  replace i with (length a - 1) by (rewrite <- to_Z_eq, to_Z_sub_1_0; lia); exact Ha.
  intros b i; assert (Bi := to_Z_bounded i).
  rewrite ltb_spec, to_Z_0; intro Hi1.
  rewrite ltb_spec; intros Hi2 IH.
  case_eq (a.[i - 1]); unfold implb.
  intros Ha Hb; destruct (IH Hb) as [ Heq | H ]; clear IH.
  rewrite Heq in Hi2; lia.
  destruct H as [ [ j [ Hij Hj ] ] | H ].
  right; left; exists j.
  split; [ | exact Hj ].
  revert Hij; rewrite 2!leb_spec, to_Z_sub_1_0; lia.
  right; right; intro j.
  rewrite leb_spec, sub_spec, to_Z_1, Z.mod_small by lia; intro Hij.
  rewrite ltb_spec; intro Hj.
  case (reflect_eqb j (i - 1)).
  intro Heq; rewrite Heq; exact Ha.
  rewrite <- to_Z_eq, to_Z_sub_1_0 by lia; intro Hneq.
  apply H; [ rewrite leb_spec; lia | rewrite ltb_spec; lia ].
  intros Ha _; right; left; exists (i - 1).
  split; [ rewrite leb_spec; lia | ].
  split; [ rewrite ltb_spec, 2!to_Z_sub_1_0; lia | exact Ha ].
Qed.

(* Other cases *)

Lemma afold_left_length_2 : forall A default OP t,
  (length t == 2) = true ->
  afold_left A default OP t = OP (t.[0]) (t.[1]).
Proof.
  intros A default OP t H; unfold afold_left; rewrite eqb_spec in H; rewrite H; change (2 == 0) with false; reflexivity.
Qed.


Lemma afold_right_length_2 : forall A default OP t,
  (length t == 2) = true ->
  afold_right A default OP t = OP (t.[0]) (t.[1]).
Proof.
  intros A default OP t H; unfold afold_right; rewrite eqb_spec in H; rewrite H; change (2 == 0) with false; reflexivity.
Qed.


Ltac tac_left :=
  intros t H H1 H2; rewrite afold_left_length_2;
    [rewrite H1, H2| ]; trivial.


Ltac tac_right :=
  try (intros t H H1 H2; rewrite afold_right_length_2;
    [rewrite H1, H2| ]; trivial);
  try (intros t H H1; rewrite afold_right_length_2;
    [rewrite H1| ]; trivial);
  try (rewrite implb_true_r; trivial).


Lemma afold_left_xorb_false1 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = false -> t .[ 1] = false ->
  afold_left bool false xorb t = false.
Proof. tac_left. Qed.


Lemma afold_left_xorb_false2 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = true -> t .[ 1] = true ->
  afold_left bool false xorb t = false.
Proof. tac_left. Qed.


Lemma afold_left_xorb_true1 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = false -> t .[ 1] = true ->
  afold_left bool false xorb t = true.
Proof. tac_left. Qed.


Lemma afold_left_xorb_true2 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = true -> t .[ 1] = false ->
  afold_left bool false xorb t = true.
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


Lemma afold_left_eqb_false1 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = false -> t .[ 1] = true ->
  afold_left bool true eqb t = false.
Proof. tac_left. Qed.


Lemma afold_left_eqb_false2 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = true -> t .[ 1] = false ->
  afold_left bool true eqb t = false.
Proof. tac_left. Qed.


Lemma afold_left_eqb_true1 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = true -> t .[ 1] = true ->
  afold_left bool true eqb t = true.
Proof. tac_left. Qed.


Lemma afold_left_eqb_true2 : forall t,
  (PArray.length t == 2) = true ->
  t .[ 0] = false -> t .[ 1] = false ->
  afold_left bool true eqb t = true.
Proof. tac_left. Qed.


(** Two elements in a list *)

Section List2.

  Variable A : Type.

  Inductive In2 (i j : A) : list A -> Prop :=
  | In2_hd : forall l, In j l -> In2 i j (i::l)
  | In2_tl : forall k l, In2 i j l -> In2 i j (k::l).

  Local Hint Constructors In2 : smtcoq_in2.


  Lemma In2_app : forall i j l m, In2 i j (l ++ m) <->
    In2 i j l \/ (In i l /\ In j m) \/ In2 i j m.
  Proof.
    intros i j; induction l as [ |t l IHl]; simpl; intro m; split; auto with smtcoq_in2.
    intros [H|[[H _]|H]]; auto with smtcoq_in2.
    inversion H.
    elim H.
    intro H; inversion H; clear H.
    subst i l0; rewrite in_app_iff in H1; destruct H1 as [H1|H1]; auto with smtcoq_in2.
    subst k l0; rewrite IHl in H1; destruct H1 as [H1|[[H1 H2]|H1]]; auto with smtcoq_in2.
    intros [H|[[[H|H] H1]|H]].
    inversion H; clear H.
    subst i l0; constructor 1; rewrite in_app_iff; auto with smtcoq_in2.
    subst k l0; constructor 2; rewrite IHl; left; auto with smtcoq_in2.
    subst t; constructor 1; rewrite in_app_iff; auto with smtcoq_in2.
    constructor 2; rewrite IHl; right; left; auto with smtcoq_in2.
    constructor 2; rewrite IHl; right; right; auto with smtcoq_in2.
  Qed.


  Fixpoint rev_aux acc (l:list A) :=
    match l with
      | nil => acc
      | t::q => rev_aux (t::acc) q
    end.


  Lemma In2_rev_aux : forall i j l acc, In2 i j (rev_aux acc l) <->
    In2 i j acc \/ (In i l /\ In j acc) \/ In2 j i l.
  Proof.
    intros i j; induction l as [ |t q IHq]; simpl; intro acc; split; auto with smtcoq_in2.
    intros [H|[[H _]|H]]; auto with smtcoq_in2.
    elim H.
    inversion H.
    rewrite IHq; clear IHq; intros [H|[[H1 H2]|H]]; auto with smtcoq_in2.
    inversion H; auto with smtcoq_in2.
    inversion H2; auto with smtcoq_in2; clear H2; subst t; right; right; auto with smtcoq_in2.
    intros [H|[[[H1|H1] H2]|H]]; rewrite IHq; clear IHq; auto with smtcoq_in2.
    subst t; auto with smtcoq_in2.
    right; left; split; auto with smtcoq_in2; constructor 2; auto with smtcoq_in2.
    inversion H; clear H; auto with smtcoq_in2; subst j l; right; left; split; auto with smtcoq_in2; constructor 1; auto with smtcoq_in2.
  Qed.


  Definition rev := rev_aux nil.


  Lemma In2_rev : forall i j l, In2 i j (rev l) <-> In2 j i l.
  Proof.
    intros i j l; unfold rev; rewrite In2_rev_aux; split; auto with smtcoq_in2; intros [H|[[_ H]|H]]; auto with smtcoq_in2; inversion H.
  Qed.


  Lemma In2_In : forall i j, i <> j -> forall l, (In i l /\ In j l) <-> (In2 i j l \/ In2 j i l).
  Proof.
    intros i j H l; split.
    intros [H1 H2]; generalize H1 H2; clear H1 H2; induction l as [ |t q IHq].
    intro H1; inversion H1.
    intros H1 H2; inversion H1; clear H1.
    subst t; inversion H2; auto with smtcoq_in2; elim H; auto with smtcoq_in2.
    inversion H2; clear H2.
    subst t; auto with smtcoq_in2.
    destruct (IHq H0 H1) as [H2|H2]; auto with smtcoq_in2.
    intros [H1|H1]; induction H1 as [H1|t q H1 [IH1 IH2]].
    split; [constructor 1|constructor 2]; auto with smtcoq_in2.
    split; constructor 2; auto with smtcoq_in2.
    split; [constructor 2|constructor 1]; auto with smtcoq_in2.
    split; constructor 2; auto with smtcoq_in2.
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

  Local Hint Constructors In2 : smtcoq_in2.

  Lemma distinct_aux_spec : forall l acc, distinct_aux acc l = true <->
    acc = true /\ (forall i j, In2 i j l -> eq i j = false).
  Proof.
    induction l as [ |t q IHq]; simpl.
    intro acc; split.
    intro H; split; auto with smtcoq_in2; intros i j H1; inversion H1.
    intros [H _]; auto with smtcoq_in2.
    intro acc; rewrite (IHq (distinct_aux2 acc t q)), distinct_aux2_spec; split.
    intros [[H1 H2] H3]; split; auto with smtcoq_in2; intros i j H; inversion H; auto with smtcoq_in2.
    intros [H1 H2]; repeat split; auto with smtcoq_in2.
  Qed.

  Lemma distinct_aux_spec_neg : forall l acc, distinct_aux acc l = false <->
    acc = false \/ (exists i j, In2 i j l /\ eq i j = true).
  Proof.
    induction l as [ |t q IHq]; simpl.
    intro acc; split; auto with smtcoq_in2; intros [H|[i [j [H _]]]]; auto with smtcoq_in2; inversion H.
    intro acc; rewrite (IHq (distinct_aux2 acc t q)), distinct_aux2_spec_neg; split.
    intros [[H|[i [H1 H2]]]|[i [j [H1 H2]]]]; auto with smtcoq_in2.
    right; exists t; exists i; auto with smtcoq_in2.
    right; exists i; exists j; auto with smtcoq_in2.
    intros [H|[i [j [H1 H2]]]]; auto with smtcoq_in2; inversion H1; clear H1.
    subst i l; left; right; exists j; auto with smtcoq_in2.
    subst k l; right; exists i; exists j; auto with smtcoq_in2.
  Qed.

  Definition distinct := distinct_aux true.

  Lemma distinct_spec : forall l, distinct l = true <->
    (forall i j, In2 i j l -> eq i j = false).
  Proof.
    unfold distinct; intro l; rewrite distinct_aux_spec; split; auto with smtcoq_in2; intros [_ H]; auto with smtcoq_in2.
  Qed.

  Lemma distinct_false_spec : forall l, distinct l = false <->
    (exists i j, In2 i j l /\ eq i j = true).
  Proof.
    unfold distinct; intro l; rewrite distinct_aux_spec_neg; split; auto with smtcoq_in2; intros [H|H]; auto with smtcoq_in2; discriminate.
  Qed.

End Distinct.

Arguments distinct [A] eq l.

(** Specification of aexistsbi and aforallbi *)

Definition aexistsbi {A:Type} (f:int->A->bool) (t:array A) :=
  afold_left _ false orb (amapi f t).

Lemma aexistsbi_false_spec : forall A (f : int -> A -> bool) t,
  aexistsbi f t = false <->
  forall i, i < length t = true -> f i (t.[i]) = false.
Proof.
  intros A f t; unfold aexistsbi.
  split.
  intro H; generalize (afold_left_orb_false_inv _ H); clear H.
  rewrite length_amapi; intros H i Hi.
  rewrite <- get_amapi by exact Hi.
  apply H; exact Hi.
  intro H; apply afold_left_orb_false.
  intro i; rewrite length_amapi; intro Hi; rewrite get_amapi by exact Hi; apply H; exact Hi.
Qed.

Lemma aexistsbi_spec : forall A (f : int -> A -> bool) t,
  aexistsbi f t = true <-> exists i, i < length t = true /\ f i (t.[i]) = true.
Proof.
  intros A f t; unfold aexistsbi.
  split.
  intro H; generalize (afold_left_orb_true_inv _ H); clear H.
  intros [ i [ Hi Hf ] ]; exists i.
  rewrite length_amapi in Hi; rewrite get_amapi in Hf by exact Hi.
  split; [ exact Hi | exact Hf ].
  intros [ i [ Hi Hf ] ].
  apply (afold_left_orb_true i); [ rewrite length_amapi; exact Hi | rewrite get_amapi by exact Hi; exact Hf ].
Qed.

Definition aforallbi {A:Type} (f:int->A->bool) (t:array A) :=
  afold_left _ true andb (amapi f t).

Lemma aforallbi_false_spec : forall A (f : int -> A -> bool) t,
  aforallbi f t = false <-> exists i, i < length t = true /\ f i (t.[i]) = false.
Proof.
  intros A f t; unfold aforallbi.
  split.
  intro H; generalize (afold_left_andb_false_inv _ H); clear H.
  intros [ i [ Hi Hf ] ]; exists i.
  rewrite length_amapi in Hi; rewrite get_amapi in Hf by exact Hi.
  split; [ exact Hi | exact Hf ].
  intros [ i [ Hi Hf ] ].
  apply (afold_left_andb_false i); [ rewrite length_amapi; exact Hi | rewrite get_amapi by exact Hi; exact Hf ].
Qed.

Lemma aforallbi_spec : forall A (f : int -> A -> bool) t,
  aforallbi f t = true <->
  forall i, i < length t = true -> f i (t.[i]) = true.
Proof.
  intros A f t; unfold aforallbi.
  split.
  intro H; generalize (afold_left_andb_true_inv _ H); clear H.
  rewrite length_amapi; intros H i Hi.
  rewrite <- get_amapi by exact Hi.
  apply H; exact Hi.
  intro H; apply afold_left_andb_true.
  intro i; rewrite length_amapi; intro Hi; rewrite get_amapi by exact Hi; apply H; exact Hi.
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

Arguments forallb2 {A B} f l1 l2.


(* Misc lemmas *)

Lemma neg_eq_true_eq_false b : b = false <-> b <> true.
Proof. destruct b; intuition. Qed.

Lemma is_true_iff e :  e = true <-> is_true e.
Proof. now unfold is_true. Qed.


(* Register constants for OCaml access *)
Register distinct as SMTCoq.Misc.distinct.

Register Int63.eqb as num.int63.eqb.
Register PArray.array as array.array.type.
Register PArray.make as array.array.make.
Register PArray.set as array.array.set.
Register Coq.Init.Datatypes.is_true as core.is_true.is_true.
Register Coq.PArith.BinPosDef.Pos.eqb as num.pos.eqb.
Register Coq.NArith.BinNat.N.of_nat as num.N.of_nat.
Register Coq.ZArith.BinInt.Z.ltb as num.Z.ltb.
Register Coq.ZArith.BinInt.Z.leb as num.Z.leb.
Register Coq.ZArith.BinInt.Z.gtb as num.Z.gtb.
Register Coq.ZArith.BinInt.Z.geb as num.Z.geb.
Register Coq.ZArith.BinInt.Z.eqb as num.Z.eqb.
Register Coq.Init.Datatypes.implb as core.bool.implb.
Register Coq.Bool.Bool.eqb as core.bool.eqb.
Register Coq.Bool.Bool.ifb as core.bool.ifb.
Register Coq.Bool.Bool.reflect as core.bool.reflect.
Register Coq.Init.Datatypes.length as core.list.length.
Register Coq.micromega.ZMicromega.ZArithProof as micromega.ZMicromega.ZArithProof.


(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import Bvector.
(* Require Export BigNumPrelude. *)
Require Import Int31 Cyclic31.
Require Export Int63Native.
Require Export Int63Op.
Require Import Psatz.

Local Open Scope Z_scope.


(* Taken from BigNumPrelude *)

 Lemma div_le_0 : forall p x, 0 <= x -> 0 <= x / 2 ^ p.
 Proof.
  intros p x Hle;destruct (Z_le_gt_dec 0 p).
  apply  Zdiv_le_lower_bound;auto with zarith.
  replace (2^p) with 0.
  destruct x;compute;intro;discriminate.
  destruct p;trivial;discriminate.
 Qed.

 Lemma div_lt : forall p x y, 0 <= x < y -> x / 2^p < y.
 Proof.
  intros p x y H;destruct (Z_le_gt_dec 0 p).
  apply Zdiv_lt_upper_bound;auto with zarith.
  apply Z.lt_le_trans with y;auto with zarith.
  rewrite <- (Z.mul_1_r y);apply Z.mul_le_mono_nonneg;auto with zarith.
  assert (0 < 2^p);auto with zarith.
  replace (2^p) with 0.
  destruct x;change (0<y);auto with zarith.
  destruct p;trivial;discriminate.
 Qed.


(* Int63Axioms *)

Definition wB := (2^(Z_of_nat size)).

Notation "[| x |]" := (to_Z x)  (at level 0, x at level 99) : int63_scope.

Notation "[+| c |]" :=
   (interp_carry 1 wB to_Z c)  (at level 0, c at level 99) : int63_scope.

Notation "[-| c |]" :=
   (interp_carry (-1) wB to_Z c)  (at level 0, c at level 99) : int63_scope.

Notation "[|| x ||]" :=
   (zn2z_to_Z wB to_Z x)  (at level 0, x at level 99) : int63_scope.

Local Open Scope int63_scope.
Local Open Scope Z_scope.

(* Bijection : int63 <-> Bvector size *)

Theorem to_Z_inj : forall x y, [|x|] = [|y|] -> x = y.
Proof Ring31.Int31_canonic.

Theorem of_to_Z : forall x, of_Z ([|x|]) = x.
Proof. exact phi_inv_phi. Qed.

(* Comparisons *)
Theorem eqb_refl x : (x == x)%int = true.
Proof. now rewrite Ring31.eqb31_eq. Qed.

Theorem ltb_spec x y : (x < y)%int = true <-> [|x|] < [|y|].
Proof.
  unfold ltb. rewrite spec_compare, <- Z.compare_lt_iff.
  change (phi x ?= phi y) with ([|x|] ?= [|y|]).
  case ([|x|] ?= [|y|]); intuition; discriminate.
Qed.

Theorem leb_spec x y : (x <= y)%int = true <-> [|x|] <= [|y|].
Proof.
  unfold leb. rewrite spec_compare, <- Z.compare_le_iff.
  change (phi x ?= phi y) with ([|x|] ?= [|y|]).
  case ([|x|] ?= [|y|]); intuition; discriminate.
Qed.


(** Specification of logical operations *)
Lemma lsl_spec_alt p :
  forall x, [| addmuldiv31_alt p x 0 |] = ([|x|] * 2^(Z.of_nat p)) mod wB.
Proof.
  induction p as [ |p IHp]; simpl; intro x.
  - rewrite Z.mul_1_r. symmetry. apply Zmod_small. apply phi_bounded.
  - rewrite IHp, phi_twice, Zmult_mod_idemp_l, Z.double_spec,
            Z.mul_comm, Z.mul_assoc, Z.mul_comm,
            Z.pow_pos_fold, Zpos_P_of_succ_nat, <- Z.add_1_r, Z.pow_add_r.
    * reflexivity.
    * apply Zle_0_nat.
    * exact Z.le_0_1.
Qed.

Theorem lsl_spec x p : [| x << p |] = ([|x|] * 2^[|p|]) mod wB.
Proof.
  unfold lsl.
  rewrite addmuldiv31_equiv, lsl_spec_alt, Nat2Z.inj_abs_nat, Z.abs_eq.
  - reflexivity.
  - now destruct (phi_bounded p).
Qed.


Lemma div_greater (p x:int) (H:Z.of_nat Int31.size <= [|p|]) : [|x|] / 2 ^ [|p|] = 0.
Proof.
  apply Z.div_small. destruct (phi_bounded x) as [H1 H2]. split; auto.
  apply (Z.lt_le_trans _ _ _ H2). apply Z.pow_le_mono_r; auto.
  exact Z.lt_0_2.
Qed.

Theorem lsr_spec x p : [|x >> p|] = [|x|] / 2 ^ [|p|].
Proof.
  unfold lsr. case_eq (p < 31%int31)%int; intro Heq.
  - assert (H : [|31%int31 - p|] = 31 - [|p|]).
    * rewrite spec_sub. rewrite Zmod_small; auto.
      split.
      + rewrite ltb_spec in Heq. assert (forall x y, x < y -> 0 <= y - x) by (intros;lia); auto.
      + assert (H:forall x y z, 0 <= y /\ x < z -> x - y < z) by (intros;lia).
        apply H. destruct (phi_bounded p). destruct (phi_bounded (31%int31)). split; auto.
    * rewrite spec_add_mul_div.
      + rewrite Z.add_0_l. change (phi (31%int31 - p)) with [|31%int31 - p|]. rewrite H. replace (31 - (31 - [|p|])) with [|p|] by ring. apply Zmod_small. split.
        ++ apply div_le_0. now destruct (phi_bounded x).
        ++ apply div_lt. apply phi_bounded.
      + change (phi (31%int31 - p)) with [|31%int31 - p|]. rewrite H. assert (forall x y, 0 <= y -> x - y <= x) by (intros;lia). apply H0. now destruct (phi_bounded p).
  - rewrite div_greater; auto.
    destruct (Z.le_gt_cases [|31%int31|] [|p|]); auto.
    rewrite <- ltb_spec in H. rewrite H in Heq. discriminate.
Qed.


Lemma bit_testbit x i : bit x i = Z.testbit [|x|] [|i|].
Admitted.
(* Proof. *)
(*   case_eq [|i|]. *)
(*   - simpl. change 0 with [|0|]. intro Heq. apply Ring31.Int31_canonic in Heq. subst i. *)
(*     unfold bit.  *)


Lemma Z_pos_xO_pow i x (Hi:0 <= i) : Z.pos x < 2 ^ i <-> Z.pos x~0 < 2 ^ (i+1).
Proof. rewrite Pos2Z.inj_xO, Z.pow_add_r; auto using Z.le_0_1; lia. Qed.

Lemma Z_pos_xI_pow i x (Hi:0 <= i) : Z.pos x < 2 ^ i <-> Z.pos x~1 < 2 ^ (i+1).
Proof. rewrite Pos2Z.inj_xI, Z.pow_add_r; auto using Z.le_0_1; lia. Qed.

Lemma pow_nonneg i (Hi : 1 <= 2 ^ i) : 0 <= i.
Proof.
  destruct (Z.le_gt_cases 0 i); auto.
  rewrite (Z.pow_neg_r _ _ H) in Hi. lia.
Qed.

Lemma pow_pos i (Hi : 1 < 2 ^ i) : 0 < i.
Proof.
  destruct (Z.lt_trichotomy 0 i) as [H|[H|H]]; auto.
  - subst i. lia.
  - rewrite (Z.pow_neg_r _ _ H) in Hi. lia.
Qed.

Lemma pos_land_bounded : forall x y i,
  Z.pos x < 2 ^ i -> Z.pos y < 2 ^ i -> Z.of_N (Pos.land x y) < 2 ^ i.
Proof.
  induction x as [x IHx|x IHx| ]; intros [y|y| ] i; auto.
  - simpl. intro H.
    assert (H4:0 <= i - 1) by (assert (H4:0 < i); try lia; apply pow_pos; apply (Z.le_lt_trans _ (Z.pos x~1)); auto; lia).
    generalize H. replace i with ((i-1)+1) at 1 2 by ring. rewrite <- !Z_pos_xI_pow; auto. intros H1 H2.
    assert (H3:=IHx _ _ H1 H2).
    unfold Pos.Nsucc_double. case_eq (Pos.land x y).
    * intros _. eapply Z.le_lt_trans; [ |exact H]. clear. lia.
    * intros p Hp. revert H3. rewrite Hp, N2Z.inj_pos, Z_pos_xI_pow; auto.
      replace (i - 1 + 1) with i by ring. clear. lia.
  - simpl. intro H.
    assert (H4:0 <= i - 1) by (assert (H4:0 < i); try lia; apply pow_pos; apply (Z.le_lt_trans _ (Z.pos x~1)); auto; lia).
    generalize H. replace i with ((i-1)+1) at 1 2 by ring. rewrite <- Z_pos_xI_pow, <- Z_pos_xO_pow; auto. intros H1 H2.
    assert (H3:=IHx _ _ H1 H2).
    unfold Pos.Ndouble. case_eq (Pos.land x y).
    * intros _. eapply Z.le_lt_trans; [ |exact H]. clear. lia.
    * intros p Hp. revert H3. rewrite Hp, N2Z.inj_pos, Z_pos_xO_pow; auto.
      replace (i - 1 + 1) with i by ring. clear. lia.
  - simpl. intro H.
    assert (H4:0 <= i - 1) by (assert (H4:0 < i); try lia; apply pow_pos; apply (Z.le_lt_trans _ (Z.pos x~0)); auto; lia).
    generalize H. replace i with ((i-1)+1) at 1 2 by ring. rewrite <- Z_pos_xI_pow, <- Z_pos_xO_pow; auto. intros H1 H2.
    assert (H3:=IHx _ _ H1 H2).
    unfold Pos.Ndouble. case_eq (Pos.land x y).
    * intros _. eapply Z.le_lt_trans; [ |exact H]. clear. lia.
    * intros p Hp. revert H3. rewrite Hp, N2Z.inj_pos, Z_pos_xO_pow; auto.
      replace (i - 1 + 1) with i by ring. clear. lia.
  - simpl. intro H.
    assert (H4:0 <= i - 1) by (assert (H4:0 < i); try lia; apply pow_pos; apply (Z.le_lt_trans _ (Z.pos x~0)); auto; lia).
    generalize H. replace i with ((i-1)+1) at 1 2 by ring. rewrite <- !Z_pos_xO_pow; auto. intros H1 H2.
    assert (H3:=IHx _ _ H1 H2).
    unfold Pos.Ndouble. case_eq (Pos.land x y).
    * intros _. eapply Z.le_lt_trans; [ |exact H]. clear. lia.
    * intros p Hp. revert H3. rewrite Hp, N2Z.inj_pos, Z_pos_xO_pow; auto.
      replace (i - 1 + 1) with i by ring. clear. lia.
  - simpl. intros H _. apply (Z.le_lt_trans _ (Z.pos x~0)); lia.
  - simpl. intros H _. apply (Z.le_lt_trans _ 1); lia.
Qed.


Lemma Z_land_bounded i : forall x y,
  0 <= x < 2 ^ i -> 0 <= y < 2 ^ i -> 0 <= Z.land x y < 2 ^ i.
Proof.
  intros [ |p|p] [ |q|q]; auto.
  - intros [_ H1] [_ H2]. simpl. split.
    * apply N2Z.is_nonneg.
    * now apply pos_land_bounded.
Admitted.

Theorem land_spec x y i : bit (x land y) i = bit x i && bit y i.
Proof.
  rewrite !bit_testbit. change (x land y) with (land31 x y). unfold land31.
  rewrite phi_phi_inv. rewrite Zmod_small.
  - apply Z.land_spec.
  - split.
    * rewrite Z.land_nonneg. left. now destruct (phi_bounded x).
    * now destruct (Z_land_bounded _ _ _ (phi_bounded x) (phi_bounded y)).
Qed.


Axiom lor_spec: forall x y i, bit (x lor y) i = bit x i || bit y i.

Axiom lxor_spec: forall  x y i, bit (x lxor y) i = xorb (bit x i) (bit y i).

(** Specification of basic opetations *)

(* Arithmetic modulo operations *)

(* Remarque : les axiomes seraient plus simple si on utilise of_Z a la place :
   exemple : add_spec : forall x y, of_Z (x + y) = of_Z x + of_Z y. *)

Axiom add_spec : forall x y, [|x + y|] = ([|x|] + [|y|]) mod wB.

Axiom sub_spec : forall x y, [|x - y|] = ([|x|] - [|y|]) mod wB.

Axiom mul_spec : forall x y, [| x * y |]  = [|x|] * [|y|] mod wB.

Axiom mulc_spec : forall x y, [|x|] * [|y|] = [|fst (mulc x y)|] * wB + [|snd (mulc x y)|].

Axiom div_spec : forall x y, [|x / y|] = [|x|] / [|y|].

Axiom mod_spec : forall x y, [|x \% y|] = [|x|] mod [|y|].

(** Iterators *)

Axiom foldi_cont_gt : forall A B f from to cont,
  (to < from)%int = true -> foldi_cont (A:=A) (B:=B) f from to cont = cont.

Axiom foldi_cont_eq : forall A B f from to cont,
  from = to -> foldi_cont (A:=A) (B:=B) f from to cont = f from cont.

Axiom foldi_cont_lt : forall A B f from to cont,
  (from < to)%int = true->
  foldi_cont (A:=A) (B:=B) f from to cont =
  f from (fun a' => foldi_cont f (from + 1%int) to cont a').

Axiom foldi_down_cont_lt : forall A B f from downto cont,
  (from < downto)%int = true -> foldi_down_cont (A:=A) (B:=B) f from downto cont = cont.

Axiom foldi_down_cont_eq : forall A B f from downto cont,
  from = downto -> foldi_down_cont (A:=A) (B:=B) f from downto cont = f from cont.

Axiom foldi_down_cont_gt : forall A B f from downto cont,
  (downto < from)%int = true->
  foldi_down_cont (A:=A) (B:=B) f from downto cont =
  f from (fun a' => foldi_down_cont f (from-1) downto cont a').

(** Print *)

Axiom print_int_spec : forall x, x = print_int x.

(** Axioms on operations which are just short cut *)

Axiom compare_def_spec : forall x y, compare x y = compare_def x y.

Axiom head0_spec  : forall x,  0 < [|x|] ->
	 wB/ 2 <= 2 ^ ([|head0 x|]) * [|x|] < wB.

Axiom tail0_spec  : forall x, 0 < [|x|] ->
         (exists y, 0 <= y /\ [|x|] = (2 * y + 1) * (2 ^ [|tail0 x|]))%Z.

Axiom addc_def_spec : forall x y, (x +c y)%int = addc_def x y.

Axiom addcarryc_def_spec : forall x y, addcarryc x y = addcarryc_def x y.

Axiom subc_def_spec : forall x y, (x -c y)%int = subc_def x y.

Axiom subcarryc_def_spec : forall x y, subcarryc x y = subcarryc_def x y.

Axiom diveucl_def_spec : forall x y, diveucl x y = diveucl_def x y.

Axiom diveucl_21_spec :  forall a1 a2 b,
   let (q,r) := diveucl_21 a1 a2 b in
   ([|q|],[|r|]) = Z.div_eucl ([|a1|] * wB + [|a2|]) [|b|].

Axiom addmuldiv_def_spec : forall p x y,
  addmuldiv p x y = addmuldiv_def p x y.


(* 
   Local Variables:
   coq-load-path: ((rec "../../.." "SMTCoq"))
   End: 
*)

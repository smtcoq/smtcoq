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


From Trakt Require Import Trakt.
Require Import Database_trakt.
Require Import ZArith.

Require SMT_classes BVList FArray.


(* Conversion tactic *)

Infix "--->" := implb (at level 60, right associativity) : bool_scope.
Infix "<--->" := Bool.eqb (at level 60, right associativity) : bool_scope.


(* Get all hypotheses of type Prop *)

Ltac get_hyps_option :=
  match goal with
  | H : ?P |- _ =>
    let _ := match goal with _ => revert H end in
    let acc := get_hyps_option in
    let _ := match goal with _ => intro H end in
    let S := type of P in
    lazymatch S with
    | Prop =>
      lazymatch acc with
      | Some ?acc' => constr:(Some (acc',H))
      | None => constr:(Some H)
      end
    | _ => constr:(acc)
    end
  | _ => constr:(@None unit)
  end.


(* Assert global and local hypotheses (local: to avoid problems with Section variables) *)

Ltac pose_hyps Hs acc :=
  lazymatch Hs with
  | (?Hs1, ?Hs2) =>
    let acc1 := pose_hyps Hs1 acc in
    let acc2 := pose_hyps Hs2 acc1 in
    constr:(acc2)
  | ?H' =>
    let H := fresh "H" in
    let _ := match goal with _ => assert (H := H') end in
    lazymatch acc with
    | Some ?acc' => constr:(Some (acc', H))
    | None => constr:(Some H)
    end
  end.

(* Goal True. *)
(*   let Hs := pose_hyps ((@List.nil_cons positive 5%positive nil), (@List.nil_cons N 42%N nil), List.nil_cons) (@None unit) in *)
(*   idtac Hs. *)
(* Abort. *)


(* Get all the hypotheses and the goal *)

Ltac get_context b :=
  match goal with
  | H : ?P |- _ =>
    let _ := match goal with _ => revert H end in
    let acc := get_context b in
    let _ := match goal with _ => intro H end in
    constr:((acc,P))
  | _ => constr:(b)
  end.

Ltac get_context_concl :=
  match goal with
  | |- ?g => get_context g
  end.

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive. *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   let h := get_context_concl in idtac h. *)
(* Abort. *)


(* List of interpreted types *)

Ltac is_interpreted_type T :=
  lazymatch T with
  | BVList.BITVECTOR_LIST.bitvector _ => constr:(true)
  | FArray.farray _ _ => constr:(true)
  | Z => constr:(true) | nat => constr:(true) | positive => constr:(true)
  | bool => constr:(true)
  | _ => constr:(false)
  end.


(* Add CompDec for types over which an equality appears in the goal or
   in a local hypothesis *)

Ltac add_compdecs_term u :=
  match u with
  | context C [@Logic.eq ?t _ _] => 
    let u' := context C [True] in
    lazymatch is_interpreted_type t with
    | true =>
      (* For interpreted types, we need a specific Boolean equality *)
      add_compdecs_term u'
    | false =>
      (* For uninterpreted types, we use CompDec *)
      match goal with
      (* If it is already in the local context, do nothing *)
      | _ : SMT_classes.CompDec t |- _ => add_compdecs_term u'
      (* Otherwise, add it in the local context *)
      | _ =>
        let p := fresh "p" in
        assert (p:SMT_classes.CompDec t);
        [ try (exact _)       (* Use the typeclass machinery *)
        | add_compdecs_term u' ]
      end
    end
  | _ => idtac
  end.

Ltac add_compdecs_terms t :=
  match t with
  | (?t', ?H) =>
    add_compdecs_term H;
    add_compdecs_terms t'
  | ?g => add_compdecs_term g
  end.

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   let h := get_context_concl in add_compdecs_terms h. *)
(*   Show 3. *)
(* Abort. *)


Ltac add_compdecs :=
  let h := get_context_concl in
  add_compdecs_terms h.

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs. *)
(*   Show 3. *)
(* Abort. *)


(* Collect CompDec in local hypotheses *)

Ltac collect_compdecs :=
  match goal with
  | H : SMT_classes.CompDec ?T |- _ =>
    let _ := match goal with _ => change (id (SMT_classes.CompDec T)) in H end in
    let acc := collect_compdecs in
    let _ := match goal with _ => change (SMT_classes.CompDec T) in H end in
    let res :=
        lazymatch is_interpreted_type T with
        | true => constr:(acc)
        | false => constr:((acc, H))
        end
    in
    constr:(res)
  | _ => constr:(unit)
  end.

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs. *)
(*   Focus 3. *)
(*   let cs := collect_compdecs in idtac cs. *)
(* Abort. *)


(* Generate CompDec rels for trakt *)

Ltac generate_rels compdecs :=
  lazymatch compdecs with
  | (?compdecs', ?HA) =>
    let ty := type of HA in
    lazymatch ty with
    | SMT_classes.CompDec ?A =>
      let rel := constr:((@eq A, @SMT_classes.eqb_of_compdec A HA, @SMT_classes.compdec_eq_eqb A HA)) in
      let acc := generate_rels compdecs' in
      lazymatch acc with
      | None => constr:(Some rel)
      | Some ?res => constr:(Some (res, rel))
      end
    end
  | _ => constr:(@None unit)
  end.

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs. *)
(*   Focus 3. *)
(*   let cs := collect_compdecs in *)
(*   let rels := generate_rels cs in *)
(*   idtac rels. *)
(* Abort. *)


(* Use trakt *)

Ltac trakt_rels rels :=
  lazymatch rels with
  | Some ?rels' => trakt Z bool with rel rels'
  | None => trakt Z bool
  end.

Ltac revert_and_trakt Hs rels :=
  lazymatch Hs with
  | (?Hs, ?H) =>
    revert H;
    revert_and_trakt Hs rels
    (* intro H *)
  | ?H =>
    revert H;
    trakt_rels rels
    (* intro H *)
  end.


Definition sep := True.

Ltac get_hyps_upto_sep :=
  lazymatch goal with
  | H' : ?P |- _ =>
    lazymatch P with
    | sep => constr:(@None unit)
    | _ =>
      let T := type of P in
      lazymatch T with
      | Prop =>
        let _ := match goal with _ => revert H' end in
        let acc := get_hyps_upto_sep in
        let _ := match goal with _ => intro H' end in
        lazymatch acc with
        | Some ?acc' => constr:(Some (acc', H'))
        | None => constr:(Some H')
        end
      | _ =>
        let _ := match goal with _ => revert H' end in
        let acc := get_hyps_upto_sep in
        let _ := match goal with _ => intro H' end in
        acc
      end
    end
  end.


(* Goal False -> 1 = 1 -> unit -> false = true -> True. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   assert (H : sep) by exact I. *)
(*   intros H3 H4. *)
(*   let Hs := get_hyps_upto_sep in idtac Hs. *)
(* Abort. *)


Ltac intros_names :=
  let H := fresh in
  let _ := match goal with _ => assert (H : sep) by exact I; intros end in
  let Hs := get_hyps_upto_sep in
  let _ := match goal with _ => clear H end in
  Hs.


(* Goal False -> 1 = 1 -> unit -> false = true -> True. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   let Hs := intros_names in idtac Hs. *)
(* Abort. *)


Ltac post_trakt Hs :=
  lazymatch Hs with
  | (?Hs1, ?Hs2) =>
    post_trakt Hs1;
    post_trakt Hs2
  | ?H => try (revert H; trakt_reorder_quantifiers; trakt_boolify_arrows; intro H)
  end.

Ltac trakt1 rels Hs :=
  lazymatch Hs with
  | Some ?Hs => revert_and_trakt Hs rels
  | None => trakt_rels rels
  end.


(* Section Test. *)
(*   Variables (A:Type) (HA:SMT_classes.CompDec A). *)

(*   Goal forall (a1 a2:A), a1 = a2. *)
(*   Proof. *)
(*     intros a1 a2. *)
(*     trakt Z bool with rel (@eq A, @SMT_classes.eqb_of_compdec A HA, @SMT_classes.compdec_eq_eqb A HA). *)
(*   Abort. *)
(* End Test. *)

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros H. *)
(*   add_compdecs. *)
(*   Focus 3. *)
(*   (* Set Printing All. *) *)
(*   let cs := collect_compdecs in *)
(*   let rels := generate_rels cs in *)
(*   trakt1 rels (Some H). *)
(* Abort. *)


(* Remove quantifications on CompDecs in hypotheses *)

Ltac remove_compdec_hyp H :=
  let TH := type of H in
  match TH with
  | forall p : SMT_classes.CompDec ?A, _ =>
    match goal with
    | [ p' : SMT_classes.CompDec A |- _ ] =>
      let H1 := fresh in
      assert (H1 := H p'); clear H; assert (H := H1); clear H1;
      remove_compdec_hyp H
    | _ =>
      let c := fresh "c" in
      assert (c : SMT_classes.CompDec A);
      [ try (exact _)
      | let H1 := fresh in
        assert (H1 := H c); clear H; assert (H := H1); clear H1;
        remove_compdec_hyp H ]
    end
  | _ => idtac
  end.

Ltac remove_compdec_hyps Hs :=
  lazymatch Hs with
  | (?Hs1, ?Hs2) =>
    remove_compdec_hyps Hs1;
    remove_compdec_hyps Hs2
  | ?H => remove_compdec_hyp H
  end.

Ltac remove_compdec_hyps_option Hs :=
  lazymatch Hs with
  | Some ?Hs => remove_compdec_hyps Hs
  | None => idtac
  end.


(* Perform all the preprocessing *)

Ltac preprocess1 Hs :=
  add_compdecs;
  [ .. |
    remove_compdec_hyps_option Hs;
    let cpds := collect_compdecs in
    let rels := generate_rels cpds in
    trakt1 rels Hs].


(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7) (* /\ 0%N = 0%N *). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   assert (H1 := @List.nil_cons positive 5%positive nil). *)
(*   preprocess1 (Some (H1, H)). *)
(*   Show 3. *)
(* Abort. *)

Ltac preprocess2 Hs' :=
  lazymatch Hs' with
  | Some ?Hs' => post_trakt Hs'
  | None => idtac
  end.

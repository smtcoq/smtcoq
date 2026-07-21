(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


From Stdlib Require Import ZArith.

From Ltac2 Require Import Ltac2.
(* Set Default Proof Mode "Classic". *)

From Trakt Require Import Trakt.

From SMTCoq.utils Require Import CompDec.
From SMTCoq.structures Require Import BVList FArray.

Require Import DatabaseTrakt.



(* Conversion tactic *)

Infix "--->" := implb (at level 60, right associativity) : bool_scope.
Infix "<--->" := Bool.eqb (at level 60, right associativity) : bool_scope.


(* Assert global and local hypotheses (local: to avoid problems with Section variables) *)

Ltac2 pose_hyps_ltac2_aux hs acc id :=
  List.fold_left (
    fun (a, ids) h' =>
      (* Starting from 9.1, the following two lines can be replaced by Fresh.next *)
      let h := Fresh.fresh ids id in
      let ids' := Fresh.Free.union ids (Fresh.Free.of_ids [h]) in
      ltac1:(h h' |- assert (h := h')) (Ltac1.of_ident h) (Ltac1.of_constr h');
      (h::a, ids')
  ) acc hs.

Ltac2 pose_hyps_ltac2 hs acc :=
  match Ident.of_string "H" with
  | Some id =>
      let (r, _) := pose_hyps_ltac2_aux hs (acc, Fresh.Free.of_goal ()) id in
      r
  | None => Control.throw (Tactic_failure (Some (Message.of_string "Error in Conversion.pose_hyps")))
  end.

Goal True.
  let hs := pose_hyps_ltac2 ['(@List.nil_cons positive 5%positive nil); '(@List.nil_cons N 42%N nil); 'List.nil_cons] [] in
  List.iter (fun h => Message.print (Message.of_ident h)) hs.
Abort.


(* List of interpreted types *)

Ltac2 is_interpreted_type ty :=
  lazy_match! ty with
  | BVList.BITVECTOR_LIST.bitvector _ => true
  | FArray.farray _ _ => true
  | Z => true | nat => true | positive => true
  | bool => true
  | _ => false
  end.


(* Add CompDec for types over which an equality appears in the goal or
   in a local hypothesis *)

Ltac2 rec add_compdecs_term u :=
  match! u with
  | context c [@Logic.eq ?t _ _] =>
    let u' := Pattern.instantiate c 'True in
    match is_interpreted_type t with
    | true =>
      (* We skip interpreted types, since they have a dedicated Boolean equality *)
      add_compdecs_term u'
    | false =>
      (* For uninterpreted types, we use CompDec *)
      match! goal with
      (* If it is already in the local context, skip *)
      | [ _ : CompDec.CompDec ?t' |- _ ] =>
          if Constr.equal t t' then add_compdecs_term u' else fail
      (* Otherwise, add it in the local context *)
      | [ |- _ ] =>
          let pid :=
            match Ident.of_string "p" with
            | Some id => id
            | None => Control.throw (Tactic_failure (Some (Message.of_string "Error in Conversion.add_compdecs_term")))
            end
          in
          let p := Fresh.in_goal pid in
          ltac1:(p t |- assert (p: CompDec.CompDec t)) (Ltac1.of_ident p) (Ltac1.of_constr t);
          Control.dispatch [
              (fun () => ltac1:(try (exact _)) (* Use the typeclass machinery *));
              (fun () => add_compdecs_term u')
            ]
      end
    end
  | _ => ()
  end.


Ltac2 rec add_compdecs_rec l :=
  match l with
  | [] => ()
  | u::us =>
      let n := Control.numgoals () in
      Control.focus n n
        (fun () =>
           add_compdecs_term u;
           add_compdecs_rec us
        )
  end.


Ltac2 add_compdecs () :=
  let h := Control.hyps () in
  let h' := Ltac2.List.map (fun icc => let (_, _, c) := icc in c) h in
  let g := Control.goal () in
  add_compdecs_rec (g::h').

(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs (). *)
(*   Show 4. *)
(* Abort. *)


(* Collect CompDec in local hypotheses *)

Ltac2 rec collect_compdecs () :=
  let hs := Control.hyps () in
  let hs' :=
    List.filter (fun (_, _, v) =>
                   match! v with
                   | CompDec.CompDec ?t =>
                       (* Negation in Ltac2? *)
                       if is_interpreted_type t then false else true
                   | _ => false
                   end
      ) hs
  in
  List.map (fun (id, _, v) => (id, v)) hs'.

(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs (). *)
(*   Focus 3. *)
(*   let cs := collect_compdecs () in *)
(*   List.iter (fun (h, v) => Message.print (Message.of_ident h); *)
(*                            Message.print (Message.of_constr v)) cs. *)
(* Abort. *)


(* Generate CompDec rels for trakt *)

From Ltac2 Require Import Constr.
Import Unsafe.

Ltac2 rec generate_rels compdecs :=
  match compdecs with
  | [] => []
  | (ha, ty)::compdecs' =>
      match! ty with
      | CompDec.CompDec ?a =>
          let hac := Control.hyp ha in
          let rel := '(2%nat, @Logic.eq $a, @CompDec.eqb_of_compdec $a $hac, @CompDec.compdec_eq_eqb $a $hac) in
          rel::(generate_rels compdecs')
      end
  end.

(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs (). *)
(*   Focus 3. *)
(*   let cs := collect_compdecs () in *)
(*   let rels := generate_rels cs in *)
(*   List.iter (fun h => Message.print (Message.of_constr h)) rels. *)
(* Abort. *)


(* Use trakt *)

Ltac trakt_rels rels :=
  lazymatch rels with
  | Some ?rels' => first [trakt Z bool with rel rels' | trakt bool with rel rels']
  | None => first [trakt Z bool | trakt bool]
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
(*   Variables (A:Type) (HA:CompDec.CompDec A). *)

(*   Goal forall (a1 a2:A), a1 = a2. *)
(*   Proof. *)
(*     intros a1 a2. *)
(*     trakt Z bool with rel (2%nat, @eq A, @CompDec.eqb_of_compdec A HA, @Classes.compdec_eq_eqb A HA). *)
(*   Abort. *)
(* End Test. *)

(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
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
  | forall p : CompDec.CompDec ?A, _ =>
    match goal with
    | [ p' : CompDec.CompDec A |- _ ] =>
      let H1 := fresh in
      assert (H1 := H p'); clear H; assert (H := H1); clear H1;
      remove_compdec_hyp H
    | _ =>
      let c := fresh "c" in
      assert (c : CompDec.CompDec A);
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
  ltac2:(add_compdecs ());
  [ .. |
    remove_compdec_hyps_option Hs;
    let cpds := collect_compdecs in
    let rels := generate_rels cpds in
    trakt1 rels Hs].


(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
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

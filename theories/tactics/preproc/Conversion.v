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

From SMTCoq.utils Require Import Misc CompDec.
From SMTCoq.structures Require Import BVList FArray CompDecInstances.

Require Import DatabaseTrakt.


(* Section Test. *)
(*   Variables (A:Type) (HA:CompDec.CompDec A). *)

(*   Goal forall (a1 a2:A), a1 = a2. *)
(*   Proof. *)
(*     intros a1 a2. *)
(*     ltac1:(trakt Z bool with rel (2%nat, @Logic.eq A, @CompDec.eqb_of_compdec A HA, @CompDec.compdec_eq_eqb A HA)). *)
(*   Abort. *)
(* End Test. *)


(* Conversion tactic *)

Infix "--->" := implb (at level 60, right associativity) : bool_scope.
Infix "<--->" := Bool.eqb (at level 60, right associativity) : bool_scope.


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
(*   Focus 4. *)
(*   let cs := collect_compdecs () in *)
(*   let rels := generate_rels cs in *)
(*   List.iter (fun h => Message.print (Message.of_constr h)) rels. *)
(* Abort. *)


(* Use trakt *)

Ltac2 trakt_rels rels :=
  match! tupleify rels with
  | Some ?rels' =>
      ltac1:(rels' |- first [trakt Z bool with rel rels' | trakt bool with rel rels'])
              (Ltac1.of_constr rels')
  | None => ltac1:(first [trakt Z bool | trakt bool])
  end.

(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   add_compdecs (). *)
(*   Focus 4. *)
(*   revert H. *)
(*   let cs := collect_compdecs () in *)
(*   let rels := generate_rels cs in *)
(*   trakt_rels rels. *)
(* Abort. *)


(* Remove quantifications on CompDecs in hypotheses *)

Ltac2 rec remove_compdec_hyp name h :=
  let n := Control.numgoals () in
  Control.focus n n (fun () =>
    let hhyp := Control.hyp h in
    let th := Constr.type hhyp in
    match! th with
    | forall p : CompDec.CompDec ?a, _ =>
      match! goal with
      | [ p' : CompDec.CompDec ?a' |- _ ] =>
          if Constr.equal a a' then (
            let idh1 := Fresh.in_goal name in
            ltac1:(h h1 p' |- assert (h1 := h p'); clear h; assert (h := h1); clear h1)
                    (Ltac1.of_ident h) (Ltac1.of_ident idh1) (Ltac1.of_ident p');
            remove_compdec_hyp name h
          ) else (
            fail
          )
      | [ |- _ ] =>
          let c := Fresh.in_goal name in
          ltac1:(c a |- assert (c : CompDec.CompDec a))
                  (Ltac1.of_ident c) (Ltac1.of_constr a);
          Control.dispatch [
            (fun () => ltac1:(try (exact _)));
            (fun () =>
               let idh1 := Fresh.in_goal name in
               ltac1:(h h1 c |- assert (h1 := h c); clear h; assert (h := h1); clear h1)
                       (Ltac1.of_ident h) (Ltac1.of_ident idh1) (Ltac1.of_ident c);
               remove_compdec_hyp name h
            )
          ]
      end
    | _ => ()
    end
  ).

Ltac2 remove_compdec_hyps hs :=
  match Ident.of_string "c" with
  | Some id =>
      List.iter (remove_compdec_hyp id) hs
  | None => Control.throw (Tactic_failure (Some (Message.of_string "Error in Conversion.remove_compdec_hyps")))
  end.

(* Goal forall (A B:Type), CompDec.CompDec A -> *)
(*       (CompDec.CompDec A -> CompDec.CompDec B -> CompDec.CompDec Z -> forall (a:A), a = a) -> *)
(*       (CompDec.CompDec B -> CompDec.CompDec Z -> forall (x:Z), x = x) *)
(*     -> True. *)
(* Proof. *)
(*   intros A B HA H1 H2. *)
(*   remove_compdec_hyps []. *)
(*   remove_compdec_hyps [@H1; @H2]. *)
(*   Show 2. *)
(* Abort. *)


(* Post-processing of Trakt *)

Ltac2 rec post_trakt hs :=
  match hs with
  | [] => ()
  | h::hs =>
      ltac1:(h |- try (revert h; trakt_reorder_quantifiers; trakt_boolify_arrows; intro h)) (Ltac1.of_ident h);
      post_trakt hs
  end.


(* Perform all the preprocessing *)

Ltac2 preprocess1 global :=
  Control.enter (fun () =>
    let local := List.map (fun (id, _) => Control.hyp id) (get_hyps_prop ()) in
    let hsglob := pose_hyps global [] in
    let hs := pose_hyps local hsglob in
    add_compdecs ();
    let n := Control.numgoals () in
    Control.focus n n (fun () =>
      remove_compdec_hyps hs;
      let n := Control.numgoals () in
      Control.focus n n (fun () =>
        let cpds := collect_compdecs () in
        let rels := generate_rels cpds in
        revert_hyps hs;
        trakt_rels rels;
        let hs := intros_and_return_props () in
        post_trakt hs
      )
    )
  ).


(* Goal forall (A B C:Type) (HA:CompDec.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), *)
(*     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 -> *)
(*     17%positive = 42%positive /\ (5,6) = (6,7) (* /\ 0%N = 0%N *). *)
(* Proof. *)
(*   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros. *)
(*   assert (H1 := @List.nil_cons positive 5%positive nil). *)
(*   preprocess1 ['Z.add_0_r]. *)
(*   Show 3. *)
(* Abort. *)

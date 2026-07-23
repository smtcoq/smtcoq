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


From Stdlib Require Import Uint63 List Bool ZArith.
From Trakt Require Import Trakt.
From Ltac2 Require Import Ltac2 Bool.
Set Default Proof Mode "Classic".

From SMTCoq.utils Require Import PArray.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.

Require Import Conversion QInst.

Declare ML Module "rocq-smtcoq.smtcoq".


(** verit tactics *)

Ltac verit_bool_base_auto h := verit_bool_base h; try (exact _).
Ltac verit_bool_no_check_base_auto h := verit_bool_no_check_base h; try (exact _).

Tactic Notation "verit_bool_base_auto_timeout" constr(h) int_or_var(timeout) :=
  verit_bool_base_timeout h timeout; auto with typeclass_instances.
Tactic Notation "verit_bool_no_check_base_auto_timeout" constr(h) int_or_var(timeout) :=
  verit_bool_no_check_base_timeout h timeout; auto with typeclass_instances.


Ltac2 global_of_ltac1_constr h :=
  match Ltac1.to_constr h with
  | Some h => untupleify h
  | None => []
  end.

Ltac2 timeout_of_ltac1_int i :=
  match Ltac1.to_int i with
  | Some t => t
  | None => 0
  end.

Ltac2 verit_call_tactic nocheck timeout r :=
  if nocheck && (Int.equal timeout 0) then
    ltac1:(r |- verit_bool_no_check_base_auto r) (Ltac1.of_constr r)
  else if nocheck && (Int.gt timeout 0) then
    ltac1:(r t |- verit_bool_no_check_base_auto_timeout r t)
            (Ltac1.of_constr r) (Ltac1.of_int timeout)
  else if (neg nocheck) && (Int.equal timeout 0) then
    ltac1:(r |- verit_bool_base_auto r) (Ltac1.of_constr r)
  else if (neg nocheck) && (Int.gt timeout 0) then
    ltac1:(r t |- verit_bool_base_auto_timeout r t)
            (Ltac1.of_constr r) (Ltac1.of_int timeout)
  else
    Control.throw (Tactic_failure (Some (Message.of_string "timeout should be non-negative"))).

Ltac2 verit_tac global inbool nocheck timeout :=
  Control.enter (fun () =>
    ltac1:(intros; unfold is_true in *);
    let local := List.map (fun (id, _) => Control.hyp id) (get_hyps_prop ()) in
    let hsglob := pose_hyps global [] in
    let hs := pose_hyps local hsglob in
    if inbool then (
      let r := tupleify (List.map Control.hyp hs) in
      verit_call_tactic nocheck timeout r
    ) else (
        preprocess1 hs;
        let n := Control.numgoals () in
        Control.focus n n (fun () =>
          let hs' := preprocess2 () in
          let hs' := List.map Control.hyp hs' in
          let r := tupleify hs' in
          verit_call_tactic nocheck timeout r
        )
    );
    ltac1:(QInst.vauto)
  ).


Tactic Notation "verit_bool" constr(h) :=
  let tac := ltac2:(h |- verit_tac (global_of_ltac1_constr h) true false 0) in
  tac h.
Tactic Notation "verit_bool" := ltac2:(verit_tac [] true false 0).
Tactic Notation "verit_bool_no_check" constr(h) :=
  let tac := ltac2:(h |- verit_tac (global_of_ltac1_constr h) true true 0) in
  tac h.
Tactic Notation "verit_bool_no_check" := ltac2:(verit_tac [] true true 0).

Tactic Notation "verit" constr(h) :=
  let tac := ltac2:(h |- verit_tac (global_of_ltac1_constr h) false false 0) in
  tac h.
Tactic Notation "verit" := ltac2:(verit_tac [] false false 0).
Tactic Notation "verit_no_check" constr(h) :=
  let tac := ltac2:(h |- verit_tac (global_of_ltac1_constr h) false true 0) in
  tac h.
Tactic Notation "verit_no_check" := ltac2:(verit_tac [] false true 0).

Tactic Notation "verit_bool_timeout" constr(h) int_or_var(timeout) :=
  let tac := ltac2:(h t |- verit_tac (global_of_ltac1_constr h) true false (timeout_of_ltac1_int t)) in
  tac h timeout.
Tactic Notation "verit_bool_timeout" int_or_var(timeout) :=
  let tac := ltac2:(t |- verit_tac [] true false (timeout_of_ltac1_int t)) in
  tac timeout.
Tactic Notation "verit_bool_no_check_timeout" constr(h) int_or_var (timeout) :=
  let tac := ltac2:(h t |- verit_tac (global_of_ltac1_constr h) true true (timeout_of_ltac1_int t)) in
  tac h timeout.
Tactic Notation "verit_bool_no_check_timeout" int_or_var(timeout) :=
  let tac := ltac2:(t |- verit_tac [] true true (timeout_of_ltac1_int t)) in
  tac timeout.

Tactic Notation "verit_timeout" constr(h) int_or_var(timeout) :=
  let tac := ltac2:(h t |- verit_tac (global_of_ltac1_constr h) false false (timeout_of_ltac1_int t)) in
  tac h timeout.
Tactic Notation "verit_timeout" int_or_var(timeout) :=
  let tac := ltac2:(t |- verit_tac [] false false (timeout_of_ltac1_int t)) in
  tac timeout.
Tactic Notation "verit_no_check_timeout" constr(h) int_or_var (timeout) :=
  let tac := ltac2:(h t |- verit_tac (global_of_ltac1_constr h) false true (timeout_of_ltac1_int t)) in
  tac h timeout.
Tactic Notation "verit_no_check_timeout" int_or_var(timeout) :=
  let tac := ltac2:(t |- verit_tac [] false true (timeout_of_ltac1_int t)) in
  tac timeout.


(* (** Tactics in Prop **) *)

(* Ltac zchaff          := trakt bool; Tactics.zchaff_bool. *)
(* Ltac zchaff_no_check := trakt bool; Tactics.zchaff_bool_no_check. *)


(* (* CVC4 *) *)
(* From SMTCoq.tactics.preproc Require Import ReflectFacts. *)

(* Ltac prop2boolImp := *)
(*   repeat *)
(*     match goal with *)
(*     | [ |- context[?G0 = true -> ?G1 = true ] ] => *)
(*         rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1)); *)
(*         [ | apply implyP] *)
(*     end. *)

(* Tactic Notation "cvc4"          := *)
(*   ltac2:(intros; unfold is_true in *; get_hyps_cont_ltac1 ltac1:(local |- *)
(*   let Hs := *)
(*       lazymatch local with *)
(*       | Some ?local' => pose_hyps local' (@None unit) *)
(*       | None => constr:(@None unit) *)
(*       end *)
(*   in *)
(*   preprocess1 Hs; *)
(*   [ .. | *)
(*     prop2boolImp; *)
(*     cvc4_bool *)
(*   ])). *)

(* Tactic Notation "cvc4_no_check" := *)
(*   ltac2:(intros; unfold is_true in *; get_hyps_cont_ltac1 ltac1:(local |- *)
(*   let Hs := *)
(*       lazymatch local with *)
(*       | Some ?local' => pose_hyps local' (@None unit) *)
(*       | None => constr:(@None unit) *)
(*       end *)
(*   in *)
(*   preprocess1 Hs; *)
(*   [ .. | *)
(*     prop2boolImp; *)
(*     cvc4_bool_no_check *)
(*   ])). *)

(* Tactic Notation "smt" constr(h) := try verit h; cvc4; try verit h. *)
(* Tactic Notation "smt"           := try verit  ; cvc4; try verit. *)
(* Tactic Notation "smt_no_check" constr(h) := *)
(*   try verit_no_check h; cvc4_no_check; try verit_no_check h. *)
(* Tactic Notation "smt_no_check"           := *)
(*   try verit_no_check  ; cvc4_no_check; try verit_no_check. *)

(* Tactic Notation "abduce" int_or_var(i) := *)
(*   let tac := *)
(*   ltac2:(i |- intros; unfold is_true in *; get_hyps_cont_ltac1 *)
(*   (ltac1:(i local |- *)
(*   let Hs := *)
(*       lazymatch local with *)
(*       | Some ?local' => pose_hyps local' (@None unit) *)
(*       | None => constr:(@None unit) *)
(*       end *)
(*   in *)
(*   preprocess1 Hs; *)
(*   [ .. | *)
(*     let Hs' := intros_names in *)
(*     preprocess2 Hs'; *)
(*     cvc5_bool_abduct i Hs'; *)
(*     QInst.vauto *)
(*   ]) i)) in tac i. *)

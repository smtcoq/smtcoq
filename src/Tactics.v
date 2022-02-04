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
Require Import Conversion.
Require Import Int63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.

Declare ML Module "smtcoq_plugin".


Ltac zchaff          := trakt Z bool; Tactics.zchaff_bool.
Ltac zchaff_no_check := trakt Z bool; Tactics.zchaff_bool_no_check.

Tactic Notation "verit_bool_base_auto" constr(h) := verit_bool_base h; try (exact _).
Tactic Notation "verit_bool_no_check_base_auto" constr(h) := verit_bool_no_check_base h; try (exact _).

Tactic Notation "verit" constr(global) :=
  intros;
  unfold is_true in *;
  let Hsglob := pose_hyps global (@None unit) in
  let local := get_hyps_option in
  let Hs :=
      lazymatch local with
      | Some ?local' => pose_hyps local' Hsglob
      | None => constr:(Hsglob)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := intros_names in
    preprocess2 Hs';
    verit_bool_base_auto Hs';
    QInst.vauto
  ].

Tactic Notation "verit"           :=
  intros;
  unfold is_true in *;
  let local := get_hyps_option in
  let Hs :=
      lazymatch local with
      | Some ?local' => pose_hyps local' (@None unit)
      | None => constr:(@None unit)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := intros_names in
    preprocess2 Hs';
    verit_bool_base_auto Hs';
    QInst.vauto
  ].

Tactic Notation "verit_no_check" constr(global) :=
  intros;
  unfold is_true in *;
  let Hsglob := pose_hyps global (@None unit) in
  let local := get_hyps_option in
  let Hs :=
      lazymatch local with
      | Some ?local' => pose_hyps local' Hsglob
      | None => constr:(Hsglob)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := intros_names in
    preprocess2 Hs';
    verit_bool_no_check_base_auto Hs';
    QInst.vauto
  ].

Tactic Notation "verit_no_check"           :=
  intros;
  unfold is_true in *;
  let local := get_hyps_option in
  let Hs :=
      lazymatch local with
      | Some ?local' => pose_hyps local' (@None unit)
      | None => constr:(@None unit)
      end
  in
  preprocess1 Hs;
  [ .. |
    let Hs' := intros_names in
    preprocess2 Hs';
    verit_bool_no_check_base_auto Hs';
    QInst.vauto
  ].

Ltac cvc4            := trakt Z bool; [ .. | cvc4_bool ].
Ltac cvc4_no_check   := trakt Z bool; [ .. | cvc4_bool_no_check ].

Tactic Notation "smt" constr(h) := intros; try verit h; cvc4; try verit h.
Tactic Notation "smt"           := intros; try verit  ; cvc4; try verit.
Tactic Notation "smt_no_check" constr(h) :=
  intros; try verit_no_check h; cvc4_no_check; try verit_no_check h.
Tactic Notation "smt_no_check"           :=
  intros; try verit_no_check  ; cvc4_no_check; try verit_no_check.




(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

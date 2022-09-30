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


From Trakt Require Import Trakt.
Require Import Conversion.
Require Import Uint63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.

Declare ML Module "smtcoq_plugin".


(* Collect all the hypotheses from the context *)

Ltac get_hyps_acc acc :=
  match goal with
  | [ H : ?P |- _ ] =>
    let T := type of P in
    lazymatch T with
    | Prop =>
      lazymatch P with
      | id _ => fail
      | _ =>
        let _ := match goal with _ => change P with (id P) in H end in
        lazymatch acc with
        | Some ?t => get_hyps_acc (Some (H, t))
        | None => get_hyps_acc (Some H)
        end
      end
    | _ => fail
    end
  | _ => acc
  end.

Ltac eliminate_id :=
  repeat match goal with
  | [ H : ?P |- _ ] =>
    lazymatch P with
    | id ?Q => change P with Q in H
    | _ => fail
    end
  end.

Ltac get_hyps :=
  let Hs := get_hyps_acc (@None nat) in
  let _ := match goal with _ => eliminate_id end in
  Hs.


(** Tactics in bool *)

Tactic Notation "verit_bool_base_auto" constr(h) := verit_bool_base h; try (exact _).
Tactic Notation "verit_bool_no_check_base_auto" constr(h) := verit_bool_no_check_base h; try (exact _).

Tactic Notation "verit_bool" constr(h) :=
  let Hs := get_hyps in
  match Hs with
  | Some ?Hs => verit_bool_base_auto (Some (h, Hs))
  | None => verit_bool_base_auto (Some h)
  end;
  vauto.
Tactic Notation "verit_bool"           :=
  let Hs := get_hyps in
  verit_bool_base_auto Hs; vauto.

Tactic Notation "verit_bool_no_check" constr(h) :=
  let Hs := get_hyps in
  match Hs with
  | Some ?Hs => verit_bool_no_check_base_auto (Some (h, Hs))
  | None => verit_bool_no_check_base_auto (Some h)
  end;
  vauto.
Tactic Notation "verit_bool_no_check"           :=
  let Hs := get_hyps in
  fun Hs => verit_bool_no_check_base_auto Hs; vauto.


(** Tactics in bool with timeout **)

Tactic Notation "verit_bool_base_auto_timeout" constr(h) int_or_var(timeout) := verit_bool_base_timeout h timeout; auto with typeclass_instances.
Tactic Notation "verit_bool_no_check_base_auto_timeout" constr(h) int_or_var(timeout) := verit_bool_no_check_base_timeout h timeout; auto with typeclass_instances.

Tactic Notation "verit_bool_timeout" constr(h) int_or_var(timeout) :=
  let Hs := get_hyps in
  match Hs with
  | Some ?Hs => verit_bool_base_auto_timeout (Some (h, Hs)) timeout
  | None => verit_bool_base_auto_timeout (Some h) timeout
  end;
  vauto.
Tactic Notation "verit_bool_timeout"  int_or_var(timeout)         :=
  let Hs := get_hyps in
  verit_bool_base_auto_timeout Hs timeout; vauto.

Tactic Notation "verit_bool_no_check_timeout" constr(h) int_or_var (timeout) :=
  let Hs := get_hyps in
  match Hs with
  | Some ?Hs => verit_bool_no_check_base_auto_timeout (Some (h, Hs)) timeout
  | None => verit_bool_no_check_base_auto_timeout (Some h) timeout
  end;
  vauto.
Tactic Notation "verit_bool_no_check_timeout"   int_or_var(timeout)        :=
  let Hs := get_hyps in
  verit_bool_no_check_base_auto_timeout Hs timeout; vauto.


(** Tactics in Prop **)

Ltac zchaff          := trakt Z bool; Tactics.zchaff_bool.
Ltac zchaff_no_check := trakt Z bool; Tactics.zchaff_bool_no_check.

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

Tactic Notation "verit_timeout" constr(global) int_or_var(timeout) :=
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
    verit_bool_base_auto_timeout Hs' timeout;
    QInst.vauto
  ].

Tactic Notation "verit_timeout"           int_or_var(timeout) :=
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
    verit_bool_base_auto_timeout Hs' timeout;
    QInst.vauto
  ].

Tactic Notation "verit_no_check_timeout" constr(global) int_or_var(timeout) :=
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
    verit_bool_no_check_base_auto_timeout Hs' timeout;
    QInst.vauto
  ].

Tactic Notation "verit_no_check_timeout"           int_or_var(timeout) :=
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
    verit_bool_no_check_base_auto_timeout Hs' timeout;
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

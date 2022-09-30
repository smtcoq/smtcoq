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


Require Import PropToBool.
Require Import Uint63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.

Declare ML Module "smtcoq_plugin".


(** Collect all the hypotheses from the context *)

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


(* Section Test. *)
(*   Variable A : Type. *)
(*   Hypothesis H1 : forall a:A, a = a. *)
(*   Variable n : Z. *)
(*   Hypothesis H2 : n = 17%Z. *)

(*   Goal True. *)
(*   Proof. *)
(*     let Hs := get_hyps in idtac Hs. *)
(*   Abort. *)
(* End Test. *)


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

Ltac zchaff          := add_compdecs; [ .. | prop2bool; zchaff_bool; bool2prop ].
Ltac zchaff_no_check := add_compdecs; [ .. | prop2bool; zchaff_bool_no_check; bool2prop].

Tactic Notation "verit" constr(h) :=
  intros;
  let Hs := get_hyps in
  let Hs :=
    lazymatch Hs with
    | Some ?Hs => constr:(Some (h, Hs))
    | None => constr:(Some h)
    end
  in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_base_auto Hs; vauto ]
  ].
Tactic Notation "verit"           :=
  intros;
  let Hs := get_hyps in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_base_auto Hs; vauto ]
  ].
Tactic Notation "verit_no_check" constr(h) :=
  intros;
  let Hs := get_hyps in
  let Hs :=
    lazymatch Hs with
    | Some ?Hs => constr:(Some (h, Hs))
    | None => constr:(Some h)
    end
  in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_no_check_base_auto Hs; vauto ]
  ].
Tactic Notation "verit_no_check"           :=
  intros;
  let Hs := get_hyps in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_no_check_base_auto Hs; vauto ]
  ].

Tactic Notation "verit_timeout" constr(h) int_or_var(timeout) :=
  intros;
  let Hs := get_hyps in
  let Hs :=
    lazymatch Hs with
    | Some ?Hs => constr:(Some (h, Hs))
    | None => constr:(Some h)
    end
  in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_base_auto_timeout Hs timeout; vauto ]
  ].
Tactic Notation "verit_timeout"           int_or_var(timeout) :=
  intros;
  let Hs := get_hyps in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_base_auto_timeout Hs timeout; vauto ]
  ].
Tactic Notation "verit_no_check_timeout" constr(h) int_or_var(timeout) :=
  intros;
  let Hs := get_hyps in
  let Hs :=
    lazymatch Hs with
    | Some ?Hs => constr:(Some (h, Hs))
    | None => constr:(Some h)
    end
  in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_no_check_base_auto_timeout Hs timeout; vauto ]
  ].
Tactic Notation "verit_no_check_timeout"           int_or_var(timeout) :=
  intros;
  let Hs := get_hyps in
  add_compdecs Hs;
  [ .. | prop2bool;
         lazymatch Hs with
         | Some ?Hs => prop2bool_hyps Hs
         | None => idtac
         end;
         [ .. | verit_bool_no_check_base_auto_timeout Hs timeout; vauto ]
  ].

Ltac cvc4            := add_compdecs; [ .. | prop2bool; cvc4_bool; bool2prop ].
Ltac cvc4_no_check   := add_compdecs; [ .. | prop2bool; cvc4_bool_no_check; bool2prop ].

Tactic Notation "smt" constr(h) :=
  add_compdecs; [ .. | prop2bool; try verit h; cvc4_bool; try verit h; bool2prop ].
Tactic Notation "smt"           :=
  add_compdecs; [ .. | prop2bool; try verit  ; cvc4_bool; try verit  ; bool2prop ].
Tactic Notation "smt_no_check" constr(h) :=
  add_compdecs; [ .. | prop2bool; try verit_no_check h; cvc4_bool_no_check; try verit_no_check h; bool2prop].
Tactic Notation "smt_no_check"           :=
  add_compdecs; [ .. | prop2bool; try verit_no_check  ; cvc4_bool_no_check; try verit_no_check  ; bool2prop].


(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

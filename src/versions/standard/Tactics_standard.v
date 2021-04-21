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


Require Import PropToBool.
Require Import Int63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.

Declare ML Module "smtcoq_plugin".


Tactic Notation "verit_bool" constr(h) := verit_bool_base (Some h); vauto.
Tactic Notation "verit_bool"           := verit_bool_base (@None nat); vauto.

Tactic Notation "verit_bool_no_check" constr(h) := verit_bool_no_check_base (Some h); vauto.
Tactic Notation "verit_bool_no_check"           := verit_bool_no_check_base (@None nat); vauto.


(** Tactics in Prop **)

Ltac zchaff          := prop2bool; zchaff_bool; bool2prop.
Ltac zchaff_no_check := prop2bool; zchaff_bool_no_check; bool2prop.

Tactic Notation "verit" constr(h) := prop2bool; [ .. | prop2bool_hyps h; [ .. | verit_bool h; bool2prop ] ].
Tactic Notation "verit"           := prop2bool; [ .. | verit_bool  ; bool2prop ].
Tactic Notation "verit_no_check" constr(h) := prop2bool; [ .. | prop2bool_hyps h; [ .. | verit_bool_no_check h; bool2prop ] ].
Tactic Notation "verit_no_check"           := prop2bool; [ .. | verit_bool_no_check  ; bool2prop ].

Ltac cvc4            := prop2bool; [ .. | cvc4_bool; bool2prop ].
Ltac cvc4_no_check   := prop2bool; [ .. | cvc4_bool_no_check; bool2prop ].

Tactic Notation "smt" constr(h) := (prop2bool; [ .. | try (prop2bool_hyps h; [ .. | verit_bool h ]); cvc4_bool; try (prop2bool_hyps h; [ .. | verit_bool h ]); bool2prop ]).
Tactic Notation "smt"           := (prop2bool; [ .. | try verit_bool  ; cvc4_bool; try verit_bool  ; bool2prop ]).
Tactic Notation "smt_no_check" constr(h) := (prop2bool; [ .. | try (prop2bool_hyps h; [ .. | verit_bool_no_check h ]); cvc4_bool_no_check; try (prop2bool_hyps h; [ .. | verit_bool_no_check h ]); bool2prop]).
Tactic Notation "smt_no_check"           := (prop2bool; [ .. | try verit_bool_no_check  ; cvc4_bool_no_check; try verit_bool_no_check  ; bool2prop]).



(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

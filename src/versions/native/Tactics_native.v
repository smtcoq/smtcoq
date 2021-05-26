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


Require Import Psatz.

Declare ML Module "smtcoq_plugin".



Tactic Notation "verit_bool" constr_list(h) :=
  fail "Tactics are not supported with native-coq".

Tactic Notation "verit_bool_no_check" constr_list(h) :=
  fail "Tactics are not supported with native-coq".


(** Tactics in Prop **)

Ltac zchaff          :=
  fail "Tactics are not supported with native-coq".
Ltac zchaff_no_check :=
  fail "Tactics are not supported with native-coq".

Tactic Notation "verit" constr_list(h) :=
  fail "Tactics are not supported with native-coq".
Tactic Notation "verit_no_check" constr_list(h) :=
  fail "Tactics are not supported with native-coq".

Ltac cvc4            :=
  fail "Tactics are not supported with native-coq".
Ltac cvc4_no_check   :=
  fail "Tactics are not supported with native-coq".


Tactic Notation "smt" constr_list(h) :=
  fail "Tactics are not supported with native-coq".
Tactic Notation "smt_no_check" constr_list(h) :=
  fail "Tactics are not supported with native-coq".



(* 
   Local Variables:
   coq-load-path: ((rec "../.." "SMTCoq"))
   End: 
*)

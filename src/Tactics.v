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
Require Import Int63 List PArray Bool ZArith.
Require Import SMTCoq.State SMTCoq.SMT_terms SMTCoq.Trace SMT_classes_instances QInst.
From Ltac2 Require Import Ltac2.

Declare ML Module "smtcoq_plugin".

(** A printer for testing Ltac2 functions returning hypothesis *)

Ltac2 rec hyps_printer (h : (ident * constr option * constr) list) 
:=
match h with
| [] => ()
| x :: xs => match x with
            | (id, opt, cstr) => 
let () := Message.print (Message.concat (Message.of_ident id)
                                        (Message.concat (Message.of_string " : ")
                                                        (Message.of_constr cstr))) 
in hyps_printer xs
end 
end.


(* Collect all the hypotheses from the context *)

Ltac2 get_hyps_aux () :=
let h := Control.hyps () in
List.filter (fun x => match x with
                    | (id, opt, c) => let ty := Constr.type c in Constr.equal ty '(Prop)
                    end) h.

Ltac2 get_hyps_ltac2 () :=
let hs := get_hyps_aux () in
match hs with
| [] => '(@None nat)
| x :: xs => 
    match x with
    | (id, opt, c) => 
    let h := Control.hyp id in
    let rec tac_aux xs acc :=
      match xs with
      | y :: ys => 
        match y with
        | (id', opt', c') => 
        let h1 := Control.hyp id' in let res := tac_aux ys acc in '($h1, $res)
        end
      | [] => acc
      end in let res := tac_aux xs h in '(Some ($res))
  end
end. 

Ltac2 get_hyps_cont_ltac1 (tac : Ltac1.t -> unit) := 
Control.enter (fun () =>
let hs := Ltac1.of_constr (get_hyps_ltac2 ()) in
tac hs).

(*
Section Test.
Variable A : Type.
Hypothesis H1 : forall a:A, a = a.
Variable n : Z.
Hypothesis H2 : n = 17%Z.

Goal True.
Proof.
let hs := get_hyps_aux () in hyps_printer hs. 
let hs := get_hyps_ltac2 () in Message.print (Message.of_constr hs).
get_hyps_cont_ltac1 ltac1:(H |- idtac H).
Abort.

Goal True.
Proof. clear A H1 n H2.
let hs := get_hyps_aux () in hyps_printer hs. 
let hs := get_hyps () in Message.print (Message.of_constr hs).
Abort.
End Test.  *)



(** Tactics in bool *)

Tactic Notation "verit_bool_base_auto" constr(h) := verit_bool_base h; try (exact _).
Tactic Notation "verit_bool_no_check_base_auto" constr(h) := verit_bool_no_check_base h; try (exact _).

Tactic Notation "verit_bool" constr(h) :=
  let tac :=
  ltac2:(h |- get_hyps_cont_ltac1
  (ltac1:(h hs |- 
  match hs with
  | Some ?hs => verit_bool_base_auto (Some (h, hs))
  | None => verit_bool_base_auto (Some h)
  end;
  vauto) h)) in tac h.

Tactic Notation "verit_bool" :=
  ltac2:(get_hyps_cont_ltac1 ltac1:(hs |- verit_bool_base_auto hs; vauto)).

Tactic Notation "verit_bool_no_check" constr(h) :=
  let tac :=
  ltac2:(h |- get_hyps_cont_ltac1 (ltac1:(h hs |-
  match hs with
  | Some ?hs => verit_bool_no_check_base_auto (Some (h, hs))
  | None => verit_bool_no_check_base_auto (Some h)
  end;
  vauto) h)) in tac h.

Tactic Notation "verit_bool_no_check" :=
  ltac2:(get_hyps_cont_ltac1 ltac1:(hs |- verit_bool_no_check_base_auto hs; vauto)).


(** Tactics in bool with timeout **)

Tactic Notation "verit_bool_base_auto_timeout" constr(h) int_or_var(timeout) := verit_bool_base_timeout h timeout; auto with typeclass_instances.
Tactic Notation "verit_bool_no_check_base_auto_timeout" constr(h) int_or_var(timeout) := verit_bool_no_check_base_timeout h timeout; auto with typeclass_instances.

Tactic Notation "verit_bool_timeout" constr(h) int_or_var(timeout) :=
  let tac :=
  ltac2:(h timeout |- get_hyps_cont_ltac1
  (ltac1:(h timeout hs |- 
  match hs with
  | Some ?hs => verit_bool_base_auto_timeout (Some (h, hs)) timeout
  | None => verit_bool_base_auto_timeout (Some h) timeout
  end;
  vauto) h timeout)) in tac h timeout.

Tactic Notation "verit_bool_timeout" int_or_var(timeout) :=
  let tac :=
  ltac2:(timeout |- get_hyps_cont_ltac1 (ltac1:(timeout hs |- verit_bool_base_auto_timeout hs timeout; vauto) timeout))
  in tac timeout.

Tactic Notation "verit_bool_no_check_timeout" constr(h) int_or_var (timeout) :=
  let tac :=
  ltac2:(h timeout |- get_hyps_cont_ltac1
  (ltac1:(h timeout hs |- 
  match hs with
  | Some ?hs => verit_bool_no_check_base_auto_timeout (Some (h, hs)) timeout
  | None => verit_bool_no_check_base_auto_timeout (Some h) timeout
  end;
  vauto) h timeout)) in tac h timeout.

Tactic Notation "verit_bool_no_check_timeout"   int_or_var(timeout)        :=
  let tac :=
  ltac2:(timeout |- get_hyps_cont_ltac1 (ltac1:(timeout hs |- verit_bool_no_check_base_auto_timeout hs timeout; vauto) timeout))
  in tac timeout.



(** Tactics in Prop **)

Ltac zchaff          := trakt bool; Tactics.zchaff_bool.
Ltac zchaff_no_check := trakt bool; Tactics.zchaff_bool_no_check.

Tactic Notation "verit" constr(global) :=
  let tac :=
  ltac2:(h |- intros; unfold is_true in *; get_hyps_cont_ltac1
  (ltac1:(h local |-
  let Hsglob := pose_hyps h (@None unit) in
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
  ]) h)) in tac global.

Tactic Notation "verit"           :=
  ltac2:(intros; unfold is_true in *; get_hyps_cont_ltac1 ltac1:(local |-
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
  ])).

Tactic Notation "verit_no_check" constr(global) :=
  let tac :=
  ltac2:(h |- intros; unfold is_true in *; get_hyps_cont_ltac1 (ltac1:(h local |-
  let Hsglob := pose_hyps h (@None unit) in
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
  ]) h)) in tac global.

Tactic Notation "verit_no_check"           :=
  ltac2:(intros; unfold is_true in *; get_hyps_cont_ltac1 ltac1:(local |-
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
  ])).

Tactic Notation "verit_timeout" constr(global) int_or_var(timeout) :=
  let tac :=
  ltac2:(h timeout |- intros; unfold is_true in *; get_hyps_cont_ltac1
  (ltac1:(h timeout local |-
  let Hsglob := pose_hyps h (@None unit) in
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
  ]) h timeout)) in tac global timeout.

Tactic Notation "verit_timeout"           int_or_var(timeout) :=
  let tac :=
  ltac2:(timeout |- intros; unfold is_true in *; get_hyps_cont_ltac1
  (ltac1:(timeout local |-
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
  ]) timeout)) in tac timeout.

Tactic Notation "verit_no_check_timeout" constr(global) int_or_var(timeout) :=
  let tac :=
  ltac2:(h timeout |- intros; unfold is_true in *; get_hyps_cont_ltac1
  (ltac1:(h timeout local |-
  let Hsglob := pose_hyps h (@None unit) in
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
  ]) h timeout)) in tac global timeout.

Tactic Notation "verit_no_check_timeout"           int_or_var(timeout) :=
  let tac :=
  ltac2:(timeout |- intros; unfold is_true in *; get_hyps_cont_ltac1
  (ltac1:(timeout local |-
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
  ]) timeout)) in tac timeout.


(* CVC4 *)
Require Import ReflectFacts.

Ltac prop2boolImp :=
  repeat
    match goal with
    | [ |- context[?G0 = true -> ?G1 = true ] ] =>
        rewrite (@reflect_iff (G0 = true -> G1 = true) (implb G0 G1));
        [ | apply implyP]
    end.

Tactic Notation "cvc4"          :=
  ltac2:(intros; unfold is_true in *; get_hyps_cont_ltac1 ltac1:(local |-
  let Hs :=
      lazymatch local with
      | Some ?local' => pose_hyps local' (@None unit)
      | None => constr:(@None unit)
      end
  in
  preprocess1 Hs;
  [ .. |
    prop2boolImp;
    cvc4_bool
  ])).

Tactic Notation "cvc4_no_check" :=
  ltac2:(intros; unfold is_true in *; get_hyps_cont_ltac1 ltac1:(local |-
  let Hs :=
      lazymatch local with
      | Some ?local' => pose_hyps local' (@None unit)
      | None => constr:(@None unit)
      end
  in
  preprocess1 Hs;
  [ .. |
    prop2boolImp;
    cvc4_bool_no_check
  ])).

Tactic Notation "smt" constr(h) := try verit h; cvc4; try verit h.
Tactic Notation "smt"           := try verit  ; cvc4; try verit.
Tactic Notation "smt_no_check" constr(h) :=
  try verit_no_check h; cvc4_no_check; try verit_no_check h.
Tactic Notation "smt_no_check"           :=
  try verit_no_check  ; cvc4_no_check; try verit_no_check.

Tactic Notation "abduce" int_or_var(i) :=
  let tac :=
  ltac2:(i |- intros; unfold is_true in *; get_hyps_cont_ltac1
  (ltac1:(i local |-
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
    cvc5_bool_abduct i Hs';
    QInst.vauto
  ]) i)) in tac i.


(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

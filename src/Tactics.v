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


(** Collect all the hypotheses from the context *)

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
let hs := Ltac1.of_constr (get_hyps_ltac2 ()) in
tac hs.

(* Section Test.
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

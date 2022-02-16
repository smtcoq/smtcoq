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


Require Import Int63.

Require Import List.


Section Trace.

  Definition trace (step:Type) := ((list step) * step)%type.

  Definition trace_to_list {step:Type} (t:trace step) : list step :=
    let (t, _) := t in t.

  Definition trace_length {step:Type} (t:trace step) : int :=
    let (t,_) := t in
    List.fold_left (fun i _ => (i+1)%int) t 0%int.

  Fixpoint trace_get_aux {step:Type} (t:list step) (def:step) (i:int) : step :=
    match t with
    | nil => def
    | s::ss =>
      if (i == 0)%int then
        s
      else
        trace_get_aux ss def (i-1)
    end.
  Definition trace_get {step:Type} (t:trace step) : int -> step :=
    let (t,def) := t in trace_get_aux t def.

  Definition trace_fold {state step:Type} (transition: state -> step -> state) (s0:state) (t:trace step) :=
    let (t,_) := t in
    List.fold_left transition t s0.

  Lemma trace_fold_ind (state step : Type) (P : state -> Prop) (transition : state -> step -> state) (t : trace step)
      (IH: forall (s0 : state) (i : int), (i < trace_length t)%int = true -> P s0 -> P (transition s0 (trace_get t i))) :
      forall s0 : state, P s0 -> P (trace_fold transition s0 t).
  Admitted.

End Trace.


Require Import PeanoNat.

Definition nat_eqb := Nat.eqb.
Definition nat_eqb_eq := Nat.eqb_eq.
Definition nat_eqb_refl := Nat.eqb_refl.


(*
   Local Variables:
   coq-load-path: ((rec "../.." "SMTCoq"))
   End:
*)

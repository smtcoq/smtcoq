(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*       from the Int63 library of native-coq                             *)
(*       by Benjamin Gregoire and Laurent Thery                           *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* Add LoadPath "." as SMTCoq.Int63.standard.versions. *)
Require Export DoubleType.
Require Import Int31 Cyclic31 Ring31.
Require Import ZArith.
Require Import Bool.


Definition size := size.

Notation int := int31.

Delimit Scope int63_scope with int.
Bind Scope int63_scope with int.

(* Some constants *)
Notation "0" := 0%int31 : int63_scope.
Notation "1" := 1%int31 : int63_scope.
Notation "2" := 2%int31 : int63_scope.
Notation "3" := 3%int31 : int63_scope.

(* Logical operations *)
Definition lsl : int -> int -> int :=
  fun i j => nshiftl i (N.to_nat (Z.to_N (phi j))).
Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Definition lsr : int -> int -> int :=
  fun i j => nshiftr i (N.to_nat (Z.to_N (phi j))).
Infix ">>" := lsr (at level 30, no associativity) : int63_scope.

(* For the bitwise operations, I add a useless pattern matching to avoid
   too much unfolding of their definitions at Qed (since Qed bypasses
   the Opaque declaration) *)
Definition land : int -> int -> int :=
  fun i => match i with
  | 0%int31 | _ => fun j =>
    recrbis _ j (fun d _ acc =>
                   let r := acc in
                   let d' := firstl r in
                   let dr := match d, d' with | D1, D1 => D1 | _, _ => D0 end in
                   sneakl dr r
                ) i
           end.
Global Arguments land i j : simpl never.
Global Opaque land.
Infix "land" := land (at level 40, left associativity) : int63_scope.

Definition lor : int -> int -> int :=
  fun i => match i with
  | 0%int31 | _ => fun j =>
    recrbis _ j (fun d _ acc =>
                   let r := acc in
                   let d' := firstl r in
                   let dr := match d, d' with | D0, D0 => D0 | _, _ => D1 end in
                   sneakl dr r
                ) i
           end.
Global Arguments lor i j : simpl never.
Global Opaque lor.
Infix "lor" := lor (at level 40, left associativity) : int63_scope.

Definition lxor : int -> int -> int :=
  fun i => match i with
  | 0%int31 | _ => fun j =>
    recrbis _ j (fun d _ acc =>
                   let r := acc in
                   let d' := firstl r in
                   let dr := match d, d' with | D0, D0 | D1, D1 => D0 | _, _ => D1 end in
                   sneakl dr r
                ) i
           end.
Global Arguments lxor i j : simpl never.
Global Opaque lxor.
Infix "lxor" := lxor (at level 40, left associativity) : int63_scope.

(* Arithmetic modulo operations *)
(* Definition add : int -> int -> int := add63. *)
(* Notation "n + m" := (add n m) : int63_scope. *)
Notation "n + m" := (add31 n m) : int63_scope.

(* Definition sub : int -> int -> int := sub63. *)
(* Notation "n - m" := (sub n m) : int63_scope. *)
Notation "n - m" := (sub31 n m) : int63_scope.

(* Definition mul : int -> int -> int := mul63. *)
(* Notation "n * m" := (mul n m) : int63_scope. *)
Notation "n * m" := (mul31 n m) : int63_scope.

Definition mulc : int -> int -> int * int :=
  fun i j => match mul31c i j with
               | W0 => (0%int, 0%int)
               | WW h l => (h, l)
             end.

Definition div : int -> int -> int :=
  fun i j => let (q,_) := div31 i j in q.
Notation "n / m" := (div n m) : int63_scope.

Definition modulo : int -> int -> int :=
  fun i j => let (_,r) := div31 i j in r.
Notation "n '\%' m" := (modulo n m) (at level 40, left associativity) : int63_scope.

(* Comparisons *)
Definition eqb := eqb31.
Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

Definition ltb : int -> int -> bool :=
  fun i j => match compare31 i j with | Lt => true | _ => false end.
Notation "m < n" := (ltb m n) : int63_scope.

Definition leb : int -> int -> bool :=
  fun i j => match compare31 i j with | Gt => false | _ => true end.
Notation "m <= n" := (leb m n) : int63_scope.


(* TODO: fill this proof (should be in the stdlib) *)
Lemma eqb_correct : forall i j, (i==j)%int = true -> i = j.
Admitted.


(* Iterators *)

Definition foldi_cont
     {A B     : Type}
     (f       : int -> (A -> B) -> A -> B)
     (from to : int)
     (cont    : A -> B)                      : A -> B :=
  if ltb to from then
    cont
  else
    let (_,r) := iter_int31 (to - from) _ (fun (jy: (int * (A -> B))%type) =>
                     let (j,y) := jy in ((j-1)%int, f j y)
                                      ) (to, cont) in
    f from r.

Definition foldi_down_cont
    {A B         : Type}
    (f           : int -> (A -> B) -> A -> B)
    (from downto : int)
    (cont        : A -> B)                      : A -> B :=
  if ltb from downto then
    cont
  else
    let (_,r) := iter_int31 (from - downto) _ (fun (jy: (int * (A -> B))%type) =>
                     let (j,y) := jy in ((j+1)%int, f j y)
                                      ) (downto, cont) in
    f from r.

(* Fake print *)

Definition print_int : int -> int := fun i => i.

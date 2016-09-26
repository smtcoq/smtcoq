(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*       from the Int31 library                                           *)
(*         by Arnaud Spiwack and Pierre Letouzey                          *)
(*       and the Int63 library of native-coq                              *)
(*         by Benjamin Gregoire and Laurent Thery                         *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
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
  fun i j => nshiftl i (Z.to_nat (phi j)).
Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Definition lsr : int -> int -> int :=
  fun i j => nshiftr i (Z.to_nat (phi j)).
Infix ">>" := lsr (at level 30, no associativity) : int63_scope.

Definition band b1 b2 :=
  match b1, b2 with
  | D1, D1 => D1
  | _, _ => D0
  end.
Definition land : int -> int -> int :=
  fun i j => match i, j with
             | I31 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30,
               I31 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 =>
               I31 (band a0 b0) (band a1 b1) (band a2 b2) (band a3 b3) (band a4 b4) (band a5 b5) (band a6 b6) (band a7 b7) (band a8 b8) (band a9 b9) (band a10 b10) (band a11 b11) (band a12 b12) (band a13 b13) (band a14 b14) (band a15 b15) (band a16 b16) (band a17 b17) (band a18 b18) (band a19 b19) (band a20 b20) (band a21 b21) (band a22 b22) (band a23 b23) (band a24 b24) (band a25 b25) (band a26 b26) (band a27 b27) (band a28 b28) (band a29 b29) (band a30 b30)
             end.
Global Arguments land i j : simpl never.
Global Opaque land.
Infix "land" := land (at level 40, left associativity) : int63_scope.

Definition bor b1 b2 :=
  match b1, b2 with
  | D0, D0 => D0
  | _, _ => D1
  end.
Definition lor : int -> int -> int :=
  fun i j => match i, j with
             | I31 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30,
               I31 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 =>
               I31 (bor a0 b0) (bor a1 b1) (bor a2 b2) (bor a3 b3) (bor a4 b4) (bor a5 b5) (bor a6 b6) (bor a7 b7) (bor a8 b8) (bor a9 b9) (bor a10 b10) (bor a11 b11) (bor a12 b12) (bor a13 b13) (bor a14 b14) (bor a15 b15) (bor a16 b16) (bor a17 b17) (bor a18 b18) (bor a19 b19) (bor a20 b20) (bor a21 b21) (bor a22 b22) (bor a23 b23) (bor a24 b24) (bor a25 b25) (bor a26 b26) (bor a27 b27) (bor a28 b28) (bor a29 b29) (bor a30 b30)
             end.
Global Arguments lor i j : simpl never.
Global Opaque lor.
Infix "lor" := lor (at level 40, left associativity) : int63_scope.

Definition bxor b1 b2 :=
  match b1, b2 with
  | D0, D0 | D1, D1 => D0
  | _, _ => D1
  end.
Definition lxor : int -> int -> int :=
  fun i j => match i, j with
             | I31 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30,
               I31 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 =>
               I31 (bxor a0 b0) (bxor a1 b1) (bxor a2 b2) (bxor a3 b3) (bxor a4 b4) (bxor a5 b5) (bxor a6 b6) (bxor a7 b7) (bxor a8 b8) (bxor a9 b9) (bxor a10 b10) (bxor a11 b11) (bxor a12 b12) (bxor a13 b13) (bxor a14 b14) (bxor a15 b15) (bxor a16 b16) (bxor a17 b17) (bxor a18 b18) (bxor a19 b19) (bxor a20 b20) (bxor a21 b21) (bxor a22 b22) (bxor a23 b23) (bxor a24 b24) (bxor a25 b25) (bxor a26 b26) (bxor a27 b27) (bxor a28 b28) (bxor a29 b29) (bxor a30 b30)
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

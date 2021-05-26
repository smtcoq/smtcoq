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

(* Comparisons *)
Definition eqb := eqb31.
Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

Definition ltb : int -> int -> bool :=
  fun i j => match compare31 i j with | Lt => true | _ => false end.
Notation "m < n" := (ltb m n) : int63_scope.

Definition leb : int -> int -> bool :=
  fun i j => match compare31 i j with | Gt => false | _ => true end.
Notation "m <= n" := (leb m n) : int63_scope.


Lemma eqb_correct : forall i j, (i==j)%int = true -> i = j.
Proof. exact eqb31_correct. Qed.

(* Logical operations *)
Definition lsl : int -> int -> int :=
  fun i j => addmuldiv31 j i 0.
Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Definition lsr : int -> int -> int :=
  fun i j => if (j < 31%int31)%int then addmuldiv31 (31-j)%int31 0 i else 0%int31.
Infix ">>" := lsr (at level 30, no associativity) : int63_scope.

Definition land : int -> int -> int := land31.
Global Arguments land i j : simpl never.
Global Opaque land.
Infix "land" := land (at level 40, left associativity) : int63_scope.

Definition lor : int -> int -> int := lor31.
Global Arguments lor i j : simpl never.
Global Opaque lor.
Infix "lor" := lor (at level 40, left associativity) : int63_scope.

Definition lxor : int -> int -> int := lxor31.
Global Arguments lxor i j : simpl never.
Global Opaque lxor.
Infix "lxor" := lxor (at level 40, left associativity) : int63_scope.

(* Arithmetic modulo operations *)
Notation "n + m" := (add31 n m) : int63_scope.
Notation "n - m" := (sub31 n m) : int63_scope.
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


(* Iterators *)

Definition firstr i := if ((i land 1) == 0)%int then D0 else D1.
Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int31->A->A)
 (i:int31) : A :=
  match n with
  | O => case0
  | S next =>
          if (i == 0)%int then
             case0
          else
             let si := (i >> 1)%int in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end.
Definition recr := recr_aux size.
Definition iter_int31 i A f :=
  recr (A->A) (fun x => x)
   (fun b si rec => match b with
      | D0 => fun x => rec (rec x)
      | D1 => fun x => f (rec (rec x))
    end)
    i.

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

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
  fun i j => nshiftl (N.to_nat (Z.to_N (phi j))) i.
Infix "<<" := lsl (at level 30, no associativity) : int63_scope.

Definition lsr : int -> int -> int :=
  fun i j => nshiftr (N.to_nat (Z.to_N (phi j))) i.
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
(* We do not use eqb63 to be able to easily prove eqb_correct *)
(* Definition eqb_digits d1 d2 := *)
(*   match d1, d2 with *)
(*     | D0, D0 | D1, D1 => true *)
(*     | _, _ => false *)
(*   end. *)

(* Definition eqb i j := *)
(*   match i, j with *)
(*     | I63 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62, I63 d'0 d'1 d'2 d'3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30 d'31 d'32 d'33 d'34 d'35 d'36 d'37 d'38 d'39 d'40 d'41 d'42 d'43 d'44 d'45 d'46 d'47 d'48 d'49 d'50 d'51 d'52 d'53 d'54 d'55 d'56 d'57 d'58 d'59 d'60 d'61 d'62 => *)
(*       (eqb_digits d0 d'0) && (eqb_digits d1 d'1) && (eqb_digits d2 d'2) && (eqb_digits d3 d'3) && (eqb_digits d4 d'4) && (eqb_digits d5 d'5) && (eqb_digits d6 d'6) && (eqb_digits d7 d'7) && (eqb_digits d8 d'8) && (eqb_digits d9 d'9) && (eqb_digits d10 d'10) && (eqb_digits d11 d'11) && (eqb_digits d12 d'12) && (eqb_digits d13 d'13) && (eqb_digits d14 d'14) && (eqb_digits d15 d'15) && (eqb_digits d16 d'16) && (eqb_digits d17 d'17) && (eqb_digits d18 d'18) && (eqb_digits d19 d'19) && (eqb_digits d20 d'20) && (eqb_digits d21 d'21) && (eqb_digits d22 d'22) && (eqb_digits d23 d'23) && (eqb_digits d24 d'24) && (eqb_digits d25 d'25) && (eqb_digits d26 d'26) && (eqb_digits d27 d'27) && (eqb_digits d28 d'28) && (eqb_digits d29 d'29) && (eqb_digits d30 d'30) && (eqb_digits d31 d'31) && (eqb_digits d32 d'32) && (eqb_digits d33 d'33) && (eqb_digits d34 d'34) && (eqb_digits d35 d'35) && (eqb_digits d36 d'36) && (eqb_digits d37 d'37) && (eqb_digits d38 d'38) && (eqb_digits d39 d'39) && (eqb_digits d40 d'40) && (eqb_digits d41 d'41) && (eqb_digits d42 d'42) && (eqb_digits d43 d'43) && (eqb_digits d44 d'44) && (eqb_digits d45 d'45) && (eqb_digits d46 d'46) && (eqb_digits d47 d'47) && (eqb_digits d48 d'48) && (eqb_digits d49 d'49) && (eqb_digits d50 d'50) && (eqb_digits d51 d'51) && (eqb_digits d52 d'52) && (eqb_digits d53 d'53) && (eqb_digits d54 d'54) && (eqb_digits d55 d'55) && (eqb_digits d56 d'56) && (eqb_digits d57 d'57) && (eqb_digits d58 d'58) && (eqb_digits d59 d'59) && (eqb_digits d60 d'60) && (eqb_digits d61 d'61) && (eqb_digits d62 d'62) *)
(*   end. *)
Definition eqb := eqb31.
Notation "m '==' n" := (eqb m n) (at level 70, no associativity) : int63_scope.

Definition ltb : int -> int -> bool :=
  fun i j => match compare31 i j with | Lt => true | _ => false end.
Notation "m < n" := (ltb m n) : int63_scope.

Definition leb : int -> int -> bool :=
  fun i j => match compare31 i j with | Gt => false | _ => true end.
Notation "m <= n" := (leb m n) : int63_scope.

(* This operator has the following reduction rule
     eqb_correct i i (eq_refl true) ---> (eq_refl i) *)
(* Lemma eqb_digits_correct : *)
(*   forall d1 d2, eqb_digits d1 d2 = true <-> d1 = d2. *)
(* Proof. intros [|] [|]; split; try reflexivity; discriminate. Defined. *)

(* Lemma andb_true_iff : forall b1 b2, *)
(*   b1 && b2 = true <-> b1 = true /\ b2 = true. *)
(* Proof. intros [|] [|]; repeat split; try reflexivity; try discriminate; intros [H1 H2]; discriminate. Defined. *)

Lemma eqb_correct : forall i j, (i==j)%int = true -> i = j.
Admitted.
(* Proof. *)
(*   unfold eqb. intros [d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 d32 d33 d34 d35 d36 d37 d38 d39 d40 d41 d42 d43 d44 d45 d46 d47 d48 d49 d50 d51 d52 d53 d54 d55 d56 d57 d58 d59 d60 d61 d62] [d'0 d'1 d'2 d'3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30 d'31 d'32 d'33 d'34 d'35 d'36 d'37 d'38 d'39 d'40 d'41 d'42 d'43 d'44 d'45 d'46 d'47 d'48 d'49 d'50 d'51 d'52 d'53 d'54 d'55 d'56 d'57 d'58 d'59 d'60 d'61 d'62]. *)
(*   do 62 (rewrite andb_true_iff; intros [H1 H2]; rewrite eqb_digits_correct in H2; subst; revert H1). *)
(*   rewrite eqb_digits_correct. intros ->. reflexivity. *)
(* Defined. *)


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

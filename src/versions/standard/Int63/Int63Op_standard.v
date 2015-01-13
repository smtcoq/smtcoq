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


Require Export Int63Native.
Require Import BigNumPrelude.
Require Import Bvector.

Set Vm Optimize.


Local Open Scope int63_scope.

(** The number of digits as a int *)
Definition digits := 63.

(** The bigger int *)
Definition max_int := Eval vm_compute in 0 - 1.
Register max_int as PrimInline.

(** Access to the nth digits *)
Definition get_digit x p := (0 < (x land (1 << p))).

Definition set_digit x p (b:bool) :=
  if (0 <= p) && (p < digits) then 
    if b then x lor (1 << p)
    else x land (max_int lxor (1 << p))
  else x.

(** Equality to 0 *)
Definition is_zero (i:int) := i == 0.
Register is_zero as PrimInline.

(** Parity *)
Definition is_even (i:int) := is_zero (i land 1).
Register is_even as PrimInline.

(** Bit *)

Definition bit i n :=  negb (is_zero ((i >> n) << (digits - 1))).
(* Register bit as PrimInline. *)

(** Extra modulo operations *)
Definition opp (i:int) := 0 - i.
Register opp as PrimInline.
Notation "- x" := (opp x) : int63_scope.

Definition oppcarry i := max_int - i.
Register oppcarry as PrimInline.

Definition succ i := i + 1.
Register succ as PrimInline.

Definition pred i := i - 1.
Register pred as PrimInline.

Definition addcarry i j := i + j + 1.
Register addcarry as PrimInline.

Definition subcarry i j := i - j - 1.
Register subcarry as PrimInline.

(** Exact arithmetic operations *)

Definition addc_def x y :=
  let r := x + y in
  if r < x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Register addc      : int -> int -> carry int as int63_addc.
Notation "n '+c' m" := (addc n m) (at level 50, no associativity) : int63_scope.

Definition addcarryc_def x y :=
  let r := addcarry x y in
  if r <= x then C1 r else C0 r.
(* the same but direct implementation for effeciancy *)
Register addcarryc : int -> int -> carry int as int63_addcarryc.

Definition subc_def x y := 
  if y <= x then C0 (x - y) else C1 (x - y).
(* the same but direct implementation for effeciancy *)
Register subc      : int -> int -> carry int as int63_subc.
Notation "n '-c' m" := (subc n m) (at level 50, no associativity) : int63_scope.

Definition subcarryc_def x y :=
  if y < x then C0 (x - y - 1) else C1 (x - y - 1).
(* the same but direct implementation for effeciancy *)
Register subcarryc : int -> int -> carry int as int63_subcarryc.

Definition diveucl_def x y := (x/y, x\%y).
(* the same but direct implementation for effeciancy *) 
Register diveucl   : int -> int -> int * int as int63_diveucl.

Register diveucl_21    : int -> int -> int -> int * int as int63_div21.

Definition addmuldiv_def p x y :=
  (x << p) lor (y >> (digits - p)).
Register addmuldiv   : int -> int -> int -> int as int63_addmuldiv.

Definition oppc (i:int) := 0 -c i.
Register oppc as PrimInline.

Definition succc i := i +c 1.
Register succc as PrimInline.

Definition predc i := i -c 1.
Register predc as PrimInline.

(** Comparison *)
Definition compare_def x y :=
  if x < y then Lt 
  else if (x == y) then Eq else Gt.

Register compare : int -> int -> comparison as int63_compare.
Notation "n ?= m" := (compare n m) (at level 70, no associativity) : int63_scope.

(** Exotic operations *)

(** I should add the definition (like for compare) *)
Register head0 : int -> int as int63_head0.
Register tail0 : int -> int as int63_tail0.

(** Iterators *)

Definition foldi {A} (f:int -> A -> A) from to :=
  foldi_cont (fun i cont a => cont (f i a)) from to (fun a => a).
Register foldi as PrimInline.

Definition fold {A} (f: A -> A) from to :=
  foldi_cont (fun i cont a => cont (f a)) from to (fun a => a).
Register fold as PrimInline.

Definition foldi_down {A} (f:int -> A -> A) from downto :=
  foldi_down_cont (fun i cont a => cont (f i a)) from downto (fun a => a).
Register foldi_down as PrimInline.

Definition fold_down {A} (f:A -> A) from downto :=
  foldi_down_cont (fun i cont a => cont (f a)) from downto (fun a => a).
Register fold_down as PrimInline.

Definition forallb (f:int -> bool) from to :=
  foldi_cont (fun i cont _ => if f i then cont tt else false) from to (fun _ => true) tt.

Definition existsb (f:int -> bool) from to :=
  foldi_cont (fun i cont _ => if f i then true else cont tt) from to (fun _ => false) tt.

(** Translation to Z *)

Fixpoint to_Z_rec (n:nat) (i:int) :=
  match n with 
  | O => 0%Z 
  | S n => 
    (if is_even i then Zdouble else Zdouble_plus_one) (to_Z_rec n (i >> 1))
  end.

Definition to_Z := to_Z_rec size.

Fixpoint of_pos_rec (n:nat) (p:positive) :=
  match n, p with 
  | O, _ => 0
  | S n, xH => 1
  | S n, xO p => (of_pos_rec n p) << 1
  | S n, xI p => (of_pos_rec n p) << 1 lor 1
  end.

Definition of_pos := of_pos_rec size.

Definition of_Z z := 
  match z with
  | Zpos p => of_pos p
  | Z0 => 0
  | Zneg p => - (of_pos p)
  end.

(** Gcd **)
Fixpoint gcd_rec (guard:nat) (i j:int) {struct guard} :=
   match guard with
   | O => 1
   | S p => if j == 0 then i else gcd_rec p j (i \% j)
   end.

Definition gcd := gcd_rec (2*size).

(** Square root functions using newton iteration **)

Definition sqrt_step (rec: int -> int -> int) (i j: int)  :=
  let quo := i/j in
  if quo < j then rec i ((j + i/j) >> 1)
  else j.

Definition iter_sqrt :=
 Eval lazy beta delta [sqrt_step] in
 fix iter_sqrt (n: nat) (rec: int -> int -> int)
          (i j: int) {struct n} : int :=
  sqrt_step
   (fun i j => match n with
      O =>  rec i j
   | S n => (iter_sqrt n (iter_sqrt n rec)) i j
   end) i j.

Definition sqrt i :=
  match compare 1 i with
    Gt => 0
  | Eq => 1
  | Lt => iter_sqrt size (fun i j => j) i (i >> 1)
  end.

Definition high_bit := 1 << (digits - 1).

Definition sqrt2_step (rec: int -> int -> int -> int)
   (ih il j: int)  :=
  if ih < j then
    let (quo,_) := diveucl_21 ih il j in
    if quo < j then
      match j +c quo with
      | C0 m1 => rec ih il (m1 >> 1)
      | C1 m1 => rec ih il ((m1 >> 1) + high_bit)
      end 
    else j
  else j.

Definition iter2_sqrt :=
 Eval lazy beta delta [sqrt2_step] in
 fix iter2_sqrt (n: nat)
          (rec: int  -> int -> int -> int)
          (ih il j: int) {struct n} : int :=
  sqrt2_step
   (fun ih il j => 
     match n with
     | O =>  rec ih il j
     | S n => (iter2_sqrt n (iter2_sqrt n rec)) ih il j
   end) ih il j.

Definition sqrt2 ih il :=
  let s := iter2_sqrt size (fun ih il j => j) ih il max_int in
  let (ih1, il1) := mulc s s in
  match il -c il1 with
  | C0 il2 =>
    if ih1 < ih then (s, C1 il2) else (s, C0 il2)
  | C1 il2 =>
    if ih1 < (ih - 1) then (s, C1 il2) else (s, C0 il2)
  end.

(* Extra function on equality *)
 
Definition cast i j :=
     (if i == j as b return ((b = true -> i = j) -> option (forall P : int -> Type, P i -> P j))
      then fun Heq : true = true -> i = j =>
             Some
             (fun (P : int -> Type) (Hi : P i) =>
               match Heq (eq_refl true) in (_ = y) return (P y) with
               | eq_refl => Hi
               end)
      else fun _ : false = true -> i = j => None) (eqb_correct i j).

Definition eqo i j :=
   (if i == j as b return ((b = true -> i = j) -> option (i=j))
    then fun Heq : true = true -> i = j =>
             Some (Heq (eq_refl true))
     else fun _ : false = true -> i = j => None) (eqb_correct i j).

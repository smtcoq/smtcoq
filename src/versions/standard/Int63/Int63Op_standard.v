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


Require Import Int31 Cyclic31.
Require Export Int63Native.
Require Import BigNumPrelude.
Require Import Bvector.


Local Open Scope int63_scope.

(** The number of digits as a int *)
Definition digits := 31%int31.

(** The bigger int *)
Definition max_int := Eval vm_compute in 0 - 1.

(** Access to the nth digits *)
Definition get_digit x p := (0 < (x land (1 << p))).

Definition set_digit x p (b:bool) :=
  if (0 <= p) && (p < digits) then
    if b then x lor (1 << p)
    else x land (max_int lxor (1 << p))
  else x.

(** Equality to 0 *)
Definition is_zero (i:int) := i == 0.

(** Parity *)
Definition is_even (i:int) := is_zero (i land 1).

(** Bit *)

Definition bit i n :=  negb (is_zero ((i >> n) << (digits - 1))).
(* Register bit as PrimInline. *)

(** Extra modulo operations *)
Definition opp (i:int) := 0 - i.
Notation "- x" := (opp x) : int63_scope.

Definition oppcarry i := max_int - i.

Definition succ i := i + 1.

Definition pred i := i - 1.

Definition addcarry i j := i + j + 1.

Definition subcarry i j := i - j - 1.

(** Exact arithmetic operations *)

Definition addc_def x y :=
  let r := x + y in
  if r < x then C1 r else C0 r.
(* the same but direct implementation for efficiancy *)
Definition addc : int -> int -> carry int := add31c.
Notation "n '+c' m" := (addc n m) (at level 50, no associativity) : int63_scope.

Definition addcarryc_def x y :=
  let r := addcarry x y in
  if r <= x then C1 r else C0 r.
(* the same but direct implementation for efficiancy *)
Definition addcarryc : int -> int -> carry int := add31carryc.

Definition subc_def x y :=
  if y <= x then C0 (x - y) else C1 (x - y).
(* the same but direct implementation for efficiancy *)
Definition subc : int -> int -> carry int := sub31c.
Notation "n '-c' m" := (subc n m) (at level 50, no associativity) : int63_scope.

Definition subcarryc_def x y :=
  if y < x then C0 (x - y - 1) else C1 (x - y - 1).
(* the same but direct implementation for efficiancy *)
Definition subcarryc : int -> int -> carry int := sub31carryc.

Definition diveucl_def x y := (x/y, x\%y).
(* the same but direct implementation for efficiancy *)
Definition diveucl : int -> int -> int * int := div31.

Definition diveucl_21 : int -> int -> int -> int * int := div3121.

Definition addmuldiv_def p x y :=
  (x << p) lor (y >> (digits - p)).
(* the same but direct implementation for efficiancy *)
Definition addmuldiv : int -> int -> int -> int := addmuldiv31.

Definition oppc (i:int) := 0 -c i.

Definition succc i := i +c 1.

Definition predc i := i -c 1.

(** Comparison *)
Definition compare_def x y :=
  if x < y then Lt
  else if (x == y) then Eq else Gt.

Definition compare : int -> int -> comparison := compare31.
Notation "n ?= m" := (compare n m) (at level 70, no associativity) : int63_scope.

(** Exotic operations *)

(** I should add the definition (like for compare) *)
Definition head0 : int -> int := head031.
Definition tail0 : int -> int := tail031.

(** Iterators *)

Definition foldi {A} (f:int -> A -> A) from to :=
  foldi_cont (fun i cont a => cont (f i a)) from to (fun a => a).

Definition fold {A} (f: A -> A) from to :=
  foldi_cont (fun i cont a => cont (f a)) from to (fun a => a).

Definition foldi_down {A} (f:int -> A -> A) from downto :=
  foldi_down_cont (fun i cont a => cont (f i a)) from downto (fun a => a).

Definition fold_down {A} (f:A -> A) from downto :=
  foldi_down_cont (fun i cont a => cont (f a)) from downto (fun a => a).

Definition forallb (f:int -> bool) from to :=
  foldi_cont (fun i cont _ => if f i then cont tt else false) from to (fun _ => true) tt.

Definition existsb (f:int -> bool) from to :=
  foldi_cont (fun i cont _ => if f i then true else cont tt) from to (fun _ => false) tt.

(** Translation to Z *)

(* Fixpoint to_Z_rec (n:nat) (i:int) := *)
(*   match n with *)
(*   | O => 0%Z *)
(*   | S n => *)
(*     (if is_even i then Zdouble else Zdouble_plus_one) (to_Z_rec n (i >> 1)) *)
(*   end. *)

(* Definition to_Z := to_Z_rec size. *)

Definition to_Z := phi.
Definition of_Z := phi_inv.

(* Fixpoint of_pos_rec (n:nat) (p:positive) := *)
(*   match n, p with *)
(*   | O, _ => 0 *)
(*   | S n, xH => 1 *)
(*   | S n, xO p => (of_pos_rec n p) << 1 *)
(*   | S n, xI p => (of_pos_rec n p) << 1 lor 1 *)
(*   end. *)

(* Definition of_pos := of_pos_rec size. *)

(* Definition of_Z z := *)
(*   match z with *)
(*   | Zpos p => of_pos p *)
(*   | Z0 => 0 *)
(*   | Zneg p => - (of_pos p) *)
(*   end. *)

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
  if quo < j then rec i ((j + (i/j)%int) >> 1)
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

Definition cast_digit d1 d2 :
  option (forall P : Int31.digits -> Type, P d1 -> P d2) :=
  match d1, d2 with
  | D0, D0 | D1, D1 => Some (fun P h => h)
  | _, _ => None
  end.

(* May need to improve this definition, but no reported efficiency problem for the moment *)
Definition cast i j :
  option (forall P : int -> Type, P i -> P j) :=
  match i, j return option (forall P : int -> Type, P i -> P j) with
  | I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30, I31 d'0 d'1 d'2 d'3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30 =>
    match
      cast_digit d0 d'0,
      cast_digit d1 d'1,
      cast_digit d2 d'2,
      cast_digit d3 d'3,
      cast_digit d4 d'4,
      cast_digit d5 d'5,
      cast_digit d6 d'6,
      cast_digit d7 d'7,
      cast_digit d8 d'8,
      cast_digit d9 d'9,
      cast_digit d10 d'10,
      cast_digit d11 d'11,
      cast_digit d12 d'12,
      cast_digit d13 d'13,
      cast_digit d14 d'14,
      cast_digit d15 d'15,
      cast_digit d16 d'16,
      cast_digit d17 d'17,
      cast_digit d18 d'18,
      cast_digit d19 d'19,
      cast_digit d20 d'20,
      cast_digit d21 d'21,
      cast_digit d22 d'22,
      cast_digit d23 d'23,
      cast_digit d24 d'24,
      cast_digit d25 d'25,
      cast_digit d26 d'26,
      cast_digit d27 d'27,
      cast_digit d28 d'28,
      cast_digit d29 d'29,
      cast_digit d30 d'30
    with
    | Some k0,
      Some k1,
      Some k2,
      Some k3,
      Some k4,
      Some k5,
      Some k6,
      Some k7,
      Some k8,
      Some k9,
      Some k10,
      Some k11,
      Some k12,
      Some k13,
      Some k14,
      Some k15,
      Some k16,
      Some k17,
      Some k18,
      Some k19,
      Some k20,
      Some k21,
      Some k22,
      Some k23,
      Some k24,
      Some k25,
      Some k26,
      Some k27,
      Some k28,
      Some k29,
      Some k30 =>
      Some (fun P h =>
              k0 (fun d0 => P (I31 d0 d'1 d'2 d'3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k1 (fun d1 => P (I31 d0 d1 d'2 d'3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k2 (fun d2 => P (I31 d0 d1 d2 d'3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k3 (fun d3 => P (I31 d0 d1 d2 d3 d'4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k4 (fun d4 => P (I31 d0 d1 d2 d3 d4 d'5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k5 (fun d5 => P (I31 d0 d1 d2 d3 d4 d5 d'6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k6 (fun d6 => P (I31 d0 d1 d2 d3 d4 d5 d6 d'7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k7 (fun d7 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d'8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k8 (fun d8 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d'9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k9 (fun d9 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d'10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k10 (fun d10 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d'11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k11 (fun d11 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d'12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k12 (fun d12 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d'13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k13 (fun d13 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d'14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k14 (fun d14 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d'15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k15 (fun d15 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d'16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k16 (fun d16 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d'17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k17 (fun d17 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d'18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k18 (fun d18 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d'19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k19 (fun d19 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d'20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k20 (fun d20 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d'21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k21 (fun d21 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d'22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k22 (fun d22 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d'23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k23 (fun d23 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d'24 d'25 d'26 d'27 d'28 d'29 d'30)) (k24 (fun d24 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d'25 d'26 d'27 d'28 d'29 d'30)) (k25 (fun d25 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d'26 d'27 d'28 d'29 d'30)) (k26 (fun d26 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d'27 d'28 d'29 d'30)) (k27 (fun d27 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d'28 d'29 d'30)) (k28 (fun d28 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d'29 d'30)) (k29 (fun d29 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d'30)) (k30 (fun d30 => P (I31 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30)) h)))))))))))))))))))))))))))))))
    | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => None
    end
  end.


Definition eqo i j : option (i = j) :=
  match cast i j with
  | Some k => Some (k (fun j => i = j) (refl_equal i))
  | None => None
  end.


(* 
   Local Variables:
   coq-load-path: ((rec "../../.." "SMTCoq"))
   End: 
*)

(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

Require Import NaryFunctions.
Require Import Wf_nat.
Require Export ZArith.
Require Export DoubleType.

(** * 63-bit integers *)

(** This file contains basic definitions of a 63-bit integer arithmetic.
  It is based on the Int31 library, using its genericity. *)

Definition size := 63%nat.

(** Digits *)

Inductive digits : Type := D0 | D1.

(** The type of 63-bit integers *)

(** The type [int63] has a unique constructor [I63] that expects
   63 arguments of type [digits]. *)

Definition digits63 t := Eval compute in nfun digits size t.

Inductive int63 : Type := I63 : digits63 int63.

Notation int := int63.

(* spiwack: Registration of the type of integers, so that the matchs in
   the functions below perform dynamic decompilation (otherwise some segfault
   occur when they are applied to one non-closed term and one closed term). *)

Delimit Scope int63_scope with int.
Bind Scope int63_scope with int.
Local Open Scope int63_scope.

(** * Constants *)

(** Zero is [I63 D0 ... D0] *)
Definition On : int63 := Eval compute in napply_cst _ _ D0 size I63.
Notation "0" := On : int63_scope.

(** One is [I63 D0 ... D0 D1] *)
Definition In : int63 := Eval compute in (napply_cst _ _ D0 (size-1) I63) D1.
Notation "1" := In : int63_scope.

(** The biggest integer is [I63 D1 ... D1], corresponding to [(2^size)-1] *)
Definition Tn : int63 := Eval compute in napply_cst _ _ D1 size I63.

(** Two is [I63 D0 ... D0 D1 D0] *)
Definition Twon : int63 := Eval compute in (napply_cst _ _ D0 (size-2) I63) D1 D0.
Notation "2" := Twon : int63_scope.

(** * Bits manipulation *)


(** [sneakr b x] shifts [x] to the right by one bit.
   Rightmost digit is lost while leftmost digit becomes [b].
   Pseudo-code is
    [ match x with (I63 d0 ... dN) => I63 b d0 ... d(N-1) end ]
*)

Definition sneakr : digits -> int63 -> int63 := Eval compute in
 fun b => int63_rect _ (napply_except_last _ _ (size-1) (I63 b)).

(** [sneakl b x] shifts [x] to the left by one bit.
   Leftmost digit is lost while rightmost digit becomes [b].
   Pseudo-code is
    [ match x with (I63 d0 ... dN) => I63 d1 ... dN b end ]
*)

Definition sneakl : digits -> int63 -> int63 := Eval compute in
 fun b => int63_rect _ (fun _ => napply_then_last _ _ b (size-1) I63).


(** [shiftl], [shiftr], [twice] and [twice_plus_one] are direct
    consequences of [sneakl] and [sneakr]. *)

Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.
Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.

(** [firstl x] returns the leftmost digit of number [x].
    Pseudo-code is [ match x with (I63 d0 ... dN) => d0 end ] *)

Definition firstl : int63 -> digits := Eval compute in
 int63_rect _ (fun d => napply_discard _ _ d (size-1)).

(** [firstr x] returns the rightmost digit of number [x].
    Pseudo-code is [ match x with (I63 d0 ... dN) => dN end ] *)

Definition firstr : int63 -> digits := Eval compute in
 int63_rect _ (napply_discard _ _ (fun d=>d) (size-1)).

(** [iszero x] is true iff [x = I63 D0 ... D0]. Pseudo-code is
    [ match x with (I63 D0 ... D0) => true | _ => false end ] *)

Definition iszero : int63 -> bool := Eval compute in
 let f d b := match d with D0 => b | D1 => false end
 in int63_rect _ (nfold_bis _ _ f true size).

(* NB: DO NOT transform the above match in a nicer (if then else).
   It seems to work, but later "unfold iszero" takes forever. *)


(** [base] is [2^63], obtained via iterations of [Z.double].
   It can also be seen as the smallest b > 0 s.t. phi_inv b = 0
   (see below) *)

Definition base := Eval compute in
 iter_nat size Z Z.double 1%Z.

(** * Recursors *)

Fixpoint recl_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int63->A->A)
 (i:int63) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftl i in
             caserec (firstl i) si (recl_aux next A case0 caserec si)
  end.

Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int63->A->A)
 (i:int63) : A :=
  match n with
  | O => case0
  | S next =>
          if iszero i then
             case0
          else
             let si := shiftr i in
             caserec (firstr i) si (recr_aux next A case0 caserec si)
  end.

Definition recl := recl_aux size.
Definition recr := recr_aux size.

(** * Conversions *)

(** From int63 to Z, we simply iterates [Z.double] or [Z.succ_double]. *)

Definition phi : int63 -> Z :=
 recr Z (0%Z)
  (fun b _ => match b with D0 => Z.double | D1 => Z.succ_double end).

(** From positive to int63. An abstract definition could be :
      [ phi_inv (2n) = 2*(phi_inv n) /\
        phi_inv 2n+1 = 2*(phi_inv n) + 1 ] *)

Fixpoint phi_inv_positive p :=
  match p with
    | xI q => twice_plus_one (phi_inv_positive q)
    | xO q => twice (phi_inv_positive q)
    | xH => In
  end.

(** The negative part : 2-complement  *)

Fixpoint complement_negative p :=
  match p with
    | xI q => twice (complement_negative q)
    | xO q => twice_plus_one (complement_negative q)
    | xH => twice Tn
  end.

(** A simple incrementation function *)

Definition incr : int63 -> int63 :=
 recr int63 In
   (fun b si rec => match b with
     | D0 => sneakl D1 si
     | D1 => sneakl D0 rec end).

(** We can now define the conversion from Z to int63. *)

Definition phi_inv : Z -> int63 := fun n =>
 match n with
 | Z0 => On
 | Zpos p => phi_inv_positive p
 | Zneg p => incr (complement_negative p)
 end.

(** [phi_inv2] is similar to [phi_inv] but returns a double word
    [zn2z int63] *)

Definition phi_inv2 n :=
  match n with
  | Z0 => W0
  | _ => WW (phi_inv (n/base)%Z) (phi_inv n)
  end.

(** [phi2] is similar to [phi] but takes a double word (two args) *)

Definition phi2 nh nl :=
  ((phi nh)*base+(phi nl))%Z.

(** * Addition *)

(** Addition modulo [2^63] *)

Definition add63 (n m : int63) := phi_inv ((phi n)+(phi m)).
Notation "n + m" := (add63 n m) : int63_scope.

(** Addition with carry (the result is thus exact) *)

(* spiwack : when executed in non-compiled*)
(* mode, (phi n)+(phi m) is computed twice*)
(* it may be considered to optimize it *)

Definition add63c (n m : int63) :=
  let npm := n+m in
  match (phi npm ?= (phi n)+(phi m))%Z with
  | Eq => C0 npm
  | _ => C1 npm
  end.
Notation "n '+c' m" := (add63c n m) (at level 50, no associativity) : int63_scope.

(**  Addition plus one with carry (the result is thus exact) *)

Definition add63carryc (n m : int63) :=
  let npmpone_exact := ((phi n)+(phi m)+1)%Z in
  let npmpone := phi_inv npmpone_exact in
  match (phi npmpone ?= npmpone_exact)%Z with
  | Eq => C0 npmpone
  | _ => C1 npmpone
  end.

(** * Substraction *)

(** Subtraction modulo [2^63] *)

Definition sub63 (n m : int63) := phi_inv ((phi n)-(phi m)).
Notation "n - m" := (sub63 n m) : int63_scope.

(** Subtraction with carry (thus exact) *)

Definition sub63c (n m : int63) :=
  let nmm := n-m in
  match (phi nmm ?= (phi n)-(phi m))%Z with
  | Eq => C0 nmm
  | _ => C1 nmm
  end.
Notation "n '-c' m" := (sub63c n m) (at level 50, no associativity) : int63_scope.

(** subtraction minus one with carry (thus exact) *)

Definition sub63carryc (n m : int63) :=
  let nmmmone_exact := ((phi n)-(phi m)-1)%Z in
  let nmmmone := phi_inv nmmmone_exact in
  match (phi nmmmone ?= nmmmone_exact)%Z with
  | Eq => C0 nmmmone
  | _ => C1 nmmmone
  end.

(** Opposite *)

Definition opp63 x := On - x.
Notation "- x" := (opp63 x) : int63_scope.

(** Multiplication *)

(** multiplication modulo [2^63] *)

Definition mul63 (n m : int63) := phi_inv ((phi n)*(phi m)).
Notation "n * m" := (mul63 n m) : int63_scope.

(** multiplication with double word result (thus exact) *)

Definition mul63c (n m : int63) := phi_inv2 ((phi n)*(phi m)).
Notation "n '*c' m" := (mul63c n m) (at level 40, no associativity) : int63_scope.


(** * Division *)

(** Division of a double size word modulo [2^63] *)

Definition div6321 (nh nl m : int63) :=
  let (q,r) := Z.div_eucl (phi2 nh nl) (phi m) in
  (phi_inv q, phi_inv r).

(** Division modulo [2^63] *)

Definition div63 (n m : int63) :=
  let (q,r) := Z.div_eucl (phi n) (phi m) in
  (phi_inv q, phi_inv r).
Notation "n / m" := (div63 n m) : int63_scope.


(** * Unsigned comparison *)

Definition compare63 (n m : int63) := ((phi n)?=(phi m))%Z.
Notation "n ?= m" := (compare63 n m) (at level 70, no associativity) : int63_scope.

Definition eqb63 (n m : int63) :=
 match n ?= m with Eq => true | _ => false end.


(** Computing the [i]-th iterate of a function:
    [iter_int63 i A f = f^i] *)

Definition iter_int63 i A f :=
  recr (A->A) (fun x => x)
   (fun b si rec => match b with
      | D0 => fun x => rec (rec x)
      | D1 => fun x => f (rec (rec x))
    end)
    i.

(** Combining the [(63-p)] low bits of [i] above the [p] high bits of [j]:
    [addmuldiv63 p i j = i*2^p+j/2^(63-p)]  (modulo [2^63]) *)

Definition addmuldiv63 p i j :=
 let (res, _ ) :=
 iter_int63 p (int63*int63)
  (fun ij => let (i,j) := ij in (sneakl (firstl j) i, shiftl j))
  (i,j)
 in
 res.


Fixpoint euler (guard:nat) (i j:int63) {struct guard} :=
  match guard with
    | O => In
    | S p => match j ?= On with
               | Eq => i
               | _ => euler p j (let (_, r ) := i/j in r)
             end
  end.

Definition gcd63 (i j:int63) := euler (2*size)%nat i j.

(** Square root functions using newton iteration
    we use a very naive upper-bound on the iteration
    2^63 instead of the usual 63.
**)



Definition sqrt63_step (rec: int63 -> int63 -> int63) (i j: int63)  :=
Eval lazy delta [Twon] in
  let (quo,_) := i/j in
  match quo ?= j with
    Lt => rec i (fst ((j + quo)/Twon))
  | _ =>  j
  end.

Fixpoint iter63_sqrt (n: nat) (rec: int63 -> int63 -> int63)
          (i j: int63) {struct n} : int63 :=
  sqrt63_step
   (match n with
      O =>  rec
   | S n => (iter63_sqrt n (iter63_sqrt n rec))
   end) i j.

Definition sqrt63 i :=
Eval lazy delta [On In Twon] in
  match compare63 In i with
    Gt => On
  | Eq => In
  | Lt => iter63_sqrt 63 (fun i j => j) i (fst (i/Twon))
  end.

Definition v30 := Eval compute in (addmuldiv63 (phi_inv (Z.of_nat size - 1)) In On).

Definition sqrt632_step (rec: int63 -> int63 -> int63 -> int63)
   (ih il j: int63)  :=
Eval lazy delta [Twon v30] in
  match ih ?= j with Eq => j | Gt => j | _ =>
  let (quo,_) := div6321 ih il j in
  match quo ?= j with
    Lt => let m := match j +c quo with
                    C0 m1 => fst (m1/Twon)
                  | C1 m1 => fst (m1/Twon) + v30
                  end in rec ih il m
  | _ =>  j
  end end.

Fixpoint iter632_sqrt (n: nat)
          (rec: int63  -> int63 -> int63 -> int63)
          (ih il j: int63) {struct n} : int63 :=
  sqrt632_step
   (match n with
      O =>  rec
   | S n => (iter632_sqrt n (iter632_sqrt n rec))
   end) ih il j.

Definition sqrt632 ih il :=
Eval lazy delta [On In] in
  let s := iter632_sqrt 63 (fun ih il j => j) ih il Tn in
           match s *c s with
            W0 => (On, C0 On) (* impossible *)
          | WW ih1 il1 =>
             match il -c il1 with
                C0 il2 =>
                  match ih ?= ih1 with
                    Gt => (s, C1 il2)
                  | _  => (s, C0 il2)
                  end
              | C1 il2 =>
                  match (ih - In) ?= ih1 with (* we could parametrize ih - 1 *)
                    Gt => (s, C1 il2)
                  | _  => (s, C0 il2)
                  end
              end
          end.


Fixpoint p2i n p : (N*int63)%type :=
  match n with
    | O => (Npos p, On)
    | S n => match p with
               | xO p => let (r,i) := p2i n p in (r, Twon*i)
               | xI p => let (r,i) := p2i n p in (r, Twon*i+In)
               | xH => (N0, In)
             end
  end.

Definition positive_to_int63 (p:positive) := p2i size p.

(** Constant 63 converted into type int63.
    It is used as default answer for numbers of zeros
    in [head0] and [tail0] *)

Definition T63 : int63 := Eval compute in phi_inv (Z.of_nat size).

Definition head063 (i:int63) :=
  recl _ (fun _ => T63)
   (fun b si rec n => match b with
     | D0 => rec (add63 n In)
     | D1 => n
    end)
   i On.

Definition tail063 (i:int63) :=
  recr _ (fun _ => T63)
   (fun b si rec n => match b with
     | D0 => rec (add63 n In)
     | D1 => n
    end)
   i On.

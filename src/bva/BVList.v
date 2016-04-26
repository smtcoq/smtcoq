(**************************************************************************)
(*                                                                        *)
(*     NDBvector                                                          *)
(*     Copyright (C) 2016                                                 *)
(*                                                                        *)
(*     Tianyi Liang                                                       *)
(*     Chantal Keller                                                     *)
(*     Alain Mebsout                                                      *)
(*     Burak Ekici                                                        *)
(*                                                                        *)
(*     The University of Iowa                                             *)
(*     LRI - Université Paris Sud - Université Paris Saclay               *)
(*                                                                        *)
(*   TODO: This file is distributed under the terms of SOME licence       *)
(*                                                                        *)
(**************************************************************************)


Require Import List NArith.
Import ListNotations.

Local Open Scope list_scope.
Local Open Scope nat_scope.

Set Implicit Arguments.
Unset Strict Implicit.


(** Some useful functions *)

Section Map2.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1, l2 with
    | b1::tl1, b2::tl2 => (f b1 b2)::(map2 f tl1 tl2)
    | _, _ => nil
  end.

Lemma l_rl: forall {A: Type} {a: A} (l: list A), length l =  length (List.removelast (a :: l)).
Proof. intros.
         induction l.
           - simpl; reflexivity.
           - unfold length in *. rewrite IHl. simpl in *. apply f_equal. induction l; reflexivity.
Qed.

(* Representation of bit vectors as a Coq Record and implementation of standard operations *)

End Map2.

Module DTBV.

(* Definition vsize := 5. *)

Record bv : Type :=
  mk_bv
  {
       size : nat;
       bits : list bool 
   (*  wf   : N.of_nat (length bits) = size *)
  }.
Check bv.
Check mk_bv.
Check @bits.
Check bits.
Check size.
Check @size.
Check bits.
Print bv.
Print mk_bv.

Definition concat_bv (a b: bv) : bv.
Proof. destruct a, b. refine (@mk_bv (size0 + size1) (bits0 ++ bits1)). Defined.
Check concat_bv.


Definition empty_bv: bv.
Proof. refine (@mk_bv 0 nil). Defined.
Check empty_bv.

Definition is_empty_bv (a: bv) : bool :=
  match a with
    | mk_bv _ nil => true
    | _           => false
  end.
Check is_empty_bv.

Definition is_zero_bv (a: bv): bool :=
  match a with
    | mk_bv _ l1 => List.forallb (fun x => negb x) l1
  end.
Check is_zero_bv.

Definition not_bv (a: bv) : bv.
Proof. destruct a. refine (@mk_bv size0 (List.map negb bits0)). Defined.
Check not_bv.

Definition and_bv (a b: bv): bv.
Proof. intros. destruct a, b. refine (@mk_bv size0 (map2 andb bits0 bits1)). Defined.
Check and_bv.

Definition or_bv (a b: bv): bv.
Proof. intros. destruct a, b. refine (@mk_bv size0 (map2 orb bits0 bits1)). Defined.
Check or_bv.

Definition lower_bv (a: bv) : bool :=
  match a with
    | mk_bv _ l1 => List.hd false l1 
  end.
Check lower_bv.

Definition higher_bv (a: bv) : bool :=
  match a with
    | mk_bv _ l1 => List.last l1 false 
  end.
Check higher_bv.

Definition shiftleft_bv (a: bv): bv.
Proof. destruct a. refine (@mk_bv  size0 (List.removelast (false :: bits0))). Defined. 
Check shiftleft_bv.

Definition shiftright_bv (a: bv): bv.
Proof. destruct a. refine (@mk_bv size0 ((List.tl bits0) ++ (false::nil))). Defined.
Check shiftright_bv.

Fixpoint shiftleft_n_bv (n: nat) (a: bv) : bv :=
  match n with
    | 0%nat => a
    | S n'  => (@shiftleft_n_bv n' (@shiftleft_bv a) )
  end.
Check shiftleft_n_bv.

Fixpoint shiftright_n_bv (n: nat) (a: bv): bv :=
  match n with
    | 0%nat => a
    | S n'  => (@shiftright_n_bv n' (@shiftright_bv a))
  end.
Check shiftright_n_bv.

Definition bb_nth_bv (n: nat) (a: bv): bool :=
  match a with
    | mk_bv _ l => nth n l false
  end.
Check bb_nth_bv.

Fixpoint b2p_bv (b : list bool) : option positive :=
  match b with
    | nil => None
    | false::b =>
    match b2p_bv b with
      | Some p => Some (xO p)
      | None => None
    end
    | true::b =>
    match b2p_bv b with
      | Some p => Some (xI p)
      | None => Some xH
    end
  end.
Check b2p_bv.

Definition bv2n_bv (a: bv): nat :=
  match a with
    | mk_bv _ l =>
    match b2p_bv l with
      | None   => 0
      | Some p => Pos.to_nat p 
    end
  end.
Check bv2n_bv.

Fixpoint p2bv_bv (p: positive) (size: nat) : bv :=
  match p with
    | xO p => 
    match p2bv_bv p size with
      | mk_bv s l => (mk_bv size (false :: l))
    end
      | xI p =>
    match p2bv_bv p size with
      | mk_bv s l => (mk_bv size (true :: l))
    end
    | xH => mk_bv size (true :: nil) 
  end.

Eval compute in p2bv_bv 16 3.

(* Definition N_decrement (n: N) := n - 1. *)

Fixpoint first_N_bv (l : list bool) (n : nat) : list bool :=
  match n with
    | O => nil
    | S n2 =>
    match l with
      | nil => nil
      | x :: l2 => x :: (first_N_bv l2 (n - 1))
    end
  end.
Check first_N_bv.

Definition p2bv_bv' (p: positive) (size: nat) : bv :=
  match p2bv_bv p size with
    | mk_bv s l => mk_bv size (first_N_bv l size)
  end.

Eval compute in p2bv_bv' 15 3.
Eval compute in p2bv_bv' 26 6.
Eval compute in p2bv_bv' 26 5.
Eval compute in p2bv_bv' 26 4.
Eval compute in p2bv_bv' 26 3.
Eval compute in p2bv_bv' 15 1.

Definition n2bv_bv (m: nat) (size: nat) : bv :=
  match m with
    | O => (mk_bv size (nil))
    | p => p2bv_bv' (Pos.of_nat p) size
  end.
Check n2bv_bv.

Definition n2b_bv (m: nat) (size: nat) : list bool := 
  match n2bv_bv m size with
    | mk_bv _ l => l
  end.
Check n2b_bv.

Definition add_bv (a b: bv) (size: nat) : bv :=
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c + d in
    n2bv_bv e size.
Check add_bv.

Fixpoint compare_naturals (a b: nat): comparison :=
  match a with
    | O => 
    match b with
      | O => Eq
      | _ => Lt
    end
    | S n => 
    match b with
      | O   => Gt
      | S m => compare_naturals n m
    end
  end.

Eval compute in compare_naturals 10 12.

Fixpoint append_false (a: bv) (size: nat) {struct size} : bv :=
  match size with
    | O => a
    | S n =>  
    match a with
      | mk_bv s l =>
      match (compare_naturals (length l) (size + s + 1) ) with
        | Eq => a
        | Lt => append_false (mk_bv (length l + 1) (l ++ [false])) n
        | Gt => a
      end
    end
  end.

Definition append_false' (a: bv) (size: nat) :=
  match a with
    | mk_bv s l => append_false a (size - (length l))
  end.

Eval compute in append_false' (mk_bv 23 [true; true; true ; true ; true]) 21.

(*(N.to_nat (N.div (N.of_nat (length l)) 2) - 3)*)

Definition eq_bv (a b: bv): bool.
Admitted.

Definition add_bv2 (a b: bv) (size: nat) : bv :=
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c + d in
    (append_false' (n2bv_bv e size) size).

Eval compute in add_bv2 (mk_bv 3 [true ; false ; true]) (mk_bv 3 [true; true; false]) 5.
Eval compute in add_bv (mk_bv 3 [false ; false ; false]) (mk_bv 3 [false; false; false]) 3.
 

Eval compute in
  let a := (mk_bv 5 [false; false; true; true; true]) in
    let b := (mk_bv 3 [true; true; true; true; true]) in
      add_bv a b 6.

Definition sub_bv (a b: bv) (size: nat) : bv := 
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c - d in 
    n2bv_bv e size.
Check sub_bv.

Definition mul_bv (a b: bv) (size: nat) : bv :=
  let c := bv2n_bv a in
  let d := bv2n_bv b in
  let e := c * d in
    n2bv_bv e size.
Check mul_bv.

Fixpoint exp (m n: nat) {struct n}: nat :=
  match n with
    | O    => 1%nat
    | S n' => m * (exp m n')
  end.
Notation "x ^ y" := (exp x y).

Definition neg_bv (a: bv) (size: nat): bv :=
  let b := exp 2 size in
  let c := bv2n_bv a in
  let d := b - c in
    n2bv_bv d size. 
Check neg_bv.

Definition div_bv (a b: bv) (size: nat): bv := 
  let c := (bv2n_bv b) in
    match c with
      | O => mk_bv 0 nil
      | _ => let d := (bv2n_bv a) in mk_bv size (n2b_bv size (N.to_nat (N.div (N.of_nat d) (N.of_nat c))))
    end.
Check div_bv.

Definition urem_bv (a b: bv) (size: nat) : bv :=
  let c := (bv2n_bv b) in
    match c with
      | O => mk_bv 0 nil
      | _ => let d := (bv2n_bv a) in mk_bv size (n2b_bv size (N.to_nat (N.modulo (N.of_nat d) (N.of_nat c))))
   end.
Check urem_bv.

Definition ult_bv (a b: bv) :=
  let c := (bv2n_bv a) in
  let d := (bv2n_bv b) in
    (c < d).
Check ult_bv.

Fixpoint drop_n_bv (l : list bool) (n : nat) : list bool :=
  match n with
    | O => l
    | S n2 => drop_n_bv (@List.tl bool l) n2
  end.
Check drop_n_bv.

Fixpoint first_n_bv (l : list bool) (n : nat) : list bool :=
  match n with
    | O => nil
    | S n2 =>
    match l with
      | nil => nil
      | x :: l2 => x :: (first_n_bv l2 n2)
    end
  end.
Check first_n_bv.

Definition extract_bv (l : list bool) (i : nat) (j : nat) : list bool :=
  let l2 := drop_n_bv l i in (first_n_bv l2 j).
Check extract_bv.

Definition wd (a: bv) : Prop :=
  match a with
    | mk_bv s l => length l = s
  end.
Check wd.
Eval compute in wd (mk_bv 6 [false ; false ; true ; true ; true]).

Lemma concat_wd : forall (m: nat) (a b: bv), wd a -> wd b -> wd (concat_bv a b).
Proof. intros.
         induction a. induction b. 
           simpl. rewrite app_length. destruct H, H0; reflexivity.
Qed.
Check concat_wd.

(*

Lemma and_wd: forall (a b: bv), wd a -> wd b -> wd (and_bv a b).
Proof. intros a b H0 H1.
         destruct a, b. unfold wd in *.
           induction bits0.
           - induction bits1.
             + simpl. easy.
             + simpl. 

*)
(*
Lemma add_wd: forall (size: nat) (a b: bv),
match add_bv2 a b size with
    | mk_bv s l => (length l) = size
  end.
Proof. intros. destruct a, b.
          induction bits0. 
           - induction bits1.
             + unfold add_bv2.
          destruct (append_false' (n2bv_bv 
                                    (bv2n_bv {| size := size0; bits := [] |} +    
                                     bv2n_bv {| size := size1; bits := [] |}) 0) 0). 
          simpl.
          destruct (append_false {| size := size0; bits := [] |} (size0 - 0)).
*)

(*
Eval compute in add_bv2 (mk_bv 3 [ true ; true ; true; false ]) (mk_bv 4 [false ; false ; true ; true ; true]) 20.
Eval compute in add_bv (mk_bv 3 [ true ; true ; true ]) (mk_bv 0 []) 3.
Eval compute in add_bv (mk_bv 0 []) (mk_bv 0 []) 0.
Eval compute in bv2n_bv (mk_bv 0 []).
Eval compute in n2bv_bv 0 0.
Eval compute in add_bv (mk_bv 3 [false ; false ; false]) (mk_bv 3 [false; false; false]) 3.
Eval compute in 
  match add_bv (mk_bv 3 [false ; false ; false]) (mk_bv 3 [false; false; false]) 3 with
    | mk_bv _ l => length l
  end.
Eval compute in 
  match add_bv (mk_bv 3 [true ; true ; true]) (mk_bv 3 [true; false; true]) 3 with
    | mk_bv _ l => length l
  end.
Eval compute in 
  match mul_bv (mk_bv 3 [true ; true ; true]) (mk_bv 3 [true; true; true]) 5 with
    | mk_bv _ l => length l
  end.

Eval compute in neg_bv (mk_bv 0 [ false]).
Eval compute in bv2n_bv (mk_bv 0 [ false]).
Eval compute in bv2n_bv (mk_bv 0 [true]).
Eval compute in exp 2 5.
Eval compute in neg_bv (mk_bv 2 [ true; true ]) 5.
*)

(*
Lemma add_wd: forall (size: nat) (a b: bv), 
  match (add_bv2 a b size) with
    | mk_bv s l => length l = size
  end.
Proof. destruct a, b. intros. unfold wd in *.
         induction bits0 as [ | hd1 tl1 ih1 ].
         - induction bits1 as [ | hd2 tl2 ih2 ].
           + unfold add_bv2. unfold bv2n_bv. simpl. unfold append_false. simpl.
         - induction bits1 as [ | hd2 tl2 ih2 ].
           + simpl in *. easy.
           + contradict H. simpl. easy.


Lemma add_wd: forall (size: nat) (a b: bv), 
  match a with
    | mk_bv s1 l1 =>
    match b with
      | mk_bv s2 l2 => s1 = s2 -> wd a -> wd b -> wd (add_bv2 a b s1)
    end
  end.
Proof. destruct a, b. intros. destruct H0, H1. unfold wd in *.
         induction bits0 as [ | hd1 tl1 ih1 ]. 
         - induction bits1 as [ | hd2 tl2 ih2 ].
           + simpl in *. easy.
           + contradict H. simpl. easy.
         - induction bits1 as [ | hd2 tl2 ih2 ]. 
           + simpl in *. contradict H. easy.
           + unfold add_bv2 in *. rewrite H. unfold bv2n_bv in *. unfold b2p_bv in *.

 simpl in *.
           rewrite <- H. apply ih2.

 unfold add_bv2. destruct bv2n_bv. simpl.

 append_false', n2bv_bv. destruct bv2n_bv. simpl.


 destruct (add_bv2 (mk_bv  (length (hd1 :: tl1)) (hd1 :: tl1)) (mk_bv (length (hd1 :: tl1)) (hd2 :: tl2)) (length (hd1 :: tl1))).
 destruct (add_bv2 (mk_bv  (length (hd1 :: tl1)) (hd1 :: tl1)) (mk_bv (length tl2) tl2) (length (hd1 :: tl1))).
 simpl in *. unfold add_bv2 in *. destruct bv2n_bv in *. destruct bv2n_bv in *. simpl in *.

 SearchRewrite (_ :: _).
 destruct add_bv2.
*)

Lemma nth_appendl A : forall (l1 l2:list A) (i:nat) (d:A),
    (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d.
Proof.
  induction l1 as [ |a l1 IHl1].
  - simpl.
    intros l2 i d H. elim (Lt.lt_n_0 _ H).
  - simpl. intros l2 [ |i] d Hi.
    * reflexivity.
    * apply IHl1. apply Lt.lt_S_n. assumption.
Qed.
Check nth_appendl.


Lemma nth_concat_l_bv : forall (a b: bv) (i : nat),
      match a with
        | mk_bv s l1 => wd a -> wd b -> (i < s) -> bb_nth_bv i (concat_bv a b) = bb_nth_bv i a
      end.
Proof. intros.
         induction a. induction b.
           simpl. intros. rewrite nth_appendl.
             - reflexivity.
             - rewrite H. exact H1.
Qed.
Check nth_concat_l_bv. 


End DTBV.


(* Representation of bit vectors as a pair of boolean list and size; followed by implementation of standard operations *)

Module BV.

Import N.
Local Open Scope N_scope.

  (** The type of bit vectors *)
  Definition t := (list bool * N)%type.

  (** The empty bit vector *)
  Definition empty : t := (nil, 0).


  (** Test weither a bit vector is empty *)
  Definition is_empty (bv : t) : bool :=
    let (_, n) := bv in
    match n with
    | N0 => true
    | _ => false
    end.

  (** Test weither a bit vector is zero (this defines the semantics of
      the 0 bit vector) *)
  Definition is_zero (bv : t) : bool :=
    let (b, _) := bv in
    List.forallb (fun x => negb x) b.

  (** Concatenation of two bit vectors *)
  Definition concat (bv1 bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (b1 ++ b2, n1 + n2).

  (** Bitwise not *)
  Definition not (bv : t) : t :=
    let (b, n) := bv in
    (List.map negb b, n).

  (** Bitwise and *)
  Definition and (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 andb b1 b2, n1).

  (** Bitwise or *)
  Definition or (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 orb b1 b2, n1).

  (** Bitwise xor *)
  Definition xor (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    (map2 xorb b1 b2, n1).

  (** Lower weight bit *)
  Definition lower (bv : t) : bool :=
    let (b, _) := bv in
    List.hd false b.

  (** Higher weight bit *)
  Definition high (bv : t) : bool :=
    let (b, _) := bv in
    List.last b false.

  (** Left shift *)
  Definition shiftleft (bv : t) : t :=
    let (b, n) := bv in
    (false::(List.removelast b), n).

  (** Right shift *)
  Definition shiftright (bv : t) : t :=
    let (b, n) := bv in
    ((List.tl b) ++ (false::nil), n).

  (** Left shift of [n] bits *)
  Fixpoint shiftleft_n (bv : t) (n : nat) : t :=
    match n with
      | O => bv
      | S n2 => shiftleft_n (shiftleft bv) n2
    end.

  (** Right shift of [n] bits *)
  Fixpoint shiftright_n (bv : t) (n : nat) : t :=
    match n with
      | O => bv
      | S n2 => shiftright_n (shiftright bv) n2
    end.

  (** Computes the [i]th bit *)
  Definition bb_nth (i : nat) (bv : t) : bool :=
    let (b, _) := bv in
    nth i b false.

  (** Computation of the unsigned integer represented by a bit vector *)
  Fixpoint b2p (b : list bool) : option positive :=
    match b with
    | nil => None
    | false::b =>
      match b2p b with
      | Some p => Some (xO p)
      | None => None
      end
    | true::b =>
      match b2p b with
      | Some p => Some (xI p)
      | None => Some xH
      end
    end.

  Definition bv2n (bv : t) : N :=
    let (b, _) := bv in
    match b2p b with
    | None => N0
    | Some p => Npos p
    end.

  (** Computation of the bit vector representing an integer *)
  Fixpoint p2bv (p : positive) : t :=
    match p with
    | xO p =>
      let (b,n) := p2bv p in
      (false::b, n+1)
    | xI p =>
      let (b,n) := p2bv p in
      (true::b, n+1)
    | xH => (true::nil, 1)
    end.

  Definition n2bv (n : N) : t :=
    match n with
    | N0 => (false::nil, 1)
    | Npos p => p2bv p
    end.

  Definition n2b (n : N) : list bool :=
    let (b, _) := n2bv n in b.

  (* We may want to change the definition of arithmetic operations *)
  (** Addition *)
  Definition add (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 + n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Subtraction *)
  Definition sub (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 - n4) in
    let b3 := (n2b n5) in
    (b3, n1).

  (** Multiplication *)
  Definition mul (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n3 := (bv2n bv1) in
    let n4 := (bv2n bv2) in
    let n5 := (n3 * n4) in
    let b3 := (n2b n5) in
    (b3, n1).

(* Eval compute in mul ((false :: true :: false :: true :: nil), 4) ((false :: true :: false :: false :: nil), 4). *)

  (** Negation *)
  Definition neg (bv1 : t) (n : N) : t :=
    let (b1, n1) := bv1 in
    let n2 := 2 ^ n in
    let n3 := (bv2n bv1) in
    let n4 := n2 - n3 in
    ((n2b n4), n).

Eval compute in neg ([ true ; false ], 2) 5.
Eval compute in neg ([ true ; true ], 2) 5.

  (** Division *)
  Definition udiv (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2b (n3 / n4)), n1)
    end.

  (** Reminder *)
  Definition urem (bv1 : t) (bv2 : t) : t :=
    let (b1, n1) := bv1 in
    let (b2, n2) := bv2 in
    let n4 := (bv2n bv2) in
    match n4 with
      | 0 => (nil, 0)
      | _ =>
      let n3 := (bv2n bv1) in
      ((n2b (n3 mod n4)), n1)
    end.

  (** Unsigned less than *)
  Definition ult (bv1 : t) (bv2 : t) :=
    let n1 := (bv2n bv1) in
    let n2 := (bv2n bv2) in
    (n1 < n2).

  (** Drops the [n] bits of lowest weight *)
  Fixpoint drop_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => l
      | S n2 => drop_n (@List.tl bool l) n2
    end.

  (** Keep the [n] bits of lowest weight *)
  Fixpoint first_n (l : list bool) (n : nat) : list bool :=
    match n with
      | O => nil
      | S n2 =>
      match l with
        | nil => nil
        | x :: l2 => x :: (first_n l2 n2)
      end
    end.

  (** Extracts the bits between i (included) and j (excluded) *)
  Definition extract (l : list bool) (i : nat) (j : nat) : list bool :=
    let l2 := drop_n l i in
    (first_n l2 j).

End BV.



Module BVProof.

  Import BV.
  Local Open Scope N_scope.

  (** Bit vectors are well-founded when their length match the length of their list *)
  Definition wf (bv:t) : Prop :=
     let (b,n) := bv in N.of_nat (length b) = n.
(*  Eval compute in wf ((true::nil), 2). *)

  (** All the operations preserve well-foundness *)

  Lemma empty_wf : wf empty.
  Proof. reflexivity. Qed.

  Lemma concat_wf : forall (bv1 bv2:t), wf bv1 -> wf bv2 -> wf (concat bv1 bv2).
  Proof.
    intros [b1 n1] [b2 n2] H1 H2.
    simpl.
    rewrite app_length.
    rewrite Nat2N.inj_add.
    simpl in H1. simpl in H2.
    rewrite H1. rewrite H2.
    reflexivity.
  Qed.  

  (** Auxiliary lemmas *)

  Lemma nth_appendl A : forall (l1 l2:list A) (i:nat) (d:A),
    (i < length l1)%nat -> nth i (l1 ++ l2) d = nth i l1 d.
  Proof.
    induction l1 as [ |a l1 IHl1].
    - simpl.
      intros l2 i d H. elim (Lt.lt_n_0 _ H).
    - simpl. intros l2 [ |i] d Hi.
      * reflexivity.
      * apply IHl1. apply Lt.lt_S_n. assumption.
  Qed.  

  Lemma Nat2N_inj_lt i j :
    (N.of_nat i < N.of_nat j) -> (i < j)%nat.
  Proof.
    now rewrite Compare_dec.nat_compare_lt, Nat2N.inj_compare.
  Qed.


  (** Properties of the operations on well-founded bit vectors *)

  Lemma nth_concat_l : forall(bv1 bv2:t) (i : nat),
    let (b1, n1) := bv1 in
    wf bv1 -> wf bv2 -> (N.of_nat i < n1) -> bb_nth i (concat bv1 bv2) = bb_nth i bv1.
  Proof.
    intros [b1 n1] [b2 n2]. simpl. intros i H1 H2 Hi.
    rewrite nth_appendl.
    - reflexivity.
    - rewrite <- H1 in Hi.
      apply Nat2N_inj_lt.
      assumption.
  Qed.

End BVProof.

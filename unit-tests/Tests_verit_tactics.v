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


Add Rec LoadPath "../src" as SMTCoq.

Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.
Open Scope Z_scope.


(* verit tactic *)

Lemma check_univ (x1: bool):
  (x1 && (negb x1)) = false.
Proof using.
  verit.
Qed.

Lemma fun_const2 :
  forall f (g : Z -> Z -> bool),
    (forall x, g (f x) 2) -> g (f 3) 2.
Proof using. verit. Qed.


(* Simple connectives *)

Goal forall (a:bool), a || negb a.
Proof using.
  verit.
Qed.

Goal forall a, negb (a || negb a) = false.
Proof using.
  verit.
Qed.

Goal forall a, (a && negb a) = false.
Proof using.
  verit.
Qed.

Goal forall a, negb (a && negb a).
Proof using.
  verit.
Qed.

Goal forall a, implb a a.
Proof using.
  verit.
Qed.

Goal forall a, negb (implb a a) = false.
Proof using.
  verit.
Qed.

Goal forall a , (xorb a a) || negb (xorb a a).
Proof using.
  verit.
Qed.

Goal forall a, (a||negb a) || negb (a||negb a).
Proof using.
  verit.
Qed.

Goal true.
Proof using.
  verit.
Qed.

Goal negb false.
Proof using.
  verit.
Qed.

Goal forall a, Bool.eqb a a.
Proof using.
  verit.
Qed.

Goal forall (a:bool), a = a.
Proof using.
  verit.
Qed.


(* Other connectives *)

Goal (false || true) && false = false.
Proof using.
  verit.
Qed.


Goal negb true = false.
Proof using.
  verit.
Qed.


Goal false = false.
Proof using.
  verit.
Qed.


Goal forall x y, Bool.eqb (xorb x y) ((x && (negb y)) || ((negb x) && y)).
Proof using.
  verit.
Qed.


Goal forall x y, Bool.eqb (negb (xorb x y)) ((x && y) || ((negb x) && (negb y))).
Proof using.
  verit.
Qed.


Goal forall x y, Bool.eqb (implb x y) ((x && y) || (negb x)).
Proof using.
  verit.
Qed.


Goal forall x y z, Bool.eqb (ifb x y z) ((x && y) || ((negb x) && z)).
Proof using.
  verit.
Qed.


(* Multiple negations *)

Goal forall a, orb a (negb (negb (negb a))) = true.
Proof using.
  verit.
Qed.


(* Polarities *)

Goal forall a b, andb (orb a b) (negb (orb a b)) = false.
Proof using.
  verit.
Qed.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof using.
  verit.
Qed.


(* sat2.smt *)
(* ((a ∧ b) ∨ (b ∧ c)) ∧ ¬b = ⊥ *)

Goal forall a b c, (((a && b) || (b && c)) && (negb b)) = false.
Proof using.
  verit.
Qed.


(* sat3.smt *)
(* (a ∨ a) ∧ ¬a = ⊥ *)

Goal forall a, ((a || a) && (negb a)) = false.
Proof using.
  verit.
Qed.


(* sat4.smt *)
(* ¬(a ∨ ¬a) = ⊥ *)

Goal forall a, (negb (a || (negb a))) = false.
Proof using.
  verit.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
    (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof using.
  verit.
Qed.


(* The same, but with a, b and c being concrete terms *)

Goal forall i j k,
    let a := i == j in
    let b := j == k in
    let c := k == i in
    (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof using.
  verit.
Qed.


(* sat6.smt *)
(* (a ∧ b) ∧ (c ∨ d) ∧ ¬(c ∨ (a ∧ b ∧ d)) = ⊥ *)

Goal forall a b c d, ((a && b) && (c || d) && (negb (c || (a && b && d)))) = false.
Proof using.
  verit.
Qed.


(* sat7.smt *)
(* a ∧ b ∧ c ∧ (¬a ∨ ¬b ∨ d) ∧ (¬d ∨ ¬c) = ⊥ *)

Goal forall a b c d, (a && b && c && ((negb a) || (negb b) || d) && ((negb d) || (negb c))) = false.
Proof using.
  verit.
Qed.


(* Pigeon hole: 4 holes, 5 pigeons *)

Goal forall x11 x12 x13 x14 x15 x21 x22 x23 x24 x25 x31 x32 x33 x34 x35 x41 x42 x43 x44 x45, (
  (orb (negb x11) (negb x21)) &&
  (orb (negb x11) (negb x31)) &&
  (orb (negb x11) (negb x41)) &&
  (orb (negb x21) (negb x31)) &&
  (orb (negb x21) (negb x41)) &&
  (orb (negb x31) (negb x41)) &&

  (orb (negb x12) (negb x22)) &&
  (orb (negb x12) (negb x32)) &&
  (orb (negb x12) (negb x42)) &&
  (orb (negb x22) (negb x32)) &&
  (orb (negb x22) (negb x42)) &&
  (orb (negb x32) (negb x42)) &&

  (orb (negb x13) (negb x23)) &&
  (orb (negb x13) (negb x33)) &&
  (orb (negb x13) (negb x43)) &&
  (orb (negb x23) (negb x33)) &&
  (orb (negb x23) (negb x43)) &&
  (orb (negb x33) (negb x43)) &&

  (orb (negb x14) (negb x24)) &&
  (orb (negb x14) (negb x34)) &&
  (orb (negb x14) (negb x44)) &&
  (orb (negb x24) (negb x34)) &&
  (orb (negb x24) (negb x44)) &&
  (orb (negb x34) (negb x44)) &&

  (orb (negb x15) (negb x25)) &&
  (orb (negb x15) (negb x35)) &&
  (orb (negb x15) (negb x45)) &&
  (orb (negb x25) (negb x35)) &&
  (orb (negb x25) (negb x45)) &&
  (orb (negb x35) (negb x45)) &&


  (orb (negb x11) (negb x12)) &&
  (orb (negb x11) (negb x13)) &&
  (orb (negb x11) (negb x14)) &&
  (orb (negb x11) (negb x15)) &&
  (orb (negb x12) (negb x13)) &&
  (orb (negb x12) (negb x14)) &&
  (orb (negb x12) (negb x15)) &&
  (orb (negb x13) (negb x14)) &&
  (orb (negb x13) (negb x15)) &&
  (orb (negb x14) (negb x15)) &&

  (orb (negb x21) (negb x22)) &&
  (orb (negb x21) (negb x23)) &&
  (orb (negb x21) (negb x24)) &&
  (orb (negb x21) (negb x25)) &&
  (orb (negb x22) (negb x23)) &&
  (orb (negb x22) (negb x24)) &&
  (orb (negb x22) (negb x25)) &&
  (orb (negb x23) (negb x24)) &&
  (orb (negb x23) (negb x25)) &&
  (orb (negb x24) (negb x25)) &&

  (orb (negb x31) (negb x32)) &&
  (orb (negb x31) (negb x33)) &&
  (orb (negb x31) (negb x34)) &&
  (orb (negb x31) (negb x35)) &&
  (orb (negb x32) (negb x33)) &&
  (orb (negb x32) (negb x34)) &&
  (orb (negb x32) (negb x35)) &&
  (orb (negb x33) (negb x34)) &&
  (orb (negb x33) (negb x35)) &&
  (orb (negb x34) (negb x35)) &&

  (orb (negb x41) (negb x42)) &&
  (orb (negb x41) (negb x43)) &&
  (orb (negb x41) (negb x44)) &&
  (orb (negb x41) (negb x45)) &&
  (orb (negb x42) (negb x43)) &&
  (orb (negb x42) (negb x44)) &&
  (orb (negb x42) (negb x45)) &&
  (orb (negb x43) (negb x44)) &&
  (orb (negb x43) (negb x45)) &&
  (orb (negb x44) (negb x45)) &&


  (orb (orb (orb x11 x21) x31) x41) &&
  (orb (orb (orb x12 x22) x32) x42) &&
  (orb (orb (orb x13 x23) x33) x43) &&
  (orb (orb (orb x14 x24) x34) x44) &&
  (orb (orb (orb x15 x25) x35) x45)) = false.
Proof using.
  verit.
Qed.


(* uf1.smt *)

Goal forall a b c f p, ( (a =? c) && (b =? c) && ((negb (f a =?f b)) || ((p a) && (negb (p b))))) = false.
Proof using.
  verit.
Qed.


(* uf2.smt *)

Goal forall a b c (p : Z -> bool), ((((p a) && (p b)) || ((p b) && (p c))) && (negb (p b))) = false.
Proof using.
  verit.
Qed.


(* uf3.smt *)

Goal forall x y z f, ((x =? y) && (y =? z) && (negb (f x =? f z))) = false.
Proof using.
  verit.
Qed.


(* uf4.smt *)

Goal forall x y z f, ((negb (f x =? f y)) && (y =? z) && (f x =? f (f z)) && (x =? y)) = false.
Proof using.
  verit.
Qed.


(* uf5.smt *)

Goal forall a b c d e f, ((a =? b) && (b =? c) && (c =? d) && (c =? e) && (e =? f) && (negb (a =? f))) = false.
Proof using.
  verit.
Qed.


(* lia1.smt *)

Goal forall x y z, implb ((x <=? 3) && ((y <=? 7) || (z <=? 9)))
                         ((x + y <=? 10) || (x + z <=? 12)) = true.
Proof using.
  verit.
Qed.

(* lia2.smt *)

Goal forall x, implb (x - 3 =? 7) (x >=? 10) = true.
Proof using.
  verit.
Qed.

(* lia3.smt *)

Goal forall x y, implb (x >? y) (y + 1 <=? x) = true.
Proof using.
  verit.
Qed.

(* lia4.smt *)

Goal forall x y, Bool.eqb (x <? y) (x <=? y - 1) = true.
Proof using.
  verit.
Qed.

(* lia5.smt *)

Goal forall x y, ((x + y <=? - (3)) && (y >=? 0)
                  || (x <=? - (3))) && (x >=? 0) = false.
Proof using.
  verit.
Qed.

(* lia6.smt *)

Goal forall x, implb (andb ((x - 3) <=? 7) (7 <=? (x - 3))) (x >=? 10) = true.
Proof using.
  verit.
Qed.

(* lia7.smt *)

Goal forall x, implb (x - 3 =? 7) (10 <=? x) = true.
Proof using.
  verit.
Qed.

(* Misc *)

Lemma irrelf_ltb a b c:
  (Z.ltb a b) && (Z.ltb b c) && (Z.ltb c a) = false.
Proof using.
  verit.
Qed.

Lemma comp f g (x1 x2 x3 : Z) :
  ifb (Z.eqb x1 (f x2))
      (ifb (Z.eqb x2 (g x3))
           (Z.eqb x1 (f (g x3)))
           true)
      true.
Proof using. verit. Qed.


(* More general examples *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof using.
  verit.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
    (negb (f a =? b)) || (negb (P (f a))) || (P b).
Proof using.
  verit.
Qed.


Goal forall b1 b2 x1 x2,
    implb
      (ifb b1
           (ifb b2 (2*x1+1 =? 2*x2+1) (2*x1+1 =? 2*x2))
           (ifb b2 (2*x1 =? 2*x2+1) (2*x1 =? 2*x2)))
      ((implb b1 b2) && (implb b2 b1) && (x1 =? x2)).
Proof using.
  verit.
Qed.


(* With let ... in ... *)

Goal forall b,
    let a := b in
    a && (negb a) = false.
Proof using.
  verit.
Qed.

Goal forall b,
    let a := b in
    a || (negb a) = true.
Proof using.
  verit.
Qed.
(* Does not work since the [is_true] coercion includes [let in]
Goal forall b,
  let a := b in
  a || (negb a).
Proof using.
  verit.
Qed.
*)

(* With concrete terms *)

Goal forall i j,
    let a := i == j in
    a && (negb a) = false.
Proof using.
  verit.
Qed.

Goal forall i j,
    let a := i == j in
    a || (negb a) = true.
Proof using.
  verit.
Qed.

Goal forall (i j:int),
    (i == j) && (negb (i == j)) = false.
Proof using.
  verit.
Qed.

Goal forall (i j:int),
    ~ ((i = j) /\ (~ (i = j))).
Proof using. verit. Qed.

Goal forall i j, (i == j) || (negb (i == j)).
Proof using.
  verit.
Qed.

Goal forall (i j:int), (i = j) \/ (~ (i = j)).
Proof using.
  verit.
Qed.


(* Congruence in which some premises are REFL *)

Goal forall (f:Z -> Z -> Z) x y z,
    implb (x =? y) (f z x =? f z y).
Proof using.
  verit.
Qed.

Goal forall (P:Z -> Z -> bool) x y z,
    implb (x =? y) (implb (P z x) (P z y)).
Proof using.
  verit.
Qed.


(* Some examples of using verit with lemmas. Use <verit H1 .. Hn>
   to temporarily add the lemmas H1 .. Hn to the verit environment. *)

Lemma taut1_bool :
  forall f, f 2 =? 0 -> f 2 =? 0.
Proof using. verit. Qed.

Lemma taut1 :
  forall f, f 2 = 0 -> f 2 = 0.
Proof using. verit. Qed.

Lemma taut2_bool :
  forall f, 0 =? f 2 -> 0 =? f 2.
Proof using. verit. Qed.

Lemma taut2 :
  forall f, 0 = f 2 -> 0 = f 2.
Proof using. verit. Qed.

Lemma taut3_bool :
  forall f, f 2 =? 0 -> f 3 =? 5 -> f 2 =? 0.
Proof using. verit. Qed.

Lemma taut3 :
  forall f, f 2 = 0 -> f 3 = 5 -> f 2 = 0.
Proof using. verit. Qed.

Lemma taut4_bool :
  forall f, f 3 =? 5 -> f 2 =? 0 -> f 2 =? 0.
Proof using. verit. Qed.

Lemma taut4 :
  forall f, f 3 = 5 -> f 2 = 0 -> f 2 = 0.
Proof using. verit. Qed.

Lemma test_eq_sym a b : implb (a =? b) (b =? a).
Proof using. verit. Qed.

Lemma taut5_bool :
  forall f, 0 =? f 2 -> f 2 =? 0.
Proof using. verit. Qed.

Lemma taut5 :
  forall f, 0 = f 2 -> f 2 = 0.
Proof using. verit. Qed.

Lemma fun_const_Z_bool :
  forall f , (forall x, f x =? 2) ->
             f 3 =? 2.
Proof using. verit. Qed.

Lemma fun_const_Z :
  forall f , (forall x, f x = 2) ->
             f 3 = 2.
Proof using. verit. Qed.

Lemma lid (A : bool) :  A -> A.
Proof using. verit. Qed.

Lemma lpartial_id A :
  (xorb A A) -> (xorb A A).
Proof using. verit. Qed.

Lemma llia1_bool X Y Z:
  (X <=? 3) && ((Y <=? 7) || (Z <=? 9)) ->
  (X + Y <=? 10) || (X + Z <=? 12).
Proof using. verit. Qed.

Lemma llia1 X Y Z:
  (X <= 3) /\ ((Y <= 7) \/ (Z <= 9)) ->
  (X + Y <= 10) \/ (X + Z <= 12).
Proof using. verit. Qed.

Lemma llia2_bool X:
  X - 3 =? 7 -> X >=? 10.
Proof using. verit. Qed.

Lemma llia2 X:
  X - 3 = 7 -> X >= 10.
Proof using. verit. Qed.

Lemma llia3_bool X Y:
  X >? Y -> Y + 1 <=? X.
Proof using. verit. Qed.

Lemma llia3 X Y:
  X > Y -> Y + 1 <= X.
Proof using. verit. Qed.

Lemma llia6_bool X:
  andb ((X - 3) <=? 7) (7 <=? (X - 3)) -> X >=? 10.
Proof using. verit. Qed.

Lemma llia6 X:
  ((X - 3) <= 7) /\ (7 <= (X - 3)) -> X >= 10.
Proof using. verit. Qed.

Lemma even_odd b1 b2 x1 x2:
  (ifb b1
       (ifb b2 (2*x1+1 =? 2*x2+1) (2*x1+1 =? 2*x2))
       (ifb b2 (2*x1 =? 2*x2+1) (2*x1 =? 2*x2))) ->
  ((implb b1 b2) && (implb b2 b1) && (x1 =? x2)).
Proof using. verit. Qed.

Lemma lcongr1_bool (a b : Z) (P : Z -> bool) f:
  (f a =? b) -> (P (f a)) -> P b.
Proof using. verit. Qed.

Lemma lcongr1 (a b : Z) (P : Z -> bool) f:
  (f a = b) -> (P (f a)) -> P b.
Proof using. verit. Qed.

Lemma lcongr2_bool (f:Z -> Z -> Z) x y z:
  x =? y -> f z x =? f z y.
Proof using. verit. Qed.

Lemma lcongr2 (f:Z -> Z -> Z) x y z:
  x = y -> f z x = f z y.
Proof using. verit. Qed.

Lemma lcongr3_bool (P:Z -> Z -> bool) x y z:
  x =? y -> P z x -> P z y.
Proof using. verit. Qed.

Lemma lcongr3 (P:Z -> Z -> bool) x y z:
  x = y -> P z x -> P z y.
Proof using. verit. Qed.

Lemma test20_bool :  forall x, (forall a, a <? x) -> 0 <=? x = false.
Proof using. verit. Qed.

Lemma test20 :  forall x, (forall a, a < x) -> ~ (0 <= x).
Proof using. verit. Qed.

Lemma test21_bool : forall x, (forall a, negb (x <=? a)) -> negb (0 <=? x).
Proof using. verit. Qed.

Lemma test21 : forall x, (forall a, ~ (x <= a)) -> ~ (0 <= x).
Proof using. verit. Qed.

Lemma un_menteur_bool (a b c d : Z) dit:
  dit a =? c ->
  dit b =? d ->
  (d =? a) || (b =? c) ->
  (a =? c) || (a =? d) ->
  (b =? c) || (b =? d) ->
  a =? d.
Proof using. verit. Qed.

Lemma un_menteur (a b c d : Z) dit:
  dit a = c ->
  dit b = d ->
  (d = a) \/ (b = c) ->
  (a = c) \/ (a = d) ->
  (b = c) \/ (b = d) ->
  a = d.
Proof using. verit. Qed.

Lemma const_fun_is_eq_val_0_bool :
  forall f : Z -> Z,
    (forall a b, f a =? f b) ->
    forall x, f x =? f 0.
Proof using. verit. Qed.

Lemma const_fun_is_eq_val_0 :
  forall f : Z -> Z,
    (forall a b, f a = f b) ->
    forall x, f x = f 0.
Proof using. verit. Qed.

(* You can use <Add_lemmas H1 .. Hn> to permanently add the lemmas H1 ..
   Hn to the environment. You should use <Clear_lemmas> when you do not
   need them anymore (all the time, but especially for lemmas that were
   section hypotheses before closing the section) *)

Section S.
  Variable f : Z -> Z.
  Hypothesis th : forall x, Z.eqb (f x) 3.
  Add_lemmas th.
  Goal forall x, Z.eqb ((f x) + 1) 4.
  Proof using th. verit. Qed.
  Clear_lemmas.
End S.

Section fins_sat6.
  Variables a b c d : bool.
  Hypothesis andab : andb a b.
  Hypothesis orcd  : orb c d.
  Add_lemmas andab orcd.

  Lemma sat6 :  orb c (andb a (andb b d)).
  Proof using andab orcd. verit. Qed.
  Clear_lemmas.
End fins_sat6.


Section fins_lemma_multiple.
  Variable f' : Z -> Z.
  Variable g : Z -> Z.
  Variable k : Z.
  Hypothesis g_k_linear : forall x, g (x + 1) =? (g x) + k.
  Hypothesis f'_equal_k : forall x, f' x =? k.
  Add_lemmas g_k_linear f'_equal_k.

  Lemma apply_lemma_multiple : forall x y, g (x + 1) =? g x + f' y.
  Proof using g_k_linear f'_equal_k. verit. Qed.

  Clear_lemmas.
End fins_lemma_multiple.


Section fins_find_apply_lemma.
  Variable u : Z -> Z.
  Hypothesis u_is_constant : forall x y, u x =? u y.
  Add_lemmas u_is_constant.

  Lemma apply_lemma : forall x, u x =? u 2.
  Proof using u_is_constant. verit. Qed.

  Lemma find_inst :
    implb (u 2 =? 5) (u 3 =? 5).
  Proof using u_is_constant. verit. Qed.

  Clear_lemmas.
End fins_find_apply_lemma.


Section mult3.
  Variable mult3 : Z -> Z.
  Hypothesis mult3_0 : mult3 0 =? 0.
  Hypothesis mult3_Sn : forall n, mult3 (n+1) =? mult3 n + 3.
  Add_lemmas mult3_0 mult3_Sn.

  Lemma mult3_4_12 : mult3 4 =? 12.
  Proof using mult3_0 mult3_Sn. verit. Qed. (* slow to verify with standard coq *)

  Clear_lemmas.
End mult3.


(* the program veriT doesn't return in reasonable time on the following lemma*)
(* Section mult. *)
(*   Variable mult : Z -> Z -> Z. *)
(*   Hypothesis mult_0 : forall x, mult 0 x =? 0. *)
(*   Hypothesis mult_Sx : forall x y, mult (x+1) y =? mult x y + y. *)

(*   Lemma mult_1_x : forall x, mult 1 x =? x. *)
(*   Proof using. verit mult_0 mult_Sx. *)
(*   Qed. *)
(* End mult. *)

Section implicit_transform.
  Variable A : Type.
  Variable HA : CompDec A.
  Variable f : A -> bool.
  Variable a1 a2 : A.
  Hypothesis f_const : forall b, implb (f b) (f a2).
  Hypothesis f_a1 : f a1.
  Add_lemmas f_const f_a1.

  Lemma implicit_transform :
    f a2.
  Proof using HA f_const f_a1. verit. Qed.

  Clear_lemmas.
End implicit_transform.

Section list.
  Hypothesis dec_Zlist : CompDec (list Z).
  Variable inlist : Z -> (list Z) -> bool.

  Hypothesis in_eq : forall a l, inlist a (a :: l).
  Hypothesis in_cons : forall a b l, implb (inlist a l) (inlist a (b::l)).
  Add_lemmas in_eq in_cons.

  Lemma in_cons1 :
    inlist 1 (1::2::nil).
  Proof using dec_Zlist in_eq in_cons. verit. Qed.

  Lemma in_cons2 :
    inlist 12 (2::4::12::nil).
  Proof using dec_Zlist in_eq in_cons. verit. Qed.

  Lemma in_cons3 :
    inlist 1 (5::1::(0-1)::nil).
  Proof using dec_Zlist in_eq in_cons. verit. Qed.

  Lemma in_cons4 :
    inlist 22 ((- (1))::22::nil).
  Proof using dec_Zlist in_eq in_cons. verit. Qed.

  Lemma in_cons5 :
    inlist 1 ((- 1)::1::nil).
  Proof using dec_Zlist in_eq in_cons. verit. Qed.

  (* Lemma in_cons_false1 : *)
  (*   inlist 1 (2::3::nil). *)
  (* verit. (*returns unknown*) *)

  (* Lemma in_cons_false2 : *)
  (*   inlist 1 ((-1)::3::nil). *)
  (* verit. (*returns unknown*) *)

  (* Lemma in_cons_false3 : *)
  (*   inlist 12 (11::13::(-12)::1::nil). *)
  (*   verit. (*returns unknown*) *)

  Hypothesis in_or_app : forall a l1 l2,
      implb (orb (inlist a l1) (inlist a l2))
            (inlist a (l1 ++ l2)).
  Add_lemmas in_or_app.

  Lemma in_app1 :
    inlist 1 (1::2::nil ++ nil).
  Proof using dec_Zlist in_eq in_cons in_or_app. verit. Qed.

  Lemma in_app2 :
    inlist 1 (nil ++ 2::1::nil).
  Proof using dec_Zlist in_eq in_cons in_or_app. verit. Qed.

  Lemma in_app3 :
    inlist 1 (1::3::nil ++ 2::1::nil).
  Proof using dec_Zlist in_eq in_cons in_or_app. verit. Qed.

  (* Lemma in_app_false1 : *)
  (*   inlist 1 (nil ++ 2::3::nil). *)
  (*   verit. (* returns unknown *) *)

  (* Lemma in_app_false2 : *)
  (*   inlist 1 (2::3::nil ++ nil). *)
  (*   verit. (* returns unknown *) *)


  (* Lemma in_app_false3 : *)
  (*   inlist 1 (2::3::nil ++ 5::6::nil). *)
  (*   verit. (* returns unknown*) *)

  Hypothesis in_nil :
    forall a, negb (inlist a nil).
  Hypothesis in_inv :
    forall a b l,
      implb (inlist b (a::l))
            (orb (a =? b) (inlist b l)).
  Hypothesis inlist_app_comm_cons:
    forall l1 l2 a b,
      Bool.eqb (inlist b (a :: (l1 ++ l2)))
               (inlist b ((a :: l1) ++ l2)).
  Add_lemmas in_nil in_inv inlist_app_comm_cons.

  Lemma coqhammer_example l1 l2 x y1 y2 y3:
    implb (orb (inlist x l1) (orb (inlist x l2) (orb (x =? y1) (inlist x (y2 ::y3::nil)))))
          (inlist x (y1::(l1 ++ (y2 :: (l2 ++ (y3 :: nil)))))).
  Proof using dec_Zlist in_eq in_cons in_or_app in_nil in_inv inlist_app_comm_cons. verit_no_check. Qed.

  Clear_lemmas.
End list.


Section GroupZ.
  Variable op : Z -> Z -> Z.
  Variable inv : Z -> Z.
  Variable e : Z.

  Hypothesis associative :
    forall a b c : Z, op a (op b c) =? op (op a b) c.
  Hypothesis identity :
    forall a : Z, (op e a =? a) && (op a e =? a).
  Hypothesis inverse :
    forall a : Z, (op a (inv a) =? e) && (op (inv a) a =? e).
  Add_lemmas associative identity inverse.

  Lemma unique_identity_Z e':
    (forall z, op e' z =? z) -> e' =? e.
  Proof using associative identity inverse. verit. Qed.

  Lemma simplification_right_Z x1 x2 y:
      op x1 y =? op x2 y -> x1 =? x2.
  Proof using associative identity inverse. verit. Qed.

  Lemma simplification_left_Z x1 x2 y:
      op y x1 =? op y x2 -> x1 =? x2.
  Proof using associative identity inverse. verit. Qed.

  Clear_lemmas.
End GroupZ.


Section GroupBool.
  Variable G : Type.
  Variable HG : CompDec G.
  Variable op : G -> G -> G.
  Variable inv : G -> G.
  Variable e : G.

  Notation "a ==? b" := (@eqb_of_compdec G HG a b) (at level 60).

  Hypothesis associative :
    forall a b c : G, op a (op b c) ==? op (op a b) c.
  Hypothesis identity :
    forall a : G, (op e a ==? a) && (op a e ==? a).
  Hypothesis inverse :
    forall a : G, (op a (inv a) ==? e) && (op (inv a) a ==? e).
  Add_lemmas associative identity inverse.

  Lemma unique_identity_bool e':
    (forall z, op e' z ==? z) -> e' ==? e.
  Proof using associative identity inverse. verit. Qed.

  Lemma simplification_right_bool x1 x2 y:
      op x1 y ==? op x2 y -> x1 ==? x2.
  Proof using associative identity inverse. verit. Qed.

  Lemma simplification_left_bool x1 x2 y:
      op y x1 ==? op y x2 -> x1 ==? x2.
  Proof using associative identity inverse. verit. Qed.

  Clear_lemmas.
End GroupBool.


Section Group.
  Variable G : Type.
  Variable HG : CompDec G.
  Variable op : G -> G -> G.
  Variable inv : G -> G.
  Variable e : G.

  Hypothesis associative :
    forall a b c : G, op a (op b c) = op (op a b) c.
  Hypothesis identity :
    forall a : G, (op e a = a) /\ (op a e = a).
  Hypothesis inverse :
    forall a : G, (op a (inv a) = e) /\ (op (inv a) a = e).
  (* TODO: apply [prop2bool_hyp] to lemmas added with [Add_lemmas] *)
  (* Add_lemmas associative identity inverse. *)

  Lemma unique_identity e':
    (forall z, op e' z = z) -> e' = e.
  Proof using associative identity inverse HG.
    intros pe'.
    verit (associative, identity, inverse, pe').
  Qed.

  Lemma simplification_right x1 x2 y:
      op x1 y = op x2 y -> x1 = x2.
  Proof using associative identity inverse HG.
    verit (associative, identity, inverse).
  Qed.

  Lemma simplification_left x1 x2 y:
      op y x1 = op y x2 -> x1 = x2.
  Proof using associative identity inverse HG.
    verit (associative, identity, inverse).
  Qed.

  Clear_lemmas.
End Group.


Section Linear1.
  Variable f : Z -> Z.
  Hypothesis f_spec : forall x,  (f (x+1) =? f x + 1)  && (f 0 =? 0).

  (* Cuts are not automatically proved when one equality is switched *)
  Lemma f_1 : f 1 =? 1.
  Proof using f_spec.
    verit_bool f_spec; replace (0 =? f 0) with (f 0 =? 0) by apply Z.eqb_sym; auto.
  Qed.
End Linear1.

Section Linear2.
  Variable g : Z -> Z.

  Hypothesis g_2_linear : forall x, Z.eqb (g (x + 1)) ((g x) + 2).

(* The call to veriT does not terminate *)
(* Lemma apply_lemma_infinite : *)
(*   forall x y, Z.eqb (g (x + y)) ((g x) + y * 2). *)
(* Proof using. verit g_2_linear. *)
End Linear2.

Section Input_switched1Bool.
  Variable m : Z -> Z.

  Hypothesis m_0 : m 0 =? 5.

  (* veriT switches the input lemma in this case *)
  Lemma five_m_0_bool : m 0 =? 5.
  Proof using m_0. verit m_0. Qed.
End Input_switched1Bool.

Section Input_switched1.
  Variable m : Z -> Z.

  Hypothesis m_0 : m 0 = 5.

  (* veriT switches the input lemma in this case *)
  Lemma five_m_0 : m 0 = 5.
  Proof using m_0. verit m_0. Qed.
End Input_switched1.

Section Input_switched2Bool.
  Variable h : Z -> Z -> Z.

  Hypothesis h_Sm_n : forall x y, h (x+1) y =? h x y.

  (* veriT switches the input lemma in this case *)
  Lemma h_1_0_bool : h 1 0 =? h 0 0.
  Proof using h_Sm_n. verit h_Sm_n. Qed.
End Input_switched2Bool.

Section Input_switched2.
  Variable h : Z -> Z -> Z.

  Hypothesis h_Sm_n : forall x y, h (x+1) y = h x y.

  (* veriT switches the input lemma in this case *)
  Lemma h_1_0 : h 1 0 = h 0 0.
  Proof using h_Sm_n. verit h_Sm_n. Qed.
End Input_switched2.


(** Examples of using the conversion tactics: TODO with trakt **)
(*
Local Open Scope positive_scope.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof using.
pos_convert.
verit.
Qed.

Goal forall (f : positive -> positive) (x y : positive),
  implb ((x + 3) =? y)
        ((3 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof using.
pos_convert.
verit.
Qed.

Local Close Scope positive_scope.

Local Open Scope N_scope.

Goal forall (f : N -> N) (x y : N),
  implb ((x + 3) =? y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof using.
N_convert.
verit.
Qed.

Goal forall (f : N -> N) (x y : N),
  implb ((x + 3) =? y)
        ((2 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof using.
N_convert.
verit.
Qed.

Local Close Scope N_scope.

Require Import NPeano.
Local Open Scope nat_scope.

Goal forall (f : nat -> nat) (x y : nat),
  implb (Nat.eqb (x + 3) y)
        ((f (x + 3)) <=? (f y))
  = true.
Proof using.
nat_convert.
verit.
Qed.

Goal forall (f : nat -> nat) (x y : nat),
  implb (Nat.eqb (x + 3) y)
        ((2 <? y) && ((f (x + 3)) <=? (f y)))
  = true.
Proof using.
nat_convert.
verit.
Qed.

Local Close Scope nat_scope.

(* An example with all 3 types and a binary function *)
Goal forall f : positive -> nat -> N, forall (x : positive) (y : nat),
  implb (x =? 3)%positive
    (implb (Nat.eqb y 7)
      (implb (f 3%positive 7%nat =? 12)%N
        (f x y =? 12)%N)) = true.
Proof using.
pos_convert.
nat_convert.
N_convert.
verit.
Qed.


(* The tactic simpl does too much here : *)
(* Goal forall x, 3 + x = x + 3. *)
(*   nat_convert. *)


(* Issue 10
   https://github.com/smtcoq/smtcoq/issues/10
*)
*)
Goal forall (x : positive), Zpos x <=? Zpos x.
Proof using.
  verit.
Qed.


Goal forall (x : positive) (a : Z), (Z.eqb a a) || negb (Zpos x <? Zpos x).
Proof using.
  verit.
Qed.


Section AppliedPolymorphicTypes1.
  Goal forall (f : option Z -> Z) (a b : Z),
      implb (Z.eqb a b) (Z.eqb (f (Some a)) (f (Some b))).
  Proof. verit. Qed.

  Goal forall (f : option Z -> Z) (a b : Z), a = b -> f (Some a) = f (Some b).
  Proof. verit. Qed.
End AppliedPolymorphicTypes1.


Section EqualityOnUninterpretedType1.
  Variable A : Type.
  Hypothesis HA : CompDec A.

  Goal forall (f : A -> Z) (a b : A), a = b -> f a = f b.
  Proof. verit. Qed.
End EqualityOnUninterpretedType1.

Section EqualityOnUninterpretedType2.
  Variable A B : Type.
  Hypothesis HA : CompDec A.
  Hypothesis HB : CompDec B.

  Goal forall (f : A -> Z) (a b : A), a = b -> f a = f b.
  Proof. verit. Qed.

  Goal forall (f : Z -> B) (a b : Z), a = b -> f a = f b.
  Proof. verit. Qed.

  Goal forall (f : A -> B) (a b : A), a = b -> f a = f b.
  Proof. verit. Qed.
End EqualityOnUninterpretedType2.

Section EqualityOnUninterpretedType3.
  Variable A B : Type.

  Goal forall (f : A -> Z) (a b : A), a = b -> f a = f b.
  Proof. verit. Abort.

  Goal forall (f : Z -> B) (a b : Z), a = b -> f a = f b.
  Proof. verit. Abort.

  Goal forall (f : A -> B) (a b : A), a = b -> f a = f b.
  Proof. verit. Abort.

  Goal forall (f : A -> A -> B) (a b c d : A), a = b -> c = d -> f a c = f b d.
  Proof. verit. Abort.
End EqualityOnUninterpretedType3.


Section AppliedPolymorphicTypes2.
  Variable B : Type.
  Variable HlB : CompDec (list B).

  Goal forall l1 l2 l3 l4 : list B,
      l1 ++ (l2 ++ (l3 ++ l4)) = l1 ++ (l2 ++ (l3 ++ l4)).
  Proof. verit. Qed.

  Hypothesis append_assoc_B :
    forall l1 l2 l3 : list B, l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.

  (* The hypothesis is not used *)
  Goal forall l1 l2 l3 l4 : list B,
      l1 ++ (l2 ++ (l3 ++ l4)) = l1 ++ (l2 ++ (l3 ++ l4)).
  Proof. verit append_assoc_B. Qed.

  (* The hypothesis is used *)
  Goal forall l1 l2 l3 l4 : list B,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof. verit append_assoc_B. Qed.
End AppliedPolymorphicTypes2.


Section Issue78.

  Goal forall (f : option Z -> Z) (a  b : Z), Some a = Some b -> f (Some a) = f (Some b).
  Proof. verit. Qed.

End Issue78.


Section SearchApp.
  Variable search : Z -> list Z -> bool.
  Hypothesis search_app : forall (x: Z) (l1 l2: list Z),
    search x (l1 ++ l2) = orb (search x l1) (search x l2).

  Lemma search_lemma : forall (x: Z) (l1 l2 l3: list Z),
      search x (l1 ++ l2 ++ l3) = search x (l3 ++ l2 ++ l1).
  Proof. verit. Qed.
End SearchApp.


Section UnknowUnderForall.
  Variable H5 : forall H : Z, Some H = None -> False.
  Variable H10 : @hd_error Z nil = None.
  Variable H6 : forall H : list (list Z),
      hd_error H = match H with
                   | nil => None
                   | x :: _ => Some x
                   end.

  Goal forall (l : list Z) (x : Z), hd_error l = Some x -> l <> nil.
  Proof. verit. Qed.
End UnknowUnderForall.


Section CompDecHypotheses.
  Variable A : Type.
  Variable H : CompDec A.
  Variable x : A.
  Variable l2 : list A.
  Hypothesis H1 : forall (x y : A) (x0 y0 : list A),
      x :: x0 = y :: y0 -> y = x /\ y0 = x0.
  Hypothesis H2 : forall (H : A) (H0 : list A), nil = H :: H0 -> False.
  Hypothesis H7_bool : forall (H : bool) (H0 H1 : list bool),
      ((H :: H0) ++ H1)%list = H :: H0 ++ H1.
  Hypothesis H7_A : forall (H : A) (H0 H1 : list A),
      ((H :: H0) ++ H1)%list = H :: H0 ++ H1.
  Hypothesis H6_bool : forall H : list bool, (nil ++ H)%list = H.
  Hypothesis H6_A : forall H : list A, (nil ++ H)%list = H.
  Variable search : forall {A : Type} {H: CompDec A}, A -> list A -> bool.
  Arguments search {_ _} _ _.
  Hypothesis H5_bool : forall (H : CompDec bool) (H0 H1 : bool) (H2 : list bool),
      search H0 (H1 :: H2) =
      (if eqb_of_compdec H H0 H1 then true else search H0 H2).
  Hypothesis H5_A : forall (H : CompDec A) (H0 H1 : A) (H2 : list A),
      search H0 (H1 :: H2) =
      (if eqb_of_compdec H H0 H1 then true else search H0 H2).
  Hypothesis H4_bool : forall (H : CompDec bool) (H0 : bool), search H0 nil = false.
  Hypothesis H4_A : forall (H : CompDec A) (H0 : A), search H0 nil = false.

  Goal search x l2 = search x l2.
  Proof. verit. Qed.

End CompDecHypotheses.


Section CompDecOnInterpretedType.
  Variable A : Type.
  Variable H : CompDec A.
  Variable x : A.
  Variable l2 : list A.
  Variable Hcompdec : CompDec (list A).
  Variable H1 : (forall (H3 H4 : A) (H5 H6 : list A),
        eqb_of_compdec Hcompdec (H3 :: H5) (H4 :: H6) --->
        eqb_of_compdec H H4 H3 && eqb_of_compdec Hcompdec H6 H5 = true).
  Variable H2 : (forall (H3 : A) (H4 : list A),
        eqb_of_compdec Hcompdec nil (H3 :: H4) ---> false = true).
  Variable Hcompdec0 : CompDec (list bool).
  Variable H7_bool : (forall (H3 : bool) (H4 H5 : list bool),
             eqb_of_compdec Hcompdec0 ((H3 :: H4) ++ H5)%list (H3 :: H4 ++ H5) = true).
  Variable H7_A : (forall (H3 : A) (H4 H5 : list A),
          eqb_of_compdec Hcompdec ((H3 :: H4) ++ H5)%list (H3 :: H4 ++ H5) = true).
  Variable H6_bool : (forall H3 : list bool,
             eqb_of_compdec Hcompdec0 (nil ++ H3)%list H3 = true).
  Variable H6_A : (forall H3 : list A, eqb_of_compdec Hcompdec (nil ++ H3)%list H3 = true).
  Variable c : CompDec bool.
  Variable search : forall {A : Type} {H: CompDec A}, A -> list A -> bool.
  Arguments search {_ _} _ _.
  Variable H5_bool : (forall (H3 H4 : bool) (H5 : list bool),
             search H3 (H4 :: H5) <---> eqb_of_compdec c H3 H4 || search H3 H5 = true).
  Variable H5_A : (forall (H3 H4 : A) (H5 : list A),
          search H3 (H4 :: H5) <---> eqb_of_compdec H H3 H4 || search H3 H5 = true).
  Variable H4_bool : (forall H3 : bool, search H3 nil <---> false = true).
  Variable H4_A : (forall H3 : A, search H3 nil <---> false = true).

  Goal search x l2 <---> search x l2 = true.
  Proof. verit. Qed.

End CompDecOnInterpretedType.



Section Issue92.
  Variable F : 0 = 1%Z.

  Goal false = false.
  Proof. verit_no_check. Qed.

  Goal 0 = 2.
  Proof. verit_no_check. Abort.
End Issue92.


Section Vauto.
  Variable A : Type.
  Variable HA : CompDec A.
  Variable H0 : forall (x y : A) (x0 y0 : list A), x :: x0 = y :: y0 -> y = x /\ y0 = x0.
  Variable H1 : forall (H : A) (H0 : list A), nil = H :: H0 -> False.
  Variable search : forall {A : Type} {H: CompDec A}, A -> list A -> bool.
  Arguments search {_ _} _ _.
  Variable H4_A : forall (H : CompDec A) (H0 H1 : A) (H2 : list A),
         search H0 (H1 :: H2) = eqb_of_compdec H H0 H1 || search H0 H2.
  Variable H2 : forall (H : CompDec (list A)) (H0 H1 : list A) (H2 : list (list A)),
       search H0 (H1 :: H2) = eqb_of_compdec H H0 H1 || search H0 H2.
  Variable H3_A : forall (H : CompDec A) (H0 : A), search H0 nil = false.
  Variable H4 : forall (H : CompDec (list A)) (H0 : list A), search H0 nil = false.
  Variables a b : A.
  Variable l : list A.
  Variable H : search b (a :: l).

  Goal eqb_of_compdec HA a b \/ search b l.
  Proof. verit_no_check. Qed.
End Vauto.


Require QInst.

Section Vauto2.
  Variable A : Type.
  Variable Inv_A : Z -> A -> Prop.
  Variable Inv_A_bool : Z -> A -> bool.
  Variable y : Z.
  Variable l : A.
  Variable z : Z.
  Variable H : Inv_A y l.
  Variable H0 : z <= y.
  Variable H2 : forall (H2 : A) (a b : Z),
      Inv_A_bool a H2 ---> (b <=? a) ---> Inv_A_bool b H2 = true.
  Variable H3 : Inv_A_bool y l = true.
  Variable H4 : (z <=? y) = true.
  Variable H5 : forall (c : A) (a b : Z),
      Inv_A_bool a c ---> (b <=? a) ---> Inv_A_bool b c = true.
  Variable CompDec0 : CompDec A.

  Goal
    (forall (c : A) (a b : Z),
        Inv_A_bool a c ---> (b <=? a) ---> Inv_A_bool b c = true) ->
    negb (Inv_A_bool y l) || negb (z <=? y) || Inv_A_bool z l.
  Proof. QInst.vauto. Qed.
End Vauto2.


Section PropToBool.
  Goal (forall (x x0 : bool) (x1 x2 : list bool), x :: x1 = x0 :: x2 -> x = x0) -> true.
  Proof. verit. Qed.
End PropToBool.


Section EqSym.
  Variable A : Type.
  Variable HA : CompDec A.
  Variable H8 : forall (h : list A) (l : list (list A)), tl (h :: l) = l.
  Variable H12_A : forall (h : A) (l : list A), tl (h :: l) = l.
  Variable H9 : forall (h : option A) (l : list (option A)), tl (h :: l) = l.
  Variable H12 : @tl (list A) nil = nil.
  Variable H13_A : @tl A nil = nil.
  Variable H14 : @tl (option A) nil = nil.
  Variable H13 : forall (h : list A) (l : list (list A)), hd_error (h :: l) = Some h.
  Variable H10_A : forall (h : A) (l : list A), hd_error (h :: l) = Some h.
  Variable H15 : forall (h : option A) (l : list (option A)), hd_error (h :: l) = Some h.
  Variable H10 : @hd_error (list A) nil = None.
  Variable H11_A : @hd_error A nil = None.
  Variable H16 : @hd_error (option A) nil = None.
  Variable H11 : forall x : list A, Some x = None -> False.
  Variable H7_A : forall x : A, Some x = None -> False.
  Variable H17 : forall x : option A, Some x = None -> False.
  Variable H7 : forall x x0 : list A, Some x = Some x0 -> x = x0.
  Variable H6_A : forall x x0 : A, Some x = Some x0 -> x = x0.
  Variable H18 : forall x x0 : option A, Some x = Some x0 -> x = x0.
  Variable H4 : forall (x : list A) (x0 : list (list A)), nil = x :: x0 -> False.
  Variable H3_A : forall (x : A) (x0 : list A), nil = x :: x0 -> False.
  Variable H5 : forall (x : option A) (x0 : list (option A)), nil = x :: x0 -> False.
  Variable H3 : forall (x x0 : list A) (x1 x2 : list (list A)), x :: x1 = x0 :: x2 -> x = x0.
  Variable H2_A : forall (x x0 : A) (x1 x2 : list A), x :: x1 = x0 :: x2 -> x = x0.
  Variable H6 : forall (x x0 : option A) (x1 x2 : list (option A)), x :: x1 = x0 :: x2 -> x = x0.
  Variable x : A.
  Variable xs : list A.
  Variable a : A.
  Variable r : list A.

  Goal hd_error (x :: xs) = Some a /\ tl (x :: xs) = r <-> x :: xs = a :: r.
  Proof. verit. Qed.
End EqSym.



Section PrenexDependentTypes.
  Variables A B : Type.
  Variable F : Type -> Type.
  Variable p : B -> F bool.
  Variable dep : forall (X:Type), A -> F X -> bool.
  Hypothesis H : forall (x : A) (y : B), dep bool x (p y) = true.

  Hypothesis HF : CompDec (F bool).
  Hypothesis HA : CompDec A.
  Hypothesis HB : CompDec B.

  Variable a : A.
  Variable b : B.

  Goal dep bool a (p b).
  Proof. verit. Qed.

End PrenexDependentTypes.


(*
Section NonPrenexDependentTypes.
  Variables A B : Type.
  Variable F : Type -> Type.
  Variable p : B -> F bool.
  Variable dep : A -> forall (X:Type), F X -> bool.
  Hypothesis H : forall (x : A) (y : B), dep x bool (p y) = true.

  Hypothesis HF : CompDec (F bool).
  Hypothesis HA : CompDec A.
  Hypothesis HB : CompDec B.

  Variable a : A.
  Variable b : B.

  Goal dep a bool (p b).
  Proof. Fail verit. Qed.

End NonPrenexDependentTypes.
*)


Section QInstAnd.

  Variable A : Type.
  Hypothesis HA : CompDec A.

  Hypothesis H : forall (a1 a2:A) l1 l2,
      eqb_of_compdec _ (a1::l1) (a2::l2) --->
        (eqb_of_compdec HA a1 a2) && (eqb_of_compdec _ l1 l2).

  Variables a1 a2 : A.
  Variables l1 l2 : list A.
  Hypothesis H1 : eqb_of_compdec _ (a1::l1) (a2::l2).

  Goal eqb_of_compdec _ a1 a2.
  Proof. verit. Qed.

  Variable inb : A -> list A -> bool.

  Hypothesis H2 : forall (a:A) l1 l2, inb a (l1++l2) ---> (inb a l1 || inb a l2).

  Goal negb (inb a1 (l1++l2)) || inb a1 l1 || inb a1 l2.
  Proof. verit. Qed.

End QInstAnd.


Section OCamlCompDec.
  Variable A : Type.
  Variable HA : CompDec A.
  Variable H2 : forall (h : A) (l x : list A), (h :: l) ++ x = h :: l ++ x.
  Variable H4 : forall x : list A, nil ++ x = x.
  Variable H5 : forall (x : A) (x0 : list A), nil = x :: x0 -> False.
  Variable H6 : forall (x : list A) (x0 : list (list A)), nil = x :: x0 -> False.
  Variable H8 : forall (x x0 : list A) (x1 x2 : list (list A)), x :: x1 = x0 :: x2 -> x = x0 /\ x1 = x2.
  Variable proj_list : forall A : Type, list A -> list A -> list A.
  Variable H0 : forall (H : list A) (H0 : A) (H1 : list A), proj_list A H (H0 :: H1) = H1.
  Variable H10 : forall (H : list (list A)) (H0 : list A) (H1 : list (list A)),
        proj_list (list A) H (H0 :: H1) = H1.
  Variable proj_list0 : forall A : Type, A -> list A -> A.
  Variable H9 : forall (H H0 : A) (H1 : list A), proj_list0 A H (H0 :: H1) = H0.
  Variable H12 : forall (H H0 : list A) (H1 : list (list A)), proj_list0 (list A) H (H0 :: H1) = H0.
  Variable H11 : forall (x : A) (x0 x1 : list A), x1 = nil \/ x1 = proj_list0 A x x1 :: proj_list A x0 x1.

  Goal forall (x y : list A) (a0 : A),
      x ++ y = a0::nil -> x = nil /\ y = a0::nil \/ x = a0::nil /\ y = nil.
  Proof. verit_no_check. Qed.
End OCamlCompDec.


Section TimeoutBool.
  Variable P : Z -> bool.
  Variable H0 : P 0.
  Variable HInd : forall n, implb (P n) (P (n + 1)).

  Goal P 3.
  Proof.
    verit_bool_base_auto_timeout (Some (H0, HInd)) 10.
  Qed.

  Goal P 3.
  Proof.
    verit_bool_no_check_base_auto_timeout (Some (H0, HInd)) 10.
  Qed.

  Goal P 3.
  Proof.
    verit_bool_timeout (H0, HInd) 10.
  Qed.

  Goal P 3.
  Proof.
    verit_bool_timeout 10.
  Qed.

  Goal P 3.
  Proof.
    verit_bool_no_check_timeout (H0, HInd) 10.
  Qed.

  Goal P 3.
  Proof.
    verit_bool_no_check_timeout 10.
  Qed.
End TimeoutBool.


Section TimeoutProp.
  Variable P : Z -> bool.
  Variable H0 : P 0.
  Variable HInd : forall n, (P n) -> (P (n + 1)).

  Goal P 3.
  Proof.
    verit_timeout (H0, HInd) 10.
  Qed.

  Goal P 3.
  Proof.
    verit_timeout 10.
  Qed.

  Goal P 3.
  Proof.
    verit_no_check_timeout (H0, HInd) 10.
  Qed.

  Goal P 3.
  Proof.
    verit_no_check_timeout 10.
  Qed.
End TimeoutProp.


(* Test CompDec open goals *)

Section OpenCompdec.

  Variable A : Type.
  Variable l : list A.
  Variable x : A.
  Variable H1 : hd_error l = Some x.
  Variable H2 : hd_error (@nil A) = None.
  Variable H3 : forall x : A, Some x = None -> False.
  Variable Hpb : forall x x0 : A, Some x = Some x0 -> x = x0.

  Goal l <> nil.
  Proof. verit. Abort.
  (* Should leave open CompDec goals but not fail *)

End OpenCompdec.

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


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.9, replace it with:
     Require Import SMTCoq.
   *)
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Require Import ZArith.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

Import FArray.
Local Open Scope farray_scope.

(* Examples that check ZChaff certificates *)

Local Open Scope int63_scope.

(* Abduction examples *)
Local Open Scope Z_scope.
Goal forall
    (x y: Z)
    (f: Z -> Z),
    (* x = y + 1 -> *) f y = f (x - 1).
Proof.
  Fail smt. Fail abduce 1.
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     x - 1 = y *)
Admitted.

(* #1 From paper *)
Goal forall (x y z : Z), 0 <= y ->  0 <= x + y + z.
Proof. 
  Fail smt.
  Fail (abduce 3).
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     0 <= x + z
     y <= x + z
     1 <= y + z + x *)
  intros. assert (0 <= x + z). { admit. } smt.
Admitted.

(* With abduct *)
Goal forall (x y z : Z), 0 <= y -> 0 <= x + z -> 0 <= x + y + z.
Proof.
  smt.
Qed.

(* #2 Commutativity *)
Section Comm.
Variable f : Z -> Z -> Z.
Goal forall (x y : Z), (f x y) >= 0 -> (f y x) >= 0.
Proof.
  Fail smt.
  Fail (abduce 5).
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     y = x
     (f y x) = 0
     (f y x) = 1
     1 <= (f y x)
     (f x y) = (f y x) *)
  intros. assert (f x y = f y x). { admit. } smt.
Admitted.

(* With abduct *)
Goal forall (x y : Z), (f x y) >= 0 -> (f x y = f y x)
      -> (f y x) >= 0.
Proof.
  smt.
Qed.


(* Possible usage *)
Variables (x y z : Z).
Theorem commf : f x y = f y x. Admitted.
Variable H : f x y >= 0.

Goal f y x >= 0.
Proof.
  Fail smt.
  Fail abduce 5.
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     y = x
     (f y x) = 0
     (f y x) = 1
     1 <= (f y x)
     (f x y) = (f y x) *)
  assert (f x y = f y x). { apply commf. }
  smt.
Qed.

(*Takes too long
Goal forall (x y : Z), (f x y) + 2 - y >= 0 -> 
  (f y x)  + 2 - y >= 0.
Proof.
  abduce.

Goal forall (x y : Z), (f x y) + 2*x - y >= 0 -> 
  (f y x)  + 2*x - y >= 0.
Proof.
  abduce.*)

End Comm.

(* Trans *)
Goal forall (x y z : Z), x <= y -> x <= z.
Proof.
  Fail smt.
  Fail abduce 3.
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     
     x <= z
     z + x = y + y *)
  intros. assert (y <= z). {admit. } smt. 
Admitted.

Goal forall (a b c d : Z), a <= c -> a + b <= c + d.
Proof.
  Fail smt.
  Fail abduce 3.
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     b <= d
     b = c && d = a
     a + b <= c + d *)
  intros. assert (b <= d). {admit. } smt. 
Admitted.

Goal forall (a b c d : bool), (implb a b) && (implb c d) 
  -> (*a && c ->*) b && d.
Proof.
  Fail smt.
  Fail abduce 4.
  (* The command has indeed failed with message:
     cvc5 returned SAT.
     The solver cannot prove the goal, but one of the following hypotheses would make it provable:
     b && c
     b && d
     a && d
     a && c *)
  intros. assert (a && c). {admit. } smt. 
Admitted.

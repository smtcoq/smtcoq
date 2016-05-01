Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.


(* zChaff vernacular commands *)

Time Zchaff_Checker "sat1.cnf" "sat1.zlog".
Time Zchaff_Checker "sat2.cnf" "sat2.zlog".
Time Zchaff_Checker "sat3.cnf" "sat3.zlog".
Time Zchaff_Checker "sat5.cnf" "sat5.zlog".
Time Zchaff_Checker "sat6.cnf" "sat6.zlog".
Time Zchaff_Checker "sat7.cnf" "sat7.zlog".
Time Zchaff_Checker "hole4.cnf" "hole4.zlog".
(* Time Zchaff_Checker "cmu-bmc-barrel6.cnf" "cmu-bmc-barrel6.zlog". *)
(* Time Zchaff_Checker "velev-sss-1.0-05.cnf" "velev-sss-1.0-05.zlog". *)


Time Zchaff_Theorem sat1 "sat1.cnf" "sat1.zlog".
Time Zchaff_Theorem sat2 "sat2.cnf" "sat2.zlog".
Time Zchaff_Theorem sat3 "sat3.cnf" "sat3.zlog".
Time Zchaff_Theorem sat5 "sat5.cnf" "sat5.zlog".
Time Zchaff_Theorem sat6 "sat6.cnf" "sat6.zlog".
Time Zchaff_Theorem sat7 "sat7.cnf" "sat7.zlog".
Time Zchaff_Theorem hole4 "hole4.cnf" "hole4.zlog".


Parse_certif_zchaff d1 t1 "sat1.cnf" "sat1.zlog".
Compute Sat_Checker.checker d1 t1.

Parse_certif_zchaff d2 t2 "sat2.cnf" "sat2.zlog".
Compute Sat_Checker.checker d2 t2.

Parse_certif_zchaff d3 t3 "sat3.cnf" "sat3.zlog".
Compute Sat_Checker.checker d3 t3.

Parse_certif_zchaff d5 t5 "sat5.cnf" "sat5.zlog".
Compute Sat_Checker.checker d5 t5.

Parse_certif_zchaff d6 t6 "sat6.cnf" "sat6.zlog".
Compute Sat_Checker.checker d6 t6.

Parse_certif_zchaff d7 t7 "sat7.cnf" "sat7.zlog".
Compute Sat_Checker.checker d7 t7.

Parse_certif_zchaff dhole4 thole4 "hole4.cnf" "hole4.zlog".
Compute Sat_Checker.checker dhole4 thole4.

(* Parse_certif_zchaff dcmubmcbarrel6 tcmubmcbarrel6 "cmu-bmc-barrel6.cnf" "cmu-bmc-barrel6.zlog". *)
(* Compute Sat_Checker.checker dcmubmcbarrel6 tcmubmcbarrel6. *)

(* Parse_certif_zchaff dvelevsss1005 tvelevsss1005 "velev-sss-1.0-05.cnf" "velev-sss-1.0-05.zlog". *)
(* Compute Sat_Checker.checker dvelevsss1005 tvelevsss1005. *)


(* zChaff tactic *)

Goal forall a, a || negb a.
  zchaff.
Qed.

Goal forall a, negb (a || negb a) = false.
  zchaff.
Qed.

Goal forall a, negb (negb (a || negb a)).
  zchaff.
Qed.

Goal forall a, (a && negb a) = false.
  zchaff.
Qed.

Goal forall a, negb (a && negb a).
  zchaff.
Qed.

Goal forall a, implb a a.
  zchaff.
Qed.

Goal forall a, negb (implb a a) = false.
  zchaff.
Qed.

Goal forall a , (xorb a a) || negb (xorb a a).
  zchaff.
Qed.

Goal forall a, (a||negb a) || negb (a||negb a).
  zchaff.
Qed.

Goal true.
  zchaff.
Qed.

Goal negb false.
  zchaff.
Qed.

Goal forall a, Bool.eqb a a.
Proof.
  zchaff.
Qed.

Goal forall (a:bool), a = a.
  zchaff.
Qed.


(* sat2.smt *)
(* ((a ∧ b) ∨ (b ∧ c)) ∧ ¬b = ⊥ *)

Goal forall a b c, (((a && b) || (b && c)) && (negb b)) = false.
Proof.
  zchaff.
Qed.


(* sat3.smt *)
(* (a ∨ a) ∧ ¬a = ⊥ *)

Goal forall a, ((a || a) && (negb a)) = false.
Proof.
  zchaff.
Qed.


(* sat4.smt *)
(* ¬(a ∨ ¬a) = ⊥ *)

Goal forall a, (negb (a || (negb a))) = false.
Proof.
  zchaff.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.


(* The same, but with a, b and c being concrete terms *)

Goal forall i j k,
  ((i == j) || (j == k) || (k == i)) && ((negb (i == j)) || (negb (j == k)) || (negb (k == i))) && ((negb (i == j)) || (j == k)) && ((negb (j == k)) || (k == i)) && ((negb (k == i)) || (i == j)) = false.
Proof.
  zchaff.
Qed.

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  zchaff.
Qed.


(* sat6.smt *)
(* (a ∧ b) ∧ (c ∨ d) ∧ ¬(c ∨ (a ∧ b ∧ d)) = ⊥ *)

Goal forall a b c d, ((a && b) && (c || d) && (negb (c || (a && b && d)))) = false.
Proof.
  zchaff.
Qed.


(* sat7.smt *)
(* a ∧ b ∧ c ∧ (¬a ∨ ¬b ∨ d) ∧ (¬d ∨ ¬c) = ⊥ *)

Goal forall a b c d, (a && b && c && ((negb a) || (negb b) || d) && ((negb d) || (negb c))) = false.
Proof.
  zchaff.
Qed.


(* Other connectives *)

Goal (false || true) && false = false.
Proof.
  zchaff.
Qed.


Goal negb true = false.
Proof.
  zchaff.
Qed.


Goal false = false.
Proof.
  zchaff.
Qed.


Goal forall x y, Bool.eqb (xorb x y) ((x && (negb y)) || ((negb x) && y)).
Proof.
  zchaff.
Qed.


Goal forall x y, Bool.eqb (implb x y) ((x && y) || (negb x)).
Proof.
  zchaff.
Qed.


Goal forall x y z, Bool.eqb (ifb x y z) ((x && y) || ((negb x) && z)).
Proof.
  zchaff.
Qed.


(* Multiple negations *)

Goal forall a, orb a (negb (negb (negb a))) = true.
Proof.
  zchaff.
Qed.


(* Polarities *)

Goal forall a b, andb (orb a b) (negb (orb a b)) = false.
Proof.
  zchaff.
Qed.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof.
  zchaff.
Qed.


(* Pigeon hole: 4 holes, 5 pigeons. xij stands for "pidgeon i goes to
   hole j". *)

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
Proof.
  zchaff.
Qed.


(* Counter examples *)

(*
Goal forall x, x && (negb x).
Proof.
  zchaff.
Abort.

Goal forall x y, (implb (implb x y) (implb y x)).
Proof.
  zchaff.
Abort.

(* Pigeon hole: 4 holes, 4 pigeons. xij stands for "pidgeon i goes to
   hole j". *)

Goal forall x11 x12 x13 x14 x21 x22 x23 x24 x31 x32 x33 x34 x41 x42 x43 x44, (
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


  (orb (negb x11) (negb x12)) &&
  (orb (negb x11) (negb x13)) &&
  (orb (negb x11) (negb x14)) &&
  (orb (negb x12) (negb x13)) &&
  (orb (negb x12) (negb x14)) &&
  (orb (negb x13) (negb x14)) &&

  (orb (negb x21) (negb x22)) &&
  (orb (negb x21) (negb x23)) &&
  (orb (negb x21) (negb x24)) &&
  (orb (negb x22) (negb x23)) &&
  (orb (negb x22) (negb x24)) &&
  (orb (negb x23) (negb x24)) &&

  (orb (negb x31) (negb x32)) &&
  (orb (negb x31) (negb x33)) &&
  (orb (negb x31) (negb x34)) &&
  (orb (negb x32) (negb x33)) &&
  (orb (negb x32) (negb x34)) &&
  (orb (negb x33) (negb x34)) &&

  (orb (negb x41) (negb x42)) &&
  (orb (negb x41) (negb x43)) &&
  (orb (negb x41) (negb x44)) &&
  (orb (negb x42) (negb x43)) &&
  (orb (negb x42) (negb x44)) &&
  (orb (negb x43) (negb x44)) &&


  (orb (orb (orb x11 x21) x31) x41) &&
  (orb (orb (orb x12 x22) x32) x42) &&
  (orb (orb (orb x13 x23) x33) x43) &&
  (orb (orb (orb x14 x24) x34) x44)) = false.
Proof.
  zchaff.
Abort.
*)

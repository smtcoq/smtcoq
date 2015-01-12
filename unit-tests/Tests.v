(* Add LoadPath ".." as SMTCoq. *)
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
Time Zchaff_Checker "cmu-bmc-barrel6.cnf" "cmu-bmc-barrel6.zlog".
Time Zchaff_Checker "velev-sss-1.0-05.cnf" "velev-sss-1.0-05.zlog".


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

Parse_certif_zchaff dcmubmcbarrel6 tcmubmcbarrel6 "cmu-bmc-barrel6.cnf" "cmu-bmc-barrel6.zlog".
Compute Sat_Checker.checker dcmubmcbarrel6 tcmubmcbarrel6.

Parse_certif_zchaff dvelevsss1005 tvelevsss1005 "velev-sss-1.0-05.cnf" "velev-sss-1.0-05.zlog".
Compute Sat_Checker.checker dvelevsss1005 tvelevsss1005.


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
Print Unnamed_thm5.

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


(* Le même, mais où a, b et c sont des termes concrets *)

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


(* Other connectors *)

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


(* veriT vernacular commands *)

Section Checker_Sat1.
  Verit_Checker "sat1.smt2" "sat1.vtlog".
End Checker_Sat1.

Section Checker_Sat2.
  Verit_Checker "sat2.smt2" "sat2.vtlog".
End Checker_Sat2.

Section Checker_Sat3.
  Verit_Checker "sat3.smt2" "sat3.vtlog".
End Checker_Sat3.

Section Checker_Sat4.
  Verit_Checker "sat4.smt2" "sat4.vtlog".
End Checker_Sat4.

Section Checker_Sat5.
  Verit_Checker "sat5.smt2" "sat5.vtlog".
End Checker_Sat5.

Section Checker_Sat6.
  Verit_Checker "sat6.smt2" "sat6.vtlog".
End Checker_Sat6.

Section Checker_Sat7.
  Verit_Checker "sat7.smt2" "sat7.vtlog".
End Checker_Sat7.

Section Checker_Sat8.
  Verit_Checker "sat8.smt2" "sat8.vtlog".
End Checker_Sat8.

Section Checker_Sat9.
  Verit_Checker "sat9.smt2" "sat9.vtlog".
End Checker_Sat9.
(*
Section Checker_Sat10.
  Verit_Checker "sat10.smt2" "sat10.vtlog".
End Checker_Sat10.
*)
Section Checker_Sat11.
  Verit_Checker "sat11.smt2" "sat11.vtlog".
End Checker_Sat11.

Section Checker_Sat12.
  Verit_Checker "sat12.smt2" "sat12.vtlog".
End Checker_Sat12.

Section Checker_Sat13.
  Verit_Checker "sat13.smt2" "sat13.vtlog".
End Checker_Sat13.

Section Checker_Hole4.
  Verit_Checker "hole4.smt2" "hole4.vtlog".
End Checker_Hole4.

Section Checker_Uf1.
  Verit_Checker "uf1.smt2" "uf1.vtlog".
End Checker_Uf1.

Section Checker_Uf2.
  Verit_Checker "uf2.smt2" "uf2.vtlog".
End Checker_Uf2.

Section Checker_Uf3.
  Verit_Checker "uf3.smt2" "uf3.vtlog".
End Checker_Uf3.

Section Checker_Uf4.
  Verit_Checker "uf4.smt2" "uf4.vtlog".
End Checker_Uf4.

Section Checker_Uf5.
  Verit_Checker "uf5.smt2" "uf5.vtlog".
End Checker_Uf5.

Section Checker_Uf6.
  Verit_Checker "uf6.smt2" "uf6.vtlog".
End Checker_Uf6.

Section Checker_Uf7.
  Verit_Checker "uf7.smt2" "uf7.vtlog".
End Checker_Uf7.

Section Checker_Lia1.
  Verit_Checker "lia1.smt2" "lia1.vtlog".
End Checker_Lia1.

Section Checker_Lia2.
  Verit_Checker "lia2.smt2" "lia2.vtlog".
End Checker_Lia2.

Section Checker_Lia3.
  Verit_Checker "lia3.smt2" "lia3.vtlog".
End Checker_Lia3.

Section Checker_Lia4.
  Verit_Checker "lia4.smt2" "lia4.vtlog".
End Checker_Lia4.

Section Checker_Lia5.
  Verit_Checker "lia5.smt2" "lia5.vtlog".
End Checker_Lia5.

Section Checker_Lia6.
  Verit_Checker "lia6.smt2" "lia6.vtlog".
End Checker_Lia6.

Section Checker_Lia7.
  Verit_Checker "lia7.smt2" "lia7.vtlog".
End Checker_Lia7.

Section Checker_Let1.
  Verit_Checker "let1.smt2" "let1.vtlog".
End Checker_Let1.

Section Checker_Let2.
  Verit_Checker "let2.smt2" "let2.vtlog".
End Checker_Let2.


Section Sat1.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1 "sat1.smt2" "sat1.vtlog".
  Compute Euf_Checker.checker t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1.
End Sat1.

Section Sat2.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2 "sat2.smt2" "sat2.vtlog".
  Compute Euf_Checker.checker t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2.
End Sat2.

Section Sat3.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3 "sat3.smt2" "sat3.vtlog".
  Compute Euf_Checker.checker t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3.
End Sat3.

Section Sat4.
  Parse_certif_verit t_i4 t_func4 t_atom4 t_form4 root4 used_roots4 trace4 "sat4.smt2" "sat4.vtlog".
  Compute Euf_Checker.checker t_i4 t_func4 t_atom4 t_form4 root4 used_roots4 trace4.
End Sat4.

Section Sat5.
  Parse_certif_verit t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5 "sat5.smt2" "sat5.vtlog".
  Compute Euf_Checker.checker t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5.
End Sat5.

Section Sat6.
  Parse_certif_verit t_i6 t_func6 t_atom6 t_form6 root6 used_roots6 trace6 "sat6.smt2" "sat6.vtlog".
  Compute Euf_Checker.checker t_i6 t_func6 t_atom6 t_form6 root6 used_roots6 trace6.
End Sat6.

Section Sat7.
  Parse_certif_verit t_i7 t_func7 t_atom7 t_form7 root7 used_roots7 trace7 "sat7.smt2" "sat7.vtlog".
  Compute Euf_Checker.checker t_i7 t_func7 t_atom7 t_form7 root7 used_roots7 trace7.
End Sat7.

Section Sat8.
  Parse_certif_verit t_i8 t_func8 t_atom8 t_form8 root8 used_roots8 trace8 "sat8.smt2" "sat8.vtlog".
  Compute Euf_Checker.checker t_i8 t_func8 t_atom8 t_form8 root8 used_roots8 trace8.
End Sat8.

Section Sat9.
  Parse_certif_verit t_i9 t_func9 t_atom9 t_form9 root9 used_roots9 trace9 "sat9.smt2" "sat9.vtlog".
  Compute Euf_Checker.checker t_i9 t_func9 t_atom9 t_form9 root9 used_roots9 trace9.
End Sat9.
(*
Section Sat10.
  Parse_certif_verit t_i10 t_func10 t_atom10 t_form10 root10 used_roots10 trace10 "sat10.smt2" "sat10.vtlog".
  Compute Euf_Checker.checker t_i10 t_func10 t_atom10 t_form10 root10 used_roots10 trace10.
End Sat10.
*)
Section Sat11.
  Parse_certif_verit t_i11 t_func11 t_atom11 t_form11 root11 used_roots11 trace11 "sat11.smt2" "sat11.vtlog".
  Compute Euf_Checker.checker t_i11 t_func11 t_atom11 t_form11 root11 used_roots11 trace11.
End Sat11.

Section Sat12.
  Parse_certif_verit t_i12 t_func12 t_atom12 t_form12 root12 used_roots12 trace12 "sat12.smt2" "sat12.vtlog".
  Compute Euf_Checker.checker t_i12 t_func12 t_atom12 t_form12 root12 used_roots12 trace12.
End Sat12.

Section Hole4.
  Parse_certif_verit t_i_hole4 t_func_hole4 t_atom_hole4 t_form_hole4 root_hole4 used_roots_hole4 trace_hole4 "hole4.smt2" "hole4.vtlog".
  Compute Euf_Checker.checker t_i_hole4 t_func_hole4 t_atom_hole4 t_form_hole4 root_hole4 used_roots_hole4 trace_hole4.
End Hole4.

Section Uf1.
  Parse_certif_verit t_i_uf1 t_func_uf1 t_atom_uf1 t_form_uf1 root_uf1 used_roots_uf1 trace_uf1 "uf1.smt2" "uf1.vtlog".
  Compute Euf_Checker.checker t_i_uf1 t_func_uf1 t_atom_uf1 t_form_uf1 root_uf1 used_roots_uf1 trace_uf1.
End Uf1.

Section Uf2.
  Parse_certif_verit t_i_uf2 t_func_uf2 t_atom_uf2 t_form_uf2 root_uf2 used_roots_uf2 trace_uf2 "uf2.smt2" "uf2.vtlog".
  Compute Euf_Checker.checker t_i_uf2 t_func_uf2 t_atom_uf2 t_form_uf2 root_uf2 used_roots_uf2 trace_uf2.
End Uf2.

Section Uf3.
  Parse_certif_verit t_i_uf3 t_func_uf3 t_atom_uf3 t_form_uf3 root_uf3 used_roots_uf3 trace_uf3 "uf3.smt2" "uf3.vtlog".
  Compute Euf_Checker.checker t_i_uf3 t_func_uf3 t_atom_uf3 t_form_uf3 root_uf3 used_roots_uf3 trace_uf3.
End Uf3.

Section Uf4.
  Parse_certif_verit t_i_uf4 t_func_uf4 t_atom_uf4 t_form_uf4 root_uf4 used_roots_uf4 trace_uf4 "uf4.smt2" "uf4.vtlog".
  Compute Euf_Checker.checker t_i_uf4 t_func_uf4 t_atom_uf4 t_form_uf4 root_uf4 used_roots_uf4 trace_uf4.
End Uf4.

Section Uf5.
  Parse_certif_verit t_i_uf5 t_func_uf5 t_atom_uf5 t_form_uf5 root_uf5 used_roots_uf5 trace_uf5 "uf5.smt2" "uf5.vtlog".
  Compute Euf_Checker.checker t_i_uf5 t_func_uf5 t_atom_uf5 t_form_uf5 root_uf5 used_roots_uf5 trace_uf5.
End Uf5.

Section Uf6.
  Parse_certif_verit t_i_uf6 t_func_uf6 t_atom_uf6 t_form_uf6 root_uf6 used_roots_uf6 trace_uf6 "uf6.smt2" "uf6.vtlog".
  Compute Euf_Checker.checker t_i_uf6 t_func_uf6 t_atom_uf6 t_form_uf6 root_uf6 used_roots_uf6 trace_uf6.
End Uf6.

Section Uf7.
  Parse_certif_verit t_i_uf7 t_func_uf7 t_atom_uf7 t_form_uf7 root_uf7 used_roots_uf7 trace_uf7 "uf7.smt2" "uf7.vtlog".
  Compute Euf_Checker.checker t_i_uf7 t_func_uf7 t_atom_uf7 t_form_uf7 root_uf7 used_roots_uf7 trace_uf7.
End Uf7.

Section Lia1.
  Parse_certif_verit t_i_lia1 t_func_lia1 t_atom_lia1 t_form_lia1 root_lia1 used_roots_lia1 trace_lia1 "lia1.smt2" "lia1.vtlog".
  Compute Euf_Checker.checker t_i_lia1 t_func_lia1 t_atom_lia1 t_form_lia1 root_lia1 used_roots_lia1 trace_lia1.
End Lia1.

Section Lia2.
  Parse_certif_verit t_i_lia2 t_func_lia2 t_atom_lia2 t_form_lia2 root_lia2 used_roots_lia2 trace_lia2 "lia2.smt2" "lia2.vtlog".
  Compute Euf_Checker.checker t_i_lia2 t_func_lia2 t_atom_lia2 t_form_lia2 root_lia2 used_roots_lia2 trace_lia2.
End Lia2.

Section Lia3.
  Parse_certif_verit t_i_lia3 t_func_lia3 t_atom_lia3 t_form_lia3 root_lia3 used_roots_lia3 trace_lia3 "lia3.smt2" "lia3.vtlog".
  Compute Euf_Checker.checker t_i_lia3 t_func_lia3 t_atom_lia3 t_form_lia3 root_lia3 used_roots_lia3 trace_lia3.
End Lia3.

Section Lia4.
  Parse_certif_verit t_i_lia4 t_func_lia4 t_atom_lia4 t_form_lia4 root_lia4 used_roots_lia4 trace_lia4 "lia4.smt2" "lia4.vtlog".
  Compute Euf_Checker.checker t_i_lia4 t_func_lia4 t_atom_lia4 t_form_lia4 root_lia4 used_roots_lia4 trace_lia4.
End Lia4.

Section Lia5.
  Parse_certif_verit t_i_lia5 t_func_lia5 t_atom_lia5 t_form_lia5 root_lia5 used_roots_lia5 trace_lia5 "lia5.smt2" "lia5.vtlog".
  Compute Euf_Checker.checker t_i_lia5 t_func_lia5 t_atom_lia5 t_form_lia5 root_lia5 used_roots_lia5 trace_lia5.
End Lia5.

Section Lia6.
  Parse_certif_verit t_i_lia6 t_func_lia6 t_atom_lia6 t_form_lia6 root_lia6 used_roots_lia6 trace_lia6 "lia6.smt2" "lia6.vtlog".
  Compute Euf_Checker.checker t_i_lia6 t_func_lia6 t_atom_lia6 t_form_lia6 root_lia6 used_roots_lia6 trace_lia6.
End Lia6.

Section Lia7.
  Parse_certif_verit t_i_lia7 t_func_lia7 t_atom_lia7 t_form_lia7 root_lia7 used_roots_lia7 trace_lia7 "lia7.smt2" "lia7.vtlog".
  Compute Euf_Checker.checker t_i_lia7 t_func_lia7 t_atom_lia7 t_form_lia7 root_lia7 used_roots_lia7 trace_lia7.
End Lia7.

Section Let1.
  Parse_certif_verit t_i_let1 t_func_let1 t_atom_let1 t_form_let1 root_let1 used_roots_let1 trace_let1 "let1.smt2" "let1.vtlog".
  Compute Euf_Checker.checker t_i_let1 t_func_let1 t_atom_let1 t_form_let1 root_let1 used_roots_let1 trace_let1.
End Let1.

Section Let2.
  Parse_certif_verit t_i_let2 t_func_let2 t_atom_let2 t_form_let2 root_let2 used_roots_let2 trace_let2 "let2.smt2" "let2.vtlog".
  Compute Euf_Checker.checker t_i_let2 t_func_let2 t_atom_let2 t_form_let2 root_let2 used_roots_let2 trace_let2.
End Let2.


Section Theorem_Sat1.
  Time Verit_Theorem theorem_sat1 "sat1.smt2" "sat1.vtlog".
End Theorem_Sat1.

Section Theorem_Sat2.
  Time Verit_Theorem theorem_sat2 "sat2.smt2" "sat2.vtlog".
End Theorem_Sat2.

Section Theorem_Sat3.
  Time Verit_Theorem theorem_sat3 "sat3.smt2" "sat3.vtlog".
End Theorem_Sat3.

Section Theorem_Sat4.
  Time Verit_Theorem theorem_sat4 "sat4.smt2" "sat4.vtlog".
End Theorem_Sat4.

Section Theorem_Sat5.
  Time Verit_Theorem theorem_sat5 "sat5.smt2" "sat5.vtlog".
End Theorem_Sat5.

Section Theorem_Sat6.
  Time Verit_Theorem theorem_sat6 "sat6.smt2" "sat6.vtlog".
End Theorem_Sat6.

Section Theorem_Sat7.
  Time Verit_Theorem theorem_sat7 "sat7.smt2" "sat7.vtlog".
End Theorem_Sat7.

Section Theorem_Sat8.
  Time Verit_Theorem theorem_sat8 "sat8.smt2" "sat8.vtlog".
End Theorem_Sat8.

Section Theorem_Sat9.
  Time Verit_Theorem theorem_sat9 "sat9.smt2" "sat9.vtlog".
End Theorem_Sat9.
(*
Section Theorem_Sat10.
  Time Verit_Theorem theorem_sat10 "sat10.smt2" "sat10.vtlog".
End Theorem_Sat10.
*)
Section Theorem_Sat11.
  Time Verit_Theorem theorem_sat11 "sat11.smt2" "sat11.vtlog".
End Theorem_Sat11.

Section Theorem_Sat12.
  Time Verit_Theorem theorem_sat12 "sat12.smt2" "sat12.vtlog".
End Theorem_Sat12.

Section Theorem_Hole4.
  Time Verit_Theorem theorem_hole4 "hole4.smt2" "hole4.vtlog".
End Theorem_Hole4.

Section Theorem_Uf1.
  Time Verit_Theorem theorem_uf1 "uf1.smt2" "uf1.vtlog".
End Theorem_Uf1.

Section Theorem_Uf2.
  Time Verit_Theorem theorem_uf2 "uf2.smt2" "uf2.vtlog".
End Theorem_Uf2.

Section Theorem_Uf3.
  Time Verit_Theorem theorem_uf3 "uf3.smt2" "uf3.vtlog".
End Theorem_Uf3.

Section Theorem_Uf4.
  Time Verit_Theorem theorem_uf4 "uf4.smt2" "uf4.vtlog".
End Theorem_Uf4.

Section Theorem_Uf5.
  Time Verit_Theorem theorem_uf5 "uf5.smt2" "uf5.vtlog".
End Theorem_Uf5.

Section Theorem_Uf6.
  Time Verit_Theorem theorem_uf6 "uf6.smt2" "uf6.vtlog".
End Theorem_Uf6.

Section Theorem_Uf7.
  Time Verit_Theorem theorem_uf7 "uf7.smt2" "uf7.vtlog".
End Theorem_Uf7.

Section Theorem_Lia1.
  Time Verit_Theorem theorem_lia1 "lia1.smt2" "lia1.vtlog".
End Theorem_Lia1.

Section Theorem_Lia2.
  Time Verit_Theorem theorem_lia2 "lia2.smt2" "lia2.vtlog".
End Theorem_Lia2.

Section Theorem_Lia3.
  Time Verit_Theorem theorem_lia3 "lia3.smt2" "lia3.vtlog".
End Theorem_Lia3.

Section Theorem_Lia4.
  Time Verit_Theorem theorem_lia4 "lia4.smt2" "lia4.vtlog".
End Theorem_Lia4.

Section Theorem_Lia5.
  Time Verit_Theorem theorem_lia5 "lia5.smt2" "lia5.vtlog".
End Theorem_Lia5.

Section Theorem_Lia6.
  Time Verit_Theorem theorem_lia6 "lia6.smt2" "lia6.vtlog".
End Theorem_Lia6.

Section Theorem_Lia7.
  Time Verit_Theorem theorem_lia7 "lia7.smt2" "lia7.vtlog".
End Theorem_Lia7.

Section Theorem_Let1.
  Time Verit_Theorem theorem_let1 "let1.smt2" "let1.vtlog".
End Theorem_Let1.

Section Theorem_Let2.
  Time Verit_Theorem theorem_let2 "let2.smt2" "let2.vtlog".
End Theorem_Let2.


(* verit tactic *)

(* Simple connectors *)

Goal forall (a:bool), a || negb a.
  verit.
Qed.

Goal forall a, negb (a || negb a) = false.
  verit.
Qed.

Goal forall a, (a && negb a) = false.
  verit.
Qed.

Goal forall a, negb (a && negb a).
  verit.
Qed.

Goal forall a, implb a a.
  verit.
Qed.

Goal forall a, negb (implb a a) = false.
  verit.
Qed.

Goal forall a , (xorb a a) || negb (xorb a a).
  verit.
Qed.
Print Unnamed_thm5.

Goal forall a, (a||negb a) || negb (a||negb a).
  verit.
Qed.

Goal true.
  verit.
Qed.

Goal negb false.
  verit.
Qed.

Goal forall a, Bool.eqb a a.
Proof.
  verit.
Qed.

Goal forall (a:bool), a = a.
  verit.
Qed.


(* Other connectors *)

Goal (false || true) && false = false.
Proof.
  verit.
Qed.


Goal negb true = false.
Proof.
  verit.
Qed.


Goal false = false.
Proof.
  verit.
Qed.


Goal forall x y, Bool.eqb (xorb x y) ((x && (negb y)) || ((negb x) && y)).
Proof.
  verit.
Qed.


Goal forall x y, Bool.eqb (implb x y) ((x && y) || (negb x)).
Proof.
  verit.
Qed.


Goal forall x y z, Bool.eqb (ifb x y z) ((x && y) || ((negb x) && z)).
Proof.
  verit.
Qed.


(* Multiple negations *)

Goal forall a, orb a (negb (negb (negb a))) = true.
Proof.
  verit.
Qed.


(* Polarities *)

Goal forall a b, andb (orb a b) (negb (orb a b)) = false.
Proof.
  verit.
Qed.


Goal forall a b, andb (orb a b) (andb (negb a) (negb b)) = false.
Proof.
  verit.
Qed.


(* sat2.smt *)
(* ((a ∧ b) ∨ (b ∧ c)) ∧ ¬b = ⊥ *)

Goal forall a b c, (((a && b) || (b && c)) && (negb b)) = false.
Proof.
  verit.
Qed.


(* sat3.smt *)
(* (a ∨ a) ∧ ¬a = ⊥ *)

Goal forall a, ((a || a) && (negb a)) = false.
Proof.
  verit.
Qed.


(* sat4.smt *)
(* ¬(a ∨ ¬a) = ⊥ *)

Goal forall a, (negb (a || (negb a))) = false.
Proof.
  verit.
Qed.


(* sat5.smt *)
(* (a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ ¬c) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ a) = ⊥ *)

Goal forall a b c,
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  verit.
Qed.


(* Le même, mais où a, b et c sont des termes concrets *)

Goal forall i j k,
  let a := i == j in
  let b := j == k in
  let c := k == i in
  (a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a) = false.
Proof.
  verit.
Qed.


(* sat6.smt *)
(* (a ∧ b) ∧ (c ∨ d) ∧ ¬(c ∨ (a ∧ b ∧ d)) = ⊥ *)

Goal forall a b c d, ((a && b) && (c || d) && (negb (c || (a && b && d)))) = false.
Proof.
  verit.
Qed.


(* sat7.smt *)
(* a ∧ b ∧ c ∧ (¬a ∨ ¬b ∨ d) ∧ (¬d ∨ ¬c) = ⊥ *)

Goal forall a b c d, (a && b && c && ((negb a) || (negb b) || d) && ((negb d) || (negb c))) = false.
Proof.
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
Proof.
  verit.
Qed.


(* uf1.smt *)

Goal forall a b c f p, ((Zeq_bool a c) && (Zeq_bool b c) && ((negb (Zeq_bool (f a) (f b))) || ((p a) && (negb (p b))))) = false.
Proof.
  verit.
Qed.


(* uf2.smt *)

Goal forall a b c (p : Z -> bool), ((((p a) && (p b)) || ((p b) && (p c))) && (negb (p b))) = false.
Proof.
  verit.
Qed.


(* uf3.smt *)

Goal forall x y z f, ((Zeq_bool x y) && (Zeq_bool y z) && (negb (Zeq_bool (f x) (f z)))) = false.
Proof.
  verit.
Qed.


(* uf4.smt *)

Goal forall x y z f, ((negb (Zeq_bool (f x) (f y))) && (Zeq_bool y z) && (Zeq_bool (f x) (f (f z))) && (Zeq_bool x y)) = false.
Proof.
  verit.
Qed.


(* uf5.smt *)

Goal forall a b c d e f, ((Zeq_bool a b) && (Zeq_bool b c) && (Zeq_bool c d) && (Zeq_bool c e) && (Zeq_bool e f) && (negb (Zeq_bool a f))) = false.
Proof.
  verit.
Qed.


(* lia1.smt *)

Goal forall x y z, implb ((x <=? 3) && ((y <=? 7) || (z <=? 9)))
  ((x + y <=? 10) || (x + z <=? 12)) = true.
Proof.
  verit.
Qed.

(* lia2.smt *)

Goal forall x, implb (Zeq_bool (x - 3) 7) (x >=? 10) = true.
Proof.
  verit.
Qed.

(* lia3.smt *)

Goal forall x y, implb (x >? y) (y + 1 <=? x) = true.
Proof.
  verit.
Qed.

(* lia4.smt *)

Goal forall x y, Bool.eqb (x <? y) (x <=? y - 1) = true.
Proof.
  verit.
Qed.

(* lia5.smt *)

Goal forall x y, ((x + y <=? - (3)) && (y >=? 0)
        || (x <=? - (3))) && (x >=? 0) = false.
Proof.
  verit.
Qed.

(* lia6.smt *)

Goal forall x, implb (andb ((x - 3) <=? 7) (7 <=? (x - 3))) (x >=? 10) = true.
Proof.
  verit.
Qed.

(* lia7.smt *)

Goal forall x, implb (Zeq_bool (x - 3) 7) (10 <=? x) = true.
Proof.
  verit.
Qed.

(* More general examples *)

Goal forall a b c, ((a || b || c) && ((negb a) || (negb b) || (negb c)) && ((negb a) || b) && ((negb b) || c) && ((negb c) || a)) = false.
Proof.
  verit.
Qed.


Goal forall (a b : Z) (P : Z -> bool) (f : Z -> Z),
  (negb (Zeq_bool (f a) b)) || (negb (P (f a))) || (P b).
Proof.
  verit.
Qed.


Goal forall b1 b2 x1 x2,
  implb
  (ifb b1
    (ifb b2 (Zeq_bool (2*x1+1) (2*x2+1)) (Zeq_bool (2*x1+1) (2*x2)))
    (ifb b2 (Zeq_bool (2*x1) (2*x2+1)) (Zeq_bool (2*x1) (2*x2))))
  ((implb b1 b2) && (implb b2 b1) && (Zeq_bool x1 x2)).
Proof.
  verit.
Qed.


(* With let ... in ... *)

Goal forall b,
  let a := b in
  a && (negb a) = false.
Proof.
  verit.
Qed.

Goal forall b,
  let a := b in
  a || (negb a) = true.
Proof.
  verit.
Qed.
(* Does not work since the [is_true] coercion includes [let in]
Goal forall b,
  let a := b in
  a || (negb a).
Proof.
  verit.
Qed.
*)

(* With concrete terms *)

Goal forall i j,
  let a := i == j in
  a && (negb a) = false.
Proof.
  verit.
Qed.

Goal forall i j,
  let a := i == j in
  a || (negb a) = true.
Proof.
  verit.
Qed.

Section Concret.
  Goal forall i j,
    (i == j) && (negb (i == j)) = false.
  Proof.
    verit.
  Qed.
End Concret.

Section Concret2.
  Lemma concret : forall i j, (i == j) || (negb (i == j)).
  Proof.
    verit.
  Qed.
  Check concret.
End Concret2.
Check concret.


(* Congruence in which some premices are REFL *)

Goal forall (f:Z -> Z -> Z) x y z,
  implb (Zeq_bool x y) (Zeq_bool (f z x) (f z y)).
Proof.
  verit.
Qed.

Goal forall (P:Z -> Z -> bool) x y z,
  implb (Zeq_bool x y) (implb (P z x) (P z y)).
Proof.
  verit.
Qed.

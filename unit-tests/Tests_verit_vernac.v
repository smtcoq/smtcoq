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


Add Rec LoadPath "../src" as SMTCoq.

Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.
Open Scope Z_scope.


(* veriT vernacular commands *)

Section Checker_Sat0.
  Verit_Checker "sat0.smt2" "sat0.vtlog".
End Checker_Sat0.

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

Section Checker_Sat14.
  Verit_Checker "sat14.smt2" "sat14.vtlog".
End Checker_Sat14.

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

(* TODO: it does not go through anymore
   Anomaly: File "trace/smtCommands.ml", line 102, characters 12-18: Assertion failed.
Section Checker_Lia4.
  Verit_Checker "lia4.smt2" "lia4.vtlog".
End Checker_Lia4.
*)

Section Checker_Lia5.
  Verit_Checker "lia5.smt2" "lia5.vtlog".
End Checker_Lia5.

Section Checker_Lia6.
  Verit_Checker "lia6.smt2" "lia6.vtlog".
End Checker_Lia6.

Section Checker_Lia7.
  Verit_Checker "lia7.smt2" "lia7.vtlog".
End Checker_Lia7.

(*
Section Checker_Let1.
  Verit_Checker "let1.smt2" "let1.vtlog".
End Checker_Let1.

Section Checker_Let2.
  Verit_Checker "let2.smt2" "let2.vtlog".
End Checker_Let2.
*)

(* Proofs with holes *)
(*
Section Checker_Sat7_holes.
  Verit_Checker "sat7.smt2" "sat7-with-holes.vtlog".
End Checker_Sat7_holes.

Section Checker_Lia5_holes.
  Verit_Checker "lia5.smt2" "lia5-with-holes.vtlog".
End Checker_Lia5_holes.
*)

Section Checker_Bv1.
  Verit_Checker "bv1.smt2" "bv1.log".
End Checker_Bv1.

Section Checker_Bv2.
  Verit_Checker "bv2.smt2" "bv2.log".
End Checker_Bv2.


Section Sat0.
  Parse_certif_verit t_i0 t_func0 t_atom0 t_form0 root0 used_roots0 trace0 "sat0.smt2" "sat0.vtlog".
  Compute @Euf_Checker.checker t_i0 t_func0 t_atom0 t_form0 root0 used_roots0 trace0.
End Sat0.

Section Sat1.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1 "sat1.smt2" "sat1.vtlog".
  Compute @Euf_Checker.checker t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1.
End Sat1.

Section Sat2.
  Parse_certif_verit t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2 "sat2.smt2" "sat2.vtlog".
  Compute @Euf_Checker.checker t_i2 t_func2 t_atom2 t_form2 root2 used_roots2 trace2.
End Sat2.

Section Sat3.
  Parse_certif_verit t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3 "sat3.smt2" "sat3.vtlog".
  Compute @Euf_Checker.checker t_i3 t_func3 t_atom3 t_form3 root3 used_roots3 trace3.
End Sat3.

Section Sat4.
  Parse_certif_verit t_i4 t_func4 t_atom4 t_form4 root4 used_roots4 trace4 "sat4.smt2" "sat4.vtlog".
  Compute @Euf_Checker.checker t_i4 t_func4 t_atom4 t_form4 root4 used_roots4 trace4.
End Sat4.

Section Sat5.
  Parse_certif_verit t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5 "sat5.smt2" "sat5.vtlog".
  Compute @Euf_Checker.checker t_i5 t_func5 t_atom5 t_form5 root5 used_roots5 trace5.
End Sat5.

Section Sat6.
  Parse_certif_verit t_i6 t_func6 t_atom6 t_form6 root6 used_roots6 trace6 "sat6.smt2" "sat6.vtlog".
  Compute @Euf_Checker.checker t_i6 t_func6 t_atom6 t_form6 root6 used_roots6 trace6.
End Sat6.

Section Sat7.
  Parse_certif_verit t_i7 t_func7 t_atom7 t_form7 root7 used_roots7 trace7 "sat7.smt2" "sat7.vtlog".
  Compute @Euf_Checker.checker t_i7 t_func7 t_atom7 t_form7 root7 used_roots7 trace7.
End Sat7.

Section Sat8.
  Parse_certif_verit t_i8 t_func8 t_atom8 t_form8 root8 used_roots8 trace8 "sat8.smt2" "sat8.vtlog".
  Compute @Euf_Checker.checker t_i8 t_func8 t_atom8 t_form8 root8 used_roots8 trace8.
End Sat8.

Section Sat9.
  Parse_certif_verit t_i9 t_func9 t_atom9 t_form9 root9 used_roots9 trace9 "sat9.smt2" "sat9.vtlog".
  Compute @Euf_Checker.checker t_i9 t_func9 t_atom9 t_form9 root9 used_roots9 trace9.
End Sat9.
(*
Section Sat10.
  Parse_certif_verit t_i10 t_func10 t_atom10 t_form10 root10 used_roots10 trace10 "sat10.smt2" "sat10.vtlog".
  Compute @Euf_Checker.checker t_i10 t_func10 t_atom10 t_form10 root10 used_roots10 trace10.
End Sat10.
*)
Section Sat11.
  Parse_certif_verit t_i11 t_func11 t_atom11 t_form11 root11 used_roots11 trace11 "sat11.smt2" "sat11.vtlog".
  Compute @Euf_Checker.checker t_i11 t_func11 t_atom11 t_form11 root11 used_roots11 trace11.
End Sat11.

Section Sat12.
  Parse_certif_verit t_i12 t_func12 t_atom12 t_form12 root12 used_roots12 trace12 "sat12.smt2" "sat12.vtlog".
  Compute @Euf_Checker.checker t_i12 t_func12 t_atom12 t_form12 root12 used_roots12 trace12.
End Sat12.

Section Hole4.
  Parse_certif_verit t_i_hole4 t_func_hole4 t_atom_hole4 t_form_hole4 root_hole4 used_roots_hole4 trace_hole4 "hole4.smt2" "hole4.vtlog".
  Compute @Euf_Checker.checker t_i_hole4 t_func_hole4 t_atom_hole4 t_form_hole4 root_hole4 used_roots_hole4 trace_hole4.
End Hole4.

Section Uf1.
  Parse_certif_verit t_i_uf1 t_func_uf1 t_atom_uf1 t_form_uf1 root_uf1 used_roots_uf1 trace_uf1 "uf1.smt2" "uf1.vtlog".
  Compute @Euf_Checker.checker t_i_uf1 t_func_uf1 t_atom_uf1 t_form_uf1 root_uf1 used_roots_uf1 trace_uf1.
End Uf1.

Section Uf2.
  Parse_certif_verit t_i_uf2 t_func_uf2 t_atom_uf2 t_form_uf2 root_uf2 used_roots_uf2 trace_uf2 "uf2.smt2" "uf2.vtlog".
  Compute @Euf_Checker.checker t_i_uf2 t_func_uf2 t_atom_uf2 t_form_uf2 root_uf2 used_roots_uf2 trace_uf2.
End Uf2.

Section Uf3.
  Parse_certif_verit t_i_uf3 t_func_uf3 t_atom_uf3 t_form_uf3 root_uf3 used_roots_uf3 trace_uf3 "uf3.smt2" "uf3.vtlog".
  Compute @Euf_Checker.checker t_i_uf3 t_func_uf3 t_atom_uf3 t_form_uf3 root_uf3 used_roots_uf3 trace_uf3.
End Uf3.

Section Uf4.
  Parse_certif_verit t_i_uf4 t_func_uf4 t_atom_uf4 t_form_uf4 root_uf4 used_roots_uf4 trace_uf4 "uf4.smt2" "uf4.vtlog".
  Compute @Euf_Checker.checker t_i_uf4 t_func_uf4 t_atom_uf4 t_form_uf4 root_uf4 used_roots_uf4 trace_uf4.
End Uf4.

Section Uf5.
  Parse_certif_verit t_i_uf5 t_func_uf5 t_atom_uf5 t_form_uf5 root_uf5 used_roots_uf5 trace_uf5 "uf5.smt2" "uf5.vtlog".
  Compute @Euf_Checker.checker t_i_uf5 t_func_uf5 t_atom_uf5 t_form_uf5 root_uf5 used_roots_uf5 trace_uf5.
End Uf5.

Section Uf6.
  Parse_certif_verit t_i_uf6 t_func_uf6 t_atom_uf6 t_form_uf6 root_uf6 used_roots_uf6 trace_uf6 "uf6.smt2" "uf6.vtlog".
  Compute @Euf_Checker.checker t_i_uf6 t_func_uf6 t_atom_uf6 t_form_uf6 root_uf6 used_roots_uf6 trace_uf6.
End Uf6.

Section Uf7.
  Parse_certif_verit t_i_uf7 t_func_uf7 t_atom_uf7 t_form_uf7 root_uf7 used_roots_uf7 trace_uf7 "uf7.smt2" "uf7.vtlog".
  Compute @Euf_Checker.checker t_i_uf7 t_func_uf7 t_atom_uf7 t_form_uf7 root_uf7 used_roots_uf7 trace_uf7.
End Uf7.

Section Lia1.
  Parse_certif_verit t_i_lia1 t_func_lia1 t_atom_lia1 t_form_lia1 root_lia1 used_roots_lia1 trace_lia1 "lia1.smt2" "lia1.vtlog".
  Compute @Euf_Checker.checker t_i_lia1 t_func_lia1 t_atom_lia1 t_form_lia1 root_lia1 used_roots_lia1 trace_lia1.
End Lia1.

Section Lia2.
  Parse_certif_verit t_i_lia2 t_func_lia2 t_atom_lia2 t_form_lia2 root_lia2 used_roots_lia2 trace_lia2 "lia2.smt2" "lia2.vtlog".
  Compute @Euf_Checker.checker t_i_lia2 t_func_lia2 t_atom_lia2 t_form_lia2 root_lia2 used_roots_lia2 trace_lia2.
End Lia2.

Section Lia3.
  Parse_certif_verit t_i_lia3 t_func_lia3 t_atom_lia3 t_form_lia3 root_lia3 used_roots_lia3 trace_lia3 "lia3.smt2" "lia3.vtlog".
  Compute @Euf_Checker.checker t_i_lia3 t_func_lia3 t_atom_lia3 t_form_lia3 root_lia3 used_roots_lia3 trace_lia3.
End Lia3.

(* TODO: it does not go through anymore
Section Lia4.
  Parse_certif_verit t_i_lia4 t_func_lia4 t_atom_lia4 t_form_lia4 root_lia4 used_roots_lia4 trace_lia4 "lia4.smt2" "lia4.vtlog".
  Compute @Euf_Checker.checker t_i_lia4 t_func_lia4 t_atom_lia4 t_form_lia4 root_lia4 used_roots_lia4 trace_lia4.
End Lia4.
*)

Section Lia5.
  Parse_certif_verit t_i_lia5 t_func_lia5 t_atom_lia5 t_form_lia5 root_lia5 used_roots_lia5 trace_lia5 "lia5.smt2" "lia5.vtlog".
  Compute @Euf_Checker.checker t_i_lia5 t_func_lia5 t_atom_lia5 t_form_lia5 root_lia5 used_roots_lia5 trace_lia5.
End Lia5.

Section Lia6.
  Parse_certif_verit t_i_lia6 t_func_lia6 t_atom_lia6 t_form_lia6 root_lia6 used_roots_lia6 trace_lia6 "lia6.smt2" "lia6.vtlog".
  Compute @Euf_Checker.checker t_i_lia6 t_func_lia6 t_atom_lia6 t_form_lia6 root_lia6 used_roots_lia6 trace_lia6.
End Lia6.

Section Lia7.
  Parse_certif_verit t_i_lia7 t_func_lia7 t_atom_lia7 t_form_lia7 root_lia7 used_roots_lia7 trace_lia7 "lia7.smt2" "lia7.vtlog".
  Compute @Euf_Checker.checker t_i_lia7 t_func_lia7 t_atom_lia7 t_form_lia7 root_lia7 used_roots_lia7 trace_lia7.
End Lia7.

(*
Section Let1.
  Parse_certif_verit t_i_let1 t_func_let1 t_atom_let1 t_form_let1 root_let1 used_roots_let1 trace_let1 "let1.smt2" "let1.vtlog".
  Compute @Euf_Checker.checker t_i_let1 t_func_let1 t_atom_let1 t_form_let1 root_let1 used_roots_let1 trace_let1.
End Let1.

Section Let2.
  Parse_certif_verit t_i_let2 t_func_let2 t_atom_let2 t_form_let2 root_let2 used_roots_let2 trace_let2 "let2.smt2" "let2.vtlog".
  Compute @Euf_Checker.checker t_i_let2 t_func_let2 t_atom_let2 t_form_let2 root_let2 used_roots_let2 trace_let2.
End Let2.
*)

(* Proofs with holes *)
(*
Section Sat7_holes.
  Parse_certif_verit t_i_sat7_holes t_func_sat7_holes t_atom_sat7_holes t_form_sat7_holes root_sat7_holes used_roots_sat7_holes trace_sat7_holes "sat7.smt2" "sat7-with-holes.vtlog".
  Compute @Euf_Checker.checker t_i_sat7_holes t_func_sat7_holes t_atom_sat7_holes t_form_sat7_holes root_sat7_holes used_roots_sat7_holes trace_sat7_holes.
End Sat7_holes.

Section Lia5_holes.
  Parse_certif_verit t_i_lia5_holes t_func_lia5_holes t_atom_lia5_holes t_form_lia5_holes root_lia5_holes used_roots_lia5_holes trace_lia5_holes "lia5.smt2" "lia5-with-holes.vtlog".
  Compute @Euf_Checker.checker t_i_lia5_holes t_func_lia5_holes t_atom_lia5_holes t_form_lia5_holes root_lia5_holes used_roots_lia5_holes trace_lia5_holes.
End Lia5_holes.
*)

Section Bv1.
  Parse_certif_verit t_i_bv1 t_func_bv1 t_atom_bv1 t_form_bv1 root_bv1 used_roots_bv1 trace_bv1 "bv1.smt2" "bv1.log".
  Compute @Euf_Checker.checker t_i_bv1 t_func_bv1 t_atom_bv1 t_form_bv1 root_bv1 used_roots_bv1 trace_bv1.
End Bv1.

Section Bv2.
  Parse_certif_verit t_i_bv2 t_func_bv2 t_atom_bv2 t_form_bv2 root_bv2 used_roots_bv2 trace_bv2 "bv2.smt2" "bv2.log".
  Compute @Euf_Checker.checker t_i_bv2 t_func_bv2 t_atom_bv2 t_form_bv2 root_bv2 used_roots_bv2 trace_bv2.
End Bv2.


Section Theorem_Sat0.
  Time Verit_Theorem theorem_sat0 "sat0.smt2" "sat0.vtlog".
End Theorem_Sat0.

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

(* TODO: it does not go through anymore
Section Theorem_Lia4.
  Time Verit_Theorem theorem_lia4 "lia4.smt2" "lia4.vtlog".
End Theorem_Lia4.
*)

Section Theorem_Lia5.
  Time Verit_Theorem theorem_lia5 "lia5.smt2" "lia5.vtlog".
End Theorem_Lia5.

Section Theorem_Lia6.
  Time Verit_Theorem theorem_lia6 "lia6.smt2" "lia6.vtlog".
End Theorem_Lia6.

Section Theorem_Lia7.
  Time Verit_Theorem theorem_lia7 "lia7.smt2" "lia7.vtlog".
End Theorem_Lia7.

(*
Section Theorem_Let1.
  Time Verit_Theorem theorem_let1 "let1.smt2" "let1.vtlog".
End Theorem_Let1.

Section Theorem_Let2.
  Time Verit_Theorem theorem_let2 "let2.smt2" "let2.vtlog".
End Theorem_Let2.
*)

(* Proofs with holes *)
(*
Section Theorem_Sat7_holes.
  Time Verit_Theorem theorem_sat7_holes "sat7.smt2" "sat7-with-holes.vtlog".
End Theorem_Sat7_holes.
Check theorem_sat7_holes.

Section Theorem_Lia5_holes.
  Time Verit_Theorem theorem_lia5_holes "lia5.smt2" "lia5-with-holes.vtlog".
End Theorem_Lia5_holes.
Check theorem_lia5_holes.
*)

Section Theorem_Bv1.
  Time Verit_Theorem theorem_bv1 "bv1.smt2" "bv1.log".
End Theorem_Bv1.

Section Theorem_Bv2.
  Time Verit_Theorem theorem_bv2 "bv2.smt2" "bv2.log".
End Theorem_Bv2.

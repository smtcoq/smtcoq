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


open Smtcoq_extr


(* Incorrect proofs *)

let testI00 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cfalse); ("t2", Api.Cfalse)]) in
  (smt, proof)

let testI01 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t1", Api.Cfalse) in
  (smt, proof)


(* Proofs of unsatisfiability of `False` *)

let testC00 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cassume 0); ("t2", Api.Cfalse)]) in
  (smt, proof)

let testC01 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cfalse); ("t2", Api.Cassume 0)]) in
  (smt, proof)


(* Proofs of unsatisfiability of `a ∧ ¬a` *)

let testC02 =
  let smt =
    let sorts = [] in
    let fa = ("a", [], "Bool") in
    let funs = [fa] in
    let a = Api.EFun (fa, []) in
    let ass = [|a; Api.ENeg a|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cassume 0); ("t2", Api.Cassume 1)]) in
  (smt, proof)

let testC03 =
  let smt =
    let sorts = [] in
    let fa = ("a", [], "Bool") in
    let funs = [fa] in
    let a = Api.EFun (fa, []) in
    let ass = [|a; Api.ENeg a|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cassume 1); ("t2", Api.Cassume 0)]) in
  (smt, proof)


(* unit-tests/lia6.vtlog *)

let test_lia6 =
  let fx = ("x", [], "Int") in
  let x = Api.EFun (fx, []) in
  let e4 = Api.EMinus (x, Api.EInt 3) in
  let e5 = Api.ELe (Api.EInt 7, e4) in
  let e3 = Api.ELe (e4, EInt 7) in
  let e2 = Api.EBAnd (e3, e5) in
  let e6 = Api.EGe (x, Api.EInt 10) in
  let e1 = Api.EImp (e2, e6) in
  let smt =
    let sorts = [] in
    let funs = [fx] in
    let f = Api.ENeg e1 in
    let ass = [|f|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cnot_implies1 t1) in
    let t3 = ("t3", Api.Cand (t2, 1)) in
    let t4 = ("t4", Api.Cnot_implies2 t1) in
    let t5 = ("t5", Api.Clia_generic [e6; Api.ENeg e5]) in
    let t6 = ("t6", Api.Cresolution [t5; t3; t4]) in
    t6
  in
  (smt, proof)


(* Error when terms are ill-typed *)

let testT00 =
  let smt =
    let sorts = [] in
    let fa = ("a", [], "Int") in
    let funs = [fa] in
    let a = Api.EFun (fa, []) in
    let ass = [|a; Api.ENeg a|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cassume 0); ("t2", Api.Cassume 1)]) in
  (smt, proof)


let _ =
  assert (let (smt, proof) = testI00 in not (Api.checker smt proof));
  assert (let (smt, proof) = testI01 in not (Api.checker smt proof));
  assert (let (smt, proof) = testC00 in Api.checker smt proof);
  assert (let (smt, proof) = testC01 in Api.checker smt proof);
  assert (let (smt, proof) = testC02 in Api.checker smt proof);
  assert (let (smt, proof) = testC03 in Api.checker smt proof);
  assert (let (smt, proof) = test_lia6 in Api.checker smt proof);
  Printf.printf "All tests suceeded\nNow testing the debugging checker:\n";
  Printf.printf "testI00:\n";
  let (smt, proof) = testI00 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "testI01:\n";
  let (smt, proof) = testI01 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "testC00:\n";
  let (smt, proof) = testC00 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "testC01:\n";
  let (smt, proof) = testC01 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "testC02:\n";
  let (smt, proof) = testC02 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "testC03:\n";
  let (smt, proof) = testC03 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "Now testing when terms are ill-typed:\n";
  try
    let (smt, proof) = testT00 in let _ = Api.checker smt proof in ()
  with
    | Failure s -> Printf.printf"%s\n" s

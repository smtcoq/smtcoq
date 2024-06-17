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
  let proof = ("t3", Api.CResolution [("t1", Api.CFalse); ("t2", Api.CFalse)]) in
  (smt, proof)

let testI01 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t1", Api.CFalse) in
  (smt, proof)


(* Proofs of unsatisfiability of `False` *)

let testC00 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.CResolution [("t1", Api.CAssert 0); ("t2", Api.CFalse)]) in
  (smt, proof)

let testC01 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.CResolution [("t1", Api.CFalse); ("t2", Api.CAssert 0)]) in
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
  let proof = ("t3", Api.CResolution [("t1", Api.CAssert 0); ("t2", Api.CAssert 1)]) in
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
  let proof = ("t3", Api.CResolution [("t1", Api.CAssert 1); ("t2", Api.CAssert 0)]) in
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
  let proof = ("t3", Api.CResolution [("t1", Api.CAssert 0); ("t2", Api.CAssert 1)]) in
  (smt, proof)


let _ =
  assert (let (smt, proof) = testI00 in not (Api.checker smt proof));
  assert (let (smt, proof) = testI01 in not (Api.checker smt proof));
  assert (let (smt, proof) = testC00 in Api.checker smt proof);
  assert (let (smt, proof) = testC01 in Api.checker smt proof);
  assert (let (smt, proof) = testC02 in Api.checker smt proof);
  assert (let (smt, proof) = testC03 in Api.checker smt proof);
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

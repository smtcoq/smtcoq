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

let test00 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.CResolution [("t1", Api.CFalse); ("t2", Api.CFalse)]) in
  (smt, proof)

let test01 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t1", Api.CFalse) in
  (smt, proof)


(* Proofs of unsatisfiability of `False` *)

let test02 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.CResolution [("t1", Api.CAssert 0); ("t2", Api.CFalse)]) in
  (smt, proof)

let test03 =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.CResolution [("t1", Api.CFalse); ("t2", Api.CAssert 0)]) in
  (smt, proof)


(* Proofs of unsatisfiability of `a ∧ ¬a` *)

let test04 =
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

let test05 =
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


let _ =
  assert (let (smt, proof) = test00 in not (Api.checker smt proof));
  assert (let (smt, proof) = test01 in not (Api.checker smt proof));
  assert (let (smt, proof) = test02 in Api.checker smt proof);
  assert (let (smt, proof) = test03 in Api.checker smt proof);
  assert (let (smt, proof) = test04 in Api.checker smt proof);
  assert (let (smt, proof) = test05 in Api.checker smt proof);
  Printf.printf "All tests suceeded\nNow testing the debugging checker:\n";
  Printf.printf "test00:\n";
  let (smt, proof) = test00 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "test01:\n";
  let (smt, proof) = test01 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "test02:\n";
  let (smt, proof) = test02 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "test03:\n";
  let (smt, proof) = test03 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "test04:\n";
  let (smt, proof) = test04 in Debug_checker.debug_checker_stdout smt proof;
  Printf.printf "test05:\n";
  let (smt, proof) = test05 in Debug_checker.debug_checker_stdout smt proof

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
    let ass = [|a; Api.ENot a|] in
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
    let ass = [|a; Api.ENot a|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cassume 1); ("t2", Api.Cassume 0)]) in
  (smt, proof)


(* Unit tests *)

let testWeakening =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let na = Api.ENot a in
  let nb = Api.ENot b in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|a; na; nb|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cweakening (t1, [a;b])) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testTrue =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.ENot Api.ETrue|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Ctrue) in
    let t3 = ("t3", Api.Cresolution [t1; t2]) in
    t3
  in
  (smt, proof)

let testFalse =
  let smt =
    let sorts = [] in
    let funs = [] in
    let ass = [|Api.EFalse|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cfalse) in
    let t3 = ("t3", Api.Cresolution [t1; t2]) in
    t3
  in
  (smt, proof)

let testEq_reflexive =
  let u = "U" in
  let fa = ("a", [], u) in
  let a  = Api.EFun (fa, []) in
  let aa = Api.EEq (a, a) in
  let smt =
    let sorts = [u] in
    let funs = [fa] in
    let ass = [|Api.ENot aa|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Ceq_reflexive a) in
    let t3 = ("t3", Api.Cresolution [t1; t2]) in
    t3
  in
  (smt, proof)

let testEq_transitive =
  let u = "U" in
  let fa = ("a", [], u) in
  let fb = ("b", [], u) in
  let fc = ("c", [], u) in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let c  = Api.EFun (fc, []) in
  let ab = Api.EEq (a, b) in
  let bc = Api.EEq (b, c) in
  let ac = Api.EEq (a, c) in
  let smt =
    let sorts = [u] in
    let funs = [fa; fb; fc] in
    let ass = [|ab; bc; Api.ENot ac|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Ceq_transitive [a; b; c]) in
    let t5 = ("t5", Api.Cresolution [t4; t1; t2; t3]) in
    t5
  in
  (smt, proof)

let testAnd =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EAnd [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cand (t1, 1)) in
    let t4 = ("t4", Api.Cresolution [t2; t3]) in
    t4
  in
  (smt, proof)

let testNot_or =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EOr [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cnot_or (t1, 1)) in
    let t4 = ("t4", Api.Cresolution [t2; t3]) in
    t4
  in
  (smt, proof)

let testOr =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EOr [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cor t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testNot_and =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EAnd [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cnot_and t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testXor1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cxor1 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testXor2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cxor2 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testNot_xor1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; Api.ENot a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cnot_xor1 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testNot_xor2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cnot_xor2 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testImplies =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EImp (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cimplies t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testNot_implies1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EImp (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; Api.ENot a|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cnot_implies1 t1) in
    let t4 = ("t4", Api.Cresolution [t2; t3]) in
    t4
  in
  (smt, proof)

let testNot_implies2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EImp (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cnot_implies2 t1) in
    let t4 = ("t4", Api.Cresolution [t2; t3]) in
    t4
  in
  (smt, proof)

let testEquiv1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cequiv1 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testEquiv2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cequiv2 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testNot_equiv1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; Api.ENot a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cnot_equiv1 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testNot_equiv2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cnot_equiv2 t1) in
    let t5 = ("t5", Api.Cresolution [t4; t2; t3]) in
    t5
  in
  (smt, proof)

let testAnd_pos =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EAnd [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cand_pos ([a; b], 1)) in
    let t4 = ("t4", Api.Cresolution [t3; t2; t1]) in
    t4
  in
  (smt, proof)

let testAnd_neg =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EAnd [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cand_neg [a; b]) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testOr_pos =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EOr [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cor_pos [a; b]) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testOr_neg =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EOr [a; b] in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cor_neg ([a; b], 1)) in
    let t4 = ("t4", Api.Cresolution [t3; t2; t1]) in
    t4
  in
  (smt, proof)

let testXor_pos1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cxor_pos1 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testXor_pos2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cxor_pos2 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testXor_neg1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; Api.ENot a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cxor_neg1 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testXor_neg2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EXor (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cxor_neg2 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testImplies_pos =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EImp (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cimplies_pos (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testImplies_neg1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EImp (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; Api.ENot a|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cimplies_neg1 (a, b)) in
    let t4 = ("t4", Api.Cresolution [t3; t2; t1]) in
    t4
  in
  (smt, proof)

let testImplies_neg2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EImp (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cimplies_neg2 (a, b)) in
    let t4 = ("t4", Api.Cresolution [t3; t2; t1]) in
    t4
  in
  (smt, proof)

let testEquiv_pos1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; Api.ENot a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cequiv_pos1 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testEquiv_pos2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|ab; a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cequiv_pos2 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testEquiv_neg1 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; a; b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cequiv_neg1 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)

let testEquiv_neg2 =
  let fa = ("a", [], "Bool") in
  let fb = ("b", [], "Bool") in
  let a  = Api.EFun (fa, []) in
  let b  = Api.EFun (fb, []) in
  let ab = Api.EEq (a, b) in
  let smt =
    let sorts = [] in
    let funs = [fa; fb] in
    let ass = [|Api.ENot ab; Api.ENot a; Api.ENot b|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cassume 1) in
    let t3 = ("t3", Api.Cassume 2) in
    let t4 = ("t4", Api.Cequiv_neg2 (a, b)) in
    let t5 = ("t5", Api.Cresolution [t4; t3; t2; t1]) in
    t5
  in
  (smt, proof)


(* unit-tests/lia6.vtlog *)

let test_lia6 =
  let fx = ("x", [], "Int") in
  let x = Api.EFun (fx, []) in
  let e4 = Api.EMinus (x, Api.EInt 3) in
  let e5 = Api.ELe (Api.EInt 7, e4) in
  let e3 = Api.ELe (e4, EInt 7) in
  let e2 = Api.EAnd [e3; e5] in
  let e6 = Api.EGe (x, Api.EInt 10) in
  let e1 = Api.EImp (e2, e6) in
  let smt =
    let sorts = [] in
    let funs = [fx] in
    let ass = [|Api.ENot e1|] in
    (sorts, funs, ass)
  in
  let proof =
    let t1 = ("t1", Api.Cassume 0) in
    let t2 = ("t2", Api.Cnot_implies1 t1) in
    let t3 = ("t3", Api.Cand (t2, 2)) in
    let t4 = ("t4", Api.Cnot_implies2 t1) in
    let t5 = ("t5", Api.Clia_generic [e6; Api.ENot e5]) in
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
    let ass = [|a; Api.ENot a|] in
    (sorts, funs, ass)
  in
  let proof = ("t3", Api.Cresolution [("t1", Api.Cassume 0); ("t2", Api.Cassume 1)]) in
  (smt, proof)


let _ =
  (* let deb t = let (smt, proof) = t in Debug_checker.debug_checker_stdout smt proof in *)
  (* deb testEquiv_neg2; *)

  let ass  t = let (smt, proof) = t in      Api.checker smt proof in
  let assn t = let (smt, proof) = t in not (Api.checker smt proof) in
  assert(assn testI00);
  assert(assn testI01);
  assert(ass  testC00);
  assert(ass  testC01);
  assert(ass  testC02);
  assert(ass  testC03);
  assert(ass  testWeakening);
  assert(ass  testTrue);
  assert(ass  testFalse);
  assert(ass  testEq_reflexive);
  assert(ass  testEq_transitive);
  assert(ass  testAnd);
  assert(ass  testNot_or);
  assert(ass  testOr);
  assert(ass  testNot_and);
  assert(ass  testXor1);
  assert(ass  testXor2);
  assert(ass  testNot_xor1);
  assert(ass  testNot_xor2);
  assert(ass  testImplies);
  assert(ass  testNot_implies1);
  assert(ass  testNot_implies2);
  assert(ass  testEquiv1);
  assert(ass  testEquiv2);
  assert(ass  testNot_equiv1);
  assert(ass  testNot_equiv2);
  assert(ass  testAnd_pos);
  assert(ass  testAnd_neg);
  assert(ass  testOr_pos);
  assert(ass  testOr_neg);
  assert(ass  testXor_pos1);
  assert(ass  testXor_pos2);
  assert(ass  testXor_neg1);
  assert(ass  testXor_neg2);
  assert(ass  testImplies_pos);
  assert(ass  testImplies_neg1);
  assert(ass  testImplies_neg2);
  assert(ass  testEquiv_pos1);
  assert(ass  testEquiv_pos2);
  assert(ass  testEquiv_neg1);
  assert(ass  testEquiv_neg2);
  assert(ass  test_lia6);
  Printf.printf "All tests suceeded\n";

  (* Printf.printf "Now testing the debugging checker:\n"; *)
  (* Printf.printf "testI00:\n"; *)
  (* deb testI00; *)
  (* Printf.printf "testI01:\n"; *)
  (* deb testI01; *)
  (* Printf.printf "testC00:\n"; *)
  (* deb testC00; *)
  (* Printf.printf "testC01:\n"; *)
  (* deb testC01; *)
  (* Printf.printf "testC02:\n"; *)
  (* deb testC02; *)
  (* Printf.printf "testC03:\n"; *)
  (* deb testC03; *)
  (* Printf.printf "Now testing when terms are ill-typed:\n"; *)
  (* try *)
  (*   let (smt, proof) = testT00 in let _ = Api.checker smt proof in () *)
  (* with *)
  (*   | Failure s -> Printf.printf"%s\n" s *)

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Entries
open Coqlib


let mklApp f args = Term.mkApp (Lazy.force f, args)
let gen_constant modules constant = lazy (gen_constant_in_modules "SMT" modules constant)


(* Int63 *)
let int63_modules = [["SMTCoq";"versions";"standard";"Int63";"Int63Native"]]

let int31_module = [["Coq";"Numbers";"Cyclic";"Int31";"Int31"]]
let cD0 = gen_constant int31_module "D0"
let cD1 = gen_constant int31_module "D1"
let cI31 = gen_constant int31_module "I31"

let mkInt : int -> Term.constr = fun i ->
  let a = Array.make 31 (Lazy.force cD0) in
  let j = ref i in
  let k = ref 30 in
  while !j <> 0 do
    if !j land 1 = 1 then a.(!k) <- Lazy.force cD1;
    j := !j lsr 1;
    decr k
  done;
  mklApp cI31 a

let cint = gen_constant int31_module "int31"

(* PArray *)
let parray_modules = [["SMTCoq";"versions";"standard";"Array";"PArray"]]

let cmake = gen_constant parray_modules "make"
let cset = gen_constant parray_modules "set"

let max_array_size : int = 4194302
let mkArray : Term.types * Term.constr array -> Term.constr =
  fun (ty, a) ->
  snd (Array.fold_left (fun (i,acc) c ->
                        let acc' = mklApp cset [|ty; acc; mkInt i; c|] in
                        (i+1,acc')
                       ) (0,mklApp cmake [|ty; mkInt (Array.length a); a.(0)|]) a)


(* Differences between the two versions of Coq *)
let dummy_loc = Util.dummy_loc

let mkConst c =
  { const_entry_body = c;
    const_entry_type = None;
    const_entry_secctx = None;
    const_entry_opaque = false}

let glob_term_CbvVm = Glob_term.CbvVm

let error = Util.error

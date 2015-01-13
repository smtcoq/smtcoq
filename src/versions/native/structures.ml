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

(* Int63 *)
let int63_modules = [["Coq";"Numbers";"Cyclic";"Int63";"Int63Native"]]

let mkInt i = Term.mkInt (Uint63.of_int i)


(* PArray *)
let parray_modules = [["Coq";"Array";"PArray"]]

let max_array_size = Parray.trunc_size (Uint63.of_int 4194303)
let mkArray = Term.mkArray

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


(* Int63 *)
let int63_modules = [["SMTCoq";"Int63Native"]]

let mkInt : int -> Term.constr =
  failwith "Not implemented yet"


(* PArray *)
let parray_modules = [["SMTCoq";"PArray"]]

let max_array_size : int =
  failwith "Not implemented yet"
let mkArray : Term.types * Term.constr array -> Term.constr =
  failwith "Not implemented yet"


(* Differences between the two versions of Coq *)
let dummy_loc = Util.dummy_loc

let mkConst c =
  { const_entry_body = c;
    const_entry_type = None;
    const_entry_secctx = None;
    const_entry_opaque = false}

let glob_term_CbvVm = Glob_term.CbvVm

let error = Util.error

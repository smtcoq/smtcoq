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



let gen_constant modules constant = lazy (gen_constant_in_modules "SMT" modules constant)



(* Int63 *)
let int63_modules = [["Coq";"Numbers";"Cyclic";"Int63";"Int63Native"]]

let mkInt : int -> Term.constr =
  fun i -> Term.mkInt (Uint63.of_int i)

let cint = gen_constant int63_modules "int"

(* PArray *)
let parray_modules = [["Coq";"Array";"PArray"]]

let max_array_size : int =
  Parray.trunc_size (Uint63.of_int 4194303)
let mkArray : Term.types * Term.constr array -> Term.constr =
  Term.mkArray


(* Differences between the two versions of Coq *)
let dummy_loc = Pp.dummy_loc

let mkConst c =
  { const_entry_body = c;
    const_entry_type = None;
    const_entry_secctx = None;
    const_entry_opaque = false;
    const_entry_inline_code = false}

let error = Errors.error

let coqtype = lazy Term.mkSet

let declare_new_type t =
  Command.declare_assumption false (Decl_kinds.Local,Decl_kinds.Definitional) (Lazy.force coqtype) [] false None (dummy_loc, t);
  Term.mkVar t

let declare_new_variable v constr_t =
  Command.declare_assumption false (Decl_kinds.Local,Decl_kinds.Definitional) constr_t [] false None (dummy_loc, v);
  Term.mkVar v

let extern_constr = Constrextern.extern_constr true Environ.empty_env

let vernacentries_interp expr =
  Vernacentries.interp (Vernacexpr.VernacCheckMayEval (Some (Glob_term.CbvVm None), None, expr))

let pr_constr_env = Printer.pr_constr_env

let lift = Term.lift

let mk_tactic t = t

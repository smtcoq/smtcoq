(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
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


(* Traces *)
(* WARNING: side effect on r! *)
let mkTrace step_to_coq next carray _ _ _ _ size step def_step r =
  let max = max_array_size - 1 in
  let q,r1 = size / max, size mod max in
  let trace =
    let len = if r1 = 0 then q + 1 else q + 2 in
    Array.make len (mkArray (step, [|def_step|])) in
  for j = 0 to q - 1 do
    let tracej = Array.make max_array_size def_step in
    for i = 0 to max - 1 do
      r := next !r;
      tracej.(i) <- step_to_coq !r;
    done;
    trace.(j) <- mkArray (step, tracej)
  done;
  if r1 <> 0 then (
    let traceq = Array.make (r1 + 1) def_step in
    for i = 0 to r1-1 do
      r := next !r;
    traceq.(i) <- step_to_coq !r;
    done;
    trace.(q) <- mkArray (step, traceq)
  );
  mkArray (Term.mkApp (Lazy.force carray, [|step|]), trace)


(* Differences between the two versions of Coq *)
type names_id_t = Names.identifier

let dummy_loc = Pp.dummy_loc

let mkUConst c =
  { const_entry_body = c;
    const_entry_type = None;
    const_entry_secctx = None;
    const_entry_opaque = false;
    const_entry_inline_code = false}

let mkTConst c _ ty =
  { const_entry_body = c;
    const_entry_type = Some ty;
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

let destruct_rel_decl (n, _, t) = n, t

let interp_constr env sigma = Constrintern.interp_constr sigma env

type constr_expr = Topconstr.constr_expr

let tclTHEN = Tacticals.tclTHEN
let tclTHENLAST = Tacticals.tclTHENLAST
let assert_before = Tactics.assert_tac

let vm_conv = Reduction.vm_conv
let vm_cast_no_check = Tactics.vm_cast_no_check
let mk_tactic tac gl =
  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let t = Tacmach.pf_concl gl in
  tac env sigma t gl
let set_evars_tac _ = Tacticals.tclIDTAC

let ppconstr_lsimpleconstr = Ppconstr.lsimple
let constrextern_extern_constr =
  let env = Global.env () in
  Constrextern.extern_constr false env

let get_rel_dec_name = fun _ -> Names.Anonymous


(* Old packaging of plugins *)
module Micromega_plugin_Certificate = Certificate
module Micromega_plugin_Coq_micromega = Coq_micromega
module Micromega_plugin_Micromega = Micromega
module Micromega_plugin_Mutils = Mutils


(* Type of coq tactics *)
type tactic = Proof_type.tactic

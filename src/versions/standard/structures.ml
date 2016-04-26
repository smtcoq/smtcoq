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
  let l = (Array.length a) - 1 in
  snd (Array.fold_left (fun (i,acc) c ->
                        let acc' =
                          if i = l then
                            acc
                          else
                            mklApp cset [|ty; acc; mkInt i; c|] in
                        (i+1,acc')
                       ) (0,mklApp cmake [|ty; mkInt l; a.(l)|]) a)


(* Differences between the two versions of Coq *)
type names_id_t = Names.Id.t

let dummy_loc = Loc.ghost

let mkConst c =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, ty = Typing.type_of env evd c in
  { const_entry_body        = Future.from_val ((c, Univ.ContextSet.empty),
                                               Safe_typing.empty_private_constants);
    const_entry_secctx      = None;
    const_entry_feedback    = None;
    const_entry_type        = Some ty;
    const_entry_polymorphic = false;
    const_entry_universes   = snd (Evd.universe_context evd);
    const_entry_opaque      = false;
    const_entry_inline_code = false }

let error = Errors.error

let coqtype = Future.from_val Term.mkSet

let declare_new_type t =
  let _ = Command.declare_assumption false (Decl_kinds.Discharge, false, Decl_kinds.Definitional) (Future.force coqtype, Univ.ContextSet.empty) [] [] false Vernacexpr.NoInline (dummy_loc, t) in
  Term.mkVar t

let declare_new_variable v constr_t =
  let _ = Command.declare_assumption false (Decl_kinds.Discharge, false, Decl_kinds.Definitional) (constr_t, Univ.ContextSet.empty) [] [] false Vernacexpr.NoInline (dummy_loc, v) in
  Term.mkVar v

let extern_constr = Constrextern.extern_constr true Environ.empty_env Evd.empty

let vernacentries_interp expr =
  Vernacentries.interp (dummy_loc, Vernacexpr.VernacCheckMayEval (Some (Genredexpr.CbvVm None), None, expr))

let pr_constr_env env = Printer.pr_constr_env env Evd.empty

let lift = Vars.lift

let mk_sat_tactic = Proofview.V82.tactic
let tclTHENLAST = Tacticals.New.tclTHENLAST
let assert_before = Tactics.assert_before
let vm_cast_no_check t = Proofview.V82.tactic (Tactics.vm_cast_no_check t)
let mk_smt_tactic tac =
  Proofview.Goal.nf_enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let t = Proofview.Goal.concl gl in
    tac env sigma t
  )

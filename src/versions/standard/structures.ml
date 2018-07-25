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


(* Traces *)
(* WARNING: side effect on r! *)
let mkTrace step_to_coq next _ clist cnil ccons cpair size step def_step r =
  let rec mkTrace s =
    if s = size then
      mklApp cnil [|step|]
    else (
      r := next !r;
      let st = step_to_coq !r in
      mklApp ccons [|step; st; mkTrace (s+1)|]
    ) in
  mklApp cpair [|mklApp clist [|step|]; step; mkTrace 0; def_step|]


(* Differences between the two versions of Coq *)
type names_id_t = Names.Id.t

let dummy_loc = Loc.ghost

let mkUConst c =
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

let mkTConst c noc ty =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, _ = Typing.type_of env evd noc in
  { const_entry_body        = Future.from_val ((c, Univ.ContextSet.empty),
                                               Safe_typing.empty_private_constants);
    const_entry_secctx      = None;
    const_entry_feedback    = None;
    const_entry_type        = Some ty;
    const_entry_polymorphic = false;
    const_entry_universes   = snd (Evd.universe_context evd);
    const_entry_opaque      = false;
    const_entry_inline_code = false }

let error = CErrors.error

let coqtype = Future.from_val Term.mkSet

let declare_new_type t =
  let _ = Command.declare_assumption false (Decl_kinds.Discharge, false, Decl_kinds.Definitional) (Future.force coqtype, Univ.ContextSet.empty) [] [] false Vernacexpr.NoInline (dummy_loc, t) in
  Term.mkVar t

let declare_new_variable v constr_t =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, _ = Typing.type_of env evd constr_t in
  let _ = Command.declare_assumption false (Decl_kinds.Discharge, false, Decl_kinds.Definitional) (constr_t, Evd.universe_context_set evd) [] [] false Vernacexpr.NoInline (dummy_loc, v) in
  Term.mkVar v

let extern_constr = Constrextern.extern_constr true Environ.empty_env Evd.empty

let vernacentries_interp expr =
  Vernacentries.interp (dummy_loc, Vernacexpr.VernacCheckMayEval (Some (Genredexpr.CbvVm None), None, expr))

let pr_constr_env env = Printer.pr_constr_env env Evd.empty

let lift = Vars.lift

type rel_decl = Context.Rel.Declaration.t

let destruct_rel_decl r = Context.Rel.Declaration.get_name r,
                          Context.Rel.Declaration.get_type r

type constr_expr = Constrexpr.constr_expr
                        
let interp_constr env sigma t = Constrintern.interp_constr env sigma t |> fst
                        
let tclTHEN = Tacticals.New.tclTHEN
let tclTHENLAST = Tacticals.New.tclTHENLAST
let assert_before = Tactics.assert_before
let vm_cast_no_check t = Tactics.vm_cast_no_check t
(* let vm_cast_no_check t = Proofview.V82.tactic (Tactics.vm_cast_no_check t) *)
let mk_tactic tac =
  Proofview.Goal.nf_enter {enter = (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let t = Proofview.Goal.concl gl in
    tac env sigma t
  )}
let set_evars_tac noc =
  mk_tactic (
      fun env sigma _ ->
      let sigma, _ = Typing.type_of env sigma noc in
      Proofview.Unsafe.tclEVARS sigma)

let ppconstr_lsimpleconstr = Ppconstr.lsimpleconstr
let constrextern_extern_constr =
  let env = Global.env () in
  Constrextern.extern_constr false env (Evd.from_env env)


(* New packaging of plugins *)
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
module Micromega_plugin_Coq_micromega = Micromega_plugin.Coq_micromega
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Mutils = Micromega_plugin.Mutils

(* Type of coq tactics *)
type tactic = unit Proofview.tactic

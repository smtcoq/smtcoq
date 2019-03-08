(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Entries


(* Constr generation and manipulation *)

type constr = Constr.t
type types = Constr.types
let mklApp f args = Constr.mkApp (Lazy.force f, args)
let decompose_app = Constr.decompose_app
let eq_constr = Constr.equal


type name = Names.Name.t

let mkName s =
  let id = Names.Id.of_string s in
  Names.Name id

let string_of_name = function
    Names.Name id -> Names.Id.to_string id
  | _ -> failwith "unnamed rel"


type cast_kind = Constr.cast_kind
let vmcast = Constr.VMcast
let mkCast = Constr.mkCast


let gen_constant_in_modules s m n = Universes.constr_of_global @@ Coqlib.gen_reference_in_modules s m n
let gen_constant modules constant = lazy (gen_constant_in_modules "SMT" modules constant)


(* Int63 *)
let int63_modules = [["SMTCoq";"versions";"standard";"Int63";"Int63Native"]]

let int31_module = [["Coq";"Numbers";"Cyclic";"Int31";"Int31"]]
let cD0 = gen_constant int31_module "D0"
let cD1 = gen_constant int31_module "D1"
let cI31 = gen_constant int31_module "I31"

let mkInt : int -> Constr.t = fun i ->
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
let mkArray : Constr.types * Constr.t array -> Constr.t =
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
let mkUConst : Constr.t -> Safe_typing.private_constants Entries.definition_entry = fun c ->
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, ty = Typing.type_of env evd (EConstr.of_constr c) in
  { Entries.const_entry_body        = Future.from_val ((c, Univ.ContextSet.empty),
                                               Safe_typing.empty_private_constants);
    const_entry_secctx      = None;
    const_entry_feedback    = None;
    const_entry_type        = Some (EConstr.Unsafe.to_constr ty); (* Cannot contain evars since it comes from a Constr.t *)
    const_entry_universes   = Evd.const_univ_entry ~poly:false evd;
    const_entry_opaque      = false;
    const_entry_inline_code = false }

let mkTConst c noc ty =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, _ = Typing.type_of env evd (EConstr.of_constr noc) in
  { const_entry_body        = Future.from_val ((c, Univ.ContextSet.empty),
                                               Safe_typing.empty_private_constants);
    const_entry_secctx      = None;
    const_entry_feedback    = None;
    const_entry_type        = Some ty;
    const_entry_universes   = Evd.const_univ_entry ~poly:false evd;
    const_entry_opaque      = false;
    const_entry_inline_code = false }

let error s = CErrors.user_err (Pp.str s)

let coqtype = Future.from_val Constr.mkSet

let declare_new_type t =
  let _ = ComAssumption.declare_assumption false (Decl_kinds.Discharge, false, Decl_kinds.Definitional) (Future.force coqtype, Entries.Monomorphic_const_entry Univ.ContextSet.empty) Universes.empty_binders [] false Vernacexpr.NoInline (CAst.make t) in
  Constr.mkVar t

let declare_new_variable v constr_t =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, _ = Typing.type_of env evd (EConstr.of_constr constr_t) in
  let _ = ComAssumption.declare_assumption false (Decl_kinds.Discharge, false, Decl_kinds.Definitional) (constr_t, Evd.const_univ_entry ~poly:false evd) Universes.empty_binders [] false Vernacexpr.NoInline (CAst.make v) in
  Constr.mkVar v

let extern_constr c = Constrextern.extern_constr true Environ.empty_env Evd.empty (EConstr.of_constr c)

let pr_constr_env env = Printer.pr_constr_env env Evd.empty

let lift = Vars.lift

let destruct_rel_decl r = Context.Rel.Declaration.get_name r,
                          Context.Rel.Declaration.get_type r

(* Cannot contain evars since it comes from a Constr.t *)
let interp_constr env sigma t = Constrintern.interp_constr env sigma t |> fst |> EConstr.Unsafe.to_constr

let tclTHEN = Tacticals.New.tclTHEN
let tclTHENLAST = Tacticals.New.tclTHENLAST
let assert_before n c = Tactics.assert_before n (EConstr.of_constr c)

let vm_conv = Vconv.vm_conv
let vm_cast_no_check c = Tactics.vm_cast_no_check (EConstr.of_constr c)
(* Cannot contain evars since it comes from a Constr.t *)
let cbv_vm env c t = EConstr.Unsafe.to_constr (Vnorm.cbv_vm env Evd.empty (EConstr.of_constr c) (EConstr.of_constr t))

let mk_tactic tac =
  Proofview.Goal.nf_enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let t = Proofview.Goal.concl gl in
    let t = EConstr.to_constr sigma t in (* The goal should not contain uninstanciated evars *)
    tac env sigma t
  )
let set_evars_tac noc =
  mk_tactic (
      fun env sigma _ ->
      let sigma, _ = Typing.type_of env sigma (EConstr.of_constr noc) in
      Proofview.Unsafe.tclEVARS sigma)

let ppconstr_lsimpleconstr = Ppconstr.lsimpleconstr
let constrextern_extern_constr c =
  let env = Global.env () in
  Constrextern.extern_constr false env (Evd.from_env env) (EConstr.of_constr c)

let get_rel_dec_name = function
  | Context.Rel.Declaration.LocalAssum (n, _) | Context.Rel.Declaration.LocalDef (n, _, _) -> n

let retyping_get_type_of env sigma c =
  (* Cannot contain evars since it comes from a Constr.t *)
  EConstr.Unsafe.to_constr (Retyping.get_type_of env sigma (EConstr.of_constr c))


(* Micromega *)
module Micromega_plugin_Certificate = Micromega_plugin.Certificate
module Micromega_plugin_Coq_micromega = Micromega_plugin.Coq_micromega
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Mutils = Micromega_plugin.Mutils

let micromega_coq_proofTerm =
  (* Cannot contain evars *)
  lazy (EConstr.Unsafe.to_constr (Lazy.force (Micromega_plugin.Coq_micromega.M.coq_proofTerm)))

let micromega_dump_proof_term p =
  (* Cannot contain evars *)
  EConstr.Unsafe.to_constr (Micromega_plugin.Coq_micromega.dump_proof_term p)


(* Types in the Coq source code *)
type tactic = unit Proofview.tactic
type names_id = Names.Id.t
type constr_expr = Constrexpr.constr_expr

(* EConstr *)
type econstr = EConstr.t
let econstr_of_constr = EConstr.of_constr

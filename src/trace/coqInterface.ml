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


(* EConstr generation and manipulation *)
type id = Names.variable
let mkId = Names.Id.of_string


type name = Names.Name.t
let name_of_id i = Names.Name i
let mkName s =
  let id = mkId s in
  name_of_id id
let string_of_name = function
    Names.Name id -> Names.Id.to_string id
  | _ -> failwith "unnamed rel"


type constr = EConstr.t
type types = EConstr.types
let eq_constr = EConstr.eq_constr
(* let hash_constr = Constr.hash *)
let mkProp = EConstr.mkProp
let mkConst = EConstr.mkConst
let mkVar = EConstr.mkVar
let mkRel = EConstr.mkRel
let isRel = EConstr.isRel
let destRel = EConstr.destRel
let lift = EConstr.Vars.lift
let mkApp = EConstr.mkApp
let decompose_app = EConstr.decompose_app
let mkbinder_annot n = Context.make_annot n Sorts.Relevant
let mkLambda (n, t, c) = EConstr.mkLambda (mkbinder_annot n, t, c)
let mkProd (n, t, c) = EConstr.mkProd (mkbinder_annot n, t, c)
let mkLetIn (n, c1, t, c2) = EConstr.mkLetIn (mkbinder_annot n, c1, t, c2)
let mkArrow a b = EConstr.mkArrow a Sorts.Relevant b

let pr_constr env sigma t = Printer.pr_econstr_env env sigma t


(* let mkUConst : Constr.t -> Evd.side_effects Declare.proof_entry = fun c ->
 *   let env = Global.env () in
 *   let evd = Evd.from_env env in
 *   let evd, ty = Typing.type_of env evd (EConstr.of_constr c) in
 *   Declare.definition_entry
 *     ~opaque:false
 *     ~inline:false
 *     ~types:(EConstr.Unsafe.to_constr ty) (\* Cannot contain evars since it comes from a Constr.t *\)
 *     ~univs:(Evd.univ_entry ~poly:false evd)
 *     c
 * 
 * let mkTConst c noc ty =
 *   let env = Global.env () in
 *   let evd = Evd.from_env env in
 *   let evd, _ = Typing.type_of env evd (EConstr.of_constr noc) in
 *   Declare.definition_entry
 *     ~opaque:false
 *     ~inline:false
 *     ~types:ty
 *     ~univs:(Evd.univ_entry ~poly:false evd)
 *     c *)

(* TODO : Set -> Type *)
(* let declare_new_type t =
 *   let _ = ComAssumption.declare_variable false ~kind:Decls.Definitional Constr.mkSet [] Glob_term.Explicit (CAst.make t) in
 *   Constr.mkVar t
 * 
 * let declare_new_variable v constr_t =
 *   let _ = ComAssumption.declare_variable false ~kind:Decls.Definitional constr_t [] Glob_term.Explicit (CAst.make v) in
 *   Constr.mkVar v
 * 
 * let declare_constant n c =
 *   Declare.declare_constant ~name:n ~kind:(Decls.IsDefinition Decls.Definition) (Declare.DefinitionEntry c) *)


type cast_kind = Constr.cast_kind
let vmcast = Constr.VMcast
let mkCast = EConstr.mkCast


(* Int63 *)
let mkInt : int -> EConstr.constr =
  fun i -> EConstr.mkInt (Uint63.of_int i)


(* PArray *)
let max_array_size : int = 4194302


(* Traces *)
(* WARNING: side effect on r! *)
(* TODO: move to another file *)
let mkTrace step_to_coq next _ clist cnil ccons cpair size step def_step r =
  let rec mkTrace s =
    if s = size then
      mkApp (Lazy.force cnil, [|step|])
    else (
      r := next !r;
      let st = step_to_coq !r in
      mkApp (Lazy.force ccons, [|step; st; mkTrace (s+1)|])
    ) in
  mkApp (Lazy.force cpair, [|mkApp (Lazy.force clist, [|step|]); step; mkTrace 0; def_step|])


(* Micromega *)
module Micromega_plugin_Micromega = Micromega_plugin.Micromega
module Micromega_plugin_Certificate = Micromega_plugin.Certificate

let micromega_dump_proof_term p =
  Micromega_plugin.Coq_micromega.dump_proof_term p


(* Tactics *)
type tactic = unit Proofview.tactic
let tclTHEN = Tacticals.New.tclTHEN
let tclTHENLAST = Tacticals.New.tclTHENLAST
let assert_before n c = Tactics.assert_before n c

let vm_cast_no_check c = Tactics.vm_cast_no_check c

let mk_tactic tac =
  Proofview.Goal.enter (fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Tacmach.New.project gl in
    let t = Proofview.Goal.concl gl in
    tac env sigma t
  )
(* let set_evars_tac noc =
 *   mk_tactic (
 *       fun env sigma _ ->
 *       let sigma, _ = Typing.type_of env sigma (EConstr.of_constr noc) in
 *       Proofview.Unsafe.tclEVARS sigma) *)


(* Errors and warnings *)
let error s = CErrors.user_err (Pp.str s)
let anomaly s = CErrors.anomaly (Pp.str s)
let warning n s = CWarnings.create ~name:n ~category:"SMTCoq plugin" Pp.str s


(* VM conversion *)
(* let vm_conv = Vconv.vm_conv *)
let cbv_vm env sigma c t = Vnorm.cbv_vm env sigma c t


(* Other differences between the two versions of Coq *)
(* type constr_expr = Constrexpr.constr_expr
 * 
 * let destruct_rel_decl r = Context.Rel.Declaration.get_name r,
 *                           Context.Rel.Declaration.get_type r
 * 
 * let interp_constr env sigma t = Constrintern.interp_constr env sigma t |> fst
 * 
 * let ppconstr_lsimpleconstr = Ppconstr.lsimpleconstr
 * 
 * let constrextern_extern_constr c =
 *   let env = Global.env () in
 *   Constrextern.extern_constr ~inctx:false env (Evd.from_env env) (EConstr.of_constr c)
 * 
 * let get_rel_dec_name = function
 *   | Context.Rel.Declaration.LocalAssum (n, _) | Context.Rel.Declaration.LocalDef (n, _, _) ->
 *      Context.binder_name n
 * 
 * let retyping_get_type_of env sigma c =
 *   (\* Cannot contain evars since it comes from a Constr.t *\)
 *   EConstr.Unsafe.to_constr (Retyping.get_type_of env sigma (EConstr.of_constr c)) *)

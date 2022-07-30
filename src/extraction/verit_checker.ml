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


open Smtcoq_plugin


module Mc = CoqInterface.Micromega_plugin_Certificate.Mc


let mkInt = Uint63.of_int

(* From trace/coqTerms.ml *)
let mkArray a =
  let l = (Array.length a) - 1 in
  snd (Array.fold_left (fun (i,acc) c ->
                        let acc' =
                          if i = l then
                            acc
                          else
                            Smt_checker.set acc (mkInt i) c in
                        (i+1,acc')
                       ) (0, Smt_checker.make (mkInt l) a.(l)) a)


(* Generate a list *)
let rec dump_list dump_elt l =
  match l with
    | [] -> Smt_checker.Nil
    | e :: l -> Smt_checker.Cons (dump_elt e, dump_list dump_elt l)


(* Correspondance between the Micromega representation of objects and
   the one that has been extracted *)
let rec dump_nat x =
  match x with
    | Mc.O -> Smt_checker.O
    | Mc.S p -> Smt_checker.S (dump_nat p)


let rec dump_positive x =
  match x with
    | Mc.XH -> Smt_checker.XH
    | Mc.XO p -> Smt_checker.XO (dump_positive p)
    | Mc.XI p -> Smt_checker.XI (dump_positive p)


let dump_z x =
  match x with
    | Mc.Z0 -> Smt_checker.Z0
    | Mc.Zpos p -> Smt_checker.Zpos (dump_positive p)
    | Mc.Zneg p -> Smt_checker.Zneg (dump_positive p)


let dump_pol e =
  let rec dump_pol e =
    match e with
      | Mc.Pc n -> Smt_checker.Pc (dump_z n)
      | Mc.Pinj(p,pol) -> Smt_checker.Pinj (dump_positive p, dump_pol pol)
      | Mc.PX(pol1,p,pol2) -> Smt_checker.PX (dump_pol pol1, dump_positive p, dump_pol pol2) in
  dump_pol e


let dump_psatz e =
  let rec dump_cone e =
    match e with
      | Mc.PsatzIn n -> Smt_checker.PsatzIn (dump_nat n)
      | Mc.PsatzMulC(e,c) -> Smt_checker.PsatzMulC (dump_pol e, dump_cone c)
      | Mc.PsatzSquare e -> Smt_checker.PsatzSquare (dump_pol e)
      | Mc.PsatzAdd(e1,e2) -> Smt_checker.PsatzAdd (dump_cone e1, dump_cone e2)
      | Mc.PsatzMulE(e1,e2) -> Smt_checker.PsatzMulE (dump_cone e1, dump_cone e2)
      | Mc.PsatzC p -> Smt_checker.PsatzC (dump_z p)
      | Mc.PsatzZ -> Smt_checker.PsatzZ in
  dump_cone e


let rec dump_proof_term = function
  | CoqInterface.Micromega_plugin_Micromega.DoneProof -> Smt_checker.DoneProof
  | CoqInterface.Micromega_plugin_Micromega.RatProof(cone,rst) ->
    Smt_checker.RatProof (dump_psatz cone, dump_proof_term rst)
  | CoqInterface.Micromega_plugin_Micromega.CutProof(cone,prf) ->
    Smt_checker.CutProof (dump_psatz cone, dump_proof_term prf)
  | CoqInterface.Micromega_plugin_Micromega.EnumProof(c1,c2,prfs) ->
    Smt_checker.EnumProof (dump_psatz c1, dump_psatz c2, dump_list dump_proof_term prfs)
  | CoqInterface.Micromega_plugin_Micromega.ExProof(p,prf) ->
    Smt_checker.ExProof (dump_positive p, dump_proof_term prf)


(* From trace/coqInterface.ml *)
(* WARNING: side effect on r! *)
let mkTrace step_to_coq next size def_step r =
  let rec mkTrace s =
    if s = size then
      Smt_checker.Nil
    else (
      r := next !r;
      let st = step_to_coq !r in
      Smt_checker.Cons (st, mkTrace (s+1))
    ) in
  (mkTrace 0, def_step)


(* From trace/smtTrace.ml *)
let to_coq to_lit
   (cRes, cWeaken, cImmFlatten,
    cTrue, cFalse, cBuildDef, cBuildDef2, cBuildProj,
    cImmBuildProj,cImmBuildDef,cImmBuildDef2,
    cEqTr, cEqCgr, cEqCgrP,
    cLiaMicromega, cLiaDiseq, cSplArith, cSplDistinctElim,
    cBBVar, cBBConst, cBBOp, cBBNot, cBBEq, cBBDiseq,
    cBBNeg, cBBAdd, cBBMul, cBBUlt, cBBSlt, cBBConc,
    cBBExtr, cBBZextn, cBBSextn,
    cBBShl, cBBShr,
    cRowEq, cRowNeq, cExt,
    cHole, cForallInst) confl =

  let out_f f = to_lit f in
  let out_c c = mkInt (SmtTrace.get_pos c) in
  let out_cl cl = List.fold_right (fun f l -> Smt_checker.Cons (out_f f, l)) cl Smt_checker.Nil in
  let step_to_coq c =
    match c.SmtCertif.kind with
    | Res res ->
	let size = List.length res.rtail + 3 in
	let args = Array.make size (mkInt 0) in
	args.(0) <- mkInt (SmtTrace.get_pos res.rc1);
	args.(1) <- mkInt (SmtTrace.get_pos res.rc2);
	let l = ref res.rtail in
	for i = 2 to size - 2 do
	  match !l with
	  | c::tl ->
	      args.(i) <- mkInt (SmtTrace.get_pos c);
	      l := tl
	  | _ -> assert false
	done;
        cRes (mkInt (SmtTrace.get_pos c), mkArray args)
    | Other other ->
	begin match other with
        | Weaken (c',l') -> cWeaken (out_c c, out_c c', out_cl l')
	| ImmFlatten (c',f) -> cImmFlatten (out_c c, out_c c', out_f f)
        | True -> cTrue (out_c c)
	| False -> cFalse (out_c c)
	| BuildDef f -> cBuildDef (out_c c, out_f f)
	| BuildDef2 f -> cBuildDef2 (out_c c, out_f f)
	| BuildProj (f, i) -> cBuildProj (out_c c, out_f f, mkInt i)
	| ImmBuildDef c' -> cImmBuildDef (out_c c, out_c c')
	| ImmBuildDef2 c' -> cImmBuildDef2 (out_c c, out_c c')
	| ImmBuildProj(c', i) -> cImmBuildProj (out_c c, out_c c', mkInt i)
        | EqTr (f, fl) ->
          let res = List.fold_right (fun f l -> Smt_checker.Cons (out_f f, l)) fl Smt_checker.Nil in
          cEqTr (out_c c, out_f f, res)
        | EqCgr (f, fl) ->
          let res = List.fold_right (fun f l -> Smt_checker.Cons ((match f with | Some f -> Smt_checker.Some (out_f f) | None -> Smt_checker.None), l)) fl Smt_checker.Nil in
          cEqCgr (out_c c, out_f f, res)
        | EqCgrP (f1, f2, fl) ->
          let res = List.fold_right (fun f l -> Smt_checker.Cons ((match f with | Some f -> Smt_checker.Some (out_f f) | None -> Smt_checker.None), l)) fl Smt_checker.Nil in
          cEqCgrP (out_c c, out_f f1, out_f f2, res)
	| LiaMicromega (cl,d) ->
          let cl' = List.fold_right (fun f l -> Smt_checker.Cons (out_f f, l)) cl Smt_checker.Nil in
          let c' = List.fold_right (fun f l -> Smt_checker.Cons (dump_proof_term f, l)) d Smt_checker.Nil in
          cLiaMicromega (out_c c, cl', c')
        | LiaDiseq l -> cLiaDiseq (out_c c, out_f l)
        | SplArith (orig,res,l) ->
          let res' = out_f res in
          let l' = List.fold_right (fun f l -> Smt_checker.Cons (dump_proof_term f, l)) l Smt_checker.Nil in
          cSplArith (out_c c, out_c orig, res', l')
	| SplDistinctElim (c',f) -> cSplDistinctElim (out_c c, out_c c', out_f f)
        | BBVar res -> cBBVar (out_c c, out_f res)
        | BBConst res -> cBBConst (out_c c, out_f res)
        | BBOp (c1,c2,res) ->
           cBBOp (out_c c, out_c c1, out_c c2, out_f res)
        | BBNot (c1,res) ->
           cBBNot (out_c c, out_c c1, out_f res)
        | BBNeg (c1,res) ->
           cBBNeg (out_c c, out_c c1, out_f res)
        | BBAdd (c1,c2,res) ->
           cBBAdd (out_c c, out_c c1, out_c c2, out_f res)
        | BBMul (c1,c2,res) ->
           cBBMul (out_c c, out_c c1, out_c c2, out_f res)
        | BBUlt (c1,c2,res) ->
           cBBUlt (out_c c, out_c c1, out_c c2, out_f res)
        | BBSlt (c1,c2,res) ->
           cBBSlt (out_c c, out_c c1, out_c c2, out_f res)
        | BBConc (c1,c2,res) ->
           cBBConc (out_c c, out_c c1, out_c c2, out_f res)
        | BBExtr (c1,res) ->
           cBBExtr (out_c c, out_c c1, out_f res)
        | BBZextn (c1,res) ->
           cBBZextn (out_c c, out_c c1, out_f res)
        | BBSextn (c1,res) ->
           cBBSextn (out_c c, out_c c1, out_f res)
        | BBShl (c1,c2,res) ->
           cBBShl (out_c c, out_c c1, out_c c2, out_f res)
        | BBShr (c1,c2,res) ->
           cBBShr (out_c c, out_c c1, out_c c2, out_f res)
        | BBEq (c1,c2,res) ->
           cBBEq (out_c c, out_c c1, out_c c2, out_f res)
        | BBDiseq (res) -> cBBDiseq (out_c c, out_f res)
        | RowEq (res) -> cRowEq (out_c c, out_f res)
        | RowNeq (cl) ->
          let out_cl cl =
            List.fold_right (fun f l -> Smt_checker.Cons (out_f f, l)) cl Smt_checker.Nil
          in
          cRowNeq (out_c c, out_cl cl)
        | Ext (res) -> cExt (out_c c, out_f res)
        | Hole (prem_id, concl) -> failwith "The proof contains a hole, which is not supported by the current version of the extracted checker; in a future version, a warning will be output but the remaining of the proof will be checked"
        | Forall_inst (cl, concl) | Qf_lemma (cl, concl) -> failwith "The current version of the extracted checker does not support quantifiers"
	end
    | _ -> assert false in
  let def_step =
    cRes (mkInt 0, mkArray [|mkInt 0|]) in
  let r = ref confl in
  let nc = ref 0 in
  while not (SmtTrace.isRoot !r.SmtCertif.kind) do r := SmtTrace.prev !r; incr nc done;
  let last_root = !r in
  (* Be careful, step_to_coq makes a side effect on cuts so it needs to be called first *)
  let res = mkTrace step_to_coq SmtTrace.next !nc def_step r in
  (res, last_root)


(* Map OCaml integers to the extracted version of N *)
(* From trace/coqTerms.ml *)
let rec mkNat = function
  | 0 -> Smt_checker.O
  | i -> Smt_checker.S (mkNat (i-1))

let rec mkPositive = function
  | 1 -> Smt_checker.XH
  | i ->
     let c =
       if (i mod 2) = 0 then
         fun c -> Smt_checker.XO c
       else
         fun c -> Smt_checker.XI c
     in
     c (mkPositive (i / 2))

let mkN = function
  | 0 -> Smt_checker.N0
  | i -> Smt_checker.Npos (mkPositive i)


(* Correspondance between the SMTCoq representation of objects and the
   one that has been extracted *)
let rec btype_to_coq = function
  | SmtBtype.TZ ->        Smt_checker.Typ.TZ
  | SmtBtype.Tbool ->     Smt_checker.Typ.Tbool
  | SmtBtype.Tpositive -> Smt_checker.Typ.Tpositive
  | SmtBtype.TBV i -> Smt_checker.Typ.TBV (mkN i)
  | SmtBtype.TFArray (k, v) -> Smt_checker.Typ.TFArray (btype_to_coq k, btype_to_coq v)
  | SmtBtype.Tindex i ->  Smt_checker.Typ.Tindex (mkN (SmtBtype.indexed_type_index i))


let c_to_coq = function
  | SmtAtom.CO_xH -> Smt_checker.Atom.CO_xH
  | SmtAtom.CO_Z0 -> Smt_checker.Atom.CO_Z0
  | SmtAtom.CO_BV bv ->
     Smt_checker.Atom.CO_BV (dump_list (fun x -> x) bv, mkN (List.length bv))


let u_to_coq = function
  | SmtAtom.UO_xO ->   Smt_checker.Atom.UO_xO
  | SmtAtom.UO_xI ->   Smt_checker.Atom.UO_xI
  | SmtAtom.UO_Zpos -> Smt_checker.Atom.UO_Zpos
  | SmtAtom.UO_Zneg -> Smt_checker.Atom.UO_Zneg
  | SmtAtom.UO_Zopp -> Smt_checker.Atom.UO_Zopp
  | SmtAtom.UO_BVbitOf (s, i) -> Smt_checker.Atom.UO_BVbitOf (mkN s, mkNat i)
  | SmtAtom.UO_BVnot s -> Smt_checker.Atom.UO_BVnot (mkN s)
  | SmtAtom.UO_BVneg s -> Smt_checker.Atom.UO_BVneg (mkN s)
  | SmtAtom.UO_BVextr (s1, s2, s3) -> Smt_checker.Atom.UO_BVextr (mkN s1, mkN s2, mkN s3)
  | SmtAtom.UO_BVzextn (s1, s2) -> Smt_checker.Atom.UO_BVzextn (mkN s1, mkN s2)
  | SmtAtom.UO_BVsextn (s1, s2) -> Smt_checker.Atom.UO_BVsextn (mkN s1, mkN s2)


let b_to_coq = function
  | SmtAtom.BO_Zplus ->  Smt_checker.Atom.BO_Zplus
  | SmtAtom.BO_Zminus -> Smt_checker.Atom.BO_Zminus
  | SmtAtom.BO_Zmult ->  Smt_checker.Atom.BO_Zmult
  | SmtAtom.BO_Zlt ->    Smt_checker.Atom.BO_Zlt
  | SmtAtom.BO_Zle ->    Smt_checker.Atom.BO_Zle
  | SmtAtom.BO_Zge ->    Smt_checker.Atom.BO_Zge
  | SmtAtom.BO_Zgt ->    Smt_checker.Atom.BO_Zgt
  | SmtAtom.BO_eq t ->   Smt_checker.Atom.BO_eq (btype_to_coq t)
  | SmtAtom.BO_BVand s -> Smt_checker.Atom.BO_BVand (mkN s)
  | SmtAtom.BO_BVor s -> Smt_checker.Atom.BO_BVor (mkN s)
  | SmtAtom.BO_BVxor s -> Smt_checker.Atom.BO_BVxor (mkN s)
  | SmtAtom.BO_BVadd s -> Smt_checker.Atom.BO_BVadd (mkN s)
  | SmtAtom.BO_BVmult s -> Smt_checker.Atom.BO_BVmult (mkN s)
  | SmtAtom.BO_BVult s -> Smt_checker.Atom.BO_BVult (mkN s)
  | SmtAtom.BO_BVslt s -> Smt_checker.Atom.BO_BVslt (mkN s)
  | SmtAtom.BO_BVconcat (s1, s2) -> Smt_checker.Atom.BO_BVconcat (mkN s1, mkN s2)
  | SmtAtom.BO_BVshl s -> Smt_checker.Atom.BO_BVshl (mkN s)
  | SmtAtom.BO_BVshr s -> Smt_checker.Atom.BO_BVshr (mkN s)
  | SmtAtom.BO_select (k ,v) -> Smt_checker.Atom.BO_select (btype_to_coq k, btype_to_coq v)
  | SmtAtom.BO_diffarray (k ,v) -> Smt_checker.Atom.BO_diffarray (btype_to_coq k, btype_to_coq v)


let t_to_coq = function
  | SmtAtom.TO_store (k ,v) -> Smt_checker.Atom.TO_store (btype_to_coq k, btype_to_coq v)


let n_to_coq = function
  | SmtAtom.NO_distinct t -> btype_to_coq t


let i_to_coq i = mkInt (SmtAtom.indexed_op_index i)


let hatom_to_coq h = mkInt (SmtAtom.Atom.index h)

let a_to_coq a =
  match a with
    | SmtAtom.Acop op -> Smt_checker.Atom.Acop (c_to_coq op)
    | SmtAtom.Auop (op,h) -> Smt_checker.Atom.Auop (u_to_coq op, hatom_to_coq h)
    | SmtAtom.Abop (op,h1,h2) ->
      Smt_checker.Atom.Abop (b_to_coq op, hatom_to_coq h1, hatom_to_coq h2)
    | SmtAtom.Atop (op,h1,h2,h3) ->
      Smt_checker.Atom.Atop (t_to_coq op, hatom_to_coq h1, hatom_to_coq h2, hatom_to_coq h3)
    | SmtAtom.Anop (op,ha) ->
      let cop = n_to_coq op in
      let cargs = Array.fold_right (fun h l -> Smt_checker.Cons (hatom_to_coq h, l)) ha Smt_checker.Nil in
      Smt_checker.Atom.Anop (cop, cargs)
    | SmtAtom.Aapp (op,args) ->
      let cop = i_to_coq op in
      let cargs = Array.fold_right (fun h l -> Smt_checker.Cons (hatom_to_coq h, l)) args Smt_checker.Nil in
      Smt_checker.Atom.Aapp (cop, cargs)


let atom_interp_tbl reify =
  let t = SmtAtom.Atom.to_array reify (Smt_checker.Atom.Acop Smt_checker.Atom.CO_xH) a_to_coq in
  mkArray t


let form_to_coq hf = mkInt (SmtAtom.Form.to_lit hf)

let args_to_coq args =
  let cargs = Array.make (Array.length args + 1) (mkInt 0) in
  Array.iteri (fun i hf -> cargs.(i) <- form_to_coq hf) args;
  mkArray cargs

let pf_to_coq pf =
  match pf with
  | SmtForm.Fatom a -> Smt_checker.Form.Fatom (hatom_to_coq a)
  | SmtForm.Fapp(op,args) ->
     (match op with
        | SmtForm.Ftrue -> Smt_checker.Form.Ftrue
        | SmtForm.Ffalse -> Smt_checker.Form.Ffalse
        | SmtForm.Fand -> Smt_checker.Form.Fand (args_to_coq args)
        | SmtForm.For  -> Smt_checker.Form.For (args_to_coq args)
        | SmtForm.Fxor -> if Array.length args = 2 then Smt_checker.Form.Fxor (form_to_coq args.(0), form_to_coq args.(1)) else assert false
        | SmtForm.Fimp -> Smt_checker.Form.Fimp (args_to_coq args)
        | SmtForm.Fiff -> if Array.length args = 2 then Smt_checker.Form.Fiff (form_to_coq args.(0), form_to_coq args.(1)) else assert false
        | SmtForm.Fite -> if Array.length args = 3 then Smt_checker.Form.Fite (form_to_coq args.(0), form_to_coq args.(1), form_to_coq args.(2)) else assert false
        | SmtForm.Fnot2 i -> Smt_checker.Form.Fnot2 (mkInt i, form_to_coq args.(0))
        | SmtForm.Fforall _ -> failwith "The current version of the extracted checker does not support quantifiers"
     )
  | SmtForm.FbbT (a, args) -> Smt_checker.Form.FbbT (hatom_to_coq a, dump_list form_to_coq args)


let form_interp_tbl reify =
  let (_,t) = SmtAtom.Form.to_array reify Smt_checker.Form.Ftrue pf_to_coq in
  mkArray t


(* Importing from SMT-LIB v.2 without generating section variables *)
(* From smtlib2/smtlib2_genConstr.ml *)
let count_btype = ref 0
let count_op = ref 0


let declare_sort sym =
  (* let s = Smtlib2_genConstr.string_of_symbol sym in *)
  let res = SmtBtype.Tindex (SmtBtype.dummy_indexed_type !count_btype) in
  incr count_btype;
  (* VeritSyntax.add_btype s res; *)
  res


let declare_fun sym arg cod =
  (* let s = string_of_symbol sym in *)
  let tyl = List.map Smtlib2_genConstr.sort_of_sort arg in
  let ty = Smtlib2_genConstr.sort_of_sort cod in
  let op = SmtAtom.dummy_indexed_op (SmtAtom.Index !count_op) (Array.of_list tyl) ty in
  incr count_op;
  (* VeritSyntax.add_fun s op; *)
  op


let declare_commands ra rf acc = function
  | Smtlib2_ast.CDeclareSort (_,sym,_) -> let _ = declare_sort sym in acc
  | Smtlib2_ast.CDeclareFun (_,sym, (_, arg), cod) -> let _ = declare_fun sym arg cod in acc
  | Smtlib2_ast.CAssert (_, t) -> (Smtlib2_genConstr.make_root ra rf t)::acc
  | _ -> acc


let import_smtlib2 ra rf filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let commands = Smtlib2_parse.main Smtlib2_lex.token lexbuf in
  close_in chan;
  match commands with
    | None -> []
    | Some (Smtlib2_ast.Commands (_,(_,res))) ->
      List.rev (List.fold_left (declare_commands ra rf) [] res)


(* The final checker *)

let this_clear_all () =
  Verit.clear_all ();
  count_btype := 0;
  count_op := 0


let certif_ops =
  ((fun (a, b) -> Smt_checker.Checker_Ext.Res (a, b)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.Weaken (a, b, c)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.ImmFlatten (a, b, c)),
   (fun a -> Smt_checker.Checker_Ext.CTrue a),
   (fun a -> Smt_checker.Checker_Ext.CFalse a),
   (fun (a, b) -> Smt_checker.Checker_Ext.BuildDef (a, b)),
   (fun (a, b) -> Smt_checker.Checker_Ext.BuildDef2 (a, b)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.BuildProj (a, b, c)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.ImmBuildProj (a, b, c)),
   (fun (a, b) -> Smt_checker.Checker_Ext.ImmBuildDef (a, b)),
   (fun (a, b) -> Smt_checker.Checker_Ext.ImmBuildDef2 (a, b)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.EqTr (a, b, c)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.EqCgr (a, b, c)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.EqCgrP (a, b, c, d)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.LiaMicromega (a, b, c)),
   (fun (a, b) -> Smt_checker.Checker_Ext.LiaDiseq (a, b)),
   (fun  (a, b, c, d) -> Smt_checker.Checker_Ext.SplArith (a, b, c, d)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.SplDistinctElim (a, b, c)),
   (fun (a, b) -> Smt_checker.Checker_Ext.BBVar (a, b)),
   (fun (a, b) -> Smt_checker.Checker_Ext.BBConst (a, b)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBOp (a, b, c, d)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.BBNot (a, b, c)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBEq (a, b, c, d)),
   (fun (a, b) -> Smt_checker.Checker_Ext.BBDiseq (a, b)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.BBNeg (a, b, c)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBAdd (a, b, c, d)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBMul (a, b, c, d)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBUlt (a, b, c, d)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBSlt (a, b, c, d)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBConcat (a, b, c, d)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.BBExtract (a, b, c)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.BBZextend (a, b, c)),
   (fun (a, b, c) -> Smt_checker.Checker_Ext.BBSextend (a, b, c)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBShl (a, b, c, d)),
   (fun (a, b, c, d) -> Smt_checker.Checker_Ext.BBShr (a, b, c, d)),
   (fun (a, b) -> Smt_checker.Checker_Ext.RowEq (a, b)),
   (fun (a, b) -> Smt_checker.Checker_Ext.RowNeq (a, b)),
   (fun (a, b) -> Smt_checker.Checker_Ext.Ext (a, b)),
   assert false,
   assert false)


(* From verit/verit.ml and trace/smtCommands.ml *)
let checker fsmt fproof =
  this_clear_all ();
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  let roots = import_smtlib2 ra rf fsmt in
  let (max_id, confl) = Verit.import_trace ra_quant rf_quant fproof None [] in

  let (tres,last_root) = to_coq (fun i -> mkInt (SmtAtom.Form.to_lit i)) certif_ops confl in
  let certif =
    Smt_checker.Checker_Ext.Certif (mkInt (max_id + 1), tres, mkInt (SmtTrace.get_pos confl)) in
  let used_roots = SmtCommands.compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    Smt_checker.Some (mkArray res) in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (SmtAtom.Form.to_lit j); incr i) roots;
    mkArray res in

  let t_atom = atom_interp_tbl ra in
  let t_form = form_interp_tbl rf in

  Smt_checker.Checker_Ext.checker_ext t_atom t_form rootsCstr used_rootsCstr certif

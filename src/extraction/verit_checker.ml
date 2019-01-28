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


open SmtMisc
open SmtCertif
open SmtCommands
open SmtForm
open SmtAtom
open SmtTrace
open Verit
open Smtlib2_ast
open Smtlib2_genConstr
(* open Smt_checker *)


module Mc = Structures.Micromega_plugin_Certificate.Mc


let mkInt = ExtrNative.of_int
let mkArray = ExtrNative.of_array


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


let rec dump_list dump_elt l =
  match l with
    | [] -> Smt_checker.Nil
    | e :: l -> Smt_checker.Cons (dump_elt e, dump_list dump_elt l)


let rec dump_proof_term = function
  | Micromega.DoneProof -> Smt_checker.DoneProof
  | Micromega.RatProof(cone,rst) ->
    Smt_checker.RatProof (dump_psatz cone, dump_proof_term rst)
  | Micromega.CutProof(cone,prf) ->
    Smt_checker.CutProof (dump_psatz cone, dump_proof_term prf)
  | Micromega.EnumProof(c1,c2,prfs) ->
    Smt_checker.EnumProof (dump_psatz c1, dump_psatz c2, dump_list dump_proof_term prfs)



let to_coq to_lit confl =
  let out_f f = to_lit f in
  let out_c c = mkInt (get_pos c) in
  let step_to_coq c =
    match c.kind with
    | Res res ->
	let size = List.length res.rtail + 3 in
	let args = Array.make size (mkInt 0) in
	args.(0) <- mkInt (get_pos res.rc1);
	args.(1) <- mkInt (get_pos res.rc2);
	let l = ref res.rtail in
	for i = 2 to size - 2 do
	  match !l with
	  | c::tl ->
	      args.(i) <- mkInt (get_pos c);
	      l := tl
	  | _ -> assert false
	done;
	Smt_checker.Euf_Checker.Res (mkInt (get_pos c), mkArray args)
    | Other other ->
	begin match other with
	| ImmFlatten (c',f) -> Smt_checker.Euf_Checker.ImmFlatten (out_c c, out_c c', out_f f)
        | True -> Smt_checker.Euf_Checker.CTrue (out_c c)
	| False -> Smt_checker.Euf_Checker.CFalse (out_c c)
	| BuildDef f -> Smt_checker.Euf_Checker.BuildDef (out_c c, out_f f)
	| BuildDef2 f -> Smt_checker.Euf_Checker.BuildDef2 (out_c c, out_f f)
	| BuildProj (f, i) -> Smt_checker.Euf_Checker.BuildProj (out_c c, out_f f, mkInt i)
	| ImmBuildDef c' -> Smt_checker.Euf_Checker.ImmBuildDef (out_c c, out_c c')
	| ImmBuildDef2 c' -> Smt_checker.Euf_Checker.ImmBuildDef2 (out_c c, out_c c')
	| ImmBuildProj(c', i) -> Smt_checker.Euf_Checker.ImmBuildProj (out_c c, out_c c',mkInt i)
        | EqTr (f, fl) ->
          let res = List.fold_right (fun f l -> Smt_checker.Cons (out_f f, l)) fl Smt_checker.Nil in
          Smt_checker.Euf_Checker.EqTr (out_c c, out_f f, res)
        | EqCgr (f, fl) ->
          let res = List.fold_right (fun f l -> Smt_checker.Cons ((match f with | Some f -> Smt_checker.Some (out_f f) | None -> Smt_checker.None), l)) fl Smt_checker.Nil in
          Smt_checker.Euf_Checker.EqCgr (out_c c, out_f f, res)
        | EqCgrP (f1, f2, fl) ->
          let res = List.fold_right (fun f l -> Smt_checker.Cons ((match f with | Some f -> Smt_checker.Some (out_f f) | None -> Smt_checker.None), l)) fl Smt_checker.Nil in
          Smt_checker.Euf_Checker.EqCgrP (out_c c, out_f f1, out_f f2, res)
	| LiaMicromega (cl,d) ->
          let cl' = List.fold_right (fun f l -> Smt_checker.Cons (out_f f, l)) cl Smt_checker.Nil in
          let c' = List.fold_right (fun f l -> Smt_checker.Cons (dump_proof_term f, l)) d Smt_checker.Nil in
          Smt_checker.Euf_Checker.LiaMicromega (out_c c, cl', c')
        | LiaDiseq l -> Smt_checker.Euf_Checker.LiaDiseq (out_c c, out_f l)
        | SplArith (orig,res,l) ->
          let res' = out_f res in
          let l' = List.fold_right (fun f l -> Smt_checker.Cons (dump_proof_term f, l)) l Smt_checker.Nil in
          Smt_checker.Euf_Checker.SplArith (out_c c, out_c orig, res', l')
	| SplDistinctElim (c',f) -> Smt_checker.Euf_Checker.SplDistinctElim (out_c c, out_c c', out_f f)
	end
    | _ -> assert false in
  let def_step =
    Smt_checker.Euf_Checker.Res (mkInt 0, mkArray [|mkInt 0|]) in
  let r = ref confl in
  let nc = ref 0 in
  while not (isRoot !r.kind) do r := prev !r; incr nc done;
  let last_root = !r in
  let size = !nc in
  let max = (Parray.trunc_size (Uint63.of_int 4194303)) - 1 in
  let q,r1 = size / max, size mod max in

  let trace =
    let len = if r1 = 0 then q + 1 else q + 2 in
    Array.make len (mkArray [|def_step|]) in
  for j = 0 to q - 1 do
    let tracej = Array.make (Parray.trunc_size (Uint63.of_int 4194303)) def_step in
    for i = 0 to max - 1 do
      r := next !r;
      tracej.(i) <- step_to_coq !r;
    done;
    trace.(j) <- mkArray tracej
  done;
  if r1 <> 0 then begin
    let traceq = Array.make (r1 + 1) def_step in
    for i = 0 to r1-1 do
    r := next !r;
    traceq.(i) <- step_to_coq !r;
    done;
    trace.(q) <- mkArray traceq
  end;

  (mkArray trace, last_root)


let btype_to_coq = function
  | TZ ->        Smt_checker.Typ.TZ
  | Tbool ->     Smt_checker.Typ.Tbool
  | Tpositive -> Smt_checker.Typ.Tpositive
  | Tindex i ->  Smt_checker.Typ.Tindex (mkInt (SmtAtom.indexed_type_index i))


let c_to_coq = function
  | CO_xH -> Smt_checker.Atom.CO_xH
  | CO_Z0 -> Smt_checker.Atom.CO_Z0


let u_to_coq = function
  | UO_xO ->   Smt_checker.Atom.UO_xO
  | UO_xI ->   Smt_checker.Atom.UO_xI
  | UO_Zpos -> Smt_checker.Atom.UO_Zpos
  | UO_Zneg -> Smt_checker.Atom.UO_Zneg
  | UO_Zopp -> Smt_checker.Atom.UO_Zopp


let b_to_coq = function
  | BO_Zplus ->  Smt_checker.Atom.BO_Zplus
  | BO_Zminus -> Smt_checker.Atom.BO_Zminus
  | BO_Zmult ->  Smt_checker.Atom.BO_Zmult
  | BO_Zlt ->    Smt_checker.Atom.BO_Zlt
  | BO_Zle ->    Smt_checker.Atom.BO_Zle
  | BO_Zge ->    Smt_checker.Atom.BO_Zge
  | BO_Zgt ->    Smt_checker.Atom.BO_Zgt
  | BO_eq t ->   Smt_checker.Atom.BO_eq (btype_to_coq t)


let n_to_coq = function
  | NO_distinct t -> btype_to_coq t


let i_to_coq i = mkInt (SmtAtom.indexed_op_index i)


let a_to_coq a =
  let to_coq h = mkInt (Atom.index h) in
  match a with
    | Acop op -> Smt_checker.Atom.Acop (c_to_coq op)
    | Auop (op,h) -> Smt_checker.Atom.Auop (u_to_coq op, to_coq h)
    | Abop (op,h1,h2) ->
      Smt_checker.Atom.Abop (b_to_coq op, to_coq h1, to_coq h2)
    | Anop (op,ha) ->
      let cop = n_to_coq op in
      let cargs = Array.fold_right (fun h l -> Smt_checker.Cons (to_coq h, l)) ha Smt_checker.Nil in
      Smt_checker.Atom.Anop (cop, cargs)
    | Aapp (op,args) ->
      let cop = i_to_coq op in
      let cargs = Array.fold_right (fun h l -> Smt_checker.Cons (to_coq h, l)) args Smt_checker.Nil in
      Smt_checker.Atom.Aapp (cop, cargs)


let atom_interp_tbl reify =
  let t = Atom.to_array reify (Smt_checker.Atom.Acop Smt_checker.Atom.CO_xH) a_to_coq in
  mkArray t


let form_to_coq hf = mkInt (Form.to_lit hf)

let args_to_coq args =
  let cargs = Array.make (Array.length args + 1) (mkInt 0) in
  Array.iteri (fun i hf -> cargs.(i) <- form_to_coq hf) args;
  mkArray cargs

let pf_to_coq = function
  | Fatom a -> Smt_checker.Form.Fatom (mkInt (Atom.index a))
  | Fapp(op,args) ->
    match op with
      | Ftrue -> Smt_checker.Form.Ftrue
      | Ffalse -> Smt_checker.Form.Ffalse
      | Fand -> Smt_checker.Form.Fand (args_to_coq args)
      | For  -> Smt_checker.Form.For (args_to_coq args)
      | Fimp -> Smt_checker.Form.Fimp (args_to_coq args)
      | Fxor -> if Array.length args = 2 then Smt_checker.Form.Fxor (form_to_coq args.(0), form_to_coq args.(1)) else assert false
      | Fiff -> if Array.length args = 2 then Smt_checker.Form.Fiff (form_to_coq args.(0), form_to_coq args.(1)) else assert false
      | Fite -> if Array.length args = 3 then Smt_checker.Form.Fite (form_to_coq args.(0), form_to_coq args.(1), form_to_coq args.(2)) else assert false
      | Fnot2 i -> Smt_checker.Form.Fnot2 (mkInt i, form_to_coq args.(0))


let form_interp_tbl reify =
  let (_,t) = Form.to_array reify Smt_checker.Form.Ftrue pf_to_coq in
  mkArray t


(* Importing from SMT-LIB v.2 without generating section variables *)

let count_btype = ref 0
let count_op = ref 0


let declare_sort sym =
  let s = string_of_symbol sym in
  let res = Tindex (dummy_indexed_type !count_btype) in
  incr count_btype;
  VeritSyntax.add_btype s res;
  res


let declare_fun sym arg cod =
  let s = string_of_symbol sym in
  let tyl = List.map sort_of_sort arg in
  let ty = sort_of_sort cod in
  let op = dummy_indexed_op !count_op (Array.of_list (List.map fst tyl)) (fst ty) in
  incr count_op;
  VeritSyntax.add_fun s op;
  op


let declare_commands ra rf acc = function
  | CDeclareSort (_,sym,_) -> let _ = declare_sort sym in acc
  | CDeclareFun (_,sym, (_, arg), cod) -> let _ = declare_fun sym arg cod in acc
  | CAssert (_, t) -> (make_root ra rf t)::acc
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


let checker fsmt fproof =
  this_clear_all ();
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = import_smtlib2 ra rf fsmt in
  let (max_id, confl) = import_trace fproof None in
  let (tres,last_root) = to_coq (fun i -> mkInt (SmtAtom.Form.to_lit i)) confl in
  let certif =
    Smt_checker.Euf_Checker.Certif (mkInt (max_id + 1), tres, mkInt (get_pos confl)) in
  let used_roots = compute_roots roots last_root in
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

  Smt_checker.Euf_Checker.checker_ext t_atom t_form rootsCstr used_rootsCstr certif

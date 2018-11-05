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


open SmtCertif
open SmtForm
open SatAtom
open SmtTrace
open Zchaff
open Sat_checker


let mkInt = ExtrNative.of_int
let mkArray = ExtrNative.of_array


let make_roots first last =
  let roots = Array.make (last.id + 2) (mkArray (Array.make 1 (mkInt 0))) in
  let mk_elem l =
    let x = match Form.pform l with
      | Fatom x -> x + 2
      | _ -> assert false  in
    mkInt (if Form.is_pos l then x lsl 1 else (x lsl 1) lxor 1) in
  let r = ref first in
  while !r.id < last.id do
    let root = Array.of_list (get_val !r) in
    let croot = Array.make (Array.length root + 1) (mkInt 0) in
    Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
    roots.(!r.id) <- mkArray croot;
    r := next !r
  done;
  let root = Array.of_list (get_val !r) in
  let croot = Array.make (Array.length root + 1) (mkInt 0) in
  Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
  roots.(!r.id) <- mkArray croot;

  mkArray roots


let to_coq to_lit (cstep,
                   cRes, cImmFlatten,
                   cTrue, cFalse, cBuildDef, cBuildDef2, cBuildProj,
                   cImmBuildProj,cImmBuildDef,cImmBuildDef2,
                   cEqTr, cEqCgr, cEqCgrP,
                   cLiaMicromega, cLiaDiseq, cSplArith, cSplDistinctElim, cHole) confl =
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
	Sat_Checker.Res (mkInt (get_pos c), mkArray args)
      | _ -> assert false in
  let def_step =
    Sat_Checker.Res (mkInt 0, mkArray [|mkInt 0|]) in
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


let checker fdimacs ftrace =
  SmtTrace.clear ();
  let _,first,last,reloc = import_cnf fdimacs in
  let d = make_roots first last in

  let max_id, confl = import_cnf_trace reloc ftrace first last in
  let (tres,_) =
    to_coq (fun _ -> assert false) certif_ops confl in
  let certif =
    Sat_Checker.Certif (mkInt (max_id + 1), tres, mkInt (get_pos confl)) in

  Sat_Checker.checker d certif

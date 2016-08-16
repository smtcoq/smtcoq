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


open SmtMisc
open CoqTerms
open SmtCertif

let notUsed = 0

let next_id = ref 0 

let clear () = next_id := 0

let next_id () =
  let id = !next_id in
  incr next_id;
  id

(** Basic functions over small certificates *)

let mk_scertif kind ov = 
  {
   id   = next_id ();
   kind = kind;
   pos  = None;
   used = notUsed;
   prev = None;
   next = None;
   value = ov 
 }
  
(** Roots *)


let mkRootGen ov = 
  let pos = next_id () in
  {
   id   = pos;
   kind = Root;
   pos  = Some pos;
   used = notUsed;
   prev = None;
   next = None;
   value = ov 
 }

(* let mkRoot = mkRootGen None *)
let mkRootV v = mkRootGen (Some v)
 
let isRoot k = k == Root 

(** Resolutions *)

let mkRes c1 c2 tl = 
  mk_scertif (Res { rc1 = c1; rc2 = c2; rtail = tl }) None

let isRes k =
  match k with
    | Res _ -> true
    | _ -> false


(** Other *)

let mkOther r ov = mk_scertif (Other r) ov


(** Moving into the trace *)
let next c =
  match c.next with
  | Some c1 -> c1
  | None -> assert false

let has_prev c =
  match c.prev with
    | Some _ -> true
    | None -> false

let prev c =
  match c.prev with
  | Some c1 -> c1
  | None -> Printf.printf "prev %i\n" c.id;flush stdout;assert false

let link c1 c2 =
  c1.next <- Some c2;
  c2.prev <- Some c1

let clear_links c =
  c.prev <- None;
  c.next <- None

let skip c =
  link (prev c) (next c);
  clear_links c

let insert_before c cprev =
  link (prev c) cprev;
  link cprev c

let get_res c s =
  match c.kind with
  | Res res -> res
  | _ -> Printf.printf "get_res %s\n" s; assert false

let get_other c s =
  match c.kind with
  | Other res -> res
  | _ -> Printf.printf "get_other %s\n" s; assert false

let get_val c =
  match c.value with
  | None -> assert false
  | Some cl -> cl

let rec repr c =
  match c.kind with
  | Root | Res _ | Other _ -> c
  | Same c -> repr c

let set_same c nc =
  c.kind <- Same (repr nc);
  skip c

let rec get_pos c =
  match c.kind with
  | Root | Res _ | Other _ ->
      begin match c.pos with
      | Some n -> n
      | _ -> assert false
      end
  | Same c -> get_pos c 

let eq_clause c1 c2 = (repr c1).id = (repr c2).id

(* Selection of useful rules *)
let select c =
  let mark c =
    if not (isRoot c.kind) then c.used <- 1 in
  mark c;
  let r = ref c in
  while not (isRoot !r.kind) do
    let p = prev !r in
    (match !r.kind with
      | Res res ->
      if !r.used == 1 then begin
        !r.used <- notUsed;
        (* let res = get_res !r "select" in *)
        mark res.rc1; mark res.rc2;
        List.iter mark res.rtail
      end else
        skip !r;
      | Same _ ->
        skip !r
      | _ ->
      if !r.used == 1 then 
	begin
          !r.used <- notUsed;
          let rl = get_other !r "select" in
          List.iter mark (used_clauses rl)
	end 
      else skip !r;
    );
    r := p
  done

 


(* Compute the number of occurence of each_clause *)

let rec occur c =
  match c.kind with
  | Root -> c.used <- c.used + 1
  | Res res ->
      if c.used == notUsed then 
	begin occur res.rc1; occur res.rc2; List.iter occur res.rtail end;
      c.used <- c.used + 1
  | Other res ->
      if c.used == notUsed then List.iter occur (used_clauses res);
      c.used <- c.used + 1;
  | Same c' ->
    occur c';
    c.used <- c.used + 1

(* Allocate clause *)

let alloc c =
  let free_pos = ref [] in

  (* free the unused roots *)

  let r = ref c in
  while isRoot !r.kind do
    if !r.used == notUsed then begin
      free_pos := get_pos !r :: !free_pos;
    end;
    r := next !r;
  done;

  (* r is the first clause defined by resolution or another rule,
     normaly the first used *)
  let last_set = ref (get_pos (prev !r)) in

  let decr_clause c =
    let rc = repr c in
      assert (rc.used > notUsed);
    rc.used <- rc.used - 1;
    if rc.used = notUsed then
      free_pos := get_pos rc :: !free_pos in

  let decr_res res =
    decr_clause res.rc1;
    decr_clause res.rc2;
    List.iter decr_clause res.rtail in

  let decr_other o =
    List.iter decr_clause (used_clauses o) in

  while !r.next <> None do
    let n = next !r in
      assert (!r.used <> notUsed);
    if isRes !r.kind then
      decr_res (get_res !r "alloc")
    else
      decr_other (get_other !r "alloc");
    begin match !free_pos with
    | p::free -> free_pos := free; !r.pos <- Some p
    | _ -> incr last_set; !r.pos <- Some !last_set
    end;
    r := n
  done;
  begin match !free_pos with
  | p::free -> free_pos := free; !r.pos <- Some p
  | _ -> incr last_set; !r.pos <- Some !last_set
  end;
  !last_set


(* A naive allocation for debugging *)

let naive_alloc c =
  let r = ref c in
  while isRoot !r.kind do
    r := next !r
  done;
  let last_set = ref (get_pos (prev !r)) in
  while !r.next <> None do
    let n = next !r in
    incr last_set; !r.pos <- Some !last_set;
    r := n
  done;
  incr last_set; !r.pos <- Some !last_set;
  !last_set


(* This function is currently inlined in verit/verit.ml and zchaff/zchaff.ml *)

let build_certif first_root confl =
  select confl;
  occur confl;
  alloc first_root


let to_coq to_lit interp (cstep,
    cRes, cWeaken, cImmFlatten,
    cTrue, cFalse, cBuildDef, cBuildDef2, cBuildProj,
    cImmBuildProj,cImmBuildDef,cImmBuildDef2,  
    cEqTr, cEqCgr, cEqCgrP, 
    cLiaMicromega, cLiaDiseq, cSplArith, cSplDistinctElim,
    cBBVar, cBBConst, cBBOp, cBBNot, cBBEq, cBBNeg, cBBAdd, cBBMul,
    cBBUlt, cBBSlt, cRowEq, cRowNeq,
    cHole) confl =

  let cuts = ref [] in

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
	mklApp cRes [|mkInt (get_pos c); Structures.mkArray (Lazy.force cint, args)|]
    | Other other ->
	begin match other with
        | Weaken (c',l') ->
           (let size = List.length l' in
            let lits = Array.make size (mkInt 0) in
            let l = ref l' in
            for i = 0 to size - 1 do
              match !l with
                | [] -> assert false
                | f::tl ->
                   (lits.(i) <- out_f f;
                    l := tl)
            done;
            mklApp cWeaken [|out_c c;out_c c'; Structures.mkArray (Lazy.force cint, lits)|])
	| ImmFlatten (c',f) -> mklApp cImmFlatten [|out_c c;out_c c'; out_f f|]
        | True -> mklApp cTrue [|out_c c|]
	| False -> mklApp cFalse [|out_c c|]
	| BuildDef f -> mklApp cBuildDef [|out_c c; out_f f|]
	| BuildDef2 f -> mklApp cBuildDef2 [|out_c c;out_f f|]
	| BuildProj (f, i) -> mklApp cBuildProj [|out_c c; out_f f;mkInt i|]
	| ImmBuildDef c' -> mklApp cImmBuildDef [|out_c c; out_c c'|]
	| ImmBuildDef2 c' -> mklApp cImmBuildDef2 [|out_c c;out_c c'|]
	| ImmBuildProj(c', i) -> mklApp cImmBuildProj [|out_c c; out_c c';mkInt i|]
        | EqTr (f, fl) ->
          let res = List.fold_right (fun f l -> mklApp ccons [|Lazy.force cint; out_f f; l|]) fl (mklApp cnil [|Lazy.force cint|]) in
          mklApp cEqTr [|out_c c; out_f f; res|]
        | EqCgr (f, fl) ->
          let res = List.fold_right (fun f l -> mklApp ccons [|mklApp coption [|Lazy.force cint|]; (match f with | Some f -> mklApp cSome [|Lazy.force cint; out_f f|] | None -> mklApp cNone [|Lazy.force cint|]); l|]) fl (mklApp cnil [|mklApp coption [|Lazy.force cint|]|]) in
          mklApp cEqCgr [|out_c c; out_f f; res|]
        | EqCgrP (f1, f2, fl) ->
          let res = List.fold_right (fun f l -> mklApp ccons [|mklApp coption [|Lazy.force cint|]; (match f with | Some f -> mklApp cSome [|Lazy.force cint; out_f f|] | None -> mklApp cNone [|Lazy.force cint|]); l|]) fl (mklApp cnil [|mklApp coption [|Lazy.force cint|]|]) in
          mklApp cEqCgrP [|out_c c; out_f f1; out_f f2; res|]
	| LiaMicromega (cl,d) ->
          let cl' = List.fold_right (fun f l -> mklApp ccons [|Lazy.force cint; out_f f; l|]) cl (mklApp cnil [|Lazy.force cint|]) in
          let c' = List.fold_right (fun f l -> mklApp ccons [|Lazy.force Coq_micromega.M.coq_proofTerm; Coq_micromega.dump_proof_term f; l|]) d (mklApp cnil [|Lazy.force Coq_micromega.M.coq_proofTerm|]) in
          mklApp cLiaMicromega [|out_c c; cl'; c'|]
        | LiaDiseq l -> mklApp cLiaDiseq [|out_c c; out_f l|]
        | SplArith (orig,res,l) ->
          let res' = out_f res in
          let l' = List.fold_right (fun f l -> mklApp ccons [|Lazy.force Coq_micromega.M.coq_proofTerm; Coq_micromega.dump_proof_term f; l|]) l (mklApp cnil [|Lazy.force Coq_micromega.M.coq_proofTerm|]) in
          mklApp cSplArith [|out_c c; out_c orig; res'; l'|]
	| SplDistinctElim (c',f) -> mklApp cSplDistinctElim [|out_c c;out_c c'; out_f f|]
        | BBVar res -> mklApp cBBVar [|out_c c; out_f res|]
        | BBConst res -> mklApp cBBConst [|out_c c; out_f res|]
        | BBOp (c1,c2,res) ->
          mklApp cBBOp [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBNot (c1,res) ->
          mklApp cBBNot [|out_c c; out_c c1; out_f res|]
        | BBNeg (c1,res) ->
          mklApp cBBNeg [|out_c c; out_c c1; out_f res|]
        | BBAdd (c1,c2,res) ->
          mklApp cBBAdd [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBMul (c1,c2,res) ->
          mklApp cBBMul [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBUlt (c1,c2,res) ->
          mklApp cBBUlt [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBSlt (c1,c2,res) ->
          mklApp cBBSlt [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBEq (c1,c2,res) ->
          mklApp cBBEq [|out_c c; out_c c1; out_c c2; out_f res|]
        | RowEq (res) -> mklApp cRowEq [|out_c c; out_f res|]
        | RowNeq (cl) ->
          let out_cl cl =
            List.fold_right (fun f l ->
                mklApp ccons [|Lazy.force cint; out_f f; l|])
              cl (mklApp cnil [|Lazy.force cint|]) in
          mklApp cRowNeq [|out_c c; out_cl cl|]
        | Hole (prem_id, concl) ->
           let prem = List.map (fun cl -> match cl.value with Some l -> l | None -> assert false) prem_id in
           let ass_name = Names.id_of_string ("ass"^(string_of_int (Hashtbl.hash concl))) in
           let ass_ty = interp (prem, concl) in
           cuts := (ass_name, ass_ty)::!cuts;
           let ass_var = Term.mkVar ass_name in
           let out_cl cl = List.fold_right (fun f l -> mklApp ccons [|Lazy.force cint; out_f f; l|]) cl (mklApp cnil [|Lazy.force cint|]) in
           let prem_id' = List.fold_right (fun c l -> mklApp ccons [|Lazy.force cint; out_c c; l|]) prem_id (mklApp cnil [|Lazy.force cint|]) in
           let prem' = List.fold_right (fun cl l -> mklApp ccons [|Lazy.force cState_C_t; out_cl cl; l|]) prem (mklApp cnil [|Lazy.force cState_C_t|]) in
           let concl' = out_cl concl in
           mklApp cHole [|out_c c; prem_id'; prem'; concl'; ass_var|]
	end
    | _ -> assert false in
  let step = Lazy.force cstep in
  let def_step = 
    mklApp cRes [|mkInt 0; Structures.mkArray (Lazy.force cint, [|mkInt 0|]) |] in
  let r = ref confl in
  let nc = ref 0 in
  while not (isRoot !r.kind) do r := prev !r; incr nc done;
  let last_root = !r in
  let size = !nc in
  let max = Structures.max_array_size - 1 in
  let q,r1 = size / max, size mod max in

  let trace = 
    let len = if r1 = 0 then q + 1 else q + 2 in
    Array.make len (Structures.mkArray (step, [|def_step|])) in
  for j = 0 to q - 1 do
    let tracej = Array.make Structures.max_array_size def_step in
    for i = 0 to max - 1 do
      r := next !r;
      tracej.(i) <- step_to_coq !r; 
    done;
    trace.(j) <- Structures.mkArray (step, tracej)
  done;
  if r1 <> 0 then begin
    let traceq = Array.make (r1 + 1) def_step in
    for i = 0 to r1-1 do 
    r := next !r; 
    traceq.(i) <- step_to_coq !r; 
    done;
    trace.(q) <- Structures.mkArray (step, traceq)
  end;

  (Structures.mkArray (mklApp carray [|step|], trace), last_root, !cuts)



(** Optimization of the trace *)

module MakeOpt (Form:SmtForm.FORM) = 
  struct 
    (* Share the certificate building a common clause *)
    let share_value c =
      let tbl = Hashtbl.create 17 in
      let to_lits v = List.map (Form.to_lit) v in
      let process c = 
	match c.value with
	| None -> ()
	| Some v ->
	    let lits = to_lits v in
	    try
	      let c' = Hashtbl.find tbl lits in
	      set_same c c'
	    with Not_found  -> Hashtbl.add tbl lits c in
      let r = ref c in
      while !r.next <> None do
	let next = next !r in
	process !r;
	r := next 
      done;
      process !r

   (* Sharing of the common prefix *)

    module HashedHeadRes =
      struct

	type t = Form.t resolution

	let equal r1 r2 =
	  eq_clause r1.rc1 r2.rc1 && eq_clause r1.rc2 r2.rc2

	let hash r = (repr r.rc1).id * 19 + (repr r.rc2).id

      end

    module HRtbl = Hashtbl.Make (HashedHeadRes)

    let common_head tl1 tl2 =
      let rec aux rhd tl1 tl2 =
	match tl1, tl2 with
	| [], _ -> List.rev rhd, tl1, tl2
	| _, [] -> List.rev rhd, tl1, tl2
	| c1::tl1', c2::tl2' ->
	    if eq_clause c1 c2 then aux (repr c1 :: rhd) tl1' tl2'
	    else List.rev rhd, tl1, tl2
      in aux [] tl1 tl2
	
    let share_prefix first_c n =
      let tbl = HRtbl.create (min n Sys.max_array_length) in
      let rec share c2 =
	if isRes c2.kind then (
	  let res2 = get_res c2 "share_prefix1" in
	  try
            let c1 = HRtbl.find tbl res2 in
            let res1 = get_res c1 "share_prefix2" in
	    (* res1 and res2 have the same head *)
            let head, tl1, tl2 = common_head res1.rtail res2.rtail in
            match tl1, tl2 with
            | [], [] ->
		set_same c2 c1;
            | [], c2'::tl2' ->
		res2.rc1 <- c1;
		res2.rc2 <- c2';
		res2.rtail <- tl2';
		share c2
            | c1'::tl1', [] ->
		skip c2;
		HRtbl.remove tbl res1;
		insert_before c1 c2;
		res1.rc1 <- c2;
		res1.rc2 <- c1';
		res1.rtail <- tl1';
		share c1
            | c1'::tl1', c2'::tl2' ->
		let c = mkRes res1.rc1 res1.rc2 head in
		HRtbl.remove tbl res1;
		insert_before c1 c;
		res1.rc1 <- c;
		res1.rc2 <- c1';
		res1.rtail <- tl1';
		res2.rc1 <- c;
		res2.rc2 <- c2';
		res2.rtail <- tl2';
		share c;
		share c1;
		share c2
	  with Not_found -> HRtbl.add tbl res2 c2
	 ) in
      let r = ref first_c in
      while !r.next <> None do
	let n = next !r in
	share !r;
	r := n
      done

  end

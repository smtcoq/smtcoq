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


open SmtMisc
open CoqTerms
open SmtCertif


(** Steps identifiers **)

let notUsed = 0

let next_id = ref 0

let clear_id () = next_id := 0

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
  | Same _ -> failwith "get_other on a Same"
  | Res _ -> failwith "get_other on a Res"
  | Root -> failwith "get_other on a Root"

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


(* Reorders the roots according to the order they were given in initially. *)
let order_roots init_index first =
  let r = ref first in
  let acc = ref [] in
  while isRoot !r.kind do
    begin match !r.value with
    | Some [f] -> let n = next !r in
                  clear_links !r;
                  acc := (init_index f, !r) :: !acc;
                  r := n
    | _ -> failwith "root value has unexpected form"
    end
  done;
  let _, lr = List.sort (fun (i1, _) (i2, _) -> Stdlib.compare i1 i2) !acc
             |> List.split
  in
  let link_to c1 c2 =
    let curr_id = c2.id -1 in
    c1.id <- curr_id;
    c1.pos <- Some curr_id;
    link c1 c2;
    c1
  in
  List.fold_right link_to lr !r, lr


(* <add_scertifs> adds the clauses <to_add> after the roots and makes sure that
the following clauses reference those clauses instead of the roots *)
let add_scertifs to_add c =
  let r = ref c in
  clear_id (); ignore (next_id ());
  while isRoot !r.kind do
    ignore (next_id ());
    r := next !r;
  done;
  let after_roots = !r in
  r := prev !r;
  let tbl : (int, 'a SmtCertif.clause) Hashtbl.t =
    Hashtbl.create 17 in
  let rec push_all = function
    | [] -> ()
    | (kind, ov, t_cl)::t -> let cl = mk_scertif kind ov in
                             Hashtbl.add tbl t_cl.id cl;
                             link !r cl;
                             r := next !r;
                             push_all t in
  push_all to_add; link !r after_roots; r:= after_roots;
  let uc c = try Hashtbl.find tbl c.id
             with Not_found -> c in
  let update_kind = function
    | Root -> Root
    | Same c -> Same (uc c)
    | Res {rc1 = r1; rc2 = r2; rtail = rt} ->
       Res {rc1 = uc r1;
            rc2 = uc r2;
            rtail = List.map uc rt}
    | Other u ->
       Other begin match u with
         | ImmBuildProj (c, x) -> ImmBuildProj (uc c, x)
         | ImmBuildDef c -> ImmBuildDef (uc c)
         | ImmBuildDef2 c -> ImmBuildDef2 (uc c)
         | Forall_inst (c, x) -> Forall_inst (uc c, x) 
         | ImmFlatten (c, x) -> ImmFlatten (uc c, x) 
         | SplArith (c, x, y) -> SplArith (uc c, x, y) 
         | SplDistinctElim (c, x) -> SplDistinctElim (uc c, x) 

         | Hole (cs, x) -> Hole (List.map uc cs, x)

         | x -> x end in
  let continue = ref true in
  while !continue do
    !r.kind <- update_kind !r.kind;
    !r.id <- next_id ();
    match !r.next with 
    | None -> continue := false
    | Some n -> r := n
  done;
  !r

(* Selection of useful rules *)
(* For <select>, <occur> and <alloc> we assume that the roots and only the 
roots are at the beginning of the smtcoq certif *)
(* After <select> no selected clauses are used so that <occur> works properly*)
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
     | Same c ->
        mark c;
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

(* Compute the number of occurence of each clause so that <alloc> works 
properly *)
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

(* Allocate clauses *)
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
     normally the first used *)
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

  let continue = ref true in
  while !continue do
    assert (!r.used <> notUsed);
    if isRes !r.kind then
      decr_res (get_res !r "alloc")
    else
      decr_other (get_other !r "alloc");
    begin try match !free_pos with
              | p::free -> free_pos := free; !r.pos <- Some p
              | _ -> incr last_set; !r.pos <- Some !last_set
          with _ -> failwith (to_string !r.kind)
    end;
    match !r.next with
    | None -> continue := false
    | Some n -> r := n
  done;
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
    cBBVar, cBBConst, cBBOp, cBBNot, cBBEq, cBBDiseq,
    cBBNeg, cBBAdd, cBBMul, cBBUlt, cBBSlt, cBBConc,
    cBBExtr, cBBZextn, cBBSextn,
    cBBShl, cBBShr,
    cRowEq, cRowNeq, cExt,
    cHole, cForallInst) confl sf =

  let cuts = ref [] in

  let out_f f = to_lit f in
  let out_c c = mkInt (get_pos c) in
  let out_cl cl = List.fold_right (fun f l -> mklApp ccons [|Lazy.force cint; out_f f; l|]) cl (mklApp cnil [|Lazy.force cint|]) in
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
	mklApp cRes [|mkInt (get_pos c); CoqTerms.mkArray (Lazy.force cint, args)|]
    | Other other ->
	begin match other with
        | Weaken (c',l') ->
          let out_cl cl =
            List.fold_right (fun f l ->
                mklApp ccons [|Lazy.force cint; out_f f; l|])
              cl (mklApp cnil [|Lazy.force cint|]) in
          mklApp cWeaken [|out_c c;out_c c'; out_cl l'|]
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
          let c' = List.fold_right (fun f l -> mklApp ccons [|Lazy.force CoqTerms.micromega_coq_proofTerm; CoqInterface.micromega_dump_proof_term f; l|]) d (mklApp cnil [|Lazy.force CoqTerms.micromega_coq_proofTerm|]) in
          mklApp cLiaMicromega [|out_c c; cl'; c'|]
        | LiaDiseq l -> mklApp cLiaDiseq [|out_c c; out_f l|]
        | SplArith (orig,res,l) ->
          let res' = out_f res in
          let l' = List.fold_right (fun f l -> mklApp ccons [|Lazy.force CoqTerms.micromega_coq_proofTerm; CoqInterface.micromega_dump_proof_term f; l|]) l (mklApp cnil [|Lazy.force CoqTerms.micromega_coq_proofTerm|]) in
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
        | BBConc (c1,c2,res) ->
          mklApp cBBConc [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBExtr (c1,res) ->
          mklApp cBBExtr [|out_c c; out_c c1; out_f res|]
        | BBZextn (c1,res) ->
          mklApp cBBZextn [|out_c c; out_c c1; out_f res|]
        | BBSextn (c1,res) ->
          mklApp cBBSextn [|out_c c; out_c c1; out_f res|]
        | BBShl (c1,c2,res) ->
          mklApp cBBShl [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBShr (c1,c2,res) ->
          mklApp cBBShr [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBEq (c1,c2,res) ->
          mklApp cBBEq [|out_c c; out_c c1; out_c c2; out_f res|]
        | BBDiseq (res) -> mklApp cBBDiseq [|out_c c; out_f res|]
        | RowEq (res) -> mklApp cRowEq [|out_c c; out_f res|]
        | RowNeq (cl) ->
          let out_cl cl =
            List.fold_right (fun f l ->
                mklApp ccons [|Lazy.force cint; out_f f; l|])
              cl (mklApp cnil [|Lazy.force cint|]) in
          mklApp cRowNeq [|out_c c; out_cl cl|]
        | Ext (res) -> mklApp cExt [|out_c c; out_f res|]
        | Hole (prem_id, concl) ->
           let prem = List.map (fun cl -> match cl.value with Some l -> l | None -> assert false) prem_id in
           let ass_name = CoqInterface.mkId ("ass"^(string_of_int (Hashtbl.hash concl))) in
           let ass_ty = interp (prem, concl) in
           cuts := (ass_name, ass_ty)::!cuts;
           let ass_var = CoqInterface.mkVar ass_name in
           let prem_id' = List.fold_right (fun c l -> mklApp ccons [|Lazy.force cint; out_c c; l|]) prem_id (mklApp cnil [|Lazy.force cint|]) in
           let prem' = List.fold_right (fun cl l -> mklApp ccons [|Lazy.force cState_C_t; out_cl cl; l|]) prem (mklApp cnil [|Lazy.force cState_C_t|]) in
           let concl' = out_cl concl in
           mklApp cHole [|out_c c; prem_id'; prem'; concl'; ass_var|]
        | Forall_inst (cl, concl) | Qf_lemma (cl, concl) ->
           let clemma, cplemma = match sf with
             | Some find -> find cl
             | None -> assert false in
           let concl' = out_cl [concl] in
           let app_name = CoqInterface.mkId ("app" ^ (string_of_int (Hashtbl.hash concl))) in
           let app_var = CoqInterface.mkVar app_name in
           let app_ty = CoqInterface.mkArrow clemma (interp ([], [concl])) in
           cuts := (app_name, app_ty)::!cuts;
           mklApp cForallInst [|out_c c; clemma; cplemma; concl'; app_var|]
	end
    | _ -> assert false in
  let step = Lazy.force cstep in
  let def_step =
    mklApp cRes [|mkInt 0; CoqTerms.mkArray (Lazy.force cint, [|mkInt 0|]) |] in
  let r = ref confl in
  let nc = ref 0 in
  while not (isRoot !r.kind) do r := prev !r; incr nc done;
  let last_root = !r in
  (* Be careful, step_to_coq makes a side effect on cuts so it needs to be called first *)
  let res =
    CoqInterface.mkTrace step_to_coq next carray clist cnil ccons cpair !nc step def_step r
  in
  (res, last_root, !cuts)



(** Optimization of the trace *)

module MakeOpt (Form:SmtForm.FORM) =
  struct
    (* Share the certificate building a common clause *)
    (* let share_value c =
     *   let tbl = Hashtbl.create 17 in
     *   let to_lits v = List.map (Form.to_lit) v in
     *   let process c =
     *     match c.value with
     *     | None -> ()
     *     | Some v ->
     *         let lits = to_lits v in
     *         try
     *           let c' = Hashtbl.find tbl lits in
     *           set_same c c'
     *         with Not_found  -> Hashtbl.add tbl lits c in
     *   let r = ref c in
     *   while !r.next <> None do
     *     let next = next !r in
     *     process !r;
     *     r := next
     *   done;
     *   process !r *)

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


let clear () = clear_id ()

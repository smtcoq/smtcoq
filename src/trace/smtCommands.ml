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
open CoqTerms
open SmtForm
open SmtAtom
open SmtTrace
open SmtCertif


let euf_checker_modules = [ ["SMTCoq";"Trace";"Euf_Checker"] ]
let certif_ops args = CoqTerms.make_certif_ops euf_checker_modules args
let cCertif = gen_constant euf_checker_modules "Certif"
let ccertif = gen_constant euf_checker_modules "certif"
let cchecker = gen_constant euf_checker_modules "checker"
let cchecker_correct = gen_constant euf_checker_modules "checker_correct"
let cchecker_b_correct =
  gen_constant euf_checker_modules "checker_b_correct"
let cchecker_b = gen_constant euf_checker_modules "checker_b"
let cchecker_eq_correct =
  gen_constant euf_checker_modules "checker_eq_correct"
let cchecker_eq = gen_constant euf_checker_modules "checker_eq"
(* let csetup_checker_step_debug =
 *   gen_constant euf_checker_modules "setup_checker_step_debug" *)
(* let cchecker_step_debug = gen_constant euf_checker_modules "checker_step_debug" *)
(* let cstep = gen_constant euf_checker_modules "step" *)
let cchecker_debug = gen_constant euf_checker_modules "checker_debug"

let cname_step = gen_constant euf_checker_modules "name_step"

let cName_Res = gen_constant euf_checker_modules "Name_Res"
let cName_Weaken= gen_constant euf_checker_modules "Name_Weaken"
let cName_ImmFlatten= gen_constant euf_checker_modules "Name_ImmFlatten"
let cName_CTrue= gen_constant euf_checker_modules "Name_CTrue"
let cName_CFalse = gen_constant euf_checker_modules "Name_CFalse"
let cName_BuildDef= gen_constant euf_checker_modules "Name_BuildDef"
let cName_BuildDef2= gen_constant euf_checker_modules "Name_BuildDef2"
let cName_BuildProj = gen_constant euf_checker_modules "Name_BuildProj"
let cName_ImmBuildDef= gen_constant euf_checker_modules "Name_ImmBuildDef"
let cName_ImmBuildDef2= gen_constant euf_checker_modules "Name_ImmBuildDef2"
let cName_ImmBuildProj = gen_constant euf_checker_modules "Name_ImmBuildProj"
let cName_EqTr = gen_constant euf_checker_modules "Name_EqTr"
let cName_EqCgr = gen_constant euf_checker_modules "Name_EqCgr"
let cName_EqCgrP= gen_constant euf_checker_modules "Name_EqCgrP"
let cName_LiaMicromega = gen_constant euf_checker_modules "Name_LiaMicromega"
let cName_LiaDiseq= gen_constant euf_checker_modules "Name_LiaDiseq"
let cName_SplArith= gen_constant euf_checker_modules "Name_SplArith"
let cName_SplDistinctElim = gen_constant euf_checker_modules "Name_SplDistinctElim"
let cName_BBVar= gen_constant euf_checker_modules "Name_BBVar"
let cName_BBConst= gen_constant euf_checker_modules "Name_BBConst"
let cName_BBOp= gen_constant euf_checker_modules "Name_BBOp"
let cName_BBNot= gen_constant euf_checker_modules "Name_BBNot"
let cName_BBNeg= gen_constant euf_checker_modules "Name_BBNeg"
let cName_BBAdd= gen_constant euf_checker_modules "Name_BBAdd"
let cName_BBConcat= gen_constant euf_checker_modules "Name_BBConcat"
let cName_BBMul= gen_constant euf_checker_modules "Name_BBMul"
let cName_BBUlt= gen_constant euf_checker_modules "Name_BBUlt"
let cName_BBSlt= gen_constant euf_checker_modules "Name_BBSlt"
let cName_BBEq= gen_constant euf_checker_modules "Name_BBEq"
let cName_BBDiseq= gen_constant euf_checker_modules "Name_BBDiseq"
let cName_BBExtract= gen_constant euf_checker_modules "Name_BBExtract"
let cName_BBZextend= gen_constant euf_checker_modules "Name_BBZextend"
let cName_BBSextend= gen_constant euf_checker_modules "Name_BBSextend"
let cName_BBShl= gen_constant euf_checker_modules "Name_BBShl"
let cName_BBShr= gen_constant euf_checker_modules "Name_BBShr"
let cName_RowEq= gen_constant euf_checker_modules "Name_RowEq"
let cName_RowNeq= gen_constant euf_checker_modules "Name_RowNeq"
let cName_Ext= gen_constant euf_checker_modules "Name_Ext"
let cName_Hole= gen_constant euf_checker_modules "Name_Hole"

(* Given an SMT-LIB2 file and a certif, build the corresponding objects *)

let compute_roots roots last_root =
  let r = ref last_root in
  while (has_prev !r) do
    r := prev !r
  done;

  let rec find_root i root = function
    | [] -> assert false
    | t::q -> if Form.equal t root then i else find_root (i+1) root q in

  let rec used_roots acc r =
    if isRoot r.kind then
      match r.value with
        | Some [root] ->
           let j = find_root 0 root roots in
           used_roots (j::acc) (next r)
        | _ -> assert false
    else acc
  in

  used_roots [] !r


let interp_uf t_i ta tf c =
  let rec interp = function
    | [] -> Lazy.force cfalse
    | [l] -> Form.interp_to_coq (Atom.interp_to_coq t_i ta) tf l
    | l::c -> mklApp corb [|Form.interp_to_coq (Atom.interp_to_coq t_i ta) tf l; interp c|] in
  interp c

let interp_conseq_uf t_i (prem, concl) =
  let ta = Hashtbl.create 17 in
  let tf = Hashtbl.create 17 in
  let rec interp = function
    | [] -> mklApp cis_true [|interp_uf t_i ta tf concl|]
    | c::prem -> Structures.mkArrow (mklApp cis_true [|interp_uf t_i ta tf c|]) (interp prem) in
  interp prem


let print_assm ty =
  Format.printf "WARNING: assuming the following hypothesis:\n%s\n@."
    (string_coq_constr ty)


let parse_certif t_i t_func t_atom t_form root used_root trace (rt, ro, ra, rf, roots, max_id, confl) =

  let t_i' = make_t_i rt in
  let ce5 = Structures.mkUConst t_i' in
  let ct_i = Structures.mkConst (Structures.declare_constant t_i ce5) in

  let t_func' = make_t_func ro ct_i in
  let ce6 = Structures.mkUConst t_func' in
  let ct_func = Structures.mkConst (Structures.declare_constant t_func ce6) in

  let t_atom' = Atom.interp_tbl ra in
  let ce1 = Structures.mkUConst t_atom' in
  let ct_atom = Structures.mkConst (Structures.declare_constant t_atom ce1) in

  let t_form' = snd (Form.interp_tbl rf) in
  let ce2 = Structures.mkUConst t_form' in
  let ct_form = Structures.mkConst (Structures.declare_constant t_form ce2) in

  (* EMPTY LEMMA LIST *)
  let (tres, last_root, cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf ct_i) (certif_ops (Some [|ct_i; ct_func; ct_atom; ct_form|])) confl None in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let used_roots = compute_roots roots last_root in
  let roots =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in
  let used_roots =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Structures.mkArray (Lazy.force cint, res)|] in
  let ce3 = Structures.mkUConst roots in
  let _ = Structures.declare_constant root ce3 in
  let ce3' = Structures.mkUConst used_roots in
  let _ = Structures.declare_constant used_root ce3' in

  let certif =
    mklApp cCertif [|ct_i; ct_func; ct_atom; ct_form; mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let ce4 = Structures.mkUConst certif in
  let _ = Structures.declare_constant trace ce4 in

  ()


(* Given an SMT-LIB2 file and a certif, build the corresponding theorem *)

let interp_roots t_i roots =
  let interp = Form.interp_to_coq (Atom.interp_to_coq t_i (Hashtbl.create 17)) (Hashtbl.create 17) in
  match roots with
    | [] -> Lazy.force ctrue
    | f::roots -> List.fold_left (fun acc f -> mklApp candb [|acc; interp f|]) (interp f) roots

let theorem name (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = Structures.mkName "t_i" in
  let ntfunc = Structures.mkName "t_func" in
  let ntatom = Structures.mkName "t_atom" in
  let ntform = Structures.mkName "t_form" in
  let nc = Structures.mkName "c" in
  let nused_roots = Structures.mkName "used_roots" in
  let nd = Structures.mkName "d" in

  let v = Structures.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  (* EMPTY LEMMA LIST *)
  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *)|])) confl None in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let certif =
    mklApp cCertif [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let used_roots = compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Structures.mkArray (Lazy.force cint, res)|] in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in

  let theorem_concl = mklApp cnot [|mklApp cis_true [|interp_roots t_i roots|]|] in
  let theorem_proof_cast =
    Structures.mkCast (
        Structures.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
        Structures.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
        Structures.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
        Structures.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
        Structures.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
        Structures.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
        Structures.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
        mklApp cchecker_correct
               [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*);
	         vm_cast_true_no_check
	           (mklApp cchecker [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|])|]))))))),
        Structures.vmcast,
        theorem_concl)
  in
  let theorem_proof_nocast =
        Structures.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
        Structures.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
        Structures.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
        Structures.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
        Structures.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
        Structures.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
        Structures.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
        mklApp cchecker_correct
               [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|])))))))
  in

  let ce = Structures.mkTConst theorem_proof_cast theorem_proof_nocast theorem_concl in
  let _ = Structures.declare_constant name ce in
  ()


(* Given an SMT-LIB2 file and a certif, call the checker *)

let checker (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = Structures.mkName "t_i" in
  let ntfunc = Structures.mkName "t_func" in
  let ntatom = Structures.mkName "t_atom" in
  let ntform = Structures.mkName "t_form" in
  let nc = Structures.mkName "c" in
  let nused_roots = Structures.mkName "used_roots" in
  let nd = Structures.mkName "d" in

  let v = Structures.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  (* EMPTY LEMMA LIST *)
  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *)|])) confl None in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let certif =
    mklApp cCertif [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let used_roots = compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Structures.mkArray (Lazy.force cint, res)|] in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in

  let tm =
   Structures.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
   Structures.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
   Structures.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
   Structures.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
   Structures.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
   Structures.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
   Structures.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
   mklApp cchecker [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|]))))))) in

  let res = Structures.cbv_vm (Global.env ()) tm (Lazy.force CoqTerms.cbool) in
  Format.eprintf "     = %s\n     : bool@."
    (if Structures.eq_constr res (Lazy.force CoqTerms.ctrue) then
        "true" else "false")

let count_used confl =
  let cpt = ref 0 in
  let rec count c =
    incr cpt;
    (* if c.used = 1 then incr cpt; *)
    match c.prev with
    | None -> !cpt
    | Some c -> count c
  in
  count confl


let checker_debug (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = Structures.mkName "t_i" in
  let ntfunc = Structures.mkName "t_func" in
  let ntatom = Structures.mkName "t_atom" in
  let ntform = Structures.mkName "t_form" in
  let nc = Structures.mkName "c" in
  let nused_roots = Structures.mkName "used_roots" in
  let nd = Structures.mkName "d" in

  let v = Structures.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*);
                          v 2(*t_atom*); v 1(* t_form *)|])) confl None in
  List.iter (fun (v,ty) ->
    let _ = Structures.declare_new_variable v ty in
    print_assm ty
  ) cuts;

  let certif =
    mklApp cCertif [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *);
                     mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let used_roots = compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|];
                   Structures.mkArray (Lazy.force cint, res)|] in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Structures.mkArray (Lazy.force cint, res) in

  let tm =
   Structures.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
   Structures.mkLetIn (ntfunc, t_func,
                 mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
   Structures.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
   Structures.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
   Structures.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*);
                                              v 2 (*t_atom*); v 1 (*t_form*)|],
   Structures.mkLetIn (nused_roots, used_rootsCstr,
                 mklApp coption [|mklApp carray [|Lazy.force cint|]|],
   Structures.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
   mklApp cchecker_debug [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*);
       v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|]))))))) in

  let res = Structures.cbv_vm (Global.env ()) tm
      (mklApp coption
         [|mklApp cprod
             [|Lazy.force cnat; Lazy.force cname_step|]|]) in

  match Structures.decompose_app res with
  | c, _ when Structures.eq_constr c (Lazy.force cNone) ->
    Structures.error ("Debug checker is only meant to be used for certificates \
                       that fail to be checked by SMTCoq.")
  | c, [_; n] when Structures.eq_constr c (Lazy.force cSome) ->
    (match Structures.decompose_app n with
     | c, [_; _; cnb; cn] when Structures.eq_constr c (Lazy.force cpair) ->
       let n = fst (Structures.decompose_app cn) in
       let name =
         if Structures.eq_constr n (Lazy.force cName_Res ) then "Res"
         else if Structures.eq_constr n (Lazy.force cName_Weaken) then "Weaken"
         else if Structures.eq_constr n (Lazy.force cName_ImmFlatten) then "ImmFlatten"
         else if Structures.eq_constr n (Lazy.force cName_CTrue) then "CTrue"
         else if Structures.eq_constr n (Lazy.force cName_CFalse ) then "CFalse"
         else if Structures.eq_constr n (Lazy.force cName_BuildDef) then "BuildDef"
         else if Structures.eq_constr n (Lazy.force cName_BuildDef2) then "BuildDef2"
         else if Structures.eq_constr n (Lazy.force cName_BuildProj ) then "BuildProj"
         else if Structures.eq_constr n (Lazy.force cName_ImmBuildDef) then "ImmBuildDef"
         else if Structures.eq_constr n (Lazy.force cName_ImmBuildDef2) then "ImmBuildDef2"
         else if Structures.eq_constr n (Lazy.force cName_ImmBuildProj ) then "ImmBuildProj"
         else if Structures.eq_constr n (Lazy.force cName_EqTr ) then "EqTr"
         else if Structures.eq_constr n (Lazy.force cName_EqCgr ) then "EqCgr"
         else if Structures.eq_constr n (Lazy.force cName_EqCgrP) then "EqCgrP"
         else if Structures.eq_constr n (Lazy.force cName_LiaMicromega ) then "LiaMicromega"
         else if Structures.eq_constr n (Lazy.force cName_LiaDiseq) then "LiaDiseq"
         else if Structures.eq_constr n (Lazy.force cName_SplArith) then "SplArith"
         else if Structures.eq_constr n (Lazy.force cName_SplDistinctElim ) then "SplDistinctElim"
         else if Structures.eq_constr n (Lazy.force cName_BBVar) then "BBVar"
         else if Structures.eq_constr n (Lazy.force cName_BBConst) then "BBConst"
         else if Structures.eq_constr n (Lazy.force cName_BBOp) then "BBOp"
         else if Structures.eq_constr n (Lazy.force cName_BBNot) then "BBNot"
         else if Structures.eq_constr n (Lazy.force cName_BBNeg) then "BBNeg"
         else if Structures.eq_constr n (Lazy.force cName_BBAdd) then "BBAdd"
         else if Structures.eq_constr n (Lazy.force cName_BBConcat) then "BBConcat"
         else if Structures.eq_constr n (Lazy.force cName_BBMul) then "BBMul"
         else if Structures.eq_constr n (Lazy.force cName_BBUlt) then "BBUlt"
         else if Structures.eq_constr n (Lazy.force cName_BBSlt) then "BBSlt"
         else if Structures.eq_constr n (Lazy.force cName_BBEq) then "BBEq"
         else if Structures.eq_constr n (Lazy.force cName_BBDiseq) then "BBDiseq"
         else if Structures.eq_constr n (Lazy.force cName_BBExtract) then "BBExtract"
         else if Structures.eq_constr n (Lazy.force cName_BBZextend) then "BBZextend"
         else if Structures.eq_constr n (Lazy.force cName_BBSextend) then "BBSextend"
         else if Structures.eq_constr n (Lazy.force cName_BBShl) then "BBShl"
         else if Structures.eq_constr n (Lazy.force cName_BBShr) then "BBShr"
         else if Structures.eq_constr n (Lazy.force cName_RowEq) then "RowEq"
         else if Structures.eq_constr n (Lazy.force cName_RowNeq) then "RowNeq"
         else if Structures.eq_constr n (Lazy.force cName_Ext) then "Ext"
         else if Structures.eq_constr n (Lazy.force cName_Hole) then "Hole"
         else string_coq_constr n
       in
       let nb = mk_nat cnb + List.length roots + (confl.id + 1 - count_used confl) in
       Structures.error ("Step number " ^ string_of_int nb ^
                         " (" ^ name ^ ") of the certificate likely failed.")
     | _ -> assert false
    )
  | _ -> assert false



(* let rec of_coq_list cl =
 *   match Structures.decompose_app cl with
 *   | c, _ when Structures.eq_constr c (Lazy.force cnil) -> []
 *   | c, [_; x; cr] when Structures.eq_constr c (Lazy.force ccons) ->
 *     x :: of_coq_list cr
 *   | _ -> assert false *)


(* let checker_debug_step t_i t_func t_atom t_form root used_root trace
 *     (rt, ro, ra, rf, roots, max_id, confl) =
 * 
 *   let t_i' = make_t_i rt in
 *   let ce5 = Structures.mkUConst t_i' in
 *   let ct_i = Structures.mkConst (Structures.declare_constant t_i ce5) in
 * 
 *   let t_func' = make_t_func ro ct_i in
 *   let ce6 = Structures.mkUConst t_func' in
 *   let ct_func =
 *     Structures.mkConst (Structures.declare_constant t_func ce6) in
 * 
 *   let t_atom' = Atom.interp_tbl ra in
 *   let ce1 = Structures.mkUConst t_atom' in
 *   let ct_atom =
 *     Structures.mkConst (Structures.declare_constant t_atom ce1) in
 * 
 *   let t_form' = snd (Form.interp_tbl rf) in
 *   let ce2 = Structures.mkUConst t_form' in
 *   let ct_form =
 *     Structures.mkConst (Structures.declare_constant t_form ce2) in
 * 
 *   let (tres, last_root, cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i))
 *       (interp_conseq_uf ct_i)
 *       (certif_ops (Some [|ct_i; ct_func; ct_atom; ct_form|])) confl None in
 *   List.iter (fun (v,ty) ->
 *     let _ = Structures.declare_new_variable v ty in
 *     print_assm ty
 *   ) cuts;
 * 
 *   let used_roots = compute_roots roots last_root in
 *   let croots =
 *     let res = Array.make (List.length roots + 1) (mkInt 0) in
 *     let i = ref 0 in
 *     List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
 *     Structures.mkArray (Lazy.force cint, res) in
 *   let cused_roots =
 *     let l = List.length used_roots in
 *     let res = Array.make (l + 1) (mkInt 0) in
 *     let i = ref (l-1) in
 *     List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
 *     mklApp cSome [|mklApp carray [|Lazy.force cint|];
 *                    Structures.mkArray (Lazy.force cint, res)|] in
 *   let ce3 = Structures.mkUConst croots in
 *   let _ = Structures.declare_constant root ce3 in
 *   let ce3' = Structures.mkUConst cused_roots in
 *   let _ = Structures.declare_constant used_root ce3' in
 * 
 *   let certif =
 *     mklApp cCertif [|ct_i; ct_func; ct_atom; ct_form; mkInt (max_id + 1);
 *                      tres;mkInt (get_pos confl)|] in
 *   let ce4 = Structures.mkUConst certif in
 *   let _ = Structures.declare_constant trace ce4 in
 * 
 *   let setup =
 *    mklApp csetup_checker_step_debug
 *      [| ct_i; ct_func; ct_atom; ct_form; croots; cused_roots; certif |] in
 * 
 *   let setup = Structures.cbv_vm (Global.env ()) setup
 *       (mklApp cprod
 *          [|Lazy.force cState_S_t;
 *            mklApp clist [|mklApp cstep
 *                             [|ct_i; ct_func; ct_atom; ct_form|]|]|]) in
 * 
 *   let s, steps = match Structures.decompose_app setup with
 *     | c, [_; _; s; csteps] when Structures.eq_constr c (Lazy.force cpair) ->
 *       s, of_coq_list csteps
 *     | _ -> assert false
 *   in
 * 
 *   let cpt = ref (List.length roots) in
 *   let debug_step s step =
 *     incr cpt;
 *     Format.eprintf "%d@." !cpt;
 *     let tm =
 *       mklApp cchecker_step_debug
 *         [| ct_i; ct_func; ct_atom; ct_form; s; step |] in
 * 
 *     let res =
 *       Structures.cbv_vm (Global.env ()) tm
 *           (mklApp cprod [|Lazy.force cState_S_t; Lazy.force cbool|]) in
 * 
 *     match Structures.decompose_app res with
 *     | c, [_; _; s; cbad] when Structures.eq_constr c (Lazy.force cpair) ->
 *       if not (mk_bool cbad) then s
 *       else Structures.error ("Step number " ^ string_of_int !cpt ^
 *                              " (" ^ string_coq_constr
 *                                (fst (Structures.decompose_app step)) ^ ")" ^
 *                              " of the certificate likely failed." )
 *     | _ -> assert false
 *   in
 * 
 *   List.fold_left debug_step s steps |> ignore;
 * 
 *   Structures.error ("Debug checker is only meant to be used for certificates \
 *                      that fail to be checked by SMTCoq.") *)



(* Tactic *)

let build_body rt ro ra rf l b (max_id, confl) vm_cast find =
  let nti = Structures.mkName "t_i" in
  let ntfunc = Structures.mkName "t_func" in
  let ntatom = Structures.mkName "t_atom" in
  let ntform = Structures.mkName "t_form" in
  let nc = Structures.mkName "c" in

  let v = Structures.mkRel in

  let t_i = make_t_i rt in
  let t_func = Structures.lift 1 (make_t_func ro (v 0 (*t_i - 1*))) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let (tres,_,cuts) = SmtTrace.to_coq Form.to_coq
      (interp_conseq_uf t_i)
      (certif_ops
         (Some [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|]))
      confl find
  in
  let certif =
    mklApp cCertif
      [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*);
        mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let add_lets t =
    Structures.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
    Structures.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(*t_i*)|]|],
    Structures.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Structures.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Structures.mkLetIn (nc, certif, mklApp ccertif
             [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    t))))) in

  let cbc =
    add_lets
      (mklApp cchecker_b [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*);
                           v 2 (*t_form*); l; b; v 1 (*certif*)|])
    |> vm_cast
  in

  let proof_cast =
    add_lets
      (mklApp cchecker_b_correct
         [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*);
           l; b; v 1 (*certif*); cbc |]) in

  let proof_nocast =
    add_lets
      (mklApp cchecker_b_correct
         [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*);
           l; b; v 1 (*certif*)|]) in

  (proof_cast, proof_nocast, cuts)


let build_body_eq rt ro ra rf l1 l2 l (max_id, confl) vm_cast find =
  let nti = Structures.mkName "t_i" in
  let ntfunc = Structures.mkName "t_func" in
  let ntatom = Structures.mkName "t_atom" in
  let ntform = Structures.mkName "t_form" in
  let nc = Structures.mkName "c" in

  let v = Structures.mkRel in

  let t_i = make_t_i rt in
  let t_func = Structures.lift 1 (make_t_func ro (v 0 (*t_i*))) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let (tres,_,cuts) = SmtTrace.to_coq Form.to_coq
      (interp_conseq_uf t_i)
      (certif_ops (Some [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|])) confl find in
  let certif =
    mklApp cCertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let add_lets t =
    Structures.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_compdec|],
    Structures.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(*t_i*)|]|],
    Structures.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Structures.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Structures.mkLetIn (nc, certif, mklApp ccertif
             [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    t))))) in

  let ceqc =
    add_lets
      (mklApp cchecker_eq [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*);
                            v 2 (*t_form*); l1; l2; l; v 1 (*certif*)|])
      |> vm_cast
  in

  let proof_cast =
    add_lets
      (mklApp cchecker_eq_correct
         [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*);
           l1; l2; l; v 1 (*certif*); ceqc|])
  in
  let proof_nocast =
    add_lets
      (mklApp cchecker_eq_correct
         [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*);
           l1; l2; l; v 1 (*certif*)|])
  in

  (proof_cast, proof_nocast, cuts)


let get_arguments concl =
  let f, args = Structures.decompose_app concl in
  match args with
  | [ty;a;b] when (Structures.eq_constr f (Lazy.force ceq)) && (Structures.eq_constr ty (Lazy.force cbool)) -> a, b
  | [a] when (Structures.eq_constr f (Lazy.force cis_true)) -> a, Lazy.force ctrue
  | _ -> failwith ("Verit.tactic: can only deal with equality over bool")


let make_proof call_solver env rt ro ra_quant rf_quant l ls_smtc =
  let root = SmtTrace.mkRootV [l] in
  call_solver env rt ro ra_quant rf_quant (root,l) ls_smtc
(* TODO: not generic anymore, the "lemma" part is currently specific to veriT *)

(* <of_coq_lemma> reifies the given coq lemma, so we can then easily print it in a
 .smt2 file. We need the reify tables to correctly recognize free variables
 of the lemma. We also need to make sure to leave unchanged the tables because
 the new objects may contain bound (by forall of the lemma) variables. *)

(* Bound variables are given fresh names to avoid variable capture *)
let gen_rel_name =
  let num = ref (-1) in
  fun () -> incr num; "SMTCoqRelName"^(string_of_int !num)

let of_coq_lemma rt ro ra_quant rf_quant env sigma solver_logic clemma =
  let warn () =
    Structures.warning "Lemma" ("Discarding the following lemma (axiom form unsupported): "^(Pp.string_of_ppcmds (Ppconstr.pr_constr_expr Environ.empty_env Evd.empty (Structures.extern_constr clemma))));
    None
  in

  let rel_context, qf_lemma = Term.decompose_prod_assum clemma in
  (* Bound variables are given fresh names to avoid variable capture *)
  let rel_context = List.map (fun rel -> Context.Rel.Declaration.set_name (Names.Name.mk_name (Names.Id.of_string (gen_rel_name ()))) rel) rel_context in

  let env_lemma = Environ.push_rel_context rel_context env in
  let f, args = Structures.decompose_app qf_lemma in
  let core_f =
    if Structures.eq_constr f (Lazy.force cis_true) then
      match args with
      | [a] -> Some a
      | _ -> warn ()
    else if Structures.eq_constr f (Lazy.force ceq) then
      match args with
      | [ty; arg1; arg2] when Structures.eq_constr ty (Lazy.force cbool) &&
                                Structures.eq_constr arg2 (Lazy.force ctrue) ->
         Some arg1
      | _ -> warn ()
    else warn () in
  let core_smt =
    match core_f with
      | Some core_f ->
         Some (Form.of_coq (Atom.of_coq ~eqsym:true rt ro ra_quant solver_logic env_lemma sigma) rf_quant core_f)
      | None -> None
  in
  let forall_args =
    let fmap r = let n, t = Structures.destruct_rel_decl r in
                 Structures.string_of_name n, SmtBtype.of_coq rt solver_logic t in
    List.map fmap rel_context
  in
  match forall_args with
    | [] -> core_smt
    | _ ->
       (match core_smt with
          | Some core_smt -> Some (Form.get rf_quant (Fapp (Fforall forall_args, [|core_smt|])))
          | None -> None)

let core_tactic call_solver solver_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl env sigma concl =
  let a, b = get_arguments concl in

  let tlcepl = List.map (Structures.interp_constr env sigma) lcepl in
  let lcpl = lcpl @ tlcepl in

  let create_lemma l =
    let cl = Structures.retyping_get_type_of env sigma l in
    match of_coq_lemma rt ro ra_quant rf_quant env sigma solver_logic cl with
      | Some smt -> Some ((cl, l), smt)
      | None -> None
  in
  let l_pl_ls = SmtMisc.filter_map create_lemma lcpl in
  let lsmt = List.map snd l_pl_ls in

  let lem_tbl : (int, Structures.constr * Structures.constr) Hashtbl.t =
    Hashtbl.create 100 in
  let new_ref ((l, pl), ls) =
    Hashtbl.add lem_tbl (Form.index ls) (l, pl) in

  List.iter new_ref l_pl_ls;

  let find_lemma cl =
    let re_hash hf = Form.hash_hform (Atom.hash_hatom ra_quant) rf_quant hf in
    match cl.value with
    | Some [l] ->
       let hl = re_hash l in
       begin try Hashtbl.find lem_tbl (Form.index hl)
             with Not_found ->
               let oc = open_out "/tmp/find_lemma.log" in
               let fmt = Format.formatter_of_out_channel oc in
               List.iter (fun u -> Format.fprintf fmt "%a\n" (Form.to_smt ~debug:true) u) lsmt;
               Format.fprintf fmt "\n%a\n" (Form.to_smt ~debug:true) hl;
               flush oc; close_out oc; failwith "find_lemma" end
      | _ -> failwith "unexpected form of root" in

  let (body_cast, body_nocast, cuts) =
    if ((Structures.eq_constr b (Lazy.force ctrue)) ||
        (Structures.eq_constr b (Lazy.force cfalse))) then (
      let l = Form.of_coq (Atom.of_coq rt ro ra solver_logic env sigma) rf a in
      let _ = Form.of_coq (Atom.of_coq ~eqsym:true rt ro ra_quant solver_logic env sigma) rf_quant a in
      let nl = if (Structures.eq_constr b (Lazy.force ctrue)) then Form.neg l else l in
      let lsmt = Form.flatten rf nl :: lsmt in
      let max_id_confl = make_proof call_solver env rt ro ra_quant rf_quant nl lsmt in
      build_body rt ro ra rf (Form.to_coq l) b max_id_confl (vm_cast env) (Some find_lemma)
    ) else (
      let l1 = Form.of_coq (Atom.of_coq rt ro ra solver_logic env sigma) rf a in
      let _ = Form.of_coq (Atom.of_coq ~eqsym:true rt ro ra_quant solver_logic env sigma) rf_quant a in
      let l2 = Form.of_coq (Atom.of_coq rt ro ra solver_logic env sigma) rf b in
      let _ = Form.of_coq (Atom.of_coq ~eqsym:true rt ro ra_quant solver_logic env sigma) rf_quant b in
      let l = Form.get rf (Fapp(Fiff,[|l1;l2|])) in
      let nl = Form.neg l in
      let lsmt = Form.flatten rf nl :: lsmt in
      let max_id_confl = make_proof call_solver env rt ro ra_quant rf_quant nl lsmt in
      build_body_eq rt ro ra rf (Form.to_coq l1) (Form.to_coq l2)
        (Form.to_coq nl) max_id_confl (vm_cast env) (Some find_lemma) ) in

      let cuts = (SmtBtype.get_cuts rt) @ cuts in

  List.fold_right (fun (eqn, eqt) tac ->
      Structures.tclTHENLAST
        (Structures.assert_before (Structures.name_of_id eqn) eqt)
        tac
    ) cuts
    (Structures.tclTHEN
       (Structures.set_evars_tac body_nocast)
       (Structures.vm_cast_no_check body_cast))


let tactic call_solver solver_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl =
  Structures.tclTHEN
    Tactics.intros
    (Structures.mk_tactic (core_tactic call_solver solver_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl))


(**********************************************)
(* Show solver models as Coq counter-examples *)
(**********************************************)


open SExpr
open Smtlib2_genConstr
open Format


let string_index_of_constr env i cf =
  try
    let s = string_coq_constr cf in
    let nc = Environ.named_context env in
    let nd = Environ.lookup_named (Structures.mkId s) env in
    let cpt = ref 0 in
    (try List.iter (fun n -> incr cpt; if n == nd then raise Exit) nc
     with Exit -> ());
    s, !cpt
  with _ -> string_coq_constr cf, -i


let vstring_i env i =
  let cf = SmtAtom.Atom.get_coq_term_op i in
  if Structures.isRel cf then
    let dbi = Structures.destRel cf in
    let s =
      Environ.lookup_rel dbi env
      |> Structures.get_rel_dec_name
      |> SmtMisc.string_of_name_def "?"
    in
    s, dbi
  else
    string_index_of_constr env i cf


let sstring_i env i v =
  let tf = SmtBtype.get_coq_type_op i in
  let (s, idx) = string_index_of_constr env i tf in
  (s^"#"^v, idx)


let smt2_id_to_coq_string env t_i ra rf name =
  try
    let l = String.split_on_char '_' name in
    match l with
      | ["op"; i] -> vstring_i env (int_of_string i)
      | ["@uc"; "Tindex"; i; j] -> sstring_i env (int_of_string i) j
      | _ -> raise Not_found
  with _ -> (name, 0)


let op_to_coq_string op = match op with
  | "=" | "+" | "-" | "*" | "/" -> op
  | "or" -> "||"
  | "and" -> "&&"
  | "xor" -> "xorb"
  | "=>" -> "implb"
  | _ -> op


let coq_bv_string s =
  let rec aux acc = function
    | true :: r -> aux (acc ^ "|1") r
    | false :: r -> aux (acc ^ "|0") r
    | [] -> "#b" ^ acc ^ "|"
  in
  if String.length s < 3 ||
     not (s.[0] = '#' && s.[1] = 'b') then failwith "not bv";
  aux "" (parse_smt2bv s)


let is_bvint bs =
  try Scanf.sscanf bs "bv%s" (fun s ->
      try ignore (Big_int.big_int_of_string s); true
      with _ -> false)
  with _ -> false


let rec smt2_sexpr_to_coq_string env t_i ra rf =
  let open SExpr in function
  | Atom "true" -> "true"
  | Atom "false" -> "false"
  | Atom s ->
    (try ignore (int_of_string s); s
     with Failure _ ->
     try coq_bv_string s
     with Failure _ ->
     try fst (smt2_id_to_coq_string env t_i ra rf s)
     with _ -> s)
  | List [Atom "as"; Atom "const"; _] -> "const_farray"
  | List [Atom "as"; s; _] -> smt2_sexpr_to_coq_string env t_i ra rf s
  | List [Atom "_"; Atom bs; Atom s] when is_bvint bs ->
    Scanf.sscanf bs "bv%s" (fun i ->
        coq_bv_string (bigint_bv (Big_int.big_int_of_string i)
                         (int_of_string s)))
  | List [Atom "-"; Atom _ as s] ->
    sprintf "-%s"
      (smt2_sexpr_to_coq_string env t_i ra rf s)
  | List [Atom "-"; s] ->
    sprintf "(- %s)"
      (smt2_sexpr_to_coq_string env t_i ra rf s)
  | List [Atom (("+"|"-"|"*"|"/"|"or"|"and"|"=") as op); s1; s2] ->
    sprintf "%s %s %s"
      (smt2_sexpr_to_coq_string env t_i ra rf s1)
      (op_to_coq_string op)
      (smt2_sexpr_to_coq_string env t_i ra rf s2)
  | List [Atom (("xor"|"=>"|"") as op); s1; s2] ->
    sprintf "(%s %s %s)"
      (op_to_coq_string op)
      (smt2_sexpr_to_coq_string env t_i ra rf s1)
      (smt2_sexpr_to_coq_string env t_i ra rf s2)
  | List [Atom "select"; a; i] ->
    sprintf "%s[%s]"
      (smt2_sexpr_to_coq_string env t_i ra rf a)
      (smt2_sexpr_to_coq_string env t_i ra rf i)
  | List [Atom "store"; a; i; v] ->
    sprintf "%s[%s <- %s]"
      (smt2_sexpr_to_coq_string env t_i ra rf a)
      (smt2_sexpr_to_coq_string env t_i ra rf i)
      (smt2_sexpr_to_coq_string env t_i ra rf v)
  | List [Atom "ite"; c; s1; s2] ->
    sprintf "if %s then %s else %s"
      (smt2_sexpr_to_coq_string env t_i ra rf c)
      (smt2_sexpr_to_coq_string env t_i ra rf s1)
      (smt2_sexpr_to_coq_string env t_i ra rf s2)
  | List l ->
    sprintf "(%s)"
      (String.concat " " (List.map (smt2_sexpr_to_coq_string env t_i ra rf) l))


let str_contains s1 s2 =
  let re = Str.regexp_string s2 in
  try ignore (Str.search_forward re s1 0); true
  with Not_found -> false

let lambda_to_coq_string l s =
  Format.sprintf "fun %s => %s"
    (String.concat " "
       (List.map (function
            | List [Atom v; _] ->
              if str_contains s v then v else "_"
            | _ -> assert false) l))
    s

type model =
  | Fun of ((string * int) * string)
  | Sort

let model_item env rt ro ra rf =
  let t_i = make_t_i rt in
  function
  | List [Atom "define-fun"; Atom n; List []; _; expr] ->
     Fun (smt2_id_to_coq_string env t_i ra rf n,
           smt2_sexpr_to_coq_string env t_i ra rf expr)

  | List [Atom "define-fun"; Atom n; List l; _; expr] ->
     Fun (smt2_id_to_coq_string env t_i ra rf n,
           lambda_to_coq_string l
             (smt2_sexpr_to_coq_string env t_i ra rf expr))

  | List [Atom "declare-sort"; Atom n; _] ->
     Sort

  | l ->
     (* let out = open_out_gen [Open_append] 700 "/tmp/test.log" in
      * let outf = Format.formatter_of_out_channel out in
      * SExpr.print outf l; pp_print_flush outf ();
      * close_out out; *)
     Structures.error ("Could not reconstruct model")


let model env rt ro ra rf = function
  | List (Atom "model" :: l) ->
     List.fold_left (fun acc m -> match model_item env rt ro ra rf m with Fun m -> m::acc | Sort -> acc) [] l
     |> List.sort (fun ((_ ,i1), _) ((_, i2), _) -> i2 - i1)
  | _ -> Structures.error ("No model")


let model_string env rt ro ra rf s =
  String.concat "\n"
    (List.map (fun ((x, _) ,v) -> Format.sprintf "%s := %s" x v)
       (model env rt ro ra rf s))

open Entries
open Declare
open Decl_kinds

open SmtMisc
open CoqTerms
open SmtForm
open SmtAtom
open SmtTrace
open SmtCertif


let euf_checker_modules = [ ["SMTCoq";"Trace";"Euf_Checker"] ]
let certif_ops = CoqTerms.make_certif_ops euf_checker_modules
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


(* Given an SMT-LIB2 file and a certif, build the corresponding objects *)

let compute_roots roots last_root =
  let r = ref last_root in
  while (has_prev !r) do
    r := prev !r
  done;

  let rec find_root i root = function
    | [] -> assert false
    | t::q -> if Form.equal t root then (i,q) else find_root (i+1) root q in

  let rec used_roots acc i roots r =
    if isRoot r.kind then
      match r.value with
        | Some [root] ->
           let (j,roots') = find_root i root roots in
           used_roots (j::acc) (j+1) roots' (next r)
        | _ -> assert false
    else
      acc in

  used_roots [] 0 roots !r


let parse_certif t_i t_func t_atom t_form root used_root trace (rt, ro, ra, rf, roots, max_id, confl) =
  let (tres, last_root) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let ce4 = Structures.mkConst certif in
  let _ = declare_constant trace (DefinitionEntry ce4, IsDefinition Definition) in
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
  let ce3 = Structures.mkConst roots in
  let _ = declare_constant root (DefinitionEntry ce3, IsDefinition Definition) in
  let ce3' = Structures.mkConst used_roots in
  let _ = declare_constant used_root (DefinitionEntry ce3', IsDefinition Definition) in
  let t_i' = make_t_i rt in
  let t_func' = make_t_func ro t_i' in
  let ce5 = Structures.mkConst t_i' in
  let _ = declare_constant t_i (DefinitionEntry ce5, IsDefinition Definition) in
  let ce6 = Structures.mkConst t_func' in
  let _ = declare_constant t_func (DefinitionEntry ce6, IsDefinition Definition) in
  let ce1 = Structures.mkConst (Atom.interp_tbl ra) in
  let _ = declare_constant t_atom (DefinitionEntry ce1, IsDefinition Definition) in
  let ce2 = Structures.mkConst (snd (Form.interp_tbl rf)) in
  let _ = declare_constant t_form (DefinitionEntry ce2, IsDefinition Definition) in
  ()


(* Given an SMT-LIB2 file and a certif, build the corresponding theorem *)

let interp_roots roots =
  let interp = Form.interp_to_coq (Atom.interp_to_coq (Hashtbl.create 17)) (Hashtbl.create 17) in
  match roots with
    | [] -> Lazy.force ctrue
    | f::roots -> List.fold_left (fun acc f -> mklApp candb [|acc; interp f|]) (interp f) roots

let build_certif (rt, ro, ra, rf, roots, max_id, confl) =
  let (tres,last_root) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
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

  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let t_i = make_t_i rt in
  let t_func = make_t_func ro t_i in

  (rootsCstr, used_rootsCstr, certif, t_atom, t_form, t_i, t_func)

let theorem name ((rt, ro, ra, rf, roots, max_id, confl) as p) =
  let (rootsCstr, used_rootsCstr, certif, t_atom, t_form, t_i, t_func) = build_certif p in

  let theorem_concl = mklApp cnot [|mklApp cis_true [|interp_roots roots|]|] in
  let theorem_proof =
   Term.mkLetIn (mkName "used_roots", used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|], (*7*)
   Term.mkLetIn (mkName "t_atom", t_atom, mklApp carray [|Lazy.force catom|], (*6*)
   Term.mkLetIn (mkName "t_form", t_form, mklApp carray [|Lazy.force cform|], (*5*)
   Term.mkLetIn (mkName "d", rootsCstr, mklApp carray [|Lazy.force cint|], (*4*)
   Term.mkLetIn (mkName "c", certif, Lazy.force ccertif, (*3*)
   Term.mkLetIn (mkName "t_i", t_i, mklApp carray [|Lazy.force ctyp_eqb|], (*2*)
   Term.mkLetIn (mkName "t_func", t_func, mklApp carray [|mklApp ctval [|t_i|]|], (*1*)
   mklApp cchecker_correct
     [|Term.mkRel 2; Term.mkRel 1; Term.mkRel 6; Term.mkRel 5; Term.mkRel 4; Term.mkRel 7; Term.mkRel 3;
	vm_cast_true
	  (mklApp cchecker [|Term.mkRel 2; Term.mkRel 1; Term.mkRel 6; Term.mkRel 5; Term.mkRel 4; Term.mkRel 7; Term.mkRel 3|])|]))))))) in
  let ce = Structures.mkConst theorem_proof in
  let _ = declare_constant name (DefinitionEntry ce, IsDefinition Definition) in
  ()


(* Given an SMT-LIB2 file and a certif, call the checker *)

let checker ((rt, ro, ra, rf, roots, max_id, confl) as p) =
  let (rootsCstr, used_rootsCstr, certif, t_atom, t_form, t_i, t_func) = build_certif p in

  let tm = mklApp cchecker [|t_i; t_func; t_atom; t_form; rootsCstr; used_rootsCstr; certif|] in

  let res = Vnorm.cbv_vm (Global.env ()) tm (Lazy.force CoqTerms.cbool) in
  Format.eprintf "     = %s\n     : bool@."
    (if Term.eq_constr res (Lazy.force CoqTerms.ctrue) then
        "true" else "false")


(* Tactic *)

let build_body rt ro ra rf l b (max_id, confl) =
  let (tres,_) = SmtTrace.to_coq Form.to_coq certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let t_i = make_t_i rt in
  let t_func = make_t_func ro t_i in

  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in

  let vtatom = Term.mkRel 5 in
  let vtform = Term.mkRel 4 in
  let vc = Term.mkRel 3 in
  let vti = Term.mkRel 2 in
  let vtfunc = Term.mkRel 1 in

  Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
  Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
  Term.mkLetIn (nc, certif, Lazy.force ccertif,
  Term.mkLetIn (nti, Structures.lift 3 t_i, mklApp carray [|Lazy.force ctyp_eqb|],
  Term.mkLetIn (ntfunc, Structures.lift 4 t_func, mklApp carray [|mklApp ctval [|t_i|]|],
  mklApp cchecker_b_correct
	 [|vti;vtfunc;vtatom; vtform; l; b; vc;
	   vm_cast_true (mklApp cchecker_b [|vti;vtfunc;vtatom;vtform;l;b;vc|])|])))))


let build_body_eq rt ro ra rf l1 l2 l (max_id, confl) =
  let (tres,_) = SmtTrace.to_coq Form.to_coq certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let t_i = make_t_i rt in
  let t_func = make_t_func ro t_i in

  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in

  let vtatom = Term.mkRel 5 in
  let vtform = Term.mkRel 4 in
  let vc = Term.mkRel 3 in
  let vti = Term.mkRel 2 in
  let vtfunc = Term.mkRel 1 in

  Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
  Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
  Term.mkLetIn (nc, certif, Lazy.force ccertif,
  Term.mkLetIn (nti, Structures.lift 3 t_i, mklApp carray [|Lazy.force ctyp_eqb|],
  Term.mkLetIn (ntfunc, Structures.lift 4 t_func, mklApp carray [|mklApp ctval [|t_i|]|],
  mklApp cchecker_eq_correct
	 [|vti;vtfunc;vtatom; vtform; l1; l2; l; vc;
	   vm_cast_true (mklApp cchecker_eq [|vti;vtfunc;vtatom;vtform;l1;l2;l;vc|])|])))))


let get_arguments concl =
  let f, args = Term.decompose_app concl in
  match args with
  | [ty;a;b] when (Term.eq_constr f (Lazy.force ceq)) && (Term.eq_constr ty (Lazy.force cbool)) -> a, b
  | [a] when (Term.eq_constr f (Lazy.force cis_true)) -> a, Lazy.force ctrue
  | _ -> failwith ("Verit.tactic: can only deal with equality over bool")


let make_proof call_solver rt ro rf l =
  let fl = Form.flatten rf l in
  let root = SmtTrace.mkRootV [l] in
  call_solver rt ro fl (root,l)


let tactic call_solver rt ro ra rf env sigma t =
  let (forall_let, concl) = Term.decompose_prod_assum t in
  let env = Environ.push_rel_context forall_let env in
  let a, b = get_arguments concl in
  let body =
    if ((Term.eq_constr b (Lazy.force ctrue)) || (Term.eq_constr b (Lazy.force cfalse))) then
      let l = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l' = if (Term.eq_constr b (Lazy.force ctrue)) then Form.neg l else l in
      let max_id_confl = make_proof call_solver rt ro rf l' in
      build_body rt ro ra rf (Form.to_coq l) b max_id_confl
    else
      let l1 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l2 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf b in
      let l = Form.neg (Form.get rf (Fapp(Fiff,[|l1;l2|]))) in
      let max_id_confl = make_proof call_solver rt ro rf l in
      build_body_eq rt ro ra rf (Form.to_coq l1) (Form.to_coq l2) (Form.to_coq l) max_id_confl in
  let compose_lam_assum forall_let body =
    List.fold_left (fun t rd -> Term.mkLambda_or_LetIn rd t) body forall_let in
  let res = compose_lam_assum forall_let body in
  let cuts = Btype.get_cuts rt in
  List.fold_right (fun (eqn, eqt) tac ->
    Structures.tclTHENLAST (Structures.assert_before (Names.Name eqn) eqt) tac
  ) cuts (Structures.vm_cast_no_check res)

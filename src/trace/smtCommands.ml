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
open Declare
open Decl_kinds

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
let cZeqbsym = gen_constant z_modules "eqb_sym"

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


let interp_uf ta tf c =
  let rec interp = function
    | [] -> Lazy.force cfalse
    | [l] -> Form.interp_to_coq (Atom.interp_to_coq ta) tf l
    | l::c -> mklApp corb [|Form.interp_to_coq (Atom.interp_to_coq ta) tf l; interp c|] in
  interp c

let interp_conseq_uf (prem, concl) =
  let ta = Hashtbl.create 17 in
  let tf = Hashtbl.create 17 in
  let rec interp = function
    | [] -> mklApp cis_true [|interp_uf ta tf concl|]
    | c::prem -> Term.mkArrow (mklApp cis_true [|interp_uf ta tf c|]) (interp prem) in
  interp prem


let print_assm ty =
  let rec fix rf x = rf (fix rf) x in
  let pr = fix Ppconstr.modular_constr_pr Pp.mt Structures.ppconstr_lsimpleconstr in
  Printf.printf "WARNING: assuming the following hypothesis:\n%s\n\n" (Pp.string_of_ppcmds (pr (Structures.constrextern_extern_constr ty)));
  flush stdout


let parse_certif t_i t_func t_atom t_form root used_root trace (rt, ro, ra, rf, roots, max_id, confl) =

  let t_i' = make_t_i rt in
  let ce5 = Structures.mkUConst t_i' in
  let ct_i = Term.mkConst (declare_constant t_i (DefinitionEntry ce5, IsDefinition Definition)) in

  let t_func' = make_t_func ro ct_i in
  let ce6 = Structures.mkUConst t_func' in
  let ct_func = Term.mkConst (declare_constant t_func (DefinitionEntry ce6, IsDefinition Definition)) in

  let t_atom' = Atom.interp_tbl ra in
  let ce1 = Structures.mkUConst t_atom' in
  let ct_atom = Term.mkConst (declare_constant t_atom (DefinitionEntry ce1, IsDefinition Definition)) in

  let t_form' = snd (Form.interp_tbl rf) in
  let ce2 = Structures.mkUConst t_form' in
  let ct_form = Term.mkConst (declare_constant t_form (DefinitionEntry ce2, IsDefinition Definition)) in

  (* EMPTY LEMMA LIST *)
  let (tres, last_root, cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) interp_conseq_uf (certif_ops (Some [|ct_i; ct_func; ct_atom; ct_form|])) confl None in
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
  let _ = declare_constant root (DefinitionEntry ce3, IsDefinition Definition) in
  let ce3' = Structures.mkUConst used_roots in
  let _ = declare_constant used_root (DefinitionEntry ce3', IsDefinition Definition) in

  let certif =
    mklApp cCertif [|ct_i; ct_func; ct_atom; ct_form; mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let ce4 = Structures.mkUConst certif in
  let _ = declare_constant trace (DefinitionEntry ce4, IsDefinition Definition) in

  ()


(* Given an SMT-LIB2 file and a certif, build the corresponding theorem *)

let interp_roots roots =
  let interp = Form.interp_to_coq (Atom.interp_to_coq (Hashtbl.create 17)) (Hashtbl.create 17) in
  match roots with
    | [] -> Lazy.force ctrue
    | f::roots -> List.fold_left (fun acc f -> mklApp candb [|acc; interp f|]) (interp f) roots

let theorem name (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let nused_roots = mkName "used_roots" in
  let nd = mkName "d" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  (* EMPTY LEMMA LIST *)
  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) interp_conseq_uf (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *)|])) confl None in
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

  let theorem_concl = mklApp cis_true [|mklApp cnegb [|interp_roots roots|]|] in
  let theorem_proof_cast =
    Term.mkCast (
        Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
        Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
        Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
        Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
        Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
        Term.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
        Term.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
        mklApp cchecker_correct
               [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*);
	         vm_cast_true
	           (mklApp cchecker [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|])|]))))))),
        Term.VMcast,
        theorem_concl)
  in
  let theorem_proof_nocast =
        Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
        Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
        Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
        Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
        Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
        Term.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
        Term.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
        mklApp cchecker_correct
               [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|])))))))
  in

  let ce = Structures.mkTConst theorem_proof_cast theorem_proof_nocast theorem_concl in
  let _ = declare_constant name (DefinitionEntry ce, IsDefinition Definition) in
  ()


(* Given an SMT-LIB2 file and a certif, call the checker *)

let checker (rt, ro, ra, rf, roots, max_id, confl) =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let nused_roots = mkName "used_roots" in
  let nd = mkName "d" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = make_t_func ro (v 1 (*t_i*)) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in

  (* EMPTY LEMMA LIST *)
  let (tres,last_root,cuts) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) interp_conseq_uf (certif_ops (Some [|v 4(*t_i*); v 3(*t_func*); v 2(*t_atom*); v 1(* t_form *)|])) confl None in
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
   Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
   Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1(* t_i *)|]|],
   Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
   Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
   Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
   Term.mkLetIn (nused_roots, used_rootsCstr, mklApp coption [|mklApp carray [|Lazy.force cint|]|],
   Term.mkLetIn (nd, rootsCstr, mklApp carray [|Lazy.force cint|],
   mklApp cchecker [|v 7 (*t_i*); v 6 (*t_func*); v 5 (*t_atom*); v 4 (*t_form*); v 1 (*d*); v 2 (*used_roots*); v 3 (*c*)|]))))))) in

  let res = Vnorm.cbv_vm (Global.env ()) tm (Lazy.force CoqTerms.cbool) in
  Format.eprintf "     = %s\n     : bool@."
    (if Term.eq_constr res (Lazy.force CoqTerms.ctrue) then
        "true" else "false")


(* Tactic *)

let build_body rt ro ra rf l b (max_id, confl) find =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = Structures.lift 1 (make_t_func ro (v 0 (*t_i - 1*))) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let (tres,_,cuts) = SmtTrace.to_coq Form.to_coq interp_conseq_uf (certif_ops (Some [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|])) confl find in
  let certif =
    mklApp cCertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let proof_cast =
    Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
    Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1 (*t_i*)|]|],
    Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    mklApp cchecker_b_correct
      [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l; b; v 1 (*certif*);
	vm_cast_true (mklApp cchecker_b [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l; b; v 1 (*certif*)|])|])))))
  in
  let proof_nocast =
    Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
    Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1 (*t_i*)|]|],
    Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    mklApp cchecker_b_correct
      [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l; b; v 1 (*certif*)|])))))
  in

  (proof_cast, proof_nocast, cuts)


let build_body_eq rt ro ra rf l1 l2 l (max_id, confl) find =
  let nti = mkName "t_i" in
  let ntfunc = mkName "t_func" in
  let ntatom = mkName "t_atom" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in

  let v = Term.mkRel in

  let t_i = make_t_i rt in
  let t_func = Structures.lift 1 (make_t_func ro (v 0 (*t_i*))) in
  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let (tres,_,cuts) = SmtTrace.to_coq Form.to_coq interp_conseq_uf (certif_ops (Some [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|])) confl find in
  let certif =
    mklApp cCertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*); mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in

  let proof_cast =
    Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
    Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1 (*t_i*)|]|],
    Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    mklApp cchecker_eq_correct
      [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l1; l2; l; v 1 (*certif*);
	vm_cast_true (mklApp cchecker_eq [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l1; l2; l; v 1 (*certif*)|])|])))))
  in
  let proof_nocast =
    Term.mkLetIn (nti, t_i, mklApp carray [|Lazy.force ctyp_eqb|],
    Term.mkLetIn (ntfunc, t_func, mklApp carray [|mklApp ctval [|v 1 (*t_i*)|]|],
    Term.mkLetIn (ntatom, t_atom, mklApp carray [|Lazy.force catom|],
    Term.mkLetIn (ntform, t_form, mklApp carray [|Lazy.force cform|],
    Term.mkLetIn (nc, certif, mklApp ccertif [|v 4 (*t_i*); v 3 (*t_func*); v 2 (*t_atom*); v 1 (*t_form*)|],
    mklApp cchecker_eq_correct
      [|v 5 (*t_i*);v 4 (*t_func*);v 3 (*t_atom*); v 2 (*t_form*); l1; l2; l; v 1 (*certif*)|])))))
  in

  (proof_cast, proof_nocast, cuts)


let get_arguments concl =
  let f, args = Term.decompose_app concl in
  match args with
  | [ty;a;b] when (Term.eq_constr f (Lazy.force ceq)) && (Term.eq_constr ty (Lazy.force cbool)) -> a, b
  | [a] when (Term.eq_constr f (Lazy.force cis_true)) -> a, Lazy.force ctrue
  | _ -> failwith ("Verit.tactic: can only deal with equality over bool")


let make_proof call_solver rt ro rf ra' rf' l' ls_smtc=
  let fl' = Form.flatten rf' l' in
  let root = SmtTrace.mkRootV [l'] in
  call_solver rt ro ra' rf' (Some (root, l')) (fl'::ls_smtc)

(* <of_coq_lemma> reifies the coq lemma given, we can then easily print it in a
 .smt2 file. We need the reify tables to correctly recognize unbound variables
 of the lemma. We also need to make sure to leave unchanged the tables because
 the new objects may contain bound (by forall of the lemma) variables. *)
exception Axiom_form_unsupported
              
let of_coq_lemma rt ro ra' rf' env sigma clemma =
  let rel_context, qf_lemma = Term.decompose_prod_assum clemma in
  let env_lemma = List.fold_right Environ.push_rel rel_context env in
  let forall_args =
    let fmap r = let n, t = Structures.destruct_rel_decl r in
                 string_of_name n, SmtBtype.of_coq rt t in
    List.map fmap rel_context in
  let f, args = Term.decompose_app qf_lemma in
  let core_f =
    if Term.eq_constr f (Lazy.force cis_true) then
      match args with
      | [a] -> a
      | _ -> raise Axiom_form_unsupported
    else if Term.eq_constr f (Lazy.force ceq) then
      match args with
      | [ty; arg1; arg2] when Term.eq_constr ty (Lazy.force cbool) &&
                                Term.eq_constr arg2 (Lazy.force ctrue) ->
         arg1
      | _ -> raise Axiom_form_unsupported
    else raise Axiom_form_unsupported in
  let core_smt = Form.of_coq (Atom.of_coq ~hash:true rt ro ra' env_lemma sigma)
                   rf' core_f in
  match forall_args with
    [] -> core_smt
  | _ -> Form.get rf' (Fapp (Fforall forall_args, [|core_smt|]))

let core_tactic call_solver rt ro ra rf ra' rf' lcpl lcepl env sigma concl =
  let a, b = get_arguments concl in
  let tlcepl = List.map (Structures.interp_constr env sigma) lcepl in
  let lcpl = lcpl @ tlcepl in
  let lcl = List.map (Retyping.get_type_of env sigma) lcpl in

  let lsmt  = List.map (of_coq_lemma rt ro ra' rf' env sigma) lcl in
  let l_pl_ls = List.combine (List.combine lcl lcpl) lsmt in

  let lem_tbl : (int, Term.constr * Term.constr) Hashtbl.t =
    Hashtbl.create 100 in
  let new_ref ((l, pl), ls) =
    Hashtbl.add lem_tbl (Form.index ls) (l, pl) in

  List.iter new_ref l_pl_ls;
  
  let find_lemma cl =
    let re_hash hf = Form.hash_hform (Atom.hash_hatom ra') rf' hf in
    match cl.value with
    | Some [l] ->
       let hl = re_hash l in
       begin try Hashtbl.find lem_tbl (Form.index hl)
             with Not_found ->
               let oc = open_out "/tmp/find_lemma.log" in
               List.iter (fun u -> Printf.fprintf oc "%s\n"
                                     (VeritSyntax.string_hform u)) lsmt;
               Printf.fprintf oc "\n%s\n" (VeritSyntax.string_hform hl);
               flush oc; close_out oc; failwith "find_lemma" end
      | _ -> failwith "unexpected form of root" in
  
  let (body_cast, body_nocast, cuts) =
    if ((Term.eq_constr b (Lazy.force ctrue)) || (Term.eq_constr b (Lazy.force cfalse))) then
      let l = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l' = Form.of_coq (Atom.of_coq ~hash:true rt ro ra' env sigma) rf' a in
      let l' = if (Term.eq_constr b (Lazy.force ctrue)) then Form.neg l' else l' in
      let max_id_confl = make_proof call_solver rt ro rf ra' rf' l' lsmt in
      build_body rt ro ra rf (Form.to_coq l) b max_id_confl (Some find_lemma)
    else
      let l1 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l2 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf b in
      let l = Form.neg (Form.get rf (Fapp(Fiff,[|l1;l2|]))) in
      let l1' = Form.of_coq (Atom.of_coq ~hash:true rt ro ra' env sigma) rf' a in
      let l2' = Form.of_coq (Atom.of_coq ~hash:true rt ro ra' env sigma) rf' b in
      let l' = Form.neg (Form.get rf' (Fapp(Fiff,[|l1';l2'|]))) in
      let max_id_confl = make_proof call_solver rt ro rf ra' rf' l' lsmt in
      build_body_eq rt ro ra rf (Form.to_coq l1) (Form.to_coq l2) (Form.to_coq l) max_id_confl (Some find_lemma) in

  let cuts = SmtBtype.get_cuts rt @ cuts in

  List.fold_right (fun (eqn, eqt) tac ->
      Structures.tclTHENLAST (Structures.assert_before (Names.Name eqn) eqt) tac)
    cuts
    (Structures.tclTHEN
       (Structures.set_evars_tac body_nocast)
       (Structures.vm_cast_no_check body_cast))

let tactic call_solver rt ro ra rf ra' rf' lcpl lcepl =
  Structures.tclTHEN
    Tactics.intros
    (Structures.mk_tactic (core_tactic call_solver rt ro ra rf ra' rf' lcpl lcepl))

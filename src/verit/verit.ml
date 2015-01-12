(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
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
open SmtCertif
open SmtTrace
open SmtAtom


let debug = false


(* Interpretation tables *)

let mk_ftype cod dom =
  let typeb = Lazy.force ctype in
  let typea = mklApp clist [|typeb|] in
  let a = Array.fold_right (fun bt acc -> mklApp ccons [|typeb; Btype.to_coq bt; acc|]) cod (mklApp cnil [|typeb|]) in
  let b = Btype.to_coq dom in
  mklApp cpair [|typea;typeb;a;b|]

let make_t_i rt = Btype.interp_tbl rt
let make_t_func ro t_i = Op.interp_tbl (mklApp ctval [|t_i|]) (fun cod dom value -> mklApp cTval [|t_i; mk_ftype cod dom; value|]) ro


(******************************************************************************)
(** Given a SMT-LIB2 file and a verit trace build                      *)
(*  the corresponding object                                                  *)
(******************************************************************************)


let import_smtlib2 rt ro ra rf filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let commands = Smtlib2_parse.main Smtlib2_lex.token lexbuf in
  close_in chan;
  match commands with
    | None -> []
    | Some (Smtlib2_ast.Commands (_,(_,res))) ->
      List.rev (List.fold_left (Smtlib2_genConstr.declare_commands rt ro ra rf) [] res)


let import_trace filename first =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let confl_num = ref (-1) in
  let first_num = ref (-1) in
  let is_first = ref true in
  let line = ref 1 in
  (* let _ = Parsing.set_trace true in *)
  try
    while true do
      confl_num := VeritParser.line VeritLexer.token lexbuf;
      if !is_first then (
        is_first := false;
        first_num := !confl_num
      );
      incr line
    done;
    raise VeritLexer.Eof
  with
    | VeritLexer.Eof ->
      close_in chan;
      let first =
        let aux = VeritSyntax.get_clause !first_num in
        match first, aux.value with
          | Some (root,l), Some (fl::nil) ->
            if Form.equal l fl then
              aux
            else (
              aux.kind <- Other (ImmFlatten(root,fl));
              SmtTrace.link root aux;
              root
            )
          | _,_ -> aux in
      let confl = VeritSyntax.get_clause !confl_num in
      SmtTrace.select confl;
      (* Trace.share_prefix first (2 * last.id); *)
      occur confl;
      (alloc first, confl)
    | Parsing.Parse_error -> failwith ("Verit.import_trace: parsing error line "^(string_of_int !line))


let euf_checker_modules = [ ["SMTCoq";"Trace";"Euf_Checker"] ]

let certif_ops = CoqTerms.make_certif_ops euf_checker_modules
let cCertif = gen_constant euf_checker_modules "Certif"


let clear_all () =
  SmtTrace.clear ();
  VeritSyntax.clear ()


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


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace fproof None in
  let (tres, last_root) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) certif_ops confl in
  let certif =
   mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let ce4 =
    { const_entry_body = certif;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant trace (DefinitionEntry ce4, IsDefinition Definition) in
  let used_roots = compute_roots roots last_root in
  let roots =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Term.mkArray (Lazy.force cint, res) in
  let used_roots =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Term.mkArray (Lazy.force cint, res)|] in
  let ce3 =
    { const_entry_body = roots;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant root (DefinitionEntry ce3, IsDefinition Definition) in
  let ce3' =
    { const_entry_body = used_roots;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant used_root (DefinitionEntry ce3', IsDefinition Definition) in
  let t_i' = make_t_i rt in
  let t_func' = make_t_func ro t_i' in
  let ce5 =
    { const_entry_body = t_i';
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant t_i (DefinitionEntry ce5, IsDefinition Definition) in
  let ce6 =
    { const_entry_body = t_func';
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant t_func (DefinitionEntry ce6, IsDefinition Definition) in
  let ce1 =
    { const_entry_body = Atom.interp_tbl ra;
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant t_atom (DefinitionEntry ce1, IsDefinition Definition) in
  let ce2 =
    { const_entry_body = snd (Form.interp_tbl rf);
      const_entry_type = None;
      const_entry_secctx = None;
      const_entry_opaque = false;
      const_entry_inline_code = false} in
  let _ = declare_constant t_form (DefinitionEntry ce2, IsDefinition Definition) in
  ()


let ccertif = gen_constant euf_checker_modules "certif"
let cchecker = gen_constant euf_checker_modules "checker"
let cchecker_correct = gen_constant euf_checker_modules "checker_correct"

let interp_roots roots =
  let interp = Form.interp_to_coq (Atom.interp_to_coq (Hashtbl.create 17)) (Hashtbl.create 17) in
  match roots with
    | [] -> Lazy.force ctrue
    | f::roots -> List.fold_left (fun acc f -> mklApp candb [|acc; interp f|]) (interp f) roots

let theorem name fsmt fproof =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace fproof None in
  let (tres,last_root) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let used_roots = compute_roots roots last_root in
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Term.mkArray (Lazy.force cint, res)|] in
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Term.mkArray (Lazy.force cint, res) in

  let t_atom = Atom.interp_tbl ra in
  let t_form = snd (Form.interp_tbl rf) in
  let t_i = make_t_i rt in
  let t_func = make_t_func ro t_i in

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
  let ce =
    { const_entry_body = theorem_proof;
      const_entry_type = Some theorem_concl;
      const_entry_secctx = None;
      const_entry_opaque = true;
      const_entry_inline_code = false} in
  let _ = declare_constant name (DefinitionEntry ce, IsDefinition Definition) in
    ()


let checker fsmt fproof =
  let t1 = Unix.time () in  (* for debug *)
  clear_all ();
  let t2 = Unix.time () in  (* for debug *)
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let t3 = Unix.time () in  (* for debug *)
  let roots = import_smtlib2 rt ro ra rf fsmt in
  let t4 = Unix.time () in  (* for debug *)
  let (max_id, confl) = import_trace fproof None in
  let t5 = Unix.time () in  (* for debug *)
  let (tres,last_root) = SmtTrace.to_coq (fun i -> mkInt (Form.to_lit i)) certif_ops confl in
  let t6 = Unix.time () in  (* for debug *)
  let certif =
    mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in
  let t7 = Unix.time () in  (* for debug *)
  let used_roots = compute_roots roots last_root in
  let t8 = Unix.time () in  (* for debug *)
  let used_rootsCstr =
    let l = List.length used_roots in
    let res = Array.make (l + 1) (mkInt 0) in
    let i = ref (l-1) in
    List.iter (fun j -> res.(!i) <- mkInt j; decr i) used_roots;
    mklApp cSome [|mklApp carray [|Lazy.force cint|]; Term.mkArray (Lazy.force cint, res)|] in
  let t9 = Unix.time () in  (* for debug *)
  let rootsCstr =
    let res = Array.make (List.length roots + 1) (mkInt 0) in
    let i = ref 0 in
    List.iter (fun j -> res.(!i) <- mkInt (Form.to_lit j); incr i) roots;
    Term.mkArray (Lazy.force cint, res) in
  let t10 = Unix.time () in  (* for debug *)

  let t_i = make_t_i rt in
  let t11 = Unix.time () in  (* for debug *)
  let t_func = make_t_func ro t_i in
  let t12 = Unix.time () in  (* for debug *)
  let t_atom = Atom.interp_tbl ra in
  let t13 = Unix.time () in  (* for debug *)
  let t_form = snd (Form.interp_tbl rf) in
  let t14 = Unix.time () in  (* for debug *)

  let tm = mklApp cchecker [|t_i; t_func; t_atom; t_form; rootsCstr; used_rootsCstr; certif|] in
  let t15 = Unix.time () in  (* for debug *)

  let res = Vnorm.cbv_vm (Global.env ()) tm (Lazy.force CoqTerms.cbool) in
  let t16 = Unix.time () in  (* for debug *)
  Format.eprintf "     = %s\n     : bool@."
    (if Term.eq_constr res (Lazy.force CoqTerms.ctrue) then
        "true" else "false");
  let t17 = Unix.time () in  (* for debug *)

  (* let expr = Constrextern.extern_constr true Environ.empty_env tm in *)
  (* let t16 = Unix.time () in  (\* for debug *\) *)
  (* let res_aux1 = Glob_term.CbvVm None in *)
  (* let t17 = Unix.time () in  (\* for debug *\) *)
  (* let res_aux2 = Vernacexpr.VernacCheckMayEval(Some res_aux1, None, expr) in *)
  (* let t18 = Unix.time () in  (\* for debug *\) *)
  (* Vernacentries.interp res_aux2; *)
  (* let t19 = Unix.time () in  (\* for debug *\) *)

  if debug then (
    Printf.printf"Clear: %f
Create hashtables: %f
Import SMT-LIB: %f
Import trace: %f
Compute trace: %f
Build certif: %f
Build roots: %f
Compute used roots: %f
Build used roots: %f
Build  t_i: %f
Build t_func: %f
Build t_atom: %f
Build t_form: %f
Build checker call: %f
Compute checker call: %f
Print result: %f\n" (t2-.t1) (t3-.t2) (t4-.t3) (t5-.t4) (t6-.t5) (t7-.t6) (t8-.t7) (t9-.t8) (t10-.t9) (t11-.t10) (t12-.t11) (t13-.t12) (t14-.t13) (t15-.t14) (t16-.t15) (t17-.t16);
(*     Printf.printf"Clear: %f *)
(* Create hashtables: %f *)
(* Import SMT-LIB: %f *)
(* Import trace: %f *)
(* Compute trace: %f *)
(* Build certif: %f *)
(* Build roots: %f *)
(* Compute used roots: %f *)
(* Build used roots: %f *)
(* Build  t_i: %f *)
(* Build t_func: %f *)
(* Build t_atom: %f *)
(* Build t_form: %f *)
(* Build checker call: %f *)
(* Build constr: %f *)
(* Build conclusion1: %f *)
(* Build conclusion2: %f *)
(* Build conclusion: %f\n" (t2-.t1) (t3-.t2) (t4-.t3) (t5-.t4) (t6-.t5) (t7-.t6) (t8-.t7) (t9-.t8) (t10-.t9) (t11-.t10) (t12-.t11) (t13-.t12) (t14-.t13) (t15-.t14) (t16-.t15) (t17-.t16) (t18-.t17) (t19-.t18); *)
    flush stdout)


(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

let export out_channel rt ro l =
  let fmt = Format.formatter_of_out_channel out_channel in
  Format.fprintf fmt "(set-logic QF_UFLIA)@.";

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    VeritSyntax.add_btype s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (Btype.to_list rt);

  List.iter (fun (i,cod,dom,op) ->
    let s = "op_"^(string_of_int i) in
    VeritSyntax.add_fun s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t -> if !is_first then is_first := false else Format.fprintf fmt " "; Btype.to_smt fmt t) cod;
    Format.fprintf fmt ") ";
    Btype.to_smt fmt dom;
    Format.fprintf fmt ")@."
  ) (Op.to_list ro);

  Format.fprintf fmt "(assert ";
  Form.to_smt Atom.to_smt fmt l;
  Format.fprintf fmt ")@\n(check-sat)@\n(exit)@."


let call_verit rt ro fl root =
  let (filename, outchan) = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan rt ro fl;
  close_out outchan;
  let logfilename = (Filename.chop_extension filename)^".vtlog" in

  let command = "veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof="^logfilename^" "^filename in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Verit = %.5f@." (t1-.t0);
  if exit_code <> 0 then
    failwith ("Verit.call_verit: command "^command^
	      " exited with code "^(string_of_int exit_code));
  try
    import_trace logfilename (Some root)
  with
    | VeritSyntax.Sat -> Errors.error "veriT can't prove this"


let cchecker_b_correct =
  gen_constant euf_checker_modules "checker_b_correct"
let cchecker_b = gen_constant euf_checker_modules "checker_b"
let cchecker_eq_correct =
  gen_constant euf_checker_modules "checker_eq_correct"
let cchecker_eq = gen_constant euf_checker_modules "checker_eq"


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
  Term.mkLetIn (nti, Term.lift 3 t_i, mklApp carray [|Lazy.force ctyp_eqb|],
  Term.mkLetIn (ntfunc, Term.lift 4 t_func, mklApp carray [|mklApp ctval [|t_i|]|],
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
  Term.mkLetIn (nti, Term.lift 3 t_i, mklApp carray [|Lazy.force ctyp_eqb|],
  Term.mkLetIn (ntfunc, Term.lift 4 t_func, mklApp carray [|mklApp ctval [|t_i|]|],
  mklApp cchecker_eq_correct
	 [|vti;vtfunc;vtatom; vtform; l1; l2; l; vc;
	   vm_cast_true (mklApp cchecker_eq [|vti;vtfunc;vtatom;vtform;l1;l2;l;vc|])|])))))


let get_arguments concl =
  let f, args = Term.decompose_app concl in
  match args with
  | [ty;a;b] when f = Lazy.force ceq && ty = Lazy.force cbool -> a, b
  | [a] when f = Lazy.force cis_true -> a, Lazy.force ctrue
  | _ -> failwith ("Verit.tactic: can only deal with equality over bool")


let make_proof rt ro rf l =
  let fl = Form.flatten rf l in
  let root = SmtTrace.mkRootV [l] in
  call_verit rt ro fl (root,l)


let tactic gl =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in

  let env = Tacmach.pf_env gl in
  let sigma = Tacmach.project gl in
  let t = Tacmach.pf_concl gl in

  let (forall_let, concl) = Term.decompose_prod_assum t in
  let env = Environ.push_rel_context forall_let env in
  let a, b = get_arguments concl in
  let body =
    if (b = Lazy.force ctrue || b = Lazy.force cfalse) then
      let l = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l' = if b = Lazy.force ctrue then Form.neg l else l in
      let max_id_confl = make_proof rt ro rf l' in
      build_body rt ro ra rf (Form.to_coq l) b max_id_confl
    else
      let l1 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf a in
      let l2 = Form.of_coq (Atom.of_coq rt ro ra env sigma) rf b in
      let l = Form.neg (Form.get rf (Fapp(Fiff,[|l1;l2|]))) in
      let max_id_confl = make_proof rt ro rf l in
      build_body_eq rt ro ra rf (Form.to_coq l1) (Form.to_coq l2) (Form.to_coq l) max_id_confl in
  let compose_lam_assum forall_let body =
    List.fold_left (fun t rd -> Term.mkLambda_or_LetIn rd t) body forall_let in
  let res = compose_lam_assum forall_let body in
  Tactics.exact_no_check res gl

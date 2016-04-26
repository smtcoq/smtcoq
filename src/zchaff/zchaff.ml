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
open SatAtom
open SmtMisc


(* Detection of trivial clauses *)

let rec is_trivial cl =
  match cl with
  | l :: cl -> 
      let nl = Form.neg l in
      List.exists (fun l' -> Form.equal nl l') cl || is_trivial cl
  | [] -> false


(* Pretty printing *)

let string_of_op = function
  | Ftrue -> "true"
  | Ffalse -> "false"
  | Fand -> "and"
  | For -> "or"
  | Fxor -> "xor"
  | Fimp -> "imp"
  | Fiff -> "iff"
  | Fite -> "ite"
  | Fnot2 i -> "!"^string_of_int i

let rec pp_form fmt l = 
  Format.fprintf fmt "(#%i %a %a)" (Form.to_lit l)pp_sign l pp_pform (Form.pform l)
and pp_sign fmt l = 
  if Form.is_pos l then () 
  else Format.fprintf fmt "-"
and pp_pform fmt p = 
  match p with
  | Fatom x -> Format.fprintf fmt "x%i" x
  | Fapp(op,args) ->
      Format.fprintf fmt "%s" (string_of_op op);
      Array.iter (fun a -> Format.fprintf fmt "%a " pp_form a) args

let pp_value fmt c = 
  match c.value with
  | Some cl ->
      Format.fprintf fmt "VAL = {";
      List.iter (Format.fprintf fmt "%a " pp_form) cl;
      Format.fprintf fmt "}@."
  | _ -> Format.fprintf fmt "Val = empty@."


let pp_kind fmt c = 
  match c.kind with
  | Root -> Format.fprintf fmt "Root"
  | Res res -> 
      Format.fprintf fmt "(Res %i %i " res.rc1.id res.rc2.id;
      List.iter (fun c -> Format.fprintf fmt "%i " c.id) res.rtail;
      Format.fprintf fmt ") "
  | Other other ->
    begin match other with
    | ImmFlatten (c,l) -> 
	Format.fprintf fmt "(ImmFlatten %i %a)"
	  c.id pp_form l
    | True -> Format.fprintf fmt "True"
    | False -> Format.fprintf fmt "False"
    | BuildDef l -> Format.fprintf fmt "(BuildDef %a)" pp_form l
    | BuildDef2 l -> Format.fprintf fmt "(BuildDef2 %a)" pp_form l
    | BuildProj (l,i) -> Format.fprintf fmt "(BuildProj %a %i)" pp_form l i
    | ImmBuildProj (c,i) ->Format.fprintf fmt "(ImmBuildProj %i %i)" c.id i
    | ImmBuildDef c -> Format.fprintf fmt "(ImmBuildDef %i)" c.id
    | ImmBuildDef2 c -> Format.fprintf fmt "(ImmBuildDef %i)" c.id
    | _ -> assert false
    end
  | Same c -> Format.fprintf fmt "(Same %i)" c.id

let rec pp_trace fmt c = 
  Format.fprintf fmt "%i = %a %a" c.id pp_kind c pp_value c;
  if c.next <> None then pp_trace fmt (next c)


(******************************************************************************)
(** Given a cnf (dimacs) files and a resolve_trace build                      *)
(*  the corresponding object                                                  *) 
(******************************************************************************)


let import_cnf filename = 
  let nvars, first, last = CnfParser.parse_cnf filename in
  let reloc = Hashtbl.create 17 in
  let count = ref 0 in
  let r = ref first in
  while !r.next <> None do
    if not (is_trivial (get_val !r)) then begin
      Hashtbl.add reloc !count !r;
      incr count
    end;
    r := next !r
  done;
  if not (is_trivial (get_val !r)) then Hashtbl.add reloc !count !r;
  nvars,first,last,reloc

let import_cnf_trace reloc filename first last =
  (* Format.fprintf Format.err_formatter "init@."; *)
  (* pp_trace Format.err_formatter first; *)
  let confl = ZchaffParser.parse_proof reloc filename last in
  (* Format.fprintf Format.err_formatter "zchaff@."; *)
  (* pp_trace Format.err_formatter first; *)
  SmtTrace.select confl;
  (* Format.fprintf Format.err_formatter "select@."; *)
  (* pp_trace Format.err_formatter first; *)
  Trace.share_prefix first (2 * last.id);
  (* Format.fprintf Format.err_formatter "share_prefix@."; *)
  (* pp_trace Format.err_formatter first; *)
  occur confl;
  let res = alloc first, confl in
  res

let make_roots first last =
  let cint = Lazy.force cint in
  let roots = Array.make (last.id + 2) (Structures.mkArray (cint, Array.make 1 (mkInt 0))) in
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
    roots.(!r.id) <- Structures.mkArray (cint, croot);
    r := next !r 
  done;
  let root = Array.of_list (get_val !r) in
  let croot = Array.make (Array.length root + 1) (mkInt 0) in
  Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
  roots.(!r.id) <- Structures.mkArray (cint, croot);

  Structures.mkArray (mklApp carray [|cint|], roots)

let interp_roots first last =
  let tbl = Hashtbl.create 17 in
  let mk_elem l = 
    let x = match Form.pform l with
    | Fatom x -> x
    | _ -> assert false in
    let ph = x lsl 1 in
    let h = if Form.is_pos l then ph else ph lxor 1 in
    try Hashtbl.find tbl h 
    with Not_found ->
      let p = Term.mkApp (Term.mkRel 1, [|mkInt (x+1)|]) in
      let np = mklApp cnegb [|p|] in
      Hashtbl.add tbl ph p;
      Hashtbl.add tbl (ph lxor 1) np;
      if Form.is_pos l then p else np in
  let interp_root c =
    match get_val c with
    | [] -> Lazy.force cfalse
    | l :: cl -> 
	List.fold_left (fun acc l -> mklApp corb [|acc; mk_elem l|]) 
	  (mk_elem l) cl in
  let res = ref (interp_root first) in
  if first.id <> last.id then begin
    let r = ref (next first) in
    while !r.id <= last.id do
      res := mklApp candb [|!res;interp_root !r|];
      r := next !r
    done;
  end;
  !res

let sat_checker_modules = [ ["SMTCoq";"Trace";"Sat_Checker"] ]

let certif_ops = CoqTerms.make_certif_ops sat_checker_modules 
let cCertif = gen_constant sat_checker_modules "Certif" 

let parse_certif dimacs trace fdimacs ftrace =
  SmtTrace.clear ();
  let _,first,last,reloc = import_cnf fdimacs in
  let d = make_roots first last in
  let ce1 = Structures.mkConst d in
  let _ = declare_constant dimacs (DefinitionEntry ce1, IsDefinition Definition) in

  let max_id, confl = import_cnf_trace reloc ftrace first last in
  let (tres,_) = SmtTrace.to_coq (fun _ -> assert false) certif_ops confl in
  let certif = 
   mklApp cCertif [|mkInt (max_id + 1); tres;mkInt (get_pos confl)|] in 
  let ce2 = Structures.mkConst certif in
  let _ = declare_constant trace (DefinitionEntry ce2, IsDefinition Definition) in
  ()

let cdimacs = gen_constant sat_checker_modules "dimacs"
let ccertif = gen_constant sat_checker_modules "certif"
let ctheorem_checker = gen_constant sat_checker_modules "theorem_checker"
let cchecker = gen_constant sat_checker_modules "checker"

let theorem name fdimacs ftrace =   
  SmtTrace.clear ();
  let _,first,last,reloc = import_cnf fdimacs in
  let d = make_roots first last in

  let max_id, confl = import_cnf_trace reloc ftrace first last in
  let (tres,_) =
    SmtTrace.to_coq (fun _ -> assert false) certif_ops confl in
  let certif =
   mklApp cCertif [|mkInt (max_id + 1);tres;mkInt (get_pos confl)|] in 

  let theorem_concl = mklApp cnot [|mklApp cis_true [|interp_roots first last|] |] in
  let vtype = Term.mkProd(Names.Anonymous, Lazy.force cint, Lazy.force cbool) in
  let theorem_type = 
    Term.mkProd (mkName "v", vtype, theorem_concl) in
  let theorem_proof =
   Term.mkLetIn (mkName "d", d, Lazy.force cdimacs,
   Term.mkLetIn (mkName "c", certif, Lazy.force ccertif,
   Term.mkLambda (mkName "v", vtype,
   mklApp ctheorem_checker
               [| Term.mkRel 3(*d*); Term.mkRel 2(*c*);
		  vm_cast_true 
		    (mklApp cchecker [|Term.mkRel 3(*d*); Term.mkRel 2(*c*)|]);
                  Term.mkRel 1(*v*)|]))) in
  let ce = Structures.mkConst theorem_proof in
  let _ = declare_constant name (DefinitionEntry ce, IsDefinition Definition) in
  ()


let checker fdimacs ftrace =
  SmtTrace.clear ();
  let _,first,last,reloc = import_cnf fdimacs in
  let d = make_roots first last in

  let max_id, confl = import_cnf_trace reloc ftrace first last in
  let (tres,_) =
    SmtTrace.to_coq (fun _ -> assert false) certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1);tres;mkInt (get_pos confl)|] in

  let tm = mklApp cchecker [|d; certif|] in
  let expr = Structures.extern_constr tm in
  Structures.vernacentries_interp expr




  
(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

let export_clause fmt cl =
  List.iter 
    (fun l -> Format.fprintf fmt "%s%i " 
	(if Form.is_pos l then "" else "-") (Form.index l + 1)) cl;
  Format.fprintf fmt "0@\n"

let export out_channel nvars first =
  let fmt = Format.formatter_of_out_channel out_channel in 
  let reloc = Hashtbl.create 17 in
  let count = ref 0 in
  (* count the number of non trivial clause *)
  let r = ref first in
  let add_count c = 
    match c.value with
    | Some cl -> if not (is_trivial cl) then incr count
    | _ -> () in
  while !r.next <> None do add_count !r; r := next !r done;
  add_count !r;
  Format.fprintf fmt "p cnf %i %i@." nvars !count;
  count := 0; r := first; 
  (* ouput clause *)
  let out c = 
    match c.value with
    | Some cl -> 
	if not (is_trivial cl) then begin
	  Hashtbl.add reloc !count c;
	  incr count;
	  export_clause fmt cl
	end
    | None -> assert false in
  while !r.next <> None do out !r; r := next !r done;
  out !r;
  Format.fprintf fmt "@.";
  reloc, !r


(* Call zchaff *)

let call_zchaff nvars root =
  let (filename, outchan) = Filename.open_temp_file "zchaff_coq" ".cnf" in
  let resfilename = (Filename.chop_extension filename)^".zlog" in
  let reloc, last = export outchan nvars root in
  close_out outchan;
  let command = "zchaff "^filename^" > "^resfilename in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Zchaff = %.5f@." (t1-.t0);  
  if exit_code <> 0 then 
    failwith ("Zchaff.call_zchaff: command "^command^
	      " exited with code "^(string_of_int exit_code));
  let logfilename = (Filename.chop_extension filename)^".log" in
  let command2 = "mv resolve_trace "^logfilename in
  let exit_code2 = Sys.command command2 in
  if exit_code2 <> 0 then 
      failwith ("Zchaff.call_zchaff: command "^command2^
                " exited with code "^(string_of_int exit_code2));
  (* import_cnf_trace reloc logfilename root last  *)
  (reloc, resfilename, logfilename, last)


(* Build the problem that it may be understoof by zchaff *)

let cnf_checker_modules = [ ["SMTCoq";"Trace";"Cnf_Checker"] ]

let certif_ops = CoqTerms.make_certif_ops cnf_checker_modules 
let ccertif = gen_constant cnf_checker_modules "certif" 
let cCertif = gen_constant cnf_checker_modules "Certif" 
let cchecker_b_correct = 
  gen_constant cnf_checker_modules "checker_b_correct" 
let cchecker_b = gen_constant cnf_checker_modules "checker_b" 
let cchecker_eq_correct = 
  gen_constant cnf_checker_modules "checker_eq_correct" 
let cchecker_eq = gen_constant cnf_checker_modules "checker_eq" 

let build_body reify_atom reify_form l b (max_id, confl) = 
  let ntvar = mkName "t_var" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let tvar = Atom.interp_tbl reify_atom in
  let _, tform = Form.interp_tbl reify_form in
  let (tres,_) =
    SmtTrace.to_coq Form.to_coq certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1);tres;mkInt (get_pos confl)|] in
  let vtvar = Term.mkRel 3 in
  let vtform = Term.mkRel 2 in
  let vc = Term.mkRel 1 in
  Term.mkLetIn (ntvar, tvar, mklApp carray [|Lazy.force cbool|],
  Term.mkLetIn (ntform, tform, mklApp carray [|Lazy.force cform|],
  Term.mkLetIn (nc, certif, Lazy.force ccertif, 
  mklApp cchecker_b_correct 
	 [|vtvar; vtform; l; b; vc; 
	   vm_cast_true (mklApp cchecker_b [|vtform;l;b;vc|])|])))


let build_body_eq reify_atom reify_form l1 l2 l (max_id, confl) =
  let ntvar = mkName "t_var" in
  let ntform = mkName "t_form" in
  let nc = mkName "c" in
  let tvar = Atom.interp_tbl reify_atom in
  let _, tform = Form.interp_tbl reify_form in
  let (tres,_) =
    SmtTrace.to_coq Form.to_coq certif_ops confl in
  let certif =
    mklApp cCertif [|mkInt (max_id + 1);tres;mkInt (get_pos confl)|] in 
  let vtvar = Term.mkRel 3 in
  let vtform = Term.mkRel 2 in
  let vc = Term.mkRel 1 in
  Term.mkLetIn (ntvar, tvar, mklApp carray [|Lazy.force cbool|],
  Term.mkLetIn (ntform, tform, mklApp carray [|Lazy.force cform|],
  Term.mkLetIn (nc, certif, Lazy.force ccertif, 
  mklApp cchecker_eq_correct 
         [|vtvar; vtform; l1; l2; l; vc;
	   vm_cast_true (mklApp cchecker_eq [|vtform;l1;l2;l;vc|])|])))

let get_arguments concl = 
  let f, args = Term.decompose_app concl in
  match args with
  | [ty;a;b] when (Constr.equal f (Lazy.force ceq)) && (Constr.equal ty (Lazy.force cbool)) -> a, b
  | [a] when (Constr.equal f (Lazy.force cis_true)) -> a, Lazy.force ctrue
  | _ -> failwith ("Zchaff.get_arguments :can only deal with equality over bool")


(* Check that the result is Unsat, otherwise raise a model *)

exception Sat of int list
exception Finished

let input_int file =
  let rec input_int acc flag =
    let c = input_char file in
    if c = '-' then
      input_int acc true
    else if c = '0' then
      input_int (10*acc) flag
    else if c = '1' then
      input_int (10*acc+1) flag
    else if c = '2' then
      input_int (10*acc+2) flag
    else if c = '3' then
      input_int (10*acc+3) flag
    else if c = '4' then
      input_int (10*acc+4) flag
    else if c = '5' then
      input_int (10*acc+5) flag
    else if c = '6' then
      input_int (10*acc+6) flag
    else if c = '7' then
      input_int (10*acc+7) flag
    else if c = '8' then
      input_int (10*acc+8) flag
    else if c = '9' then
      input_int (10*acc+9) flag
    else if c = ' ' then
      if flag then -acc else acc
    else raise Finished in
  input_int 0 false

let check_unsat filename =
  let f = open_in filename in
  let rec get_model acc =
    try
      let i = input_int f in
      get_model (i::acc)
    with
      | Finished -> acc in
  try
    while true do
      let l = input_line f in
      let n = String.length l in
      if n >= 8 && String.sub l 0 8 = "Instance" then
        if n >= 20 && String.sub l 9 11 = "Satisfiable" then
          raise (Sat (get_model []))
        else
          raise End_of_file
    done
  with
    | End_of_file -> close_in f


(* Pre-process the proof given by zchaff *)

let make_proof pform_tbl atom_tbl env reify_form l =
  let fl = Form.flatten reify_form l in
  let root = SmtTrace.mkRootV [l] in
  let _ = 
    if Form.equal l fl then Cnf.make_cnf reify_form root 
    else
      let first_c = SmtTrace.mkOther (ImmFlatten(root,fl)) (Some [fl]) in
      SmtTrace.link root first_c;
      Cnf.make_cnf reify_form first_c in
  let (reloc, resfilename, logfilename, last) =
    call_zchaff (Form.nvars reify_form) root in
  (try check_unsat resfilename with
    | Sat model -> Structures.error (List.fold_left (fun acc i ->
      let index = if i > 0 then i-1 else -i-1 in
      let ispos = i > 0 in
      try (
        let f = pform_tbl.(index) in
        match f with
          | Fatom a ->
            let t = atom_tbl.(a) in
            let value = if ispos then " = true" else " = false" in
            acc^"  "^(Pp.string_of_ppcmds (Structures.pr_constr_env env t))^value
          | Fapp _ -> acc
      ) with | Invalid_argument _ -> acc (* Because cnf computation does not put the new formulas in the table... Perhaps it should? *)
    ) "zchaff found a counterexample:\n" model)
  );
  import_cnf_trace reloc logfilename root last


(* The whole tactic *)

let tactic gl =
  SmtTrace.clear ();

  let env = Tacmach.pf_env gl in
  (* let sigma = Tacmach.project gl in *)
  let t = Tacmach.pf_concl gl in

  let (forall_let, concl) = Term.decompose_prod_assum t in
  let a, b = get_arguments concl in
  let reify_atom = Atom.create () in
  let reify_form = Form.create () in
  let body = 
    if ((Constr.equal b (Lazy.force ctrue)) || (Constr.equal b (Lazy.force cfalse))) then
      let l = Form.of_coq (Atom.get reify_atom) reify_form a in
      let l' = if (Constr.equal b (Lazy.force ctrue)) then Form.neg l else l in
      let atom_tbl = Atom.atom_tbl reify_atom in
      let pform_tbl = Form.pform_tbl reify_form in
      let max_id_confl = make_proof pform_tbl atom_tbl (Environ.push_rel_context forall_let env) reify_form l' in
      build_body reify_atom reify_form (Form.to_coq l) b max_id_confl 
    else
      let l1 = Form.of_coq (Atom.get reify_atom) reify_form a in
      let l2 = Form.of_coq (Atom.get reify_atom) reify_form b in
      let l = Form.neg (Form.get reify_form (Fapp(Fiff,[|l1;l2|]))) in
      let atom_tbl = Atom.atom_tbl reify_atom in
      let pform_tbl = Form.pform_tbl reify_form in
      let max_id_confl = make_proof pform_tbl atom_tbl (Environ.push_rel_context forall_let env) reify_form l in
      build_body_eq reify_atom reify_form 
	(Form.to_coq l1) (Form.to_coq l2) (Form.to_coq l) max_id_confl
  in
  let compose_lam_assum forall_let body =
    List.fold_left (fun t rd -> Term.mkLambda_or_LetIn rd t) body forall_let in
  let res = compose_lam_assum forall_let body in
  Tactics.exact_no_check res gl

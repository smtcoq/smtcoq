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


open Format

open SmtMisc
open CoqTerms
open SmtCertif
open SmtTrace
open SmtAtom


(******************************************************************************)
(* Given a lfsc trace build the corresponding certif and theorem             *)
(******************************************************************************)

(* Instantiate Converter with translator for SMTCoq *)
module C = Converter.Make (Tosmtcoq)

exception No_proof

(* Hard coded signatures *)
let signatures =
  let sigdir = try Sys.getenv "LFSCSIGS" with Not_found -> Sys.getcwd () in
  ["sat.plf";
   "smt.plf";
   "th_base.plf";
   "th_int.plf";
   "th_bv.plf";
   "th_bv_bitblast.plf";
   "th_bv_rewrites.plf";
   "th_arrays.plf" ]
  |> List.map (Filename.concat sigdir)


let process_signatures_once =
  let don = ref false in
  fun () ->
    if !don then ()
    else
      try
        (* don := true; *)
        List.iter (fun f ->
            let chan = open_in f in
            let lexbuf = Lexing.from_channel chan in
            LfscParser.ignore_commands LfscLexer.main lexbuf;
            close_in chan
          ) signatures
      with
      | Ast.TypingError (t1, t2) ->
        Structures.error
          (asprintf "@[<hov>LFSC typing error: expected %a, got %a@]@."
             Ast.print_term t1
             Ast.print_term t2)


let lfsc_parse_last lb =
  printf "Type-checking LFSC proof...@?";
  let t0 = Sys.time () in
  let r = LfscParser.last_command LfscLexer.main lb in
  let t1 = Sys.time () in
  printf " Done [%.3f s]@." (t1 -. t0);
  r

let lfsc_parse_one lb =
  printf "Type-checking LFSC proof...@?";
  let t0 = Sys.time () in
  let r = LfscParser.one_command LfscLexer.main lb in
  let t1 = Sys.time () in
  printf " Done [%.3f s]@." (t1 -. t0);
  r
  

let import_trace first parse lexbuf =
  Printexc.record_backtrace true;
  process_signatures_once ();
  try
    match parse lexbuf with

    | Some (Ast.Check p) ->
      (* Ast.flatten_term p; *)
      let confl_num = C.convert_pt p in
      (* Afterwards, the SMTCoq libraries will produce the remaining, you do
         not have to care *)
      let first =
        let aux = VeritSyntax.get_clause 1 in
        match first, aux.value with
        | Some (root,l), Some (fl::nil) ->
          (* Format.eprintf "Root: %a ,,,,,,\n\ *)
          (*                 input: %a@." *)
          (*   (Form.to_smt Atom.to_smt) l (Form.to_smt Atom.to_smt) fl; *)
          if Form.equal l fl then
            aux
          else (
            (* eprintf "ADDING Flatten rule@."; *)
            aux.kind <- Other (ImmFlatten(root,fl));
            SmtTrace.link root aux;
            root
          )
        | _,_ -> aux in
      let confl = VeritSyntax.get_clause confl_num in
      SmtTrace.select confl;
      occur confl;
      (alloc first, confl)

    | _ -> raise No_proof

  with
  | Ast.TypingError (t1, t2) ->
    Structures.error
      (asprintf "@[<hov>LFSC typing error: expected %a, got %a@]@."
         Ast.print_term t1
         Ast.print_term t2)



let import_trace_from_file first filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let p = import_trace first lfsc_parse_last lexbuf in
  close_in chan;
  p



let clear_all () =
  SmtTrace.clear ();
  SmtMaps.clear ();
  VeritSyntax.clear ();
  Tosmtcoq.clear ();
  C.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = Tosmtcoq.ra in
  let rf = Tosmtcoq.rf in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace_from_file None fproof in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace
    (import_all fsmt fproof)

let checker_debug fsmt fproof =
  SmtCommands.checker_debug (import_all fsmt fproof)

let theorem name fsmt fproof =
  SmtCommands.theorem name (import_all fsmt fproof)

(* let checker fsmt fproof =
 *   SmtCommands.checker (import_all fsmt fproof) *)

(* Same but print runtime *)
let checker fsmt fproof =
  let c = import_all fsmt fproof in
  printf "Coq checker...@.";
  let t0 = Sys.time () in
  let r = SmtCommands.checker c in
  let t1 = Sys.time () in
  printf "Done (Coq) [%.3f s]@." (t1 -. t0);
  r



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)


(* module Form2 = struct *)
(*   (\* Just for printing *\) *)

(*   open Form *)

(*   let rec to_smt atom_to_smt fmt f = *)
(*     if is_pos f then to_smt_pform atom_to_smt fmt (pform f) *)
(*     else fprintf fmt "(not %a)" (to_smt_pform atom_to_smt) (pform f) *)

(*   and to_smt_pform atom_to_smt fmt = function *)
(*     | Fatom a -> atom_to_smt fmt a *)
(*     | Fapp (op,args) -> to_smt_op atom_to_smt op fmt (Array.to_list args) *)
(*     | _ -> assert false *)

(*   and to_smt_op atom_to_smt op fmt args = *)
(*     match op, args with *)
(*       | Ftrue, [] -> fprintf fmt "true" *)
(*       | Ffalse, [] -> fprintf fmt "false" *)
(*       | Fand, [x; y] -> *)
(*         fprintf fmt "(and %a %a)" (to_smt atom_to_smt) x (to_smt atom_to_smt) y *)
(*       | For, [x; y] -> *)
(*         fprintf fmt "(or %a %a)" (to_smt atom_to_smt) x (to_smt atom_to_smt) y *)
(*       | Fand, x :: rargs -> *)
(*         fprintf fmt "(and %a %a)" (to_smt atom_to_smt) x *)
(*           (to_smt_op atom_to_smt Fand) rargs *)
(*       | For, x :: rargs -> *)
(*         fprintf fmt "(or %a %a)" (to_smt atom_to_smt) x *)
(*           (to_smt_op atom_to_smt For) rargs *)
(*       (\* andb and orb are left-associative in Coq *\) *)
(*       (\* | Fand, _ -> left_assoc atom_to_smt Fand fmt (List.rev args) *\) *)
(*       (\* | For, _ -> left_assoc atom_to_smt For fmt (List.rev args) *\) *)
(*       | Fxor, _ -> *)
(*         fprintf fmt "(xor%a)" *)
(*           (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args *)
(*       | Fimp, _ -> *)
(*         fprintf fmt "(=>%a)" *)
(*           (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args *)
(*       | Fiff, _ -> *)
(*         fprintf fmt "(=%a)" *)
(*           (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args *)
(*       | Fite, _ -> *)
(*         fprintf fmt "(ite%a)" *)
(*           (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args *)
(*       | Fnot2 _, _ -> *)
(*         fprintf fmt "(not (not %a))" *)
(*           (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args *)
(*       | _ -> assert false *)

(*   and left_assoc atom_to_smt op fmt args = *)
(*     (\* args is reversed *\) *)
(*     match op, args with *)
(*     | Fand, [x; y] -> *)
(*       fprintf fmt "(and %a %a)" (to_smt atom_to_smt) y (to_smt atom_to_smt) x *)
(*     | For, [x; y] -> *)
(*       fprintf fmt "(or %a %a)" (to_smt atom_to_smt) y (to_smt atom_to_smt) x *)
(*     | Fand, last :: rargs -> *)
(*       fprintf fmt "(and %a %a)" *)
(*         (left_assoc atom_to_smt Fand) rargs (to_smt atom_to_smt) last *)
(*     | For, last :: rargs -> *)
(*       fprintf fmt "(or %a %a)" *)
(*         (left_assoc atom_to_smt For) rargs (to_smt atom_to_smt) last *)
(*     | _ -> assert false *)

(* end *)


(* module Atom2 = struct *)
(*   (\* Just for printing *\) *)

(*   open Atom *)
  
(*   let distrib x l = List.map (fun y -> (x,y)) l *)

(*   let rec cross acc l = match l with *)
(*     | [] | [_] -> List.rev acc *)
(*     | x :: r -> *)
(*       cross (List.rev_append (distrib x r) acc) r *)

(*   let cross = cross [] *)
  
(*   let rec compute_int = function *)
(*     | Acop c -> *)
(*       (match c with *)
(*        | CO_xH -> 1 *)
(*        | CO_Z0 -> 0 *)
(*        | CO_BV _ -> assert false) *)
(*     | Auop (op,h) -> *)
(*       (match op with *)
(*        | UO_xO -> 2*(compute_hint h) *)
(*        | UO_xI -> 2*(compute_hint h) + 1 *)
(*        | UO_Zpos -> compute_hint h *)
(*        | UO_Zneg -> - (compute_hint h) *)
(*        | _ -> assert false) *)
(*     | _ -> assert false *)

(*   and compute_hint h = compute_int (atom h) *)

(*   let to_smt_int fmt i = *)
(*     let s1 = if i < 0 then "(- " else "" in *)
(*     let s2 = if i < 0 then ")" else "" in *)
(*     let j = if i < 0 then -i else i in *)
(*     fprintf fmt "%s%i%s" s1 j s2 *)

(*   let rec to_smt fmt h = to_smt_atom fmt (atom h) *)

(*   and to_smt_atom fmt = function *)
(*     | Acop _ as a -> to_smt_int fmt (compute_int a) *)
(*     | Auop (UO_Zopp,h) -> *)
(*       fprintf fmt "(- "; *)
(*       to_smt fmt h; *)
(*       fprintf fmt ")" *)
(*     | Auop _ as a -> to_smt_int fmt (compute_int a) *)
(*     | Abop (op,h1,h2) -> to_smt_bop fmt op h1 h2 *)
(*     | Atop (op,h1,h2,h3) -> to_smt_bop fmt op h1 h2 h3 *)
(*     | Anop (op,a) -> to_smt_nop fmt op a *)
(*     | Aapp (op,a) -> *)
(*       if Array.length a = 0 then ( *)
(*         fprintf fmt "op_%i" (indexed_op_index op); *)
(*       ) else ( *)
(*         fprintf fmt "(op_%i" (indexed_op_index op); *)
(*         Array.iter (fun h -> fprintf fmt " "; to_smt fmt h) a; *)
(*         fprintf fmt ")" *)
(*       ) *)

(*   and str_op = function *)
(*       | BO_Zplus -> "+" *)
(*       | BO_Zminus -> "-" *)
(*       | BO_Zmult -> "*" *)
(*       | BO_Zlt -> "<" *)
(*       | BO_Zle -> "<=" *)
(*       | BO_Zge -> ">=" *)
(*       | BO_Zgt -> ">" *)
(*       | BO_eq _ -> "=" *)
  
(*   and to_smt_bop fmt op h1 h2 = *)
(*     match op with *)
(*     | BO_Zlt -> fprintf fmt "(not (>= %a %a)" to_smt h1 to_smt h2 *)
(*     | BO_Zle -> fprintf fmt "(not (>= %a (+ %a 1))" to_smt h1 to_smt h2 *)
(*     | BO_Zgt -> fprintf fmt "(>= %a (+ %a 1)" to_smt h1 to_smt h2 *)
(*     | _ -> fprintf fmt "(%s %a %a)" (str_op op) to_smt h1 to_smt h2 *)

(*   and to_smt_nop fmt op a = *)
(*     let rec pp fmt = function *)
(*       | [] -> assert false *)
(*       | [x, y] -> fprintf fmt "(not (= %a %a))" to_smt x to_smt y *)
(*       | (x, y) :: r -> *)
(*         fprintf fmt "(and (not (= %a %a)) %a)" to_smt x to_smt y pp r *)
(*     in *)
(*     let pairs = cross (Array.to_list a) in *)
(*     pp fmt pairs *)

(* end *)

let string_logic ro f =
  let l = SL.union (Op.logic_ro ro) (Form.logic f) in
  if SL.is_empty l then "QF_SAT"
  else
    sprintf "QF_%s%s%s%s"
    (if SL.mem LArrays l then "A" else "")
    (if SL.mem LUF l || SL.mem LLia l then "UF" else "")
    (if SL.mem LBitvectors l then "BV" else "")
    (if SL.mem LLia l then "LIA" else "")

let check_cvc4_version () =
  begin
    try (ignore (FileUtil.which "cvc4"))
    with Not_found ->  Structures.error "cvc4 not found"
  end ;
  let re = Str.regexp_string "version 1.6" 
  and chan = Unix.open_process_in "cvc4 --version" in
  let first_line = input_line chan in
  begin
    begin
      try ignore (Str.search_forward re first_line 0)
      with Not_found -> Structures.error "Please use version 1.6 of cvc4"
    end ;
    ignore (Unix.close_process_in chan)
  end

let call_cvc4 env rt ro ra rf root _ =
  let open Smtlib2_solver in
  let fl = snd root in

  let cvc4 = create [|
      "cvc4";
      "--lang"; "smt2";
      "--proof";
      "--no-simplification"; "--fewer-preprocessing-holes";
      "--no-bv-eq"; "--no-bv-ineq"; "--no-bv-algebraic" |] in

  set_option cvc4 "print-success" true;
  set_option cvc4 "produce-assignments" true;
  set_option cvc4 "produce-proofs" true;
  set_logic cvc4 (string_logic ro fl);

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    SmtMaps.add_btype s (SmtBtype.Tindex t);
    declare_sort cvc4 s 0;
  ) (SmtBtype.to_list rt);
  
  List.iter (fun (i,cod,dom,op) ->
    let s = "op_"^(string_of_int i) in
    SmtMaps.add_fun s op;
    let args =
      Array.fold_right
        (fun t acc -> asprintf "%a" SmtBtype.to_smt t :: acc) cod [] in
    let ret = asprintf "%a" SmtBtype.to_smt dom in
    declare_fun cvc4 s args ret
  ) (Op.to_list ro);

  assume cvc4 (asprintf "%a" (Form.to_smt ~debug:false) fl);

  let proof =
    match check_sat cvc4 with
    | Unsat ->
      begin
        try get_proof cvc4 (import_trace (Some root) lfsc_parse_one)
        with
        | Ast.CVC4Sat -> Structures.error "CVC4 returned SAT"
        | No_proof -> Structures.error "CVC4 did not generate a proof"
        | Failure s -> Structures.error ("Importing of proof failed: " ^ s)
      end
    | Sat ->
      let smodel = get_model cvc4 in
      Structures.error
        ("CVC4 returned sat. Here is the model:\n\n" ^
         SmtCommands.model_string env rt ro ra rf smodel)
        (* (asprintf "CVC4 returned sat. Here is the model:\n%a" SExpr.print smodel) *)
  in

  quit cvc4;
  proof



let export out_channel rt ro l =
  let fmt = formatter_of_out_channel out_channel in
  fprintf fmt "(set-logic %s)@." (string_logic ro l);

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    SmtMaps.add_btype s (SmtBtype.Tindex t);
    fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);

  List.iter (fun (i,cod,dom,op) ->
    let s = "op_"^(string_of_int i) in
    SmtMaps.add_fun s op;
    fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t ->
        if !is_first then is_first := false
        else fprintf fmt " "; SmtBtype.to_smt fmt t
      ) cod;
    fprintf fmt ") %a)@." SmtBtype.to_smt dom;
  ) (Op.to_list ro);

  fprintf fmt "(assert %a)@\n(check-sat)@\n(exit)@."
    (Form.to_smt ~debug:false) l



let get_model_from_file filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  match SExprParser.sexps SExprLexer.main lexbuf with
  | [SExpr.Atom "sat"; m] -> m
  | _ -> Structures.error "CVC4 returned SAT but no model"


let call_cvc4_file env rt ro ra rf root =
  let fl = snd root in
  let (filename, outchan) = Filename.open_temp_file "cvc4_coq" ".smt2" in
  export outchan rt ro fl;
  close_out outchan;
  let bf = Filename.chop_extension filename in
  let prooffilename = bf ^ ".lfsc" in

  (* let cvc4_cmd = *)
  (*   "cvc4 --proof --dump-proof -m --dump-model \ *)
  (*    --no-simplification --fewer-preprocessing-holes \ *)
  (*    --no-bv-eq --no-bv-ineq --no-bv-algebraic " *)
  (*   ^ filename ^ " > " ^ prooffilename in *)
  (* CVC4 crashes when asking for both models and proofs *)
  
  let cvc4_cmd =
    "cvc4 --proof --dump-proof \
     --no-simplification --fewer-preprocessing-holes \
     --no-bv-eq --no-bv-ineq --no-bv-algebraic "
    ^ filename ^ " > " ^ prooffilename in
  (* let clean_cmd = "sed -i -e '1d' " ^ prooffilename in *)
  eprintf "%s@." cvc4_cmd;
  let t0 = Sys.time () in
  let exit_code = Sys.command cvc4_cmd in
  
  let t1 = Sys.time () in
  eprintf "CVC4 = %.5f@." (t1-.t0);

  if exit_code <> 0 then
    Structures.error ("CVC4 crashed: return code "^string_of_int exit_code);

  (* ignore (Sys.command clean_cmd); *)

  try import_trace_from_file (Some root) prooffilename
  with
  | No_proof -> Structures.error "CVC4 did not generate a proof"
  | Failure s -> Structures.error ("Importing of proof failed: " ^ s)
  | Ast.CVC4Sat ->
    let smodel = get_model_from_file prooffilename in
    Structures.error
      ("CVC4 returned sat. Here is the model:\n\n" ^
       SmtCommands.model_string env rt ro ra rf smodel)


let cvc4_logic = 
  SL.of_list [LUF; LLia; LBitvectors; LArrays]


let tactic_gen vm_cast =
  check_cvc4_version () ;
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = Tosmtcoq.ra in
  let rf = Tosmtcoq.rf in
  let ra' = Tosmtcoq.ra in
  let rf' = Tosmtcoq.rf in
  SmtCommands.tactic call_cvc4 cvc4_logic rt ro ra rf ra' rf' vm_cast [] []
  (* (\* Currently, quantifiers are not handled by the cvc4 tactic: we pass
   *    the same ra and rf twice to have everything reifed *\)
   * SmtCommands.tactic call_cvc4 cvc4_logic rt ro ra rf ra rf vm_cast [] [] *)
let tactic () = tactic_gen vm_cast_true
let tactic_no_check () = tactic_gen (fun _ -> vm_cast_true_no_check)

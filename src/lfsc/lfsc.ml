(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*     Université Paris-Sud                                               *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Format
open Entries
open Declare
open Decl_kinds

open SmtMisc
open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SmtAtom


(******************************************************************************)
(* Given a lfsc trace build the corresponding certif and theorem             *)
(******************************************************************************)

(* Instantiate Converter with translator for SMTCoq *)
module C = Converter.Make (Tosmtcoq)

exception No_proof


let import_trace filename first =
  Printexc.record_backtrace true;
  (* What you have to do: parse the certificate, and produce the
     corresponding veriT steps linearly, as you are currently doing: the
     difference is that instead of pretty-printing, you should produce
     something in the format of SmtCertif, and return the (last)
     conflicting step *)
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  try

    match LfscParser.last_command LfscLexer.main lexbuf with

    | Some (Ast.Check p) ->
      close_in chan;
      Ast.flatten_term p;
      let confl_num = C.convert p in
      (* Afterwards, the SMTCoq libraries will produce the remaining, you do
         not have to care *)
      let first =
        let aux = VeritSyntax.get_clause 1 in
        match first, aux.value with
        | Some (root,l), Some (fl::nil) ->
          Format.eprintf "Root: %a ,,,,,,\n\
                          input: %a@."
            (Form.to_smt Atom.to_smt) l (Form.to_smt Atom.to_smt) fl;
          if Form.equal l fl then
            aux
          else (
            eprintf "ADDING Flatten rule@.";
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
    eprintf "@[<hov>LFSC typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2;
    exit 1

  | e ->
    let backtrace = Printexc.get_backtrace () in
    eprintf "Fatal error: %s@." (Printexc.to_string e);
    eprintf "Backtrace:@\n%s@." backtrace;
    raise e



let clear_all () =
  SmtTrace.clear ();
  C.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace fproof None in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace (import_all fsmt fproof)
let theorem name fsmt fproof = SmtCommands.theorem name (import_all fsmt fproof)
let checker fsmt fproof = SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)


module Form2 = struct
  (* Just for printing *)

  open Form

  let rec to_smt atom_to_smt fmt f =
    if is_pos f then to_smt_pform atom_to_smt fmt (pform f)
    else fprintf fmt "(not %a)" (to_smt_pform atom_to_smt) (pform f)

  and to_smt_pform atom_to_smt fmt = function
    | Fatom a -> atom_to_smt fmt a
    | Fapp (op,args) -> to_smt_op atom_to_smt op fmt (Array.to_list args)

  and to_smt_op atom_to_smt op fmt args =
    match op, args with
      | Ftrue, [] -> fprintf fmt "true"
      | Ffalse, [] -> fprintf fmt "false"
      | Fand, [x; y] ->
        fprintf fmt "(and %a %a)" (to_smt atom_to_smt) x (to_smt atom_to_smt) y
      | For, [x; y] ->
        fprintf fmt "(or %a %a)" (to_smt atom_to_smt) x (to_smt atom_to_smt) y
      | Fand, x :: rargs ->
        fprintf fmt "(and %a %a)" (to_smt atom_to_smt) x
          (to_smt_op atom_to_smt Fand) rargs
      | For, x :: rargs ->
        fprintf fmt "(or %a %a)" (to_smt atom_to_smt) x
          (to_smt_op atom_to_smt For) rargs
      (* andb and orb are left-associative in Coq *)
      (* | Fand, _ -> left_assoc atom_to_smt Fand fmt (List.rev args) *)
      (* | For, _ -> left_assoc atom_to_smt For fmt (List.rev args) *)
      | Fxor, _ ->
        fprintf fmt "(xor%a)"
          (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args
      | Fimp, _ ->
        fprintf fmt "(=>%a)"
          (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args
      | Fiff, _ ->
        fprintf fmt "(=%a)"
          (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args
      | Fite, _ ->
        fprintf fmt "(ite%a)"
          (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args
      | Fnot2 _, _ ->
        fprintf fmt "(not (not %a))"
          (fun fmt -> List.iter (fprintf fmt " %a" (to_smt atom_to_smt))) args
      | _ -> assert false

  and left_assoc atom_to_smt op fmt args =
    (* args is reversed *)
    match op, args with
    | Fand, [x; y] ->
      fprintf fmt "(and %a %a)" (to_smt atom_to_smt) y (to_smt atom_to_smt) x
    | For, [x; y] ->
      fprintf fmt "(or %a %a)" (to_smt atom_to_smt) y (to_smt atom_to_smt) x
    | Fand, last :: rargs ->
      fprintf fmt "(and %a %a)"
        (left_assoc atom_to_smt Fand) rargs (to_smt atom_to_smt) last
    | For, last :: rargs ->
      fprintf fmt "(or %a %a)"
        (left_assoc atom_to_smt For) rargs (to_smt atom_to_smt) last
    | _ -> assert false

end


module Atom2 = struct
  (* Just for printing *)

  open Atom
  
  let distrib x l = List.map (fun y -> (x,y)) l

  let rec cross acc l = match l with
    | [] | [_] -> List.rev acc
    | x :: r ->
      cross (List.rev_append (distrib x r) acc) r

  let cross = cross []
  
  let rec compute_int = function
    | Acop c ->
      (match c with
       | CO_xH -> 1
       | CO_Z0 -> 0)
    | Auop (op,h) ->
      (match op with
       | UO_xO -> 2*(compute_hint h)
       | UO_xI -> 2*(compute_hint h) + 1
       | UO_Zpos -> compute_hint h
       | UO_Zneg -> - (compute_hint h)
       | UO_Zopp -> assert false)
    | _ -> assert false

  and compute_hint h = compute_int (atom h)

  let to_smt_int fmt i =
    let s1 = if i < 0 then "(- " else "" in
    let s2 = if i < 0 then ")" else "" in
    let j = if i < 0 then -i else i in
    fprintf fmt "%s%i%s" s1 j s2

  let rec to_smt fmt h = to_smt_atom fmt (atom h)

  and to_smt_atom fmt = function
    | Acop _ as a -> to_smt_int fmt (compute_int a)
    | Auop (UO_Zopp,h) ->
      fprintf fmt "(- ";
      to_smt fmt h;
      fprintf fmt ")"
    | Auop _ as a -> to_smt_int fmt (compute_int a)
    | Abop (op,h1,h2) -> to_smt_bop fmt op h1 h2
    | Anop (op,a) -> to_smt_nop fmt op a
    | Aapp (op,a) ->
      if Array.length a = 0 then (
        fprintf fmt "op_%i" (indexed_op_index op);
      ) else (
        fprintf fmt "(op_%i" (indexed_op_index op);
        Array.iter (fun h -> fprintf fmt " "; to_smt fmt h) a;
        fprintf fmt ")"
      )

  and str_op = function
      | BO_Zplus -> "+"
      | BO_Zminus -> "-"
      | BO_Zmult -> "*"
      | BO_Zlt -> "<"
      | BO_Zle -> "<="
      | BO_Zge -> ">="
      | BO_Zgt -> ">"
      | BO_eq _ -> "="
  
  and to_smt_bop fmt op h1 h2 =
    match op with
    | BO_Zlt -> fprintf fmt "(not (>= %a %a)" to_smt h1 to_smt h2
    | BO_Zle -> fprintf fmt "(not (>= %a (+ %a 1))" to_smt h1 to_smt h2
    | BO_Zgt -> fprintf fmt "(>= %a (+ %a 1)" to_smt h1 to_smt h2
    | _ -> fprintf fmt "(%s %a %a)" (str_op op) to_smt h1 to_smt h2

  and to_smt_nop fmt op a =
    let rec pp fmt = function
      | [] -> assert false
      | [x, y] -> fprintf fmt "(not (= %a %a))" to_smt x to_smt y
      | (x, y) :: r ->
        fprintf fmt "(and (not (= %a %a)) %a)" to_smt x to_smt y pp r
    in
    let pairs = cross (Array.to_list a) in
    pp fmt pairs

end



let export out_channel rt ro l =
  let fmt = formatter_of_out_channel out_channel in
  fprintf fmt "(set-logic QF_UFLIA)@.";

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    VeritSyntax.add_btype s (Tindex t);
    fprintf fmt "(declare-sort %s 0)@." s
  ) (Btype.to_list rt);

  List.iter (fun (i,cod,dom,op) ->
    let s = "op_"^(string_of_int i) in
    VeritSyntax.add_fun s op;
    fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t ->
        if !is_first then is_first := false
        else fprintf fmt " "; Btype.to_smt fmt t
      ) cod;
    fprintf fmt ") %a)@." Btype.to_smt dom;
  ) (Op.to_list ro);

  fprintf fmt "(assert %a)@\n(check-sat)@\n(exit)@."
    (Form.to_smt Atom.to_smt) l
  


(* val call_cvc4 : Btype.reify_tbl -> Op.reify_tbl -> Form.t -> (Form.t clause * Form.t) -> (int * Form.t clause) *)
let call_cvc4 rt ro rf root =
  (* let fl = Form.right_assoc rf fl in *)
  let fl = snd root in
  let (filename, outchan) = Filename.open_temp_file "cvc4_coq" ".smt2" in
  export outchan rt ro fl;
  close_out outchan;
  let bf = Filename.chop_extension filename in
  let logfilename = bf ^ "_tmp.lfsc" in
  let prooffilename = bf ^ ".lfsc" in

  let command =
    "cvc4 --dump-proof --no-simplification --fewer-preprocessing-holes \
     --no-bv-eq --no-bv-ineq --no-bv-algebraic"
    ^ filename ^ " | sed -e '1d; s/\\\\\\([^ ]\\)/\\\\ \\1/g' > "
    ^ logfilename in
  eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  eprintf "CVC4 = %.5f@." (t1-.t0);
  if exit_code <> 0 then
    failwith ("Lfsc.call_cvc4: command "^command^
	      " exited with code "^(string_of_int exit_code));

  let sigdir = try Sys.getenv "LFSCSIGS" with Not_found -> Sys.getcwd () in
  let signatures = [
    "sat.plf";
    "smt.plf";
    "th_base.plf";
    "th_int.plf";
    "th_bv.plf";
    "th_bv_bitblast.plf";
  ] in
  let signatures_arg =
    signatures
    |> List.map (Filename.concat sigdir)
    |> String.concat " "
  in
  Sys.command ("cat "^signatures_arg^" "^logfilename^" > "^prooffilename)
  |> ignore;
  
  try import_trace prooffilename (Some root)
  with No_proof -> Structures.error "CVC4 did not generate a proof"



let tactic env sigma t =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  SmtCommands.tactic call_cvc4 rt ro ra rf env sigma t

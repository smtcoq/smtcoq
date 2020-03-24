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
open SmtTrace
open SmtAtom
open SmtBtype
open SmtCertif


(* let debug = false *)


(******************************************************************************)
(* Given a verit trace build the corresponding certif and theorem             *)
(******************************************************************************)
(* exception Import_trace of int *)

(* let get_val = function
 *     Some a -> a
 *   | None -> assert false *)

(* For debugging certif processing : <add_scertif> <select> <occur> <alloc> *)
(* let print_certif c where=
 *   let r = ref c in
 *   let out_channel = open_out where in
 *   let fmt = Format.formatter_of_out_channel out_channel in
 *   let continue = ref true in
 *   while !continue do
 *     let kind = to_string (!r.kind) in
 *     let id = !r.id in
 *     let pos = match !r.pos with
 *       | None -> "None"
 *       | Some p -> string_of_int p in
 *     let used = !r.used in
 *     Format.fprintf fmt "id:%i kind:%s pos:%s used:%i value:" id kind pos used;
 *     begin match !r.value with
 *     | None -> Format.fprintf fmt "None"
 *     | Some l -> List.iter (fun f -> Form.to_smt Atom.to_smt fmt f;
 *                                     Format.fprintf fmt " ") l end;
 *     Format.fprintf fmt "\n";
 *     match !r.next with
 *     | None -> continue := false
 *     | Some n -> r := n
 *   done;
 *   Format.fprintf fmt "@."; close_out out_channel *)

let import_trace filename first lsmt st stl =
  let ra' = VeritSyntax.get_atom_tbl_no_add st in
  let rf' = VeritSyntax.get_form_tbl_no_add st in
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let confl_num = ref (-1) in
  let first_num = ref (-1) in
  let is_first = ref true in
  let line = ref 1 in
  (* let _ = Parsing.set_trace true in *)
  try
    while true do
      confl_num := VeritParser.line VeritLexer.token lexbuf st stl;
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
       let cfirst = ref (VeritSyntax.get_clause !first_num st) in
       let confl = ref (VeritSyntax.get_clause !confl_num st) in
       let re_hash = Form.hash_hform (Atom.hash_hatom ra') rf' in
       begin match first with
       | None -> ()
       | Some _ ->
          let init_index = VeritSyntax.init_index lsmt re_hash in
          let cf, lr = order_roots init_index !cfirst in
          cfirst := cf;
          let to_add = VeritSyntax.qf_to_add (List.tl lr) in
          let to_add =
            (match first, !cfirst.value with
             | Some (root, l), Some [fl] when init_index fl = 1 && not (Form.equal l (re_hash fl)) ->
                 let cfirst_value = !cfirst.value in
                 !cfirst.value <- root.value;
                 [Other (ImmFlatten (root, fl)), cfirst_value, !cfirst]
             | _ -> []) @ to_add in
       match to_add with
       | [] -> ()
       | _  -> confl := add_scertifs to_add !cfirst end;
       select !confl;
       occur !confl;
       (alloc !cfirst, !confl)
    | Parsing.Parse_error -> failwith ("Verit.import_trace: parsing error line "^(string_of_int !line))


let import_all fsmt fproof =
  let st = VeritSyntax.create_verit_state () in
  let stl = State.create_smtlib_state () in
  let smt_st = VeritSyntax.get_smt_state st in
  let roots = Smtlib2_genConstr.import_smtlib2 smt_st stl fsmt in
  let (max_id, confl) = import_trace fproof None [] st stl in
  (smt_st, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace
    (import_all fsmt fproof)

let checker_debug fsmt fproof =
  SmtCommands.checker_debug (import_all fsmt fproof)

let theorem name fsmt fproof =
  SmtCommands.theorem name (import_all fsmt fproof)

let checker fsmt fproof =
  SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

let export out_channel st stl lsmt =
  let rt = VeritSyntax.get_type_tbl st in
  let ro = VeritSyntax.get_op_tbl st in

  let fmt = Format.formatter_of_out_channel out_channel in
  Format.fprintf fmt "(set-logic UFLIA)@.";

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    State.add_btype stl s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);

  List.iter (fun (i,dom,cod,op) ->
    let s = "op_"^(string_of_int i) in
    State.add_fun stl s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t -> if !is_first then is_first := false else Format.fprintf fmt " "; SmtBtype.to_smt fmt t) dom;
    Format.fprintf fmt ") ";
    SmtBtype.to_smt fmt cod;
    Format.fprintf fmt ")@."
  ) (Op.to_list ro);

  List.iter (fun u -> Format.fprintf fmt "(assert ";
                      Form.to_smt fmt u;
                      Format.fprintf fmt ")\n") lsmt;

  Format.fprintf fmt "(check-sat)\n(exit)@."

exception Unknown

let call_verit st stl _ first lsmt =
  let (filename, outchan) = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan st stl lsmt;
  close_out outchan;
  let logfilename = Filename.chop_extension filename ^ ".vtlog" in
  let wname, woc = Filename.open_temp_file "warnings_verit" ".log" in
  close_out woc;
  let command = "veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=" ^ logfilename ^ " " ^ filename ^ " 2> " ^ wname in
  Format.eprintf "%s@." command;
  let t0 = Sys.time () in
  let exit_code = Sys.command command in
  let t1 = Sys.time () in
  Format.eprintf "Verit = %.5f@." (t1-.t0);

  let win = open_in wname in

  let raise_warnings_errors () =
    try
      while true do
        let l = input_line win in
        let n = String.length l in
        if l = "warning : proof_done: status is still open" then
          raise Unknown
        else if l = "Invalid memory reference" then
          Structures.warning "verit-warning" ("veriT outputted the warning: " ^ l)
        else if n >= 7 && String.sub l 0 7 = "warning" then
          Structures.warning "verit-warning" ("veriT outputted the warning: " ^ (String.sub l 7 (n-7)))
        else if n >= 8 && String.sub l 0 8 = "error : " then
          Structures.error ("veriT failed with the error: " ^ (String.sub l 8 (n-8)))
        else
          Structures.error ("veriT failed with the error: " ^ l)
      done
    with End_of_file -> () in

  try
    if exit_code <> 0 then Structures.warning "verit-non-zero-exit-code" ("Verit.call_verit: command " ^ command ^ " exited with code " ^ string_of_int exit_code);
    raise_warnings_errors ();
    let res = import_trace logfilename (Some first) lsmt st stl in
    close_in win; Sys.remove wname; res
  with x -> close_in win; Sys.remove wname;
            match x with
            | Unknown -> Structures.error "veriT returns 'unknown'"
            | VeritSyntax.Sat -> Structures.error "veriT found a counter-example"
            | _ -> raise x

let verit_logic =
  SL.of_list [LUF; LLia]

let tactic_gen vm_cast lcpl lcepl =
  let st = VeritSyntax.create_verit_state () in
  let stl = State.create_smtlib_state () in
  let smt_st = VeritSyntax.get_smt_state st in
  SmtCommands.tactic (call_verit st stl) verit_logic smt_st vm_cast lcpl lcepl
let tactic = tactic_gen vm_cast_true
let tactic_no_check = tactic_gen (fun _ -> vm_cast_true_no_check)

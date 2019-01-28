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


open Entries
open Declare
open Decl_kinds

open SmtMisc
open CoqTerms
open SmtForm
open SmtTrace
open SmtAtom
open SmtBtype
open SmtCertif


let debug = false


(******************************************************************************)
(* Given a verit trace build the corresponding certif and theorem             *)
(******************************************************************************)
exception Import_trace of int

let get_val = function
    Some a -> a
  | None -> assert false

(* For debugging certif processing : <add_scertif> <select> <occur> <alloc> *)
let print_certif c where=
  let r = ref c in
  let out_channel = open_out where in
  let fmt = Format.formatter_of_out_channel out_channel in
  let continue = ref true in
  while !continue do
    let kind = to_string (!r.kind) in
    let id = !r.id in
    let pos = match !r.pos with
      | None -> "None"
      | Some p -> string_of_int p in
    let used = !r.used in
    Format.fprintf fmt "id:%i kind:%s pos:%s used:%i value:" id kind pos used;
    begin match !r.value with
    | None -> Format.fprintf fmt "None"
    | Some l -> List.iter (fun f -> Form.to_smt Atom.to_smt fmt f;
                                    Format.fprintf fmt " ") l end;
    Format.fprintf fmt "\n";
    match !r.next with
    | None -> continue := false
    | Some n -> r := n
  done;
  Format.fprintf fmt "@."; close_out out_channel

let import_trace ra' rf' filename first lsmt =
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
       let cfirst = ref (VeritSyntax.get_clause !first_num) in
       let confl = ref (VeritSyntax.get_clause !confl_num) in
       let re_hash = Form.hash_hform (Atom.hash_hatom ra') rf' in
       begin match first with
       | None -> ()
       | Some _ ->
          let cf, lr = order_roots (VeritSyntax.init_index lsmt re_hash)
                         !cfirst in
          cfirst := cf;
          let to_add = VeritSyntax.qf_to_add (List.tl lr) in
          let to_add =
            (match first, !cfirst.value with
             | Some (root, l), Some [fl] when not (Form.equal l (re_hash fl)) ->
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


let clear_all () =
  SmtTrace.clear ();
  VeritSyntax.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra' = VeritSyntax.ra' in
  let rf' = VeritSyntax.rf' in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace ra' rf' fproof None [] in
  (rt, ro, ra, rf, roots, max_id, confl)


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

let export out_channel rt ro lsmt =
  let fmt = Format.formatter_of_out_channel out_channel in
  Format.fprintf fmt "(set-logic UFLIA)@.";

  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    VeritSyntax.add_btype s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);

  List.iter (fun (i,dom,cod,op) ->
    let s = "op_"^(string_of_int i) in
    VeritSyntax.add_fun s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t -> if !is_first then is_first := false else Format.fprintf fmt " "; SmtBtype.to_smt fmt t) dom;
    Format.fprintf fmt ") ";
    SmtBtype.to_smt fmt cod;
    Format.fprintf fmt ")@."
  ) (Op.to_list ro);

  List.iter (fun u -> Format.fprintf fmt "(assert ";
                      Form.to_smt Atom.to_smt fmt u;
                      Format.fprintf fmt ")\n") lsmt;

  Format.fprintf fmt "(check-sat)\n(exit)@."


let call_verit _ rt ro ra' rf' first lsmt =
  let (_, l') = first in
  let fl' = Form.flatten rf' l' in
  let lsmt = fl'::lsmt in
  let (filename, outchan) = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan rt ro lsmt;
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

  (* TODO: improve readability: remove the three nested try *)
  let win = open_in wname in
  try
    if exit_code <> 0 then
      failwith ("Verit.call_verit: command " ^ command ^
	          " exited with code " ^ string_of_int exit_code);

    try let _ = input_line win in
        Structures.error "veriT returns 'unknown'"
    with End_of_file ->
          try
            let res = import_trace ra' rf' logfilename (Some first) lsmt in
            close_in win; Sys.remove wname; res
          with
            | VeritSyntax.Sat -> Structures.error "veriT found a counter-example"
  with x -> close_in win; Sys.remove wname; raise x


let verit_logic =
  SL.of_list [LUF; LLia]

let tactic_gen vm_cast lcpl lcepl =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra' = VeritSyntax.ra' in
  let rf' = VeritSyntax.rf' in
  SmtCommands.tactic call_verit verit_logic rt ro ra rf ra' rf' vm_cast lcpl lcepl
let tactic = tactic_gen vm_cast_true
let tactic_no_check = tactic_gen (fun _ -> vm_cast_true_no_check)

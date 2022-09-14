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
open SmtTrace
open SmtAtom
open SmtBtype


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

let import_trace ra rf filename for_tactic lsmt =
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

       if for_tactic then (
         let re_hash = Form.hash_hform (Atom.hash_hatom ~eqsym:false ra) rf in
         let re_hash_eqsym = Form.hash_hform (Atom.hash_hatom ra) rf in
         let is_forall l = match Form.pform l with
             | SmtForm.Fapp (SmtForm.Fforall _, _) -> true
             | _ -> false
         in
         let lsmt =
           List.fold_left (fun acc f ->
               if is_forall f then
                 acc
               else
                 let forig = re_hash f in
                 let fsym = re_hash_eqsym f in
                 (forig, SmtAtom.Form.remove_double_neg rf fsym)::acc
             ) [] lsmt
         in
         let rec find_qf_lemma f = function
           | [] -> assert false
           | (x,x')::xs ->
              (
               if SmtAtom.Form.equal x' f then x else find_qf_lemma f xs
              )
         in
         let find_qf_lemma f = find_qf_lemma f lsmt in

         (* Looking for quantifier-free hypotheses (quantified
            hypotheses will be used in veriT's ForallInst rules) *)
         let r = ref !cfirst in
         let lr = ref [] in
         while SmtTrace.isRoot !r.SmtCertif.kind do
           (match !r.SmtCertif.value with
              | Some [l] when not (is_forall l) ->
                 let l = re_hash_eqsym l in
                 let x = find_qf_lemma l in
                 let id = !r.SmtCertif.id in
                 let lem = SmtTrace.mk_scertif (SmtCertif.Other (SmtCertif.Qf_lemma x)) (Some [x]) in
                 if SmtAtom.Form.equal x l then
                   lr := (lem, id)::!lr
                 else
                   let lem' = SmtTrace.mk_scertif (SmtCertif.Other (SmtCertif.ImmFlatten (lem, l))) (Some [l]) in
                   lr := (lem, id)::(lem', id)::!lr
              | _ -> ()
           );
           r := SmtTrace.next !r
         done;

         SmtCertif.print_certif SmtAtom.Form.to_smt !cfirst "avant";

         (* Adding quantifier-free lemmas used as inputs in the final
            certificate, using the ForallInst rule (which simply proves
            lemma -> lemma) *)
         let to_add = !lr in
         match to_add with
           | [] -> ()
           | _  -> confl := add_scertifs to_add !cfirst
       );

       SmtCertif.print_certif SmtAtom.Form.to_smt !cfirst "apres";

       select !confl;
       occur !confl;
       (alloc !cfirst, !confl)
    | Parsing.Parse_error -> failwith ("Verit.import_trace: parsing error line "^(string_of_int !line))


let clear_all () =
  SmtTrace.clear ();
  SmtMaps.clear ();
  VeritSyntax.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace ra rf fproof false [] in
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
    SmtMaps.add_btype s (Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);

  List.iter (fun (i,dom,cod,op) ->
    let s = "op_"^(string_of_int i) in
    SmtMaps.add_fun s op;
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

let call_verit timeout _ rt ro ra rf _ lsmt =
  let (filename, outchan) = Filename.open_temp_file "verit_coq" ".smt2" in
  export outchan rt ro lsmt;
  close_out outchan;
  let logfilename = Filename.chop_extension filename ^ ".vtlog" in
  let wname, woc = Filename.open_temp_file "warnings_verit" ".log" in
  close_out woc;
  let command = "veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=" ^ logfilename ^ " " ^ filename ^ " 2> " ^ wname in
  let command = 
    match timeout with
      | Some i -> "timeout "^(string_of_int i)^" "^command
      | None -> command
  in
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
          CoqInterface.warning "verit-warning" ("veriT outputted the warning: " ^ l)
        else if n >= 7 && String.sub l 0 7 = "warning" then
          CoqInterface.warning "verit-warning" ("veriT outputted the warning: " ^ (String.sub l 7 (n-7)))
        else if n >= 8 && String.sub l 0 8 = "error : " then
          CoqInterface.error ("veriT failed with the error: " ^ (String.sub l 8 (n-8)))
        else
          CoqInterface.error ("veriT failed with the error: " ^ l)
      done
    with End_of_file -> () in
  if exit_code = 124 (*code for timeout*) then (close_in win; Sys.remove wname; let _ = CoqInterface.anomaly "veriT timed out" in ());
  try
    if exit_code <> 0 then CoqInterface.warning "verit-non-zero-exit-code" ("Verit.call_verit: command " ^ command ^ " exited with code " ^ string_of_int exit_code);
    raise_warnings_errors ();
    let res = import_trace ra rf logfilename true lsmt in
    close_in win; Sys.remove wname; res
  with x -> close_in win; Sys.remove wname;
            match x with
            | Unknown -> CoqInterface.error "veriT returns 'unknown'"
            | VeritSyntax.Sat -> CoqInterface.error "veriT found a counter-example"
            | _ -> raise x

let verit_logic =
  SL.of_list [LUF; LLia]

let tactic_gen vm_cast timeout lcpl lcepl =
  (* Transform the tuple of lemmas given by the user into a list *)
  let lcpl =
    let lcpl = EConstr.Unsafe.to_constr lcpl in
    let lcpl = CoqTerms.option_of_constr_option lcpl in
    match lcpl with
      | Some lcpl -> CoqTerms.list_of_constr_tuple lcpl
      | None -> []
  in

  (* Core tactic *)
  clear_all ();
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  let ra = VeritSyntax.ra in
  let rf = VeritSyntax.rf in
  let ra_quant = VeritSyntax.ra_quant in
  let rf_quant = VeritSyntax.rf_quant in
  SmtCommands.tactic (call_verit timeout) verit_logic rt ro ra rf ra_quant rf_quant vm_cast lcpl lcepl false
let tactic = tactic_gen vm_cast_true
let tactic_no_check = tactic_gen (fun _ -> vm_cast_true_no_check)


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

(* TODO: replace these dummy functions with complete ones *)

let _ = Printexc.record_backtrace true


module C = Converter.Make (Tosmtcoq)

let import_trace filename =
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
      let confl = VeritSyntax.get_clause confl_num in
      (* Afterwards, the SMTCoq libraries will produce the remaining, you do
         not have to care *)
      SmtTrace.select confl;
      occur confl;
      let first = VeritSyntax.get_clause 1 in
      (* TODO change when function export is written *)
      (alloc first, confl)

    | _ -> failwith "No proof"

  with Ast.TypingError (t1, t2) ->
    Format.eprintf "@[<hov>LFSC typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2;
    exit 1

     | e ->
       let backtrace = Printexc.get_backtrace () in
       Format.eprintf "Fatal error: %s@." (Printexc.to_string e);
       Format.eprintf "Backtrace:@\n%s@." backtrace;
       exit 1
       


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
  let (max_id, confl) = import_trace fproof in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace (import_all fsmt fproof)
let theorem name fsmt fproof = SmtCommands.theorem name (import_all fsmt fproof)
let checker fsmt fproof = SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

(* TODO *)

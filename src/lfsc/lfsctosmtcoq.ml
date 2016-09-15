(**************************************************************************)
(*                                                                        *)
(*                            LFSCtoSmtCoq                                *)
(*                                                                        *)
(*                         Copyright (C) 2016                             *)
(*          by the Board of Trustees of the University of Iowa            *)
(*                                                                        *)
(*                    Alain Mebsout and Burak Ekici                       *)
(*                       The University of Iowa                           *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Ast
open Format
open Builtin
open VeritPrinter

let _ = Printexc.record_backtrace true


(* Captures the output and exit status of a unix command : aux func *)
let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  ignore(Unix.close_process (ic, oc));
  Buffer.contents buf

(* Set width of pretty printing boxes to number of columns *)
let vt_width =
  try
    let scol = syscall "tput cols" in
    let w = int_of_string (String.trim scol) in
    set_margin w;
    w
  with Not_found | Failure _ -> 80


let _ =
  pp_set_margin std_formatter vt_width;
  pp_set_margin err_formatter vt_width;
  set_max_indent (get_margin () / 3)



module C = Converter.Make (VeritPrinter)


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


let process_signatures () =
  try
    List.iter (fun f ->
        let chan = open_in f in
        let lexbuf = Lexing.from_channel chan in
        LfscParser.ignore_commands LfscLexer.main lexbuf;
        close_in chan
      ) signatures
  with
  | Ast.TypingError (t1, t2) ->
    eprintf "@[<hov>LFSC typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2


(** Translate to veriT proof format and print pretty LFSC proof with colors *)
let pretty_to_verit () =
  process_signatures ();
  let chan =
    try
      let filename = Sys.argv.(1) in
      open_in filename
    with Invalid_argument _ -> stdin
  in
  let buf = Lexing.from_channel chan in

  try
    let proof = LfscParser.proof LfscLexer.main buf in

    printf "LFSC proof:\n\n%a\n\n@." print_proof proof;

    printf "Verit proof:\n@.";
    
    match List.rev proof with
    | Check p :: _ ->
      flatten_term p;
      C.convert p |> ignore
    | _ -> eprintf "No proof@."; exit 1
    

  with Ast.TypingError (t1, t2) ->
    eprintf "@[<hov>Typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2


(** Translate to veriT proof format *)
let to_verit () =
  process_signatures ();
  let chan =
    try
      let filename = Sys.argv.(1) in
      open_in filename
    with Invalid_argument _ -> stdin
  in
  let buf = Lexing.from_channel chan in

  eprintf "Type-checking LFSC proof.@.";
  try

    match LfscParser.last_command LfscLexer.main buf with
    | Some (Check p) ->
      (* eprintf "Flattening pointer structures...@."; *)
      (* flatten_term p; *)
      (* eprintf "Done (flatten)@."; *)
      C.convert p |> ignore
    | _ -> eprintf "No proof@."; exit 1

  with
  | Ast.TypingError (t1, t2) as e ->
    let backtrace = Printexc.get_backtrace () in
    eprintf "Fatal error: %s@." (Printexc.to_string e);
    eprintf "Backtrace:@\n%s@." backtrace;

    eprintf "@[<hov>Typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2
  | Ast.CVC4Sat ->
    eprintf "CVC4 returned SAT@."; exit 1



let _ = to_verit ()




(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

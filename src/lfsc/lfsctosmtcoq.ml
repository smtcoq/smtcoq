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





let test2 () =
  let chan =
    try
      let filename = Sys.argv.(1) in
      open_in filename
    with Invalid_argument _ -> stdin
  in
  let buf = Lexing.from_channel chan in

  try
    (* let proof = LfscParser.proof LfscLexer.main buf in *)
    (* printf "LFSC proof:@.%a@." Ast.print_proof proof *)

    LfscParser.proof_print LfscLexer.main buf;
    (* LfscParser.proof_ignore LfscLexer.main buf; *)

    (* Some tests for side conditions *)
    printf "\n\ 
             Some tests for side conditions:\n\ 
             -------------------------------\n@."; 

     let res = append cln cln in 
     printf "append cln cln = %a@." print_term res; 

     let res2 = append (clc (pos v1) (clc (neg v3) cln)) (clc (neg v2) cln) in 
     printf "append (clc (pos v1) (clc (neg v3) cln)) (clc (neg v2) cln) = %a@." 
       print_term res2; 
       


     let res3 = simplify_clause 
         (concat 
            (clr (neg v1) (clc (neg v1) cln)) 
            (clr (pos v1) (clc (pos v1) cln))) in 
     printf "simplified clause : %a@." print_term res3; 



  with Ast.TypingError (t1, t2) ->
    eprintf "@[<hov>Typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2


let test3 () =
  let c1 = (clc (neg v1) (clc (neg v3) (clc (pos v2) (clc (pos v1) (clc (pos v3) (clc (neg v3) (clc (pos v1) cln)) ))))) in
  let c2 = (clr (pos v3) (clc (neg v1) (clc (neg v3) (clc (pos v2) (clc (pos v1) (clc (pos v3) (clc (neg v3) (clc (pos v1) cln)) )))))) in
  let c3 = (clr (neg v3) (clc (neg v1) (clc (neg v3) (clc (pos v2) (clc (pos v1) (clc (pos v3) (clc (neg v3) (clc (pos v1) cln)) )))))) in
    let rmv1 = remove (pos v3) c1 in
    let rmv2 = remove (neg v3) c1 in
    let app  = append rmv1 rmv2 in
    let dd   = dropdups app in
    let rsv  = resolve c1 c1 v3 in
    let clearance1 = simplify_clause c2 in
    let clearance2 = simplify_clause c3 in
    let app2 = append clearance1 clearance2 in
    let dd2  = dropdups app2 in
(*      Format.printf "removal1: %a@." print_term rmv1;*)
(*      Format.printf "removal2: %a@." print_term rmv2;*)
(*      Format.printf "append afer removals (pos) (neg): %a@." print_term app;*)
      Format.printf "clause afer dropping duplicates: %a@." print_term dd;
      Format.printf "clause afer resolve: %a@." print_term rsv;
(*      Format.printf "clause afer clearance1: %a@." print_term clearance1;*)
(*      Format.printf "clause afer clearance2: %a@." print_term clearance2;*)
      Format.printf "final clearance: %a@." print_term dd2;;
        

(* let _ = test3 () *)


module C = Converter.Make (VeritPrinter)


(** Translate to veriT proof format and print pretty LFSC proof with colors *)
let pretty_to_verit () =
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
  let chan =
    try
      let filename = Sys.argv.(1) in
      open_in filename
    with Invalid_argument _ -> stdin
  in
  let buf = Lexing.from_channel chan in

  try

    match LfscParser.last_command LfscLexer.main buf with
    | Some (Check p) ->
      flatten_term p;
      C.convert p |> ignore
    | _ -> eprintf "No proof@."; exit 1

  with Ast.TypingError (t1, t2) ->
    eprintf "@[<hov>Typing error: expected %a, got %a@]@."
      Ast.print_term t1
      Ast.print_term t2



let _ = pretty_to_verit ()




(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

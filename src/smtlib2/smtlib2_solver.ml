(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller  *                                                  *)
(*     Alain   Mebsout ♯                                                  *)
(*     Burak   Ekici   ♯                                                  *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Format
  
type result = Sat | Unsat

type t = {
  cmd : string array;
  pid : int;
  stdin : Unix.file_descr;
  stdout : Unix.file_descr;
  stderr : Unix.file_descr;
  lexbuf : Lexing.lexbuf;
}


let create cmd =
  let executable = cmd.(0) in

  (* Create pipes for input, output and error output *)
  let stdin_in, stdin_out = Unix.pipe () in
  let stdout_in, stdout_out = Unix.pipe () in 
  let stderr_in, stderr_out = Unix.pipe () in 

  (* Create solver process *)
  let pid = 
    Unix.create_process 
      executable 
      cmd 
      stdin_in
      stdout_out
      stderr_out
  in

  (* Close our end of the pipe which has been duplicated by the
     process *)
  Unix.close stdin_in;
  Unix.close stdout_out; 
  Unix.close stderr_out; 

  (* Get an output channel to read from solver's stdout *)
  let stdout_ch = Unix.in_channel_of_descr stdout_in in

  let lexbuf = Lexing.from_channel stdout_ch in

  (* Create the solver instance *)
  { cmd; pid;
    stdin = stdin_out; stdout = stdout_in; stderr = stderr_in; lexbuf }


let kill s =
  try
    Unix.close s.stdin;
    Unix.close s.stdout;
    Unix.close s.stderr;
    Unix.kill s.pid Sys.sigkill;
  with _ -> ()


let read_response { lexbuf } = 
  SExprParser.sexp SExprLexer.main lexbuf 


let error s sexp =
  kill s;
  Structures.error (asprintf "Solver error: %a." SExpr.print sexp)


let read_success s = 
  match SExprParser.sexp SExprLexer.main s.lexbuf with
  | SExpr.Atom "success" -> ()
  | r -> error s r


let no_response _ = ()


let read_check_result s = 
  match SExprParser.sexp SExprLexer.main s.lexbuf with
  | SExpr.Atom "sat" -> Sat
  | SExpr.Atom "unsat" -> Unsat
  | SExpr.Atom "unknown" -> Structures.error ("Solver returned uknown.")
  | r -> error s r


let send_command s cmd read =
  eprintf "%s@." cmd;
  let err_p1 = Unix.((fstat s.stderr).st_size) in
  try
    let in_ch = Unix.out_channel_of_descr s.stdin in
    let fmt = formatter_of_out_channel in_ch in
    pp_print_string fmt cmd;
    pp_print_newline fmt ();
    read s
  with e ->
    let err_p2 = Unix.((fstat s.stderr).st_size) in
    let len = err_p2 - err_p1 in
    (* Was something written to stderr? *)
    if len <> 0 then begin
      let buf = Bytes.create err_p2 in
      Unix.read s.stderr buf 0 err_p2 |> ignore;
      let err_msg = Bytes.sub_string buf err_p1 len in
      Structures.error ("Solver error: "^err_msg);
    end
    else (kill s; raise e)


let set_option s name b =
  send_command s
    (asprintf "(set-option :%s %b)" name b)
    read_success


let set_logic s l =
  send_command s
    (sprintf "(set-logic %s)" l)
    read_success


let declare_sort s name arity =
  send_command s
    (asprintf "(declare-sort %s %d)" name arity)
    read_success


let declare_fun s name args ret =
  send_command s
    (asprintf "(declare-fun %s (%a) %s)"
       name
       (fun fmt -> List.iter (fprintf fmt "%s ")) args
       ret)
    read_success
  

let assume s f =
  send_command s
    (sprintf "(assert %s)" f)
    read_success


let check_sat s =
  send_command s "(check-sat)" read_check_result


let get_proof s process_proof =
  send_command s "(get-proof)" (fun s -> process_proof s.lexbuf)


let get_model s =
  send_command s "(get-model)" read_response


let quit s =
  try
    send_command s "(exit)" read_success;
  with Unix.Unix_error _ -> ();
  kill s



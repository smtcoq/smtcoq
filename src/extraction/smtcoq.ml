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


open Smtcoq_extr


type solver = Zchaff | Verit


let string_of_solver = function
  | Zchaff -> "ZChaff"
  | Verit -> "veriT"


let verifier_of_solver = function
  | Zchaff -> Zchaff_checker.checker
  | Verit -> Verit_checker.checker


let run s pb trace =
  Printf.printf "Calling the %s verifier on %s and %s...\n" (string_of_solver s) pb trace;
  let v = verifier_of_solver s in
  try
    let t1 = Unix.time () in
    let res = v pb trace in
    let t2 = Unix.time () in
    if res then
      Printf.printf "The trace was correctly verified in %fs\n" (t2 -. t1)
    else
      failwith "Error"
  with | _ -> Printf.printf "The verifier failed to check the trace :-(\n"


let _ =

  let usage_verit = "Uses the verifier for veriT (default); the problem must be a SMTLIB2 file, and the trace, veriT unsatisfiability trace" in
  let usage_zchaff = "Uses the verifier for ZChaff; the problem must be a dimacs file, and the trace, ZChaff unsatisfiability trace" in
  let usage_msg = Printf.sprintf
"
Usage: smtcoq [solver] problem trace
Solver:
  -verit    %s
  -zchaff   %s
" usage_verit usage_zchaff
  in

  let verit = ref true in
  let input_files = ref [] in

  let anon_fun filename =
    input_files := filename::!input_files
  in

  let speclist =
    [("-verit", Arg.Set verit, usage_verit);
     ("-zchaff", Arg.Clear verit, usage_zchaff)]
  in

  Arg.parse speclist anon_fun usage_msg;

  let s = if !verit then Verit else Zchaff in
  let (pb, trace) =
    try
      match !input_files with
        | [trace; pb] -> (pb, trace)
        | _ -> assert false
    with
      | _ -> Printf.printf "%s" usage_msg; exit 0
  in
  run s pb trace

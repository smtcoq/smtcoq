type solver = Zchaff | Verit


let usage =
"
Usage: smtcoq [solver] problem trace
Solver:
  -zchaff   Uses the verifier for ZChaff (default); the problem must be a dimacs file, and the trace, ZChaff unsatisfiability trace
  -verit    Uses the verifier for ZChaff; the problem must be a SMTLIB2 file, and the trace, veriT unsatisfiability trace

"


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
  let (s,pb,trace) =
    try
      let s = if Sys.argv.(1) = "-verit" then Verit else Zchaff in
      let pb = Sys.argv.((Array.length Sys.argv)-2) in
      let trace = Sys.argv.((Array.length Sys.argv)-1) in
      (s,pb,trace)
    with
      | _ -> Printf.printf "%s" usage; exit 0 in
  run s pb trace

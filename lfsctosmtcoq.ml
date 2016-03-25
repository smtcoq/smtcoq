open Type
open Ast
open Format
open Builtin


let smt2_of_lfsc t =
  try
    (match t with
     | "iff" -> "="
     | "ifte" -> "ite"
     | "flet" -> "let"
     | "impl" -> "=>"
     | _ -> raise Exit)
  with Exit -> t


let rec uncurry = function
  | List (List f :: args) ->
    List (List.map uncurry (f @ args))
  | e -> e


let let_tbl = Hashtbl.create 13

let rec lfsc_term_to_smt2 = function

  | Atom t as a ->
    (try
       let def = Hashtbl.find let_tbl a in
       lfsc_term_to_smt2 def
     with Not_found ->
       Atom (smt2_of_lfsc t)
    )
    
  (* let binding *)
  | List [Atom "@"; name; t; s]  ->
    Hashtbl.add let_tbl name t;
    lfsc_term_to_smt2 s

  (* remove type argument of equality *)
  | List (Atom "=" :: _ :: l)  ->
    List (Atom "=" :: List.map lfsc_term_to_smt2 l)

  (* predicate application *)
  | List (Atom "p_app" :: l) ->
    begin match l with
      | [t] -> lfsc_term_to_smt2 t
      | _ -> List (List.map lfsc_term_to_smt2 l)
    end
    |> uncurry

  (* function application *)
  | List (Atom "apply" :: _ :: _ :: l) ->
    begin match l with
      | [t] -> lfsc_term_to_smt2 t
      | _ -> List (List.map lfsc_term_to_smt2 l)
    end
    |> uncurry

  (* other *)
  | List l -> List (List.map lfsc_term_to_smt2 l)





let sharp_tbl = Hashtbl.create 13

let cpt = ref 1
  
let rec print_input fmt s = match s with
  | Atom a -> pp_print_string fmt a

  | List [Atom "not"; s'] ->
    fprintf fmt "(not %a)" print_input s'

  | List l ->
    try
      let nb = Hashtbl.find sharp_tbl s in
      fprintf fmt "#%d" nb
    with Not_found ->
      Hashtbl.add sharp_tbl s !cpt;
      fprintf fmt "#%d:(" !cpt;
      incr cpt;
      let first = ref true in
      List.iter (fun s ->
          fprintf fmt "%s%a"
            (if !first then "" else " ")
            print_input s;
          first := false;
        ) l;
      fprintf fmt ")"


let set_cpt = ref 1

let rec print_hyp_inputs = function
  | List [Atom "%"; Atom a;
          List [Atom "th_holds"; s];
          rest] when a.[0] = 'A' ->
    (* hypothesis of the form (% A1 (th_holds s) ...) *)

    let smt2t = lfsc_term_to_smt2 s in
    printf "(set .c%d %a)@." !set_cpt print_input smt2t;
    incr set_cpt;
    print_hyp_inputs rest

  | Atom _ -> ()
              
  | List l -> List.iter print_hyp_inputs l

let test1 () =

  let filename = Sys.argv.(1) in
  let chan = open_in filename in
  let buf = Lexing.from_channel chan in
  let r = Parser.sexps Lexer.main buf in

  printf "Size of proof: %d@." (size_list r);
  printf "\nInputs in veriT:@.";
  begin
    match r with
    | [proof] -> print_hyp_inputs proof;
    | _ -> ()
  end;

  (* print_list std_formatter r; *)

  exit 0


let test2 () =
  let chan =
    try
      let filename = Sys.argv.(1) in
      open_in filename
    with Invalid_argument _ -> stdin
  in
  let buf = Lexing.from_channel chan in

  try
    (* let proof = Parser.proof Lexer.main buf in *)
    (* printf "LFSC proof:@.%a@." Ast.print_proof proof *)

    Parser.proof_print Lexer.main buf;
    (* Parser.proof_ignore Lexer.main buf; *)

(*     Some tests for side conditions *)
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



let _ =
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
        
        
let _ = test2 ()

(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

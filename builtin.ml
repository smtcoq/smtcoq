open Ast
open Format

let declare_get s ty =
  mk_declare s ty;
  mk_const s

let pi n ty t =
  let s = mk_symbol n ty in
  register_symbol s;
  let pi_abstr = mk_pi s (Lazy.force t) in
  remove_symbol s;
  pi_abstr


let var = declare_get "var" lfsc_type
let lit = declare_get "lit" lfsc_type
let clause = declare_get "clause" lfsc_type
let cln = declare_get "cln" clause

let pos_s = declare_get "pos" (pi "x" var (lazy lit))
let neg_s = declare_get "neg" (pi "x" var (lazy lit))
let clc_s = declare_get "clc" (pi "x" lit (lazy (pi "c" clause (lazy clause))))


let pos v = mk_app pos_s [v] 
let neg v = mk_app neg_s [v] 
let clc c1 c2 = mk_app clc_s [c1; c2]


let rec append c1 c2 =
  match c1.value with
  | Const _ when term_equal c1 cln -> c2
  | App (f, [l; c1']) when term_equal f clc_s ->
    clc l (append c1' c2)
  | _ -> failwith "Match failure"



(* For testing *)

let v1 = declare_get "v1" var
let v2 = declare_get "v2" var
let v3 = declare_get "v3" var

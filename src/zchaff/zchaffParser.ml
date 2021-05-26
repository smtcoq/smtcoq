(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SatParser
open SmtCertif
open SmtTrace

let _CL = "CL:"
let _INF = "<="
let _VAR = "VAR:"
let _L = "L:"
let _V = "V:"
let _A = "A:"
let _LITS = "Lits:"
let _CONF = "CONF:"
let _EQ = "=="

(** Parsing of zchaff proof *)

let alloc_res last c1 c2 tail =
  let c = mkRes c1 c2 tail in
  link last c;
  c

let rec parse_tailres reloc lb =
  if is_start_int lb then
    let cl_id = Hashtbl.find reloc (input_int lb) in
    cl_id :: parse_tailres reloc lb
  else []

let parse_resolution reloc lb last =
  let id = input_blank_int lb in
  blank_match_string lb _INF;
  let c1 = Hashtbl.find reloc (input_blank_int lb) in
  let c2 =  Hashtbl.find reloc (input_blank_int lb) in
  let tl = parse_tailres reloc lb in
  let c = alloc_res last c1 c2 tl in
  Hashtbl.add reloc id c;
  c

let parse_CL reloc lb last =
  let last = ref last in
  while blank_check_string lb _CL do
    last := parse_resolution reloc lb !last 
  done;
  !last


(* Parsing of the VAR and CONF part *)

(* let var_of_lit l = l lsr 1 *)

type var_key =
  | Var of int
  | Level of int

type 'hform var_decl = {
          var      : int;
          ante     : 'hform clause;
          ante_val : int list;
  mutable vclause  : 'hform clause option
}

type 'hform parse_var_info = (var_key, 'hform var_decl) Hashtbl.t

let var_of_lit l = l lsr 1

let parse_zclause lb =
  let zc = ref [var_of_lit (input_blank_int lb)] in
  while is_start_int lb do
    zc := var_of_lit (input_int lb) :: !zc;
  done;
  !zc

let parse_VAR_CONF reloc lb last =
  let max_level = ref (-1) in
  let vartbl = Hashtbl.create 100 in
  (* parsing of the VAR part *)
  while blank_check_string lb _VAR do
    let x = input_blank_int lb in
    blank_match_string lb _L;
    let lv = input_blank_int lb in
    blank_match_string lb _V;
    let _ = input_blank_int lb in
    blank_match_string lb _A;
    let ante = Hashtbl.find reloc (input_blank_int lb) in
    blank_match_string lb _LITS;
    let ante_val = parse_zclause lb in
    max_level := max !max_level lv;
    let vd = { var = x; ante = ante; ante_val = ante_val; vclause = None } in
    Hashtbl.add vartbl (Var x) vd;
    Hashtbl.add vartbl (Level lv) vd;
  done;
  (* Adding the resolution *)
  let rec build_res0 l =
    match l with
    | [] -> []
    | y :: l ->
      let yd =
	try Hashtbl.find vartbl (Var y)
        with Not_found ->
	  Printf.printf "Var %i not found.\n" y;raise Not_found in
      match yd.vclause with
      | Some cy -> cy :: build_res0 l
      | _ -> assert false in
  let rec build_res1 x l =
    match l with
    | [] -> assert false
    | y :: l ->
      if x = y then build_res0 l
      else
	let yd =
	  try Hashtbl.find vartbl (Var y)
	  with Not_found ->
	    Printf.printf "Var %i not found.\n" y;raise Not_found in
	match yd.vclause with
	| Some cy -> cy :: build_res1 x l
	| _ -> assert false in
  let last = ref last in
  for lv = 0 to !max_level do
    try
      let vd = Hashtbl.find vartbl (Level lv) in
      let c =
	match build_res1 vd.var vd.ante_val with
	| [] -> vd.ante
	| c2::tl -> 
	    last := alloc_res !last vd.ante c2 tl; !last in
      vd.vclause <- Some c;
    with Not_found -> ()
  done;
  (* parsing of the CONF *)
  blank_match_string lb _CONF;
  let conf = 
    let id = input_blank_int lb in
    Hashtbl.find reloc id in
  blank_match_string lb _EQ;
  let conf_val = parse_zclause lb in
  match build_res0 conf_val with
  | [] -> assert false
  | c2::tl -> alloc_res !last conf c2 tl


let parse_proof reloc filename last =
  let lb = open_file "Proof" filename in
  let last = parse_CL reloc lb last in
  let last = parse_VAR_CONF reloc lb last in
  close lb;
  last


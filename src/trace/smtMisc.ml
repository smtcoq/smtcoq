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


(** Sharing of coq Int *)
let cInt_tbl = Hashtbl.create 17 

let mkInt i = 
  try Hashtbl.find cInt_tbl i 
  with Not_found ->
    let ci = CoqInterface.mkInt i in
    Hashtbl.add cInt_tbl i ci;
    ci

(** Generic representation of shared object *)
type 'a gen_hashed = { index : int; mutable hval : 'a }


(** Functions over constr *)
let mklApp f args = CoqInterface.mkApp (Lazy.force f, args)

let string_of_name_def d n = try CoqInterface.string_of_name n with | _ -> d

let string_coq_constr t =
  let rec fix rf x = rf (fix rf) x in
  let pr = fix
      Ppconstr.modular_constr_pr Pp.mt CoqInterface.ppconstr_lsimpleconstr in
  Pp.string_of_ppcmds (pr (CoqInterface.constrextern_extern_constr t))


(** Logics *)

type logic_item =
  | LUF
  | LLia
  | LBitvectors
  | LArrays

module SL = Set.Make (struct
    type t = logic_item
    let compare = Stdlib.compare
  end)

type logic = SL.t


(** Utils *)
let rec filter_map f = function
  | [] -> []
  | x::xs -> match f x with Some x -> x::(filter_map f xs) | None -> filter_map f xs


(** Lexing *)
let char_for_backslash = function
  | 'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c -> c

let lf = '\010'

let dec_code c1 c2 c3 =
  100 * (Char.code c1 - 48) + 10 * (Char.code c2 - 48) + (Char.code c3 - 48)

let hex_code c1 c2 =
  let d1 = Char.code c1 in
  let val1 =
    if d1 >= 97 then d1 - 87
    else if d1 >= 65 then d1 - 55
    else d1 - 48 in
  let d2 = Char.code c2 in
  let val2 =
    if d2 >= 97 then d2 - 87
    else if d2 >= 65 then d2 - 55
    else d2 - 48 in
  val1 * 16 + val2

let found_newline (lexbuf:Lexing.lexbuf) diff =
  lexbuf.Lexing.lex_curr_p <-
    {
      lexbuf.Lexing.lex_curr_p with
      Lexing.pos_lnum = lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum + 1;
      Lexing.pos_bol = lexbuf.Lexing.lex_curr_p.Lexing.pos_cnum - diff;
    }

(* same length computation as in [Lexing.lexeme] *)
let lexeme_len { Lexing.lex_start_pos; Lexing.lex_curr_pos; _ } = lex_curr_pos - lex_start_pos

let main_failure lexbuf msg =
  let { Lexing.pos_lnum; Lexing.pos_bol; Lexing.pos_cnum; Lexing.pos_fname = _ } = Lexing.lexeme_start_p lexbuf in
  let msg =
    Printf.sprintf
      "Sexplib.Lexer.main: %s at line %d char %d"
      msg pos_lnum (pos_cnum - pos_bol)
  in
  failwith msg

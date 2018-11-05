(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type lex_buff = {
            buff       : string;
    mutable curr_char  : int;
    mutable buff_end   : int;
            in_ch      : in_channel
  }

let buff_length = 1024

let open_file s name =
  try
    let in_channel = open_in name in
    let buff = Bytes.create buff_length in
    let buff_end = input in_channel buff 0 buff_length in
    { buff = buff; curr_char = 0; buff_end = buff_end; in_ch = in_channel }
  with _ ->
    Printf.printf ("%s file %s does not exists.\n") s name;
    exit 1

let close lb =
  lb.buff_end <- 0;
  close_in lb.in_ch

let eof lb = lb.buff_end == 0

let curr_char lb =
  if eof lb then raise End_of_file
  else lb.buff.[lb.curr_char]

let refill lb =
  let ne = input lb.in_ch lb.buff 0 buff_length in
  lb.curr_char <- 0;
  lb.buff_end <- ne

(* Unsafe function *)
let is_space c = c == ' ' || c == '\t'

let is_space_ret c = c == ' ' || c == '\n' || c == '\t'


let skip to_skip lb =
  while not (eof lb) && to_skip lb.buff.[lb.curr_char] do
    while lb.curr_char < lb.buff_end && to_skip lb.buff.[lb.curr_char] do
      lb.curr_char <- lb.curr_char + 1
    done;
    if lb.curr_char = lb.buff_end then refill lb
  done

let skip_space lb = skip is_space lb
let skip_blank lb = skip is_space_ret lb


let skip_string lb s =
  let slen = String.length s in
  let pos = ref 0 in
  while !pos < slen && not (eof lb) && lb.buff.[lb.curr_char] == s.[!pos] do
    lb.curr_char <- lb.curr_char + 1;
    incr pos;
    while !pos < slen &&  lb.curr_char < lb.buff_end && lb.buff.[lb.curr_char] == s.[!pos] do
      lb.curr_char <- lb.curr_char + 1;
      incr pos
    done;
    if lb.curr_char = lb.buff_end then refill lb
  done;
  !pos = slen

let match_string lb s =
  if not (skip_string lb s) then raise (Invalid_argument ("match_string "^s))

let aux_buff = Bytes.create buff_length
let aux_be = ref 0
let aux_pi = ref 0
let aux_cc = ref 0

let save_lb lb =
  aux_cc := lb.curr_char;
  aux_be := lb.buff_end;
  aux_pi := pos_in lb.in_ch;
  String.blit lb.buff !aux_cc aux_buff !aux_cc (!aux_be - !aux_cc)

let restore_lb lb =
  lb.curr_char <- !aux_cc;
  lb.buff_end <- !aux_be;
  seek_in lb.in_ch !aux_pi;
  String.blit aux_buff !aux_cc lb.buff !aux_cc (!aux_be - !aux_cc)

let check_string lb s =
  let slen = String.length s in
  if String.length s <= lb.buff_end - lb.curr_char then
    let cc = lb.curr_char in
    let pos = ref 0 in
    while !pos < slen && lb.buff.[lb.curr_char] == s.[!pos] do
      lb.curr_char <- lb.curr_char + 1;
      incr pos
    done;
    if !pos = slen then begin
      if lb.curr_char = lb.buff_end then refill lb;
      true
    end else begin
      lb.curr_char <- cc;
      false
    end
  else begin
    save_lb lb;
    let b = skip_string lb s in
    if not b then restore_lb lb;
    b
  end

let blank_check_string lb s =
  skip_blank lb;
  check_string lb s

let blank_match_string lb s =
  skip_blank lb;
  match_string lb s

let is_digit c =
  '0' <= c && c <= '9'

let is_start_int lb =
  skip_blank lb;
  not (eof lb) && (is_digit lb.buff.[lb.curr_char] || lb.buff.[lb.curr_char] == '-')

let input_int lb =
  if eof lb then raise End_of_file
  else begin
    let sign =
      if lb.buff.[lb.curr_char] == '-' then begin
	lb.curr_char <- lb.curr_char + 1;
	if lb.curr_char = lb.buff_end then refill lb;
	-1
      end else
	1 in
    if eof lb then raise End_of_file;
    if not (is_digit lb.buff.[lb.curr_char]) then raise (Invalid_argument "input_int");
    let n = ref (Char.code lb.buff.[lb.curr_char] - Char.code '0') in
    lb.curr_char <- lb.curr_char + 1;
    if lb.curr_char = lb.buff_end then refill lb;
    while not (eof lb) && is_digit lb.buff.[lb.curr_char] do
      while lb.curr_char < lb.buff_end && is_digit lb.buff.[lb.curr_char] do
	n := !n*10 + (Char.code lb.buff.[lb.curr_char] - Char.code '0');
	lb.curr_char <- lb.curr_char + 1
      done;
      if lb.curr_char = lb.buff_end then refill lb
    done;
    sign * !n
  end

let input_blank_int lb =
  skip_blank lb;
  input_int lb


let skip_line lb =
  let notfound = ref true in
  while not (eof lb) && !notfound do
    while lb.curr_char < lb.buff_end && !notfound do
      if lb.buff.[lb.curr_char] == '\n' then notfound := false;
      lb.curr_char <- lb.curr_char + 1
    done;
    if lb.curr_char = lb.buff_end then refill lb
  done

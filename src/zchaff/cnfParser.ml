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


open SatParser


let skip_comment lb =
  while blank_check_string lb "c" do skip_line lb done

let parse_p_cnf lb =
  skip_comment lb;
  blank_match_string lb "p";
  blank_match_string lb "cnf";
  let nvar = input_blank_int lb in
  let _ = input_blank_int lb in
  nvar

let mklit nvars reify l =
  let sign = l > 0 in
  let x = (if sign then l else - l) - 1 in
  assert (0 <= x && x < nvars); 
  let p = SatAtom.Form.get reify (SmtForm.Fatom x) in
  if sign then p else SatAtom.Form.neg p

let rec parse_clause nvars reify lb =
  let i = input_blank_int lb in
  if i = 0 then []
  else mklit nvars reify i :: parse_clause nvars reify lb

let rec parse_clauses nvars reify lb last =
  if is_start_int lb then
    let c = SmtTrace.mkRootV (parse_clause nvars reify lb) in
    SmtTrace.link last c;
    parse_clauses nvars reify lb c
  else last 

let parse_cnf filename =
  let reify = SatAtom.Form.create () in
  let lb = open_file "CNF" filename in
  let nvars = parse_p_cnf lb in
  let first = SmtTrace.mkRootV (parse_clause nvars reify lb) in
  let last = parse_clauses nvars reify lb first in
  close lb;
  nvars, first, last


(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*     Université Paris Sud                                               *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

{
  open LfscParser
  exception Eof
}

let digit = [ '0'-'9' ]
let alpha = [ 'a'-'z' 'A' - 'Z' ]
let blank = [' ' '\t']
let newline = ['\n' '\r']
let var = alpha (alpha|digit|'_')*
let bindvar = '?' var+
let int = '-'? digit+
let any = _*


rule token = parse
  | blank +                    { token lexbuf }
  | newline +                  { EOL }

  | "unsat"                    { UNSAT }
  | "check"                    { CHECK }

  | "("                        { LPAR }
  | ")"                        { RPAR }

  | any                        { let v = Lexing.lexeme lexbuf in ANY v }

  | eof                        { raise Eof }

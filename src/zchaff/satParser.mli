(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type lex_buff
val open_file : string -> string -> lex_buff
val close : lex_buff -> unit
val blank_check_string : lex_buff -> string -> bool
val blank_match_string : lex_buff -> string -> unit
val is_start_int : lex_buff -> bool
val input_int : lex_buff -> int
val input_blank_int : lex_buff -> int
val skip_line : lex_buff -> unit

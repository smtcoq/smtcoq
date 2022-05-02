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


type lex_buff = {
  buff : bytes;
  mutable curr_char : int;
  mutable buff_end : int;
  in_ch : in_channel;
}
val buff_length : int
val open_file : string -> string -> lex_buff
val close : lex_buff -> unit
val eof : lex_buff -> bool
val curr_char : lex_buff -> char
val refill : lex_buff -> unit
val is_space : char -> bool
val is_space_ret : char -> bool
val skip : (char -> bool) -> lex_buff -> unit
val skip_space : lex_buff -> unit
val skip_blank : lex_buff -> unit
val skip_string : lex_buff -> string -> bool
val match_string : lex_buff -> string -> unit
val aux_buff : bytes
val aux_be : int ref
val aux_pi : int ref
val aux_cc : int ref
val save_lb : lex_buff -> unit
val restore_lb : lex_buff -> unit
val check_string : lex_buff -> string -> bool
val blank_check_string : lex_buff -> string -> bool
val blank_match_string : lex_buff -> string -> unit
val is_digit : char -> bool
val is_start_int : lex_buff -> bool
val input_int : lex_buff -> int
val input_blank_int : lex_buff -> int
val skip_line : lex_buff -> unit

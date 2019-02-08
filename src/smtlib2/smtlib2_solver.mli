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


type t

type result = Sat | Unsat

val create : string array -> t

val send_command : t -> string -> (t -> 'a) -> 'a

val set_option : t -> string -> bool -> unit

val set_logic : t -> string -> unit

val declare_sort : t -> string -> int -> unit

val declare_fun : t -> string -> string list -> string -> unit

val assume : t -> string -> unit

val check_sat : t -> result

val get_proof : t -> (Lexing.lexbuf -> 'a) -> 'a

val get_model : t -> SExpr.t

val quit : t -> unit



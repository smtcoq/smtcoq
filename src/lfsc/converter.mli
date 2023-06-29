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


module Make (T : Translator_sig.S) :
sig
  val ignore_all_decls : Ast.term -> Ast.term
  val ignore_preproc : Ast.term -> Ast.term
  val produce_inputs_preproc : Ast.term -> Ast.term
  val rm_duplicates : ('a -> 'a -> bool) -> 'a list -> 'a list
  val convert_pt : Ast.term -> int
  val clear : unit -> unit
end

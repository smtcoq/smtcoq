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


(** Maps that store SMT objects **)

(* SMT types *)
let btypes : (string, SmtBtype.btype) Hashtbl.t = Hashtbl.create 17
let get_btype id =
  try Hashtbl.find btypes id
  with | Not_found -> failwith ("SmtMaps.get_btype : sort symbol \""^id^"\" not found\n")
let add_btype id cl = Hashtbl.add btypes id cl
let clear_btypes () = Hashtbl.clear btypes

(* SMT function symbols *)
let funs : (string, SmtAtom.indexed_op) Hashtbl.t = Hashtbl.create 17
let get_fun id =
  try Hashtbl.find funs id
  with | Not_found -> failwith ("SmtMaps.get_fun : function symbol \""^id^"\" not found\n")
let add_fun id cl = Hashtbl.add funs id cl
let remove_fun id = Hashtbl.remove funs id
let clear_funs () = Hashtbl.clear funs

(* Clean-up of all the maps *)
let clear () =
  clear_btypes ();
  clear_funs ()

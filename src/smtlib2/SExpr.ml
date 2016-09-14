(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*     Alain   Mebsout                                                    *)
(*     Burak   Ekici                                                      *)
(*                                                                        *)
(*    Inria - École Polytechnique - Université Paris-Sud                  *)
(*    The University of Iowa                                              *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

type t = Atom of string | List of t list

let rec print fmt = function
  | Atom s -> Format.pp_print_string fmt s
  | List l ->
    Format.fprintf fmt "(@[<hov 2>";
    List.iter (Format.fprintf fmt "%a " print) l;
    Format.fprintf fmt "@])"

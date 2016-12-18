(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Alain Mebsout ♯                                                    *)
(*     Burak Ekici   ♯                                                    *)
(*                                                                        *)
(*     ♯ The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(** Type of S-expressions *)
type t = Atom of string | List of t list


let rec print fmt = function
  | Atom s -> Format.pp_print_string fmt s
  | List l ->
    Format.fprintf fmt "(";
    List.iter (Format.fprintf fmt "%a " print) l;
    Format.fprintf fmt ")"

let rec print_list fmt = function
  | [] -> ()
  | s :: r ->
    Format.fprintf fmt "%a@." print s;
    print_list fmt r

let rec size = function
  | Atom _ -> 1
  | List l -> List.fold_left (fun acc s -> size s + acc) 0 l

let rec size_list = function
  | [] -> 0
  | s :: r -> size s + size_list r

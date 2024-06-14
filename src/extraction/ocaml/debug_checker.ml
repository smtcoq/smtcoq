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


open Smtcoq_plugin


type clause = Api.form list

let pp_clause fmt (cl:clause) =
  Smt_utils.pp_list Api.pp_form " " "(" ")" fmt cl


exception Check of string


let get_assert (smt:Api.smtlib2) i =
  let (_, _, a) = smt in
  try a.(i) with Invalid_argument _ -> raise (Check "unknown assertion")


let rec resolve cl r =
  match cl with
    | [] -> raise (Check "could not find resolvant")
    | t::q ->
       (match t with
          | Api.FNeg f ->
             if List.mem f r then
               q@(List.filter (fun l -> f <> l) r)
             else if List.mem (Api.FNeg t) r then
               q@(List.filter (fun l -> (Api.FNeg t) <> l) r)
             else
               t::(resolve q r)
          | _ ->
             if List.mem (Api.FNeg t) r then
               q@(List.filter (fun l -> (Api.FNeg t) <> l) r)
             else
               t::(resolve q r)
       )


let rec debug_checker_rec fmt smt proof =
  let (name, n) = proof in
  try
    let cl =
      match n with
        | Api.CAssert i -> [get_assert smt i]
        | Api.CFalse -> [Api.FNeg Api.FFalse]
        | Api.CResolution l ->
           (let l' = List.map (debug_checker_rec fmt smt) l in
            match l' with
              | [] -> raise (Check "empty resolution")
              | t::q -> List.fold_left (fun cl r -> resolve cl r) t q
           )
    in
    Format.fprintf fmt "Checking node %s: success, produces the clause %a\n"
      name pp_clause cl;
    cl
  with
    | Check e ->
       Format.fprintf fmt "Checking node %s: failure [%s]\nStopping proof checking\n" name e;
       raise (Check "")

let debug_checker fmt (smt, proof) =
  try
    let cl = debug_checker_rec fmt smt proof in
    match cl with
      | [] ->
         Format.fprintf fmt
           "Proof checking was successful (but this checker is NOT certified)\n"
      | _ ->
         Format.fprintf fmt "Proof checking failed: does not prove the empty clause\n"
  with
    | _ -> ()


let debug_checker_stdout smt proof =
  Format.printf "%a" debug_checker (smt, proof)

let debug_checker_string smt proof =
  Format.asprintf "%a" debug_checker (smt, proof)


(** Callback from C to OCaml
    see https://ocaml.org/manual/4.09/intfc.html#sec426
 **)

let _ = Callback.register "debug_checker_string" debug_checker_string

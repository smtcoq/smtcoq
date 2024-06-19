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


type clause = Api.expr list

let pp_clause fmt (cl:clause) =
  Smt_utils.pp_list Api.pp_expr " " "(" ")" fmt cl


exception Check of string


let get_assert (smt:Api.smtlib2) i =
  let (_, _, a) = smt in
  try a.(i) with Invalid_argument _ -> raise (Check "unknown assertion")


let rec resolve cl r =
  match cl with
    | [] -> raise (Check "could not find resolvant")
    | t::q ->
       (match t with
          | Api.ENeg f ->
             if List.mem f r then
               q@(List.filter (fun l -> f <> l) r)
             else if List.mem (Api.ENeg t) r then
               q@(List.filter (fun l -> (Api.ENeg t) <> l) r)
             else
               t::(resolve q r)
          | _ ->
             if List.mem (Api.ENeg t) r then
               q@(List.filter (fun l -> (Api.ENeg t) <> l) r)
             else
               t::(resolve q r)
       )

let subclause c1 c2 =
  List.for_all (fun e ->
      e = Api.EFalse ||
        e = Api.ENeg (Api.ETrue) ||
        List.exists (fun e' -> e = e') c2
    ) c1


let cache = Hashtbl.create 17

let rec debug_checker_rec fmt smt proof =
  let (name, n) = proof in
  try
    Hashtbl.find cache name
  with | Not_found ->
  (try
    let cl =
      match n with
        | Api.Cweakening (c, l) ->
           let cl = debug_checker_rec fmt smt c in
           if subclause cl l then
             l
           else
             raise (Check "invalid weakening")
        | Api.Cassume i -> [get_assert smt i]
        | Api.Ctrue -> [Api.ETrue]
        | Api.Cfalse -> [Api.ENeg Api.EFalse]
        | Api.Cresolution l ->
           (let l' = List.map (debug_checker_rec fmt smt) l in
            match l' with
              | [] -> raise (Check "empty resolution")
              | t::q -> List.fold_left (fun cl r -> resolve cl r) t q
           )
        | Api.Clia_generic l ->
           Format.fprintf fmt "Warning: LIA is not checked in the debugging checker\n";
           l
        | Api.Ceq_reflexive e -> [Api.EEq (e, e)]
        | Api.Ceq_transitive l ->
           (match l with
              | []
              | [_] -> raise (Check "empty transitivity")
              | f::t::q ->
                 let last = ref t in
                 let r = List.fold_left (
                             fun acc e ->
                             let x = Api.ENeg (Api.EEq (!last, e)) in
                             last := e;
                             x::acc
                           ) [Api.ENeg (Api.EEq (f, t))] q in
                 (Api.EEq (f, !last))::r
           )
        | Api.Ceq_congruent (f, ts, us)
        | Api.Ceq_congruent_pred (f, ts, us) ->
           let r = List.map2 (fun t u -> Api.ENeg (Api.EEq (t, u))) ts us in
           (Api.EEq (Api.EFun (f, ts), Api.EFun (f, us)))::r
        | Api.Ceq_congruent_pred_b (f, ts, us) ->
           let r = List.map2 (fun t u -> Api.ENeg (Api.EEq (t, u))) ts us in
           (Api.ENeg (Api.EFun (f, ts)))::(Api.EFun (f, ts))::r
        | Api.Cand (c, k) ->
           (match debug_checker_rec fmt smt c with
              | [Api.EAnd l] ->  [List.nth l (k-1)]
              | _ -> raise (Check "Incorrect application of and")
           )
        | Api.Cnot_or (c, k) ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EOr l)] -> [Api.ENeg (List.nth l (k-1))]
              | _ -> raise (Check "Incorrect application of not_or")
           )
        | Api.Cor c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EOr l] -> l
              | _ -> raise (Check "Incorrect application of or")
           )
        | Api.Cnot_and c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EAnd l)] -> List.map (fun e -> Api.ENeg e) l
              | _ -> raise (Check "Incorrect application of not_and")
           )
        | Api.Cxor1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EXor (a, b)] -> [a; b]
              | _ -> raise (Check "Incorrect application of xor1")
           )
        | Api.Cxor2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EXor (a, b)] -> [Api.ENeg a; Api.ENeg b]
              | _ -> raise (Check "Incorrect application of xor2")
           )
        | Api.Cnot_xor1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EXor (a, b))] -> [a; Api.ENeg b]
              | _ -> raise (Check "Incorrect application of not_xor1")
           )
        | Api.Cnot_xor2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EXor (a, b))] -> [Api.ENeg a; b]
              | _ -> raise (Check "Incorrect application of not_xor2")
           )
        | Api.Cimplies c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EImp (a, b)] -> [Api.ENeg a; b]
              | _ -> raise (Check "Incorrect application of implies")
           )
        | Api.Cnot_implies1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EImp (a, b))] -> [a]
              | _ -> raise (Check "Incorrect application of not_implies1")
           )
        | Api.Cnot_implies2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EImp (a, b))] -> [Api.ENeg b]
              | _ -> raise (Check "Incorrect application of not_implies2")
           )
        | Api.Cequiv1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EEq (a, b)] -> [Api.ENeg a; b]
              | _ -> raise (Check "Incorrect application of equiv1")
           )
        | Api.Cequiv2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EEq (a, b)] -> [a; Api.ENeg b]
              | _ -> raise (Check "Incorrect application of equiv2")
           )
        | Api.Cnot_equiv1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EEq (a, b))] -> [a; b]
              | _ -> raise (Check "Incorrect application of not_equiv1")
           )
        | Api.Cnot_equiv2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENeg (Api.EEq (a, b))] -> [Api.ENeg a; Api.ENeg b]
              | _ -> raise (Check "Incorrect application of not_equiv2")
           )
        | Api.Cand_pos (l, k) -> [Api.ENeg (Api.EAnd l); List.nth l (k-1)]
        | Api.Cand_neg l ->
           let r = List.map (fun f -> Api.ENeg f) l in
           (Api.EAnd l)::r
        | Api.Cor_pos l -> (Api.ENeg (Api.EOr l))::l
        | Api.Cor_neg (l, k) -> [Api.EOr l; Api.ENeg (List.nth l (k-1))]
        | Api.Cxor_pos1 (a, b) -> [Api.ENeg (Api.EXor (a, b)); a; b]
        | Api.Cxor_pos2 (a, b) -> [Api.ENeg (Api.EXor (a, b)); Api.ENeg a; Api.ENeg b]
        | Api.Cxor_neg1 (a, b) -> [Api.EXor (a, b); a; Api.ENeg b]
        | Api.Cxor_neg2 (a, b) -> [Api.EXor (a, b); Api.ENeg a; b]
        | Api.Cimplies_pos (a, b) -> [Api.ENeg (Api.EImp (a, b)); Api.ENeg a; b]
        | Api.Cimplies_neg1 (a, b) -> [Api.EImp (a, b); a]
        | Api.Cimplies_neg2 (a, b) -> [Api.EImp (a, b); Api.ENeg b]
        | Api.Cequiv_pos1 (a, b) -> [Api.ENeg (Api.EEq (a, b)); a; Api.ENeg b]
        | Api.Cequiv_pos2 (a, b) -> [Api.ENeg (Api.EEq (a, b)); Api.ENeg a; b]
        | Api.Cequiv_neg1 (a, b) -> [Api.EEq (a, b); Api.ENeg a; Api.ENeg b]
        | Api.Cequiv_neg2 (a, b) -> [Api.EEq (a, b); a; b]
    in
    Format.fprintf fmt "Checking node %s: success, produces the clause %a\n"
      name pp_clause cl;
    Hashtbl.add cache name cl;
    cl
  with
    | Check e ->
       Format.fprintf fmt "Checking node %s: failure [%s]\nStopping proof checking\n" name e;
       raise (Check "")
  )

let debug_checker fmt (smt, proof) =
  Hashtbl.clear cache;
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

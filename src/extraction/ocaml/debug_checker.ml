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
  Smt_utils.pp_list Api.pp_expr " " "{" "}" fmt cl


exception Check of string


let get_assert (smt:Api.smtlib2) i =
  let (_, _, a) = smt in
  try a.(i) with Invalid_argument _ -> raise (Check "unknown assertion")


let rec resolve cl r =
  match cl with
    | [] -> raise (Check "resolution: could not find resolvant")
    | t::q ->
       (match t with
          | Api.ENot f ->
             if List.mem f r then
               q@(List.filter (fun l -> f <> l) r)
             else if List.mem (Api.ENot t) r then
               q@(List.filter (fun l -> (Api.ENot t) <> l) r)
             else
               t::(resolve q r)
          | _ ->
             if List.mem (Api.ENot t) r then
               q@(List.filter (fun l -> (Api.ENot t) <> l) r)
             else
               t::(resolve q r)
       )

let subclause c1 c2 =
  List.for_all (fun e ->
      e = Api.EFalse ||
        e = Api.ENot (Api.ETrue) ||
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
             raise (Check "weakening: invalid")
        | Api.Cassume i -> [get_assert smt i]
        | Api.Ctrue -> [Api.ETrue]
        | Api.Cfalse -> [Api.ENot Api.EFalse]
        | Api.Cresolution l ->
           (let l' = List.map (debug_checker_rec fmt smt) l in
            match l' with
              | [] -> raise (Check "resolution: empty")
              | t::q -> List.fold_left (fun cl r -> resolve cl r) t q
           )
        | Api.Clia_generic l ->
           Format.fprintf fmt "Warning: LIA is not checked in the debugging checker\n";
           l
        | Api.Ceq_reflexive e -> [Api.EEq (e, e)]
        | Api.Ceq_transitive l ->
           (match l with
              | f::t::q ->
                 let last = ref t in
                 let r = List.fold_left (
                             fun acc e ->
                             let x = Api.ENot (Api.EEq (!last, e)) in
                             last := e;
                             x::acc
                           ) [Api.ENot (Api.EEq (f, t))] q in
                 (Api.EEq (f, !last))::r
              | _ -> raise (Check "eq_transitive: should contain at least two terms")
           )
        | Api.Ceq_congruent p ->
           let (concl, prem) = List.partition (function Api.ENot _ -> false | _ -> true) p in
           let (a, b) =
             match concl with
               | [Api.EEq (a, b)] -> (a, b)
               | [_] -> raise (Check "eq_congruent: the conclusion is not an equality")
               | _ -> raise (Check "eq_congruent: multiple conclusions")
           in
           let (ts, us) =
             match a, b with
               | Api.EFun (f1, ts),   Api.EFun (f2, us) when f1 = f2 -> (ts, us)
               | Api.EAdd (t1, t2),   Api.EAdd (u1, u2)
               | Api.EMinus (t1, t2), Api.EMinus (u1, u2)
               | Api.EMult (t1, t2),  Api.EMult (u1, u2) -> ([t1; t2], [u1; u2])
               | Api.EOpp t,          Api.EOpp u       -> ([t], [u])
               | Api.ETrue,  _ | _, Api.ETrue
               | Api.EFalse, _ | _, Api.EFalse
               | Api.ENot _, _ | _, Api.ENot _
               | Api.EAnd _, _ | _, Api.EAnd _
               | Api.EOr _,  _ | _, Api.EOr _
               | Api.EXor _, _ | _, Api.EXor _
               | Api.EImp _, _ | _, Api.EImp _
               | Api.EEq _,  _ | _, Api.EEq _
               | Api.ELt _,  _ | _, Api.ELt _
               | Api.ELe _,  _ | _, Api.ELe _
               | Api.EGt _,  _ | _, Api.EGt _
               | Api.EGe _,  _ | _, Api.EGe _ ->
                  raise (Check "eq_congruent: applies only to non-Boolean terms (work in progress)")
               | _, _ -> raise (Check "eq_congruent: not the same function symbol")
           in
           List.iter2 (fun t u ->
               if not (List.exists (function
                             Api.ENot (Api.EEq (a, b))
                               when (a = t && b = u) || (a = u && b = t)
                             -> true | _ -> false) prem
                    )
               then
                 raise (Check "eq_congruent: missing equality")
             ) ts us;
           p
        | Api.Ceq_congruent_pred p ->
           let (concl, prem) = List.partition (function Api.ENot _ -> false | _ -> true) p in
           let (a, b) =
             match concl with
               | [Api.EEq (a, b)] -> (a, b)
               | [_] -> raise (Check "eq_congruent_pred: the conclusion is not an equality")
               | [] -> raise (Check "eq_congruent_pred: no conclusion")
               | _ -> raise (Check "eq_congruent_pred: multiple conclusions")
           in
           let (ts, us) =
             match a, b with
               | Api.EFun (f1, ts),   Api.EFun (f2, us) when f1 = f2 -> (ts, us)
               | Api.ELt (t1, t2), Api.ELt (u1, u2)
               | Api.ELe (t1, t2), Api.ELe (u1, u2)
               | Api.EGt (t1, t2), Api.EGt (u1, u2)
               | Api.EGe (t1, t2), Api.EGe (u1, u2) -> ([t1; t2], [u1; u2])
               | Api.ETrue,    _ | _, Api.ETrue
               | Api.EFalse,   _ | _, Api.EFalse
               | Api.ENot _,   _ | _, Api.ENot _
               | Api.EAnd _,   _ | _, Api.EAnd _
               | Api.EOr _,    _ | _, Api.EOr _
               | Api.EXor _,   _ | _, Api.EXor _
               | Api.EImp _,   _ | _, Api.EImp _
               | Api.EEq _,    _ | _, Api.EEq _
               | Api.EAdd _,   _ | _, Api.EAdd _
               | Api.EMinus _, _ | _, Api.EMinus _
               | Api.EMult _,  _ | _, Api.EMult _
               | Api.EOpp _,   _ | _, Api.EOpp _ ->
                  raise (Check "eq_congruent_pred: applies only to non-Boolean sub-terms (work in progress)")
               | _, _ -> raise (Check "eq_congruent_pred: not the same function symbol")
           in
           List.iter2 (fun t u ->
               if not (List.exists (function
                             Api.ENot (Api.EEq (a, b))
                               when (a = t && b = u) || (a = u && b = t)
                             -> true | _ -> false) prem
                    )
               then
                 raise (Check "eq_congruent_pred: missing equality")
             ) ts us;
           p
        | Api.Ceq_congruent_pred_b p ->
           let (concl, prem) =
             List.partition (function Api.ENot _ -> false | _ -> true) p
           in
           let (prem, prem_P) =
             List.partition
               (function Api.ENot (Api.EEq _) -> true | _ -> false) prem
           in
           let (a, b) =
             match concl, prem_P with
               | [a], [Api.ENot b] -> (b, a)
               | [], [_] -> raise (Check "eq_congruent_pred_b: no conclusion")
               | _, [_] -> raise (Check "eq_congruent_pred_b: multiple conclusions")
               | _, [] -> raise (Check "eq_congruent_pred_b: no predicate premisse")
               | _, _ -> raise (Check "eq_congruent_pred_b: multiple predicate premisses")
           in
           let (ts, us) =
             match a, b with
               | Api.EFun (f1, ts),   Api.EFun (f2, us) when f1 = f2 -> (ts, us)
               | Api.ELt (t1, t2), Api.ELt (u1, u2)
               | Api.ELe (t1, t2), Api.ELe (u1, u2)
               | Api.EGt (t1, t2), Api.EGt (u1, u2)
               | Api.EGe (t1, t2), Api.EGe (u1, u2) -> ([t1; t2], [u1; u2])
               | Api.ETrue,    _ | _, Api.ETrue
               | Api.EFalse,   _ | _, Api.EFalse
               | Api.ENot _,   _ | _, Api.ENot _
               | Api.EAnd _,   _ | _, Api.EAnd _
               | Api.EOr _,    _ | _, Api.EOr _
               | Api.EXor _,   _ | _, Api.EXor _
               | Api.EImp _,   _ | _, Api.EImp _
               | Api.EEq _,    _ | _, Api.EEq _
               | Api.EAdd _,   _ | _, Api.EAdd _
               | Api.EMinus _, _ | _, Api.EMinus _
               | Api.EMult _,  _ | _, Api.EMult _
               | Api.EOpp _,   _ | _, Api.EOpp _ ->
                  raise (Check "eq_congruent_pred_b: applies only to non-Boolean sub-terms (work in progress)")
               | _, _ -> raise (Check "eq_congruent_pred_b: not the same function symbol")
           in
           List.iter2 (fun t u ->
               if not (List.exists (function
                             Api.ENot (Api.EEq (a, b))
                               when (a = t && b = u) || (a = u && b = t)
                             -> true | _ -> false) prem
                    )
               then
                 raise (Check "eq_congruent_pred_b: missing equality")
             ) ts us;
           p
        | Api.Cand (c, k) ->
           (match debug_checker_rec fmt smt c with
              | [Api.EAnd l] ->  [List.nth l (k-1)]
              | _ -> raise (Check "and: incorrect application")
           )
        | Api.Cnot_or (c, k) ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EOr l)] -> [Api.ENot (List.nth l (k-1))]
              | _ -> raise (Check "not_or: incorrect application")
           )
        | Api.Cor c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EOr l] -> l
              | _ -> raise (Check "or: incorrect application")
           )
        | Api.Cnot_and c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EAnd l)] -> List.map (fun e -> Api.ENot e) l
              | _ -> raise (Check "not_and: incorrect application")
           )
        | Api.Cxor1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EXor (a, b)] -> [a; b]
              | _ -> raise (Check "xor1: incorrect application")
           )
        | Api.Cxor2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EXor (a, b)] -> [Api.ENot a; Api.ENot b]
              | _ -> raise (Check "xor2: incorrect application")
           )
        | Api.Cnot_xor1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EXor (a, b))] -> [a; Api.ENot b]
              | _ -> raise (Check "not_xor1: incorrect application")
           )
        | Api.Cnot_xor2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EXor (a, b))] -> [Api.ENot a; b]
              | _ -> raise (Check "not_xor2: incorrect application")
           )
        | Api.Cimplies c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EImp (a, b)] -> [Api.ENot a; b]
              | _ -> raise (Check "implies: incorrect application")
           )
        | Api.Cnot_implies1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EImp (a, b))] -> [a]
              | _ -> raise (Check "not_implies1: incorrect application")
           )
        | Api.Cnot_implies2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EImp (a, b))] -> [Api.ENot b]
              | _ -> raise (Check "not_implies2: incorrect application")
           )
        | Api.Cequiv1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EEq (a, b)] -> [Api.ENot a; b]
              | _ -> raise (Check "equiv1: incorrect application")
           )
        | Api.Cequiv2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.EEq (a, b)] -> [a; Api.ENot b]
              | _ -> raise (Check "equiv2: incorrect application")
           )
        | Api.Cnot_equiv1 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EEq (a, b))] -> [a; b]
              | _ -> raise (Check "not_equiv1: incorrect application")
           )
        | Api.Cnot_equiv2 c ->
           (match debug_checker_rec fmt smt c with
              | [Api.ENot (Api.EEq (a, b))] -> [Api.ENot a; Api.ENot b]
              | _ -> raise (Check "not_equiv2: incorrect application")
           )
        | Api.Cand_pos (l, k) -> [Api.ENot (Api.EAnd l); List.nth l (k-1)]
        | Api.Cand_neg l ->
           let r = List.map (fun f -> Api.ENot f) l in
           (Api.EAnd l)::r
        | Api.Cor_pos l -> (Api.ENot (Api.EOr l))::l
        | Api.Cor_neg (l, k) -> [Api.EOr l; Api.ENot (List.nth l (k-1))]
        | Api.Cxor_pos1 (a, b) -> [Api.ENot (Api.EXor (a, b)); a; b]
        | Api.Cxor_pos2 (a, b) -> [Api.ENot (Api.EXor (a, b)); Api.ENot a; Api.ENot b]
        | Api.Cxor_neg1 (a, b) -> [Api.EXor (a, b); a; Api.ENot b]
        | Api.Cxor_neg2 (a, b) -> [Api.EXor (a, b); Api.ENot a; b]
        | Api.Cimplies_pos (a, b) -> [Api.ENot (Api.EImp (a, b)); Api.ENot a; b]
        | Api.Cimplies_neg1 (a, b) -> [Api.EImp (a, b); a]
        | Api.Cimplies_neg2 (a, b) -> [Api.EImp (a, b); Api.ENot b]
        | Api.Cequiv_pos1 (a, b) -> [Api.ENot (Api.EEq (a, b)); a; Api.ENot b]
        | Api.Cequiv_pos2 (a, b) -> [Api.ENot (Api.EEq (a, b)); Api.ENot a; b]
        | Api.Cequiv_neg1 (a, b) -> [Api.EEq (a, b); Api.ENot a; Api.ENot b]
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

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtAtom
open SmtForm
open SmtCertif
open SmtTrace


(*** Syntax of veriT proof traces ***)

exception Sat

type typ = | Inpu | Deep | True | Fals | Andp | Andn | Orp | Orn | Xorp1 | Xorp2 | Xorn1 | Xorn2 | Impp | Impn1 | Impn2 | Equp1 | Equp2 | Equn1 | Equn2 | Itep1 | Itep2 | Iten1 | Iten2 | Eqre | Eqtr | Eqco | Eqcp | Dlge | Lage | Lata | Dlde | Lade | Fins | Eins | Skea | Skaa | Qnts | Qntm | Reso | Weak | And | Nor | Or | Nand | Xor1 | Xor2 | Nxor1 | Nxor2 | Imp | Nimp1 | Nimp2 | Equ1 | Equ2 | Nequ1 | Nequ2 | Ite1 | Ite2 | Nite1 | Nite2 | Tpal | Tlap | Tple | Tpne | Tpde | Tpsa | Tpie | Tpma | Tpbr | Tpbe | Tpsc | Tppp | Tpqt | Tpqs | Tpsk | Subp


(* About equality *)

let get_eq l =
  match Form.pform l with
    | Fatom ha ->
      (match Atom.atom ha with
        | Abop (BO_eq _,a,b) -> (a,b)
        | _ -> failwith "VeritSyntax.get_eq: equality was expected")
    | _ -> failwith "VeritSyntax.get_eq: equality was expected"

let get_at l =
  match Form.pform l with
    | Fatom ha -> ha
    | _ -> failwith "VeritSyntax.get_eq: equality was expected"

let is_eq l =
  match Form.pform l with
    | Fatom ha ->
      (match Atom.atom ha with
        | Abop (BO_eq _,_,_) -> true
        | _ -> false)
    | _ -> failwith "VeritSyntax.get_eq: atom was expected"


(* Transitivity *)

let rec process_trans a b prem res =
  try
    let (l,(c,c')) = List.find (fun (l,(a',b')) -> (a' = b || b' = b)) prem in
    let prem = List.filter (fun l' -> l' <> (l,(c,c'))) prem in
    let c = if c = b then c' else c in
    if a = c
    then List.rev (l::res)
    else process_trans a c prem (l::res)
  with
    |Not_found -> if a = b then [] else assert false


let mkTrans p =
  let (concl,prem) = List.partition Form.is_pos p in
  match concl with
    |[c] ->
      let a,b = get_eq c in
      let prem_val = List.map (fun l -> (l,get_eq l)) prem in
      let cert = (process_trans a b prem_val []) in
      Other (EqTr (c,cert))
    |_ -> failwith "VeritSyntax.mkTrans: no conclusion or more than one conclusion in transitivity"


(* Congruence *)

let rec process_congr a_args b_args prem res =
  match a_args,b_args with
    | a::a_args,b::b_args ->
      (* if a = b *)
      (* then process_congr a_args b_args prem (None::res) *)
      (* else *)
        let (l,(a',b')) = List.find (fun (l,(a',b')) -> (a = a' && b = b')||(a = b' && b = a')) prem in
        process_congr a_args b_args prem ((Some l)::res)
    | [],[] -> List.rev res
    | _ -> failwith "VeritSyntax.process_congr: incorrect number of arguments in function application"


let mkCongr p =
  let (concl,prem) = List.partition Form.is_pos p in
  match concl with
    |[c] ->
      let a,b = get_eq c in
      let prem_val = List.map (fun l -> (l,get_eq l)) prem in
      (match Atom.atom a, Atom.atom b with
        | Abop(aop,a1,a2), Abop(bop,b1,b2) when (aop = bop) ->
          let a_args = [a1;a2] in
          let b_args = [b1;b2] in
          let cert = process_congr a_args b_args prem_val [] in
          Other (EqCgr (c,cert))
        | Auop (aop,a), Auop (bop,b) when (aop = bop) ->
          let a_args = [a] in
          let b_args = [b] in
          let cert = process_congr a_args b_args prem_val [] in
          Other (EqCgr (c,cert))
        | Aapp (a_f,a_args), Aapp (b_f,b_args) ->
          if a_f = b_f then
            let cert = process_congr (Array.to_list a_args) (Array.to_list b_args) prem_val [] in
            Other (EqCgr (c,cert))
          else failwith "VeritSyntax.mkCongr: left function is different from right fucntion"
        | _, _ -> failwith "VeritSyntax.mkCongr: atoms are not applications")
    |_ -> failwith "VeritSyntax.mkCongr: no conclusion or more than one conclusion in congruence"


let mkCongrPred p =
  let (concl,prem) = List.partition Form.is_pos p in
  let (prem,prem_P) = List.partition is_eq prem in
  match concl with
    |[c] ->
      (match prem_P with
        |[p_p] ->
          let prem_val = List.map (fun l -> (l,get_eq l)) prem in
          (match Atom.atom (get_at c), Atom.atom (get_at p_p) with
            | Abop(aop,a1,a2), Abop(bop,b1,b2) when (aop = bop) ->
              let a_args = [a1;a2] in
              let b_args = [b1;b2] in
              let cert = process_congr a_args b_args prem_val [] in
              Other (EqCgrP (p_p,c,cert))
            | Aapp (a_f,a_args), Aapp (b_f,b_args) ->
              if a_f = b_f then
                let cert = process_congr (Array.to_list a_args) (Array.to_list b_args) prem_val [] in
                Other (EqCgrP (p_p,c,cert))
              else failwith "VeritSyntax.mkCongrPred: unmatching predicates"
            | _ -> failwith "VeritSyntax.mkCongrPred : not pred app")
        |_ ->  failwith "VeritSyntax.mkCongr: no or more than one predicate app premice in congruence")
    |[] ->  failwith "VeritSyntax.mkCongrPred: no conclusion in congruence"
    |_ -> failwith "VeritSyntax.mkCongrPred: more than one conclusion in congruence"


(* Linear arithmetic *)

let mkMicromega cl =
  let _tbl, _f, cert = Lia.build_lia_certif cl in
  let c =
    match cert with
      | None -> failwith "VeritSyntax.mkMicromega: micromega can't solve this"
      | Some c -> c in
  Other (LiaMicromega (cl,c))


let mkSplArith orig cl =
  let res =
    match cl with
      | res::nil -> res
      | _ -> failwith "VeritSyntax.mkSplArith: wrong number of literals in the resulting clause" in
  try
    let orig' =
      match orig.value with
        | Some [orig'] -> orig'
        | _ -> failwith "VeritSyntax.mkSplArith: wrong number of literals in the premise clause" in
    let _tbl, _f, cert = Lia.build_lia_certif [Form.neg orig';res] in
    let c =
      match cert with
        | None -> failwith "VeritSyntax.mkSplArith: micromega can't solve this"
        | Some c -> c in
    Other (SplArith (orig,res,c))
  with
    | _ -> Other (ImmFlatten (orig, res))


(* Elimination of operators *)

let mkDistinctElim old value =
  let rec find_res l1 l2 =
    match l1,l2 with
      | t1::q1,t2::q2 -> if t1 == t2 then find_res q1 q2 else t2
      | _, _ -> assert false in
  let l1 = match old.value with
    | Some l -> l
    | None -> assert false in
  Other (SplDistinctElim (old,find_res l1 value))


(* Clause difference (wrt to their sets of literals) *)

let clause_diff c1 c2 =
  List.filter (fun t1 -> not (List.exists (fun t2 -> t1 == t2) c2)) c1


(* Generating clauses *)

let clauses : (int,Form.t clause) Hashtbl.t = Hashtbl.create 17
let get_clause id =
  try Hashtbl.find clauses id
  with | Not_found -> failwith ("VeritSyntax.get_clause : clause number "^(string_of_int id)^" not found\n")
let add_clause id cl = Hashtbl.add clauses id cl
let clear_clauses () = Hashtbl.clear clauses

let mk_clause (id,typ,value,ids_params) =
  let kind =
    match typ with
      (* Roots *)
      | Inpu -> Root
      (* Cnf conversion *)
      | True -> Other SmtCertif.True
      | Fals -> Other False
      | Andn | Orp | Impp | Xorp1 | Xorn1 | Equp1 | Equn1 | Itep1 | Iten1 ->
        (match value with
          | l::_ -> Other (BuildDef l)
          | _ -> assert false)
      | Xorp2 | Xorn2 | Equp2 | Equn2 | Itep2 | Iten2 ->
        (match value with
          | l::_ -> Other (BuildDef2 l)
          | _ -> assert false)
      | Orn | Andp ->
        (match value,ids_params with
          | l::_, [p] -> Other (BuildProj (l,p))
          | _ -> assert false)
      | Impn1 ->
        (match value with
          | l::_ -> Other (BuildProj (l,0))
          | _ -> assert false)
      | Impn2 ->
        (match value with
          | l::_ -> Other (BuildProj (l,1))
          | _ -> assert false)
      | Nand | Or | Imp | Xor1 | Nxor1 | Equ2 | Nequ2 | Ite1 | Nite1 ->
        (match ids_params with
          | [id] -> Other (ImmBuildDef (get_clause id))
          | _ -> assert false)
      | Xor2 | Nxor2 | Equ1 | Nequ1 | Ite2 | Nite2 ->
        (match ids_params with
          | [id] -> Other (ImmBuildDef2 (get_clause id))
          | _ -> assert false)
      | And | Nor ->
        (match ids_params with
          | [id;p] -> Other (ImmBuildProj (get_clause id,p))
          | _ -> assert false)
      | Nimp1 ->
        (match ids_params with
          | [id] -> Other (ImmBuildProj (get_clause id,0))
          | _ -> assert false)
      | Nimp2 ->
        (match ids_params with
          | [id] -> Other (ImmBuildProj (get_clause id,1))
          | _ -> assert false)
      (* Equality *)
      | Eqre -> mkTrans value
      | Eqtr -> mkTrans value
      | Eqco -> mkCongr value
      | Eqcp -> mkCongrPred value
      (* Linear integer arithmetic *)
      | Dlge | Lage | Lata -> mkMicromega value
      | Lade               -> mkMicromega value (* TODO: utiliser un solveur plus simple *)
      | Dlde ->
        (match value with
          | l::_ -> Other (LiaDiseq l)
          | _ -> assert false)
      (* Resolution *)
      | Reso ->
        (match ids_params with
          | cl1::cl2::q ->
            let res = {rc1 = get_clause cl1; rc2 = get_clause cl2; rtail = List.map get_clause q} in
            Res res
          | _ -> assert false)
      (* Clause weakening *)
      | Weak ->
        (match ids_params with
         | [id] -> (* Other (Weaken (get_clause id, value)) *)
           let cid = get_clause id in
           (match cid.value with
           | None -> Other (Weaken (cid, value))
           | Some c -> Other (Weaken (cid, value @ c))
            (* need to add c, otherwise dosen't terminate or returns false,
               we would like instead: clause_diff value c *)
           )
          | _ -> assert false)
      (* Simplifications *)
      | Tpal ->
        (match ids_params with
          | id::_ -> Same (get_clause id)
          | _ -> assert false)
      | Tple ->
        (match ids_params with
          | id::_ -> Same (get_clause id)
          | _ -> assert false)
      | Tpde ->
        (match ids_params with
          | id::_ -> mkDistinctElim (get_clause id) value
          | _ -> assert false)
      | Tpsa | Tlap ->
        (match ids_params with
          | id::_ -> mkSplArith (get_clause id) value
          | _ -> assert false)
       (* Not implemented *)
      | Deep -> failwith "VeritSyntax.ml: rule deep_res not implemented yet"
      | Fins -> failwith "VeritSyntax.ml: rule forall_inst not implemented yet"
      | Eins -> failwith "VeritSyntax.ml: rule exists_inst not implemented yet"
      | Skea -> failwith "VeritSyntax.ml: rule skolem_ex_ax not implemented yet"
      | Skaa -> failwith "VeritSyntax.ml: rule skolem_all_ax not implemented yet"
      | Qnts -> failwith "VeritSyntax.ml: rule qnt_simplify_ax not implemented yet"
      | Qntm -> failwith "VeritSyntax.ml: rule qnt_merge_ax not implemented yet"
      | Tpne -> failwith "VeritSyntax.ml: rule tmp_nary_elim not implemented yet"
      | Tpie -> failwith "VeritSyntax.ml: rule tmp_ite_elim not implemented yet"
      | Tpma -> failwith "VeritSyntax.ml: rule tmp_macrosubst not implemented yet"
      | Tpbr -> failwith "VeritSyntax.ml: rule tmp_betared not implemented yet"
      | Tpbe -> failwith "VeritSyntax.ml: rule tmp_bfun_elim not implemented yet"
      | Tpsc -> failwith "VeritSyntax.ml: rule tmp_sk_connector not implemented yet"
      | Tppp -> failwith "VeritSyntax.ml: rule tmp_pm_process not implemented yet"
      | Tpqt -> failwith "VeritSyntax.ml: rule tmp_qnt_tidy not implemented yet"
      | Tpqs -> failwith "VeritSyntax.ml: rule tmp_qnt_simplify not implemented yet"
      | Tpsk -> failwith "VeritSyntax.ml: rule tmp_skolemize not implemented yet"
      | Subp -> failwith "VeritSyntax.ml: rule subproof not implemented yet"
  in
  let cl =
    (* TODO: change this into flatten when necessary *)
    if SmtTrace.isRoot kind then SmtTrace.mkRootV value
    else SmtTrace.mk_scertif kind (Some value) in
  add_clause id cl;
  if id > 1 then SmtTrace.link (get_clause (id-1)) cl;
  id


type atom_form_lit =
  | Atom of SmtAtom.Atom.t
  | Form of SmtAtom.Form.pform
  | Lit of SmtAtom.Form.t

let lit_of_atom_form_lit rf = function
  | Atom a -> Form.get rf (Fatom a)
  | Form f -> Form.get rf f
  | Lit l -> l

let solver : (int,atom_form_lit) Hashtbl.t = Hashtbl.create 17
let get_solver id =
  try Hashtbl.find solver id
  with | Not_found -> failwith ("VeritSyntax.get_solver : solver variable number "^(string_of_int id)^" not found\n")
let add_solver id cl = Hashtbl.add solver id cl
let clear_solver () = Hashtbl.clear solver

let btypes : (string,btype) Hashtbl.t = Hashtbl.create 17
let get_btype id =
  try Hashtbl.find btypes id
  with | Not_found -> failwith ("VeritSyntax.get_btype : sort symbol \""^id^"\" not found\n")
let add_btype id cl = Hashtbl.add btypes id cl
let clear_btypes () = Hashtbl.clear btypes

let funs : (string,indexed_op) Hashtbl.t = Hashtbl.create 17
let get_fun id =
  try Hashtbl.find funs id
  with | Not_found -> failwith ("VeritSyntax.get_fun : function symbol \""^id^"\" not found\n")
let add_fun id cl = Hashtbl.add funs id cl
let clear_funs () = Hashtbl.clear funs


let ra = Atom.create ()
let rf = Form.create ()

let hlets : (string, atom_form_lit) Hashtbl.t = Hashtbl.create 17


let clear () =
  clear_clauses ();
  clear_solver ();
  clear_btypes ();
  clear_funs ();
  Atom.clear ra;
  Form.clear rf;
  Hashtbl.clear hlets

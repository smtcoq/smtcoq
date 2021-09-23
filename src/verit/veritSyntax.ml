(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtAtom
open SmtForm
open SmtCertif
open SmtTrace


(*** Syntax of veriT proof traces ***)
exception Debug of string
exception Sat

type typ = 
  | Assume (* Inpu *)
  | True
  | Fals
  | Notnot (* New *)
  | Threso (* New *)
  | Reso
  | Taut (* New *)
  | Cont (* New *)
  | Refl (* New *)
  | Trans (* New *)
  | Cong (* New *)
  | Eqre
  | Eqtr
  | Eqco
  | Eqcp
  | And
  | Nor
  | Or
  | Nand
  | Xor1 
  | Xor2
  | Nxor1 
  | Nxor2
  | Imp
  | Nimp1
  | Nimp2
  | Equ1
  | Equ2
  | Nequ1
  | Nequ2
  | Andp
  | Andn
  | Orp
  | Orn
  | Xorp1
  | Xorp2
  | Xorn1
  | Xorn2
  | Impp
  | Impn1
  | Impn2
  | Equp1
  | Equp2
  | Equn1
  | Equn2
  | Ite1
  | Ite2
  | Itep1
  | Itep2
  | Iten1
  | Iten2
  | Nite1
  | Nite2
  | Conndef (* New *)
  | Andsimp (* New *)
  | Orsimp (* New *)
  | Notsimp (* New *)
  | Impsimp (* New *)
  | Eqsimp (* New *)
  | Boolsimp (* New *)
  | Acsimp (* New *)
  | Itesimp (* New *)
  | Equalsimp (* New *)
  | Hole

(*let get_type x = 
  match Form.pform l with
  | Fatom ha -> 
  | Fapp (_, _) -> raise (Debug "This is ")*)

(* About equality *)

let get_eq l =
  match Form.pform l with
  | Fatom ha ->
     (match Atom.atom ha with
      | Abop (BO_eq _,a,b) -> (a,b)
      | _ -> raise (Debug "VeritSyntax.get_eq: equality was expected"))
  | _ -> raise (Debug "VeritSyntax.get_eq: equality was expected")

let get_at l =
  match Form.pform l with
  | Fatom ha -> ha
  | _ -> raise (Debug "VeritSyntax.get_eq: equality was expected")

let is_eq l =
  match Form.pform l with
  | Fatom ha ->
     (match Atom.atom ha with
      | Abop (BO_eq _,_,_) -> true
      | _ -> false)
  | _ -> raise (Debug "VeritSyntax.get_eq: atom was expected")


(* Transitivity *)
(* list_find_remove p l finds the first element x in l, such that p(x) holds and returns (x, l') where l' is l without x *)
let rec list_find_remove p = function
    [] -> raise Not_found
  | h::t -> if p h
            then h, t
            else let (a, rest) = list_find_remove p t in
                 a, h::rest

let rec process_trans a b prem res =
  if List.length prem = 0 then (
    assert (Atom.equal a b);
    List.rev res
  ) else
    let ((l,(c,c')),prem) =
      (* Search if there is a trivial reflexivity premise *)
      try list_find_remove (fun (l,(a',b')) -> ((Atom.equal a' b) && (Atom.equal b' b))) prem
      (* If not, search for the equality [l:c = c'] s.t. [c = b] or [c' = b] *)
      with | Not_found -> list_find_remove (fun (l,(a',b')) -> ((Atom.equal a' b) || (Atom.equal b' b))) prem in
    let c = if Atom.equal c b then c' else c in
    process_trans a c prem (l::res)

let mkTrans p =
  let (concl,prem) = List.partition Form.is_pos p in
  match concl with
  |[c] ->
    let a,b = get_eq c in
    let prem_val = List.map (fun l -> (l,get_eq l)) prem in
    let cert = (process_trans a b prem_val []) in
    Other (EqTr (c,cert))
  |_ -> raise (Debug "VeritSyntax.mkTrans: no conclusion or more than one conclusion in transitivity")


(* Congruence *)

let rec process_congr a_args b_args prem res =
  match a_args,b_args with
  | a::a_args,b::b_args ->
     (* if a = b *)
     (* then process_congr a_args b_args prem (None::res) *)
     (* else *)
     let (l,(a',b')) = List.find (fun (l,(a',b')) -> ((Atom.equal a a') && (Atom.equal b b'))||((Atom.equal a b') && (Atom.equal b a'))) prem in
     process_congr a_args b_args prem ((Some l)::res)
  | [],[] -> List.rev res
  | _ -> raise (Debug "VeritSyntax.process_congr: incorrect number of arguments in function application")


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
        if indexed_op_index a_f = indexed_op_index b_f then
          let cert = process_congr (Array.to_list a_args) (Array.to_list b_args) prem_val [] in
          Other (EqCgr (c,cert))
        else raise (Debug "VeritSyntax.mkCongr: left function is different from right function")
     | _, _ -> raise (Debug "VeritSyntax.mkCongr: atoms are not applications"))
  |_ -> raise (Debug "VeritSyntax.mkCongr: no conclusion or more than one conclusion in congruence")


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
           if indexed_op_index a_f = indexed_op_index b_f then
             let cert = process_congr (Array.to_list a_args) (Array.to_list b_args) prem_val [] in
             Other (EqCgrP (p_p,c,cert))
           else raise (Debug "VeritSyntax.mkCongrPred: unmatching predicates")
        | _ -> raise (Debug "VeritSyntax.mkCongrPred : not pred app"))
     |_ ->  raise (Debug "VeritSyntax.mkCongr: no or more than one predicate app premise in congruence"))
  |[] ->  raise (Debug "VeritSyntax.mkCongrPred: no conclusion in congruence")
  |_ -> raise (Debug "VeritSyntax.mkCongrPred: more than one conclusion in congruence")


(* Linear arithmetic *)

let mkMicromega cl =
  let _tbl, _f, cert = Lia.build_lia_certif cl in
  let c =
    match cert with
    | None -> raise (Debug "VeritSyntax.mkMicromega: micromega can't solve this")
    | Some c -> c in
  Other (LiaMicromega (cl,c))


let mkSplArith orig cl =
  let res =
    match cl with
    | res::nil -> res
    | _ -> raise (Debug "VeritSyntax.mkSplArith: wrong number of literals in the resulting clause") in
  try
    let orig' =
      match orig.value with
      | Some [orig'] -> orig'
      | _ -> raise (Debug "VeritSyntax.mkSplArith: wrong number of literals in the premise clause") in
    let _tbl, _f, cert = Lia.build_lia_certif [Form.neg orig';res] in
    let c =
      match cert with
      | None -> raise (Debug "VeritSyntax.mkSplArith: micromega can't solve this")
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

(* let clause_diff c1 c2 =
 *   let r =
 *     List.filter (fun t1 -> not (List.exists (SmtAtom.Form.equal t1) c2)) c1
 *   in
 *   Format.eprintf "[";
 *   List.iter (Format.eprintf " %a ,\n" SmtAtom.(Form.to_smt Atom.to_smt)) c1;
 *   Format.eprintf "] -- [";
 *   List.iter (Format.eprintf " %a ,\n" SmtAtom.(Form.to_smt Atom.to_smt)) c2;
 *   Format.eprintf "] ==\n [";
 *   List.iter (Format.eprintf " %a ,\n" SmtAtom.(Form.to_smt Atom.to_smt)) r;
 *   Format.eprintf "] @.";
 *   r *)



(* Generating clauses *)

let clauses : (int,Form.t clause) Hashtbl.t = Hashtbl.create 17
let get_clause id =
  try Hashtbl.find clauses id
  with | Not_found -> raise (Debug ("VeritSyntax.get_clause : clause number "^(string_of_int id)^" not found\n"))
let add_clause id cl = Hashtbl.add clauses id cl
let clear_clauses () = Hashtbl.clear clauses


(* <ref_cl> maps solver integers to id integers. *)
let ref_cl : (int, int) Hashtbl.t = Hashtbl.create 17
let get_ref i = Hashtbl.find ref_cl i
let add_ref i j = Hashtbl.add ref_cl i j
let clear_ref () = Hashtbl.clear ref_cl

(* Recognizing and modifying clauses depending on a forall_inst clause. *)

let rec fins_lemma ids_params =
  match ids_params with
    [] -> raise Not_found
  | h :: t -> let cl_target = repr (get_clause h) in
              match cl_target.kind with
                Other (Forall_inst (lemma, _)) -> lemma
              | _ -> fins_lemma t

let find_remove_lemma lemma ids_params =
  let eq_lemma h = eq_clause lemma (get_clause h) in
  list_find_remove eq_lemma ids_params

(* Removes the lemma in a list of ids containing an instance of this lemma *)
let rec merge ids_params =
  let rest_opt = try let lemma = fins_lemma ids_params in
                     let _, rest = find_remove_lemma lemma ids_params in
                     Some rest
                 with Not_found -> None in
  match rest_opt with
    None -> ids_params
  | Some r -> merge r

let to_add = ref []

let mk_clause (id,typ,value,ids_params) =
  let kind =
    match typ with
      (* Roots *)
      | Assume -> Root
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
      | Nand | Imp | Xor1 | Nxor1 | Equ2 | Nequ2 | Ite1 | Nite1 ->
        (match ids_params with
          | [id] -> Other (ImmBuildDef (get_clause id))
          | _ -> assert false)
      | Or ->
         (match ids_params with
            | [id_target] ->
               let cl_target = get_clause id_target in
               begin match cl_target.kind with
                 | Other (Forall_inst _) -> Same cl_target
                 | _ -> Other (ImmBuildDef cl_target) end
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
      (* Resolution *)
      | Reso | Threso ->
         let ids_params = merge ids_params in
         (match ids_params with
            | cl1::cl2::q ->
               let res = {rc1 = get_clause cl1; rc2 = get_clause cl2; rtail = List.map get_clause q} in
               Res res
            | [fins_id] -> Same (get_clause fins_id)
            | [] -> assert false)

      (* Holes in proofs *)
      | Hole -> Other (SmtCertif.Hole (List.map get_clause ids_params, value))

      (* Not implemented *)
      | Notnot -> raise (Debug "VeritSyntax.ml: rule notnot not implemented yet")
      | Taut -> raise (Debug "VeritSyntax.ml: rule taut not implemented yet")
      | Cont -> raise (Debug "VeritSyntax.ml: rule cont not implemented yet")
      | Refl -> raise (Debug "VeritSyntax.ml: rule refl not implemented yet")
      | Trans -> raise (Debug "VeritSyntax.ml: rule trans not implemented yet")
      | Cong -> raise (Debug "VeritSyntax.ml: rule cong not implemented yet")
      | Conndef -> raise (Debug "VeritSyntax.ml: rule conndef not implemented yet")
      | Andsimp -> raise (Debug "VeritSyntax.ml: rule andsimp not implemented yet")
      | Orsimp -> raise (Debug "VeritSyntax.ml: rule orsimp not implemented yet")
      | Notsimp -> raise (Debug "VeritSyntax.ml: rule notsimp not implemented yet")
      | Impsimp -> raise (Debug "VeritSyntax.ml: rule impsimp not implemented yet")
      | Eqsimp -> raise (Debug "VeritSyntax.ml: rule eqsimp not implemented yet")
      | Boolsimp -> raise (Debug "VeritSyntax.ml: rule boolsimp not implemented yet")
      | Acsimp -> raise (Debug "VeritSyntax.ml: rule acsimp not implemented yet")
      | Itesimp -> raise (Debug "VeritSyntax.ml: rule itesimp not implemented yet")
      | Equalsimp -> raise (Debug "VeritSyntax.ml: rule equalsimp not implemented yet")
  in
  let cl =
    (* TODO: change this into flatten when necessary *)
    if SmtTrace.isRoot kind then SmtTrace.mkRootV value
    else SmtTrace.mk_scertif kind (Some value) in
  add_clause id cl;
  if id > 1 then SmtTrace.link (get_clause (id-1)) cl;
  id

let mk_clause cl =
  try mk_clause cl
  with Failure f ->
    Structures.error ("SMTCoq was not able to check the certificate \
                       for the following reason.\n"^f)

let apply_dec f (decl, a) = decl, f a

let rec list_dec = function
  | [] -> true, []
  | (decl_h, h) :: t ->
     let decl_t, l_t = list_dec t in
     decl_h && decl_t, h :: l_t

let apply_dec_atom (f:?declare:bool -> SmtAtom.hatom -> SmtAtom.hatom) = function
  | decl, Form.Atom h -> decl, Form.Atom (f ~declare:decl h)
  | _ -> assert false

let apply_bdec_atom (f:?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) o1 o2 =
  match o1, o2 with
  | (decl1, Form.Atom h1), (decl2, Form.Atom h2) ->
     let decl = decl1 && decl2 in
     decl, Form.Atom (f ~declare:decl h1 h2)
  | _ -> assert false

let apply_tdec_atom (f:?declare:bool -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t -> SmtAtom.Atom.t) o1 o2 o3 =
  match o1, o2, o3 with
  | (decl1, Form.Atom h1), (decl2, Form.Atom h2), (decl3, Form.Atom h3) ->
     let decl = decl1 && decl2 && decl3 in
     decl, Form.Atom (f ~declare:decl h1 h2 h3)
  | _ -> assert false


let solver : (int, (bool * Form.atom_form_lit)) Hashtbl.t = Hashtbl.create 17
let get_solver id =
  try Hashtbl.find solver id
  with | Not_found -> raise (Debug ("VeritSyntax.get_solver : solver variable number "^(string_of_int id)^" not found\n"))
let add_solver id cl = Hashtbl.add solver id cl
let clear_solver () = Hashtbl.clear solver

let qvar_tbl : (string, SmtBtype.btype) Hashtbl.t = Hashtbl.create 10
let find_opt_qvar s = try Some (Hashtbl.find qvar_tbl s)
                      with Not_found -> None
let add_qvar s bt = Hashtbl.add qvar_tbl s bt
let clear_qvar () = Hashtbl.clear qvar_tbl

(* Finding the index of a root in <lsmt> modulo the <re_hash> function.
   This function is used by SmtTrace.order_roots *)
let init_index lsmt re_hash =
  let form_index_init_rank : (int, int) Hashtbl.t = Hashtbl.create 20 in
  let add = Hashtbl.add form_index_init_rank in
  let find = Hashtbl.find form_index_init_rank in
  let rec walk rank = function
    | [] -> ()
    | h::t -> add (Form.to_lit (re_hash h)) rank;
              walk (rank+1) t in
  walk 1 lsmt;
  fun hf -> let re_hf = re_hash hf in
            try find (Form.to_lit re_hf)
            with Not_found ->
              let oc = open_out "/tmp/input_not_found.log" in
              let fmt = Format.formatter_of_out_channel oc in
              List.iter (fun h -> Format.fprintf fmt "%a\n" (Form.to_smt ~debug:true) (re_hash h)) lsmt;
              Format.fprintf fmt "\n%a\n@." (Form.to_smt ~debug:true) re_hf;
              flush oc; close_out oc;
              raise (Debug "Input not found: log available in /tmp/input_not_found.log")

let qf_to_add lr =
  let is_forall l = match Form.pform l with
    | Fapp (Fforall _, _) -> true
    | _ -> false in
  let rec qf_lemmas = function
    | [] -> []
    | ({value = Some [l]} as r)::t when not (is_forall l) ->
       (Other (Qf_lemma (r, l)), r.value, r) :: qf_lemmas t
    | _::t -> qf_lemmas t in
  qf_lemmas lr

let ra = Atom.create ()
let rf = Form.create ()
let ra_quant = Atom.create ()
let rf_quant = Form.create ()

let hlets : (string, Form.atom_form_lit) Hashtbl.t = Hashtbl.create 17

let clear_mk_clause () =
  to_add := [];
  clear_ref ()

let clear () =
  clear_qvar ();
  clear_mk_clause ();
  clear_clauses ();
  clear_solver ();
  Atom.clear ra;
  Form.clear rf;
  Atom.clear ra_quant;
  Form.clear rf_quant;
  Hashtbl.clear hlets
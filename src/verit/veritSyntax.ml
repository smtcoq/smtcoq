(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
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

type typ = | Inpu | Deep | True | Fals | Andp | Andn | Orp | Orn | Xorp1 | Xorp2 | Xorn1 | Xorn2 | Impp | Impn1 | Impn2 | Equp1 | Equp2 | Equn1 | Equn2 | Itep1 | Itep2 | Iten1 | Iten2 | Eqre | Eqtr | Eqco | Eqcp | Dlge | Lage | Lata | Dlde | Lade | Fins | Eins | Skea | Skaa | Qnts | Qntm | Reso | And | Nor | Or | Nand | Xor1 | Xor2 | Nxor1 | Nxor2 | Imp | Nimp1 | Nimp2 | Equ1 | Equ2 | Nequ1 | Nequ2 | Ite1 | Ite2 | Nite1 | Nite2 | Tpal | Tlap | Tple | Tpne | Tpde | Tpsa | Tpie | Tpma | Tpbr | Tpbe | Tpsc | Tppp | Tpqt | Tpqs | Tpsk | Subp | Hole

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
      (* Search if there is a trivial reflexivity premice *)
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
  |_ -> failwith "VeritSyntax.mkTrans: no conclusion or more than one conclusion in transitivity"


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
        if indexed_op_index a_f = indexed_op_index b_f then
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
           if indexed_op_index a_f = indexed_op_index b_f then
             let cert = process_congr (Array.to_list a_args) (Array.to_list b_args) prem_val [] in
             Other (EqCgrP (p_p,c,cert))
           else failwith "VeritSyntax.mkCongrPred: unmatching predicates"
        | _ -> failwith "VeritSyntax.mkCongrPred : not pred app")
     |_ ->  failwith "VeritSyntax.mkCongr: no or more than one predicate app premise in congruence")
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


(* Generating clauses *)
let clauses : (int,Form.t clause) Hashtbl.t = Hashtbl.create 17
let get_clause id =
  try Hashtbl.find clauses id
  with | Not_found -> failwith ("VeritSyntax.get_clause : clause number "^(string_of_int id)^" not found\n")
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

let rec find_remove_lemma lemma ids_params =
  let eq_lemma h = eq_clause lemma (get_clause h) in
  list_find_remove eq_lemma ids_params

(* Removes the lemma in a list of ids containing an instance of this lemma *)                   
let merge ids_params =
  try
    let lemma = fins_lemma ids_params in
    let _, rest = find_remove_lemma lemma ids_params in
    rest
  with Not_found -> ids_params

let to_add = ref []
                     
let rec mk_clause (id,typ,value,ids_params) =
  let kind =
    match typ with
    | Tpbr ->
       begin match ids_params with
       | [id] ->
          Same (get_clause id)
       | _ -> failwith "unexpected form of tmp_betared" end
    | Tpqt ->
       begin match ids_params with
       | [id] ->
          Same (get_clause id)
       | _ -> failwith "unexpected form of tmp_qnt_tidy" end
    | Fins ->
       begin match value, ids_params with
        | [inst], [ref_th] when Form.is_pos inst ->
           let cl_th = get_clause ref_th in
           Other (Forall_inst (repr cl_th, inst))
        | _ -> failwith "unexpected form of forall_inst" end
    | Or ->
       (match ids_params with
        | [id_target] ->
           let cl_target = get_clause id_target in
           begin match cl_target.kind with
           | Other (Forall_inst _) -> Same cl_target
           | _ -> Other (ImmBuildDef cl_target) end
        | _ -> assert false)
    (* Resolution *)
    | Reso ->
       let ids_params = merge ids_params in
       (match ids_params with
        | cl1::cl2::q ->
           let res = {rc1 = get_clause cl1; rc2 = get_clause cl2; rtail = List.map get_clause q} in
           Res res
        | [fins_id] -> Same (get_clause fins_id)
        | [] -> assert false)

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
    | Nand | Imp | Xor1 | Nxor1 | Equ2 | Nequ2 | Ite1 | Nite1 ->
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
    (* Holes in proofs *)
    | Hole -> Other (SmtCertif.Hole (List.map get_clause ids_params, value))
    (* Not implemented *)
    | Deep -> failwith "VeritSyntax.ml: rule deep_res not implemented yet"
    | Eins -> failwith "VeritSyntax.ml: rule exists_inst not implemented yet"
    | Skea -> failwith "VeritSyntax.ml: rule skolem_ex_ax not implemented yet"
    | Skaa -> failwith "VeritSyntax.ml: rule skolem_all_ax not implemented yet"
    | Qnts -> failwith "VeritSyntax.ml: rule qnt_simplify_ax not implemented yet"
    | Qntm -> failwith "VeritSyntax.ml: rule qnt_merge_ax not implemented yet"
    | Tpne -> failwith "VeritSyntax.ml: rule tmp_nary_elim not implemented yet"
    | Tpie -> failwith "VeritSyntax.ml: rule tmp_ite_elim not implemented yet"
    | Tpma -> failwith "VeritSyntax.ml: rule tmp_macrosubst not implemented yet"
    | Tpbe -> failwith "VeritSyntax.ml: rule tmp_bfun_elim not implemented yet"
    | Tpsc -> failwith "VeritSyntax.ml: rule tmp_sk_connector not implemented yet"
    | Tppp -> failwith "VeritSyntax.ml: rule tmp_pm_process not implemented yet"
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

(* functions for applying on a pair with a boolean when the boolean indicates
   if the entire term should be declared in the tables *)
let lit_of_atom_form_lit rf = function
  | decl, Atom a -> Form.get ~declare:decl rf (Fatom a)
  | decl, Form f -> begin match f with
                    | Fapp (Fforall _, _) when decl -> failwith "decl is true on a forall"
                    | _ -> Form.get ~declare:decl rf f end
  | decl, Lit l -> l

let apply_dec f (decl, a) = decl, f a

let rec list_dec = function
  | [] -> true, []
  | (decl_h, h) :: t ->
     let decl_t, l_t = list_dec t in
     decl_h && decl_t, h :: l_t
    
let apply_dec_atom f = function
  | decl, Atom h -> decl, Atom (f decl h)
  | _ -> assert false

let apply_bdec_atom f o1 o2 =
  match o1, o2 with
  | (decl1, Atom h1), (decl2, Atom h2) ->
     let decl = decl1 && decl2 in
     decl, Atom (f decl h1 h2)
  | _ -> assert false


let solver : (int, (bool * atom_form_lit)) Hashtbl.t = Hashtbl.create 17
let get_solver id =
  try Hashtbl.find solver id
  with | Not_found -> failwith ("VeritSyntax.get_solver : solver variable"^
                                  "number "^(string_of_int id)^" not found\n")
let add_solver id cl = Hashtbl.add solver id cl
let clear_solver () = Hashtbl.clear solver

let btypes : (string, SmtBtype.btype) Hashtbl.t = Hashtbl.create 17
let get_btype id =
  try Hashtbl.find btypes id
  with | Not_found -> failwith ("VeritSyntax.get_btype : sort symbol \""^
                                  id^"\" not found\n")
let add_btype id cl = Hashtbl.add btypes id cl
let clear_btypes () = Hashtbl.clear btypes

let funs : (string,indexed_op) Hashtbl.t = Hashtbl.create 17
let get_fun id =
  try Hashtbl.find funs id
  with | Not_found -> failwith ("VeritSyntax.get_fun : function symbol \""
                                ^id^"\" not found\n")
let add_fun id cl = Hashtbl.add funs id cl
let clear_funs () = Hashtbl.clear funs

let qvar_tbl : (string, SmtBtype.btype) Hashtbl.t = Hashtbl.create 10
let find_opt_qvar s = try Some (Hashtbl.find qvar_tbl s)
                      with Not_found -> None
let add_qvar s bt = Hashtbl.add qvar_tbl s bt
let clear_qvar () = Hashtbl.clear qvar_tbl

let string_hform = Form.to_string ~pi:true (Atom.to_string ~pi:true )

(* Finding the index of a root in <lsmt> modulo the <re_hash> function. 
   This function is used by SmtTrace.order_roots *)
let init_index lsmt re_hash =
  let form_index_init_rank : (int, int) Hashtbl.t = Hashtbl.create 20 in
  let add = Hashtbl.add form_index_init_rank in
  let find = Hashtbl.find form_index_init_rank in
  let rec walk rank = function
    | [] -> ()
    | h::t -> add (Form.to_lit h) rank;
              walk (rank+1) t in
  walk 1 lsmt;
  fun hf -> let re_hf = re_hash hf in
            try find (Form.to_lit re_hf)
            with Not_found ->
              let oc = open_out "/tmp/input_not_found.log" in
              (List.map string_hform lsmt)
              |> List.iter (Printf.fprintf oc "%s\n");
              Printf.fprintf oc "\n%s\n" (string_hform re_hf);
              flush oc; close_out oc;
              failwith "not found: log available"

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
let ra' = Atom.create ()
let rf' = Form.create ()

                     
let hlets : (string, atom_form_lit) Hashtbl.t = Hashtbl.create 17

let clear_mk_clause () = 
  to_add := [];
  clear_ref ()
                
let clear () =
  clear_qvar ();
  clear_mk_clause ();
  clear_clauses ();
  clear_solver ();
  clear_btypes ();
  clear_funs ();
  Atom.clear ra;
  Form.clear rf;
  Atom.clear ra';
  Form.clear rf';
  Hashtbl.clear hlets

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(*** Linking SMT Terms to Micromega Terms ***)
open Util
open Structures.Micromega_plugin_Micromega

open SmtForm
open SmtAtom

(* morphism for expression over Z *)

let rec pos_of_int i =
  if i <= 1
  then XH
  else
    if i land 1 = 0
    then XO(pos_of_int (i lsr 1))
    else XI(pos_of_int (i lsr 1))

type my_tbl =
    {tbl:(hatom,int) Hashtbl.t; mutable count:int}

let get_atom_var tbl ha =
  try Hashtbl.find tbl.tbl ha
  with Not_found ->
    let v = tbl.count in
    Hashtbl.add tbl.tbl ha v;
    tbl.count <- v + 1;
    v

let create_tbl n = {tbl=Hashtbl.create n;count=1}

let rec smt_Atom_to_micromega_pos ha =
  match Atom.atom ha with
  | Auop(UO_xO, ha) ->
      XO (smt_Atom_to_micromega_pos ha)
  | Auop(UO_xI, ha) ->
      XI (smt_Atom_to_micromega_pos ha)
  | Acop CO_xH -> XH
  | _ -> raise Not_found

let smt_Atom_to_micromega_Z ha =
  match Atom.atom ha with
  | Auop(UO_Zpos, ha) ->
      Zpos (smt_Atom_to_micromega_pos ha)
  | Auop(UO_Zneg, ha) ->
      Zneg (smt_Atom_to_micromega_pos ha)
  | Acop CO_Z0 -> Z0
  | _ -> raise Not_found

let rec smt_Atom_to_micromega_pExpr tbl ha =
  match Atom.atom ha with
  | Abop (BO_Zplus, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      PEadd(a, b)
  | Abop (BO_Zmult, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      PEmul(a, b)
  | Abop (BO_Zminus, ha, hb) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      let b = smt_Atom_to_micromega_pExpr tbl hb in
      PEsub(a, b)
  | Auop (UO_Zopp, ha) ->
      let a = smt_Atom_to_micromega_pExpr tbl ha in
      PEopp a
  | _ ->
      try PEc (smt_Atom_to_micromega_Z ha)
      with Not_found ->
	let v = get_atom_var tbl ha in
	PEX (pos_of_int v)


(* morphism for LIA proposition (=, >, ...) *)

let smt_binop_to_micromega_formula tbl op ha hb =
  let op =
    match op with
    | BO_Zlt -> OpLt
    | BO_Zle -> OpLe
    | BO_Zge -> OpGe
    | BO_Zgt -> OpGt
    | BO_eq _ -> OpEq
    | _ -> Structures.error
	  "lia.ml: smt_binop_to_micromega_formula expecting a formula"
  in
  let lhs = smt_Atom_to_micromega_pExpr tbl ha in
  let rhs = smt_Atom_to_micromega_pExpr tbl hb in
  {flhs = lhs; fop = op; frhs = rhs }

let smt_Atom_to_micromega_formula tbl ha =
  match Atom.atom ha with
    | Abop (op,ha,hb) -> smt_binop_to_micromega_formula tbl op ha hb
    | _ -> Structures.error
	  "lia.ml: smt_Atom_to_micromega_formula was expecting an LIA formula"

(* specialized fold *)

(* morphism for general formulas *)

let binop_array g tbl op def t =
  let n = Array.length t in
  if n = 0 then
    def
  else
    let aux = ref (g tbl t.(0)) in
    for i = 1 to (n-1) do
      aux := op !aux (g tbl t.(i))
    done;
    !aux

let rec smt_Form_to_coq_micromega_formula tbl l =
  let v =
    match Form.pform l with
      | Fatom ha -> A (smt_Atom_to_micromega_formula tbl ha, Tt)
      | Fapp (Ftrue, _) -> TT
      | Fapp (Ffalse, _) -> FF
      | Fapp (Fand, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> Cj (x,y)) TT l
      | Fapp (For, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> D (x,y)) FF l
      | Fapp (Fxor, l) -> failwith "todo:Fxor"
      | Fapp (Fimp, l) -> binop_array smt_Form_to_coq_micromega_formula tbl (fun x y -> I (x,None,y)) TT l
      | Fapp (Fiff, l) -> failwith "todo:Fiff"
      | Fapp (Fite, l) -> failwith "todo:Fite"
      | Fapp (Fnot2 _, l) ->
        if Array.length l <> 1 then
          failwith "Lia.smt_Form_to_coq_micromega_formula: wrong number of arguments for Fnot2"
        else
          smt_Form_to_coq_micromega_formula tbl l.(0)
      | FbbT _ -> assert false
      | Fapp (Fforall _, _) -> assert false
  in
  if Form.is_pos l then v
  else N(v)

let binop_list tbl op def l =
  match l with
  | [] -> def
  | f::l -> List.fold_left (fun x y -> op x (smt_Form_to_coq_micromega_formula tbl y)) (smt_Form_to_coq_micromega_formula tbl f) l

let smt_clause_to_coq_micromega_formula tbl cl =
  binop_list tbl (fun x y -> Cj (x,y)) TT (List.map Form.neg cl)


(* backported from Coq *)
type ('option,'a,'prf,'model) prover = {
  name : string ; (* name of the prover *)
  get_option : unit ->'option ; (* find the options of the prover *)
  prover : ('option *  'a list) -> ('prf, 'model) Structures.Micromega_plugin_Certificate.res ; (* the prover itself *)
  hyps : 'prf -> Structures.Micromega_plugin_Mutils.ISet.t ; (* extract the indexes of the hypotheses really used in the proof *)
  compact : 'prf -> (int -> int) -> 'prf ; (* remap the hyp indexes according to function *)
  pp_prf : out_channel -> 'prf -> unit ;(* pretting printing of proof *)
  pp_f   : out_channel -> 'a   -> unit (* pretty printing of the formulas (polynomials)*)
}

let lia_enum  = ref true
let max_depth = max_int
let lia_proof_depth = ref max_depth
let get_lia_option () =
 (!Structures.Micromega_plugin_Certificate.use_simplex,!lia_enum,!lia_proof_depth)

let lift_pexpr_prover p l =  p (List.map (fun (e,o) -> Structures.Micromega_plugin_Micromega.denorm e , o) l)

module CacheZ = Structures.Micromega_plugin_Persistent_cache.PHashtable(struct
 type prover_option = bool * bool* int
 type t = prover_option * ((Structures.Micromega_plugin_Micromega.z Structures.Micromega_plugin_Micromega.pol * Structures.Micromega_plugin_Micromega.op1) list)
  let equal = (=)
  let hash  = Hashtbl.hash
end)

let memo_zlinear_prover = CacheZ.memo ".lia.cache" (fun ((_,ce,b),s) -> lift_pexpr_prover (Structures.Micromega_plugin_Certificate.lia ce b) s)

let xhyps_of_cone base acc prf =
  let rec xtract e acc =
    match e with
    | Structures.Micromega_plugin_Micromega.PsatzC _ | Structures.Micromega_plugin_Micromega.PsatzZ | Structures.Micromega_plugin_Micromega.PsatzSquare _ -> acc
    | Structures.Micromega_plugin_Micromega.PsatzIn n -> let n = (Structures.Micromega_plugin_Mutils.CoqToCaml.nat n) in
                        if n >= base
                        then  Structures.Micromega_plugin_Mutils.ISet.add (n-base) acc
                        else acc
    | Structures.Micromega_plugin_Micromega.PsatzMulC(_,c) -> xtract  c acc
    | Structures.Micromega_plugin_Micromega.PsatzAdd(e1,e2) |  Structures.Micromega_plugin_Micromega.PsatzMulE(e1,e2) -> xtract e1 (xtract e2 acc) in

    xtract prf acc

let hyps_of_pt pt =

  let rec xhyps base pt acc =
    match pt with
      | Structures.Micromega_plugin_Micromega.DoneProof -> acc
      | Structures.Micromega_plugin_Micromega.RatProof(c,pt) ->  xhyps (base+1) pt (xhyps_of_cone base acc c)
      | Structures.Micromega_plugin_Micromega.CutProof(c,pt) -> xhyps (base+1) pt (xhyps_of_cone base acc c)
      | Structures.Micromega_plugin_Micromega.EnumProof(c1,c2,l) ->
          let s = xhyps_of_cone base (xhyps_of_cone base acc c2) c1 in
            List.fold_left (fun s x -> xhyps (base + 1) x s) s l in

    xhyps 0 pt Structures.Micromega_plugin_Mutils.ISet.empty

let compact_cone prf f  =
  let np n = Structures.Micromega_plugin_Mutils.CamlToCoq.nat (f (Structures.Micromega_plugin_Mutils.CoqToCaml.nat n)) in

  let rec xinterp prf =
    match prf with
    | Structures.Micromega_plugin_Micromega.PsatzC _ | Structures.Micromega_plugin_Micromega.PsatzZ | Structures.Micromega_plugin_Micromega.PsatzSquare _ -> prf
    | Structures.Micromega_plugin_Micromega.PsatzIn n -> Structures.Micromega_plugin_Micromega.PsatzIn (np n)
    | Structures.Micromega_plugin_Micromega.PsatzMulC(e,c) -> Structures.Micromega_plugin_Micromega.PsatzMulC(e,xinterp c)
    | Structures.Micromega_plugin_Micromega.PsatzAdd(e1,e2) -> Structures.Micromega_plugin_Micromega.PsatzAdd(xinterp e1,xinterp e2)
    | Structures.Micromega_plugin_Micromega.PsatzMulE(e1,e2) -> Structures.Micromega_plugin_Micromega.PsatzMulE(xinterp e1,xinterp e2) in

    xinterp prf

let compact_pt pt f =
  let translate ofset x =
    if x < ofset then x
    else (f (x-ofset) + ofset) in

  let rec compact_pt ofset pt =
    match pt with
      | Structures.Micromega_plugin_Micromega.DoneProof -> Structures.Micromega_plugin_Micromega.DoneProof
      | Structures.Micromega_plugin_Micromega.RatProof(c,pt) -> Structures.Micromega_plugin_Micromega.RatProof(compact_cone c (translate (ofset)), compact_pt (ofset+1) pt )
      | Structures.Micromega_plugin_Micromega.CutProof(c,pt) -> Structures.Micromega_plugin_Micromega.CutProof(compact_cone c (translate (ofset)), compact_pt (ofset+1) pt )
      | Structures.Micromega_plugin_Micromega.EnumProof(c1,c2,l) -> Structures.Micromega_plugin_Micromega.EnumProof(compact_cone c1 (translate (ofset)), compact_cone c2 (translate (ofset)),
                                                   Structures.Micromega_plugin_Micromega.map (fun x -> compact_pt (ofset+1) x) l) in
    compact_pt 0 pt

let pp_nat o n = Printf.fprintf o "%i" (Structures.Micromega_plugin_Mutils.CoqToCaml.nat n)

let pp_positive o x = Printf.fprintf o "%i" (Structures.Micromega_plugin_Mutils.CoqToCaml.positive x)

let pp_z o x = Printf.fprintf o "%s" (Big_int.string_of_big_int (Structures.Micromega_plugin_Mutils.CoqToCaml.z_big_int x))

let pp_list op cl elt o l =
  let rec _pp  o l =
    match l with
      | [] -> ()
      | [e] -> Printf.fprintf o "%a" elt e
      | e::l -> Printf.fprintf o "%a ,%a" elt e  _pp l in
  Printf.fprintf o "%s%a%s" op _pp l cl

let pp_pol pp_c o e =
  let rec pp_pol o e =
    match e with
      | Structures.Micromega_plugin_Micromega.Pc n -> Printf.fprintf o "Pc %a" pp_c n
      | Structures.Micromega_plugin_Micromega.Pinj(p,pol) -> Printf.fprintf o "Pinj(%a,%a)" pp_positive p pp_pol pol
      | Structures.Micromega_plugin_Micromega.PX(pol1,p,pol2) -> Printf.fprintf o "PX(%a,%a,%a)" pp_pol pol1 pp_positive p pp_pol pol2 in
  pp_pol o e

let pp_psatz pp_z o e =
  let rec pp_cone o e =
    match e with
      | Structures.Micromega_plugin_Micromega.PsatzIn n ->
         Printf.fprintf o "(In %a)%%nat" pp_nat n
      | Structures.Micromega_plugin_Micromega.PsatzMulC(e,c) ->
         Printf.fprintf o "( %a [*] %a)" (pp_pol pp_z) e pp_cone c
      | Structures.Micromega_plugin_Micromega.PsatzSquare e ->
         Printf.fprintf o "(%a^2)" (pp_pol pp_z) e
      | Structures.Micromega_plugin_Micromega.PsatzAdd(e1,e2) ->
         Printf.fprintf o "(%a [+] %a)" pp_cone e1 pp_cone e2
      | Structures.Micromega_plugin_Micromega.PsatzMulE(e1,e2) ->
         Printf.fprintf o "(%a [*] %a)" pp_cone e1 pp_cone e2
      | Structures.Micromega_plugin_Micromega.PsatzC p ->
         Printf.fprintf o "(%a)%%positive" pp_z p
      | Structures.Micromega_plugin_Micromega.PsatzZ    ->
         Printf.fprintf o "0" in
  pp_cone o e

let rec pp_proof_term o = function
  | Structures.Micromega_plugin_Micromega.DoneProof -> Printf.fprintf o "D"
  | Structures.Micromega_plugin_Micromega.RatProof(cone,rst) -> Printf.fprintf o "R[%a,%a]" (pp_psatz pp_z) cone pp_proof_term rst
  | Structures.Micromega_plugin_Micromega.CutProof(cone,rst) -> Printf.fprintf o "C[%a,%a]" (pp_psatz pp_z) cone pp_proof_term rst
  | Structures.Micromega_plugin_Micromega.EnumProof(c1,c2,rst) ->
      Printf.fprintf o "EP[%a,%a,%a]"
        (pp_psatz pp_z) c1 (pp_psatz pp_z) c2
     (pp_list "[" "]" pp_proof_term) rst

let linear_Z =   {
  name    = "lia";
 get_option = get_lia_option;
 prover  = memo_zlinear_prover ;
  hyps    = hyps_of_pt;
  compact = compact_pt;
  pp_prf  = pp_proof_term;
  pp_f    = fun o x -> pp_pol pp_z o (fst x)
}

let find_witness  p polys1 =
  let polys1 = List.map fst polys1 in
  match p.prover (p.get_option (), polys1) with
  | Structures.Micromega_plugin_Certificate.Model m -> Structures.Micromega_plugin_Certificate.Model m
  | Structures.Micromega_plugin_Certificate.Unknown -> Structures.Micromega_plugin_Certificate.Unknown
  | Structures.Micromega_plugin_Certificate.Prf prf -> Structures.Micromega_plugin_Certificate.Prf(prf,p)

let witness_list prover l =
 let rec xwitness_list l =
  match l with
   | [] -> Structures.Micromega_plugin_Certificate.Prf []
   | e :: l ->
      match xwitness_list l with
      | Structures.Micromega_plugin_Certificate.Model (m,e) -> Structures.Micromega_plugin_Certificate.Model (m,e)
      | Structures.Micromega_plugin_Certificate.Unknown     -> Structures.Micromega_plugin_Certificate.Unknown
      | Structures.Micromega_plugin_Certificate.Prf l ->
         match find_witness  prover e  with
         | Structures.Micromega_plugin_Certificate.Model m -> Structures.Micromega_plugin_Certificate.Model (m,e)
         | Structures.Micromega_plugin_Certificate.Unknown -> Structures.Micromega_plugin_Certificate.Unknown
         | Structures.Micromega_plugin_Certificate.Prf w ->  Structures.Micromega_plugin_Certificate.Prf (w::l) in
 xwitness_list l

let witness_list_tags = witness_list

let tauto_lia ff =
  let prover = linear_Z in
  let cnf_ff,_ = Structures.Micromega_plugin_Micromega.cnfZ ff in
  match witness_list_tags prover cnf_ff with
    | Structures.Micromega_plugin_Certificate.Prf l -> Some (List.map fst l)
    | _ -> None

(* call to micromega solver *)
let build_lia_certif cl =
  let tbl = create_tbl 13 in
  let f = I(smt_clause_to_coq_micromega_formula tbl cl, None, FF) in
  tauto_lia f

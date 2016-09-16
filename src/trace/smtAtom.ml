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


open SmtMisc
open CoqTerms
open Entries
open Declare
open Decl_kinds

(** Syntaxified version of Coq type *)
type indexed_type = Term.constr gen_hashed

let dummy_indexed_type i = {index = i; hval = Term.mkProp}
let indexed_type_index i = i.index

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | Tindex of indexed_type
  | TFArray of btype * btype



let mk_bool b =
  let c, args = Term.decompose_app b in
  if Term.eq_constr c (Lazy.force ctrue) then true
  else if Term.eq_constr c (Lazy.force cfalse) then false
  else assert false

let rec mk_bool_list bs =
  let c, args = Term.decompose_app bs in
  if Term.eq_constr c (Lazy.force cnil) then []
  else if Term.eq_constr c (Lazy.force ccons) then
    match args with
    | [_; b; bs] -> mk_bool b :: mk_bool_list bs
    | _ -> assert false
  else assert false

let rec mk_nat n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cO) then
    0
  else if Term.eq_constr c (Lazy.force cS) then
    match args with
    | [n] -> (mk_nat n) + 1
    | _ -> assert false
  else assert false

let rec mk_positive n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cxH) then
    1
  else if Term.eq_constr c (Lazy.force cxO) then
    match args with
    | [n] -> 2 * (mk_positive n)
    | _ -> assert false
  else if Term.eq_constr c (Lazy.force cxI) then
    match args with
    | [n] -> 2 * (mk_positive n) + 1
    | _ -> assert false
  else assert false


let mk_N n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cN0) then
    0
  else if Term.eq_constr c (Lazy.force cNpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else assert false


let mk_Z n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cZ0) then 0
  else if Term.eq_constr c (Lazy.force cZpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else if Term.eq_constr c (Lazy.force cZneg) then
    match args with
    | [n] -> - mk_positive n
    | _ -> assert false
  else assert false


(* size of bivectors are either N.of_nat (length l) or an N *)
let mk_bvsize n =
  let c, args = Term.decompose_app n in
  if Term.eq_constr c (Lazy.force cof_nat) then
    match args with
    | [nl] ->
      let c, args = Term.decompose_app nl in
      if Term.eq_constr c (Lazy.force clength) then
        match args with
        | [_; l] -> List.length (mk_bool_list l)
        | _ -> assert false
      else assert false
    | _ -> assert false
  else mk_N n


module Btype = 
  struct 

    let index_tbl = Hashtbl.create 17 

    let index_to_coq i =
      let i = i.index in 
      try Hashtbl.find index_tbl i
      with Not_found ->
	let interp = mklApp cTindex [|mkInt i|] in
	Hashtbl.add index_tbl i interp;
	interp

    let rec equal t1 t2 =
      match t1,t2 with
        | Tindex i, Tindex j -> i.index == j.index
        | TBV i, TBV j -> i == j
        | TFArray (ti, te), TFArray (ti', te') -> equal ti ti' && equal te te'
        | _ -> t1 == t2

    let rec to_coq = function 
      | TZ -> Lazy.force cTZ
      | Tbool -> Lazy.force cTbool
      | Tpositive -> Lazy.force cTpositive
      | TBV n -> mklApp cTBV [|mkN n|]
      | Tindex i -> index_to_coq i
      | TFArray (ti, te) ->
        mklApp cTFArray [|to_coq ti; to_coq te|]

    let rec to_smt fmt = function
      | TZ -> Format.fprintf fmt "Int"
      | Tbool -> Format.fprintf fmt "Bool"
      | Tpositive -> Format.fprintf fmt "Int"
      | TBV i -> Format.fprintf fmt "(_ BitVec %i)" i
      | Tindex i -> Format.fprintf fmt "Tindex_%i" i.index
      | TFArray (ti, te) ->
        Format.fprintf fmt "(Array %a %a)" to_smt ti to_smt te

    let rec logic = function
      | TZ | Tpositive -> SL.singleton LLia
      | Tbool -> SL.empty
      | TBV _ -> SL.singleton LBitvectors
      | Tindex _ -> SL.singleton LUF
      | TFArray (ti, te) -> SL.add LArrays (SL.union (logic ti) (logic te))
          
    (* reify table *)
    type reify_tbl = 
        { mutable count : int;
	          tbl : (Term.constr, btype) Hashtbl.t;
          mutable cuts : (Structures.names_id_t * Term.types) list
	}

    let create () = 
      let htbl = Hashtbl.create 17 in  
      Hashtbl.add htbl (Lazy.force cZ) TZ;
      Hashtbl.add htbl (Lazy.force cbool) Tbool;
      (* Hashtbl.add htbl (Lazy.force cpositive) Tpositive; *)
      { count = 0;
	tbl = htbl;
        cuts = [] }

    let get_cuts reify = reify.cuts

    let declare reify t typ_eqb =
      (* TODO: allows to have only typ_eqb *)
      assert (not (Hashtbl.mem reify.tbl t));
      let res = Tindex {index = reify.count; hval = typ_eqb} in
      Hashtbl.add reify.tbl t res;
      reify.count <- reify.count + 1;
      res


    let rec of_coq reify t =
      let c, args = Term.decompose_app t in
      if Term.eq_constr c (Lazy.force cbool) ||
         Term.eq_constr c (Lazy.force cTbool) then Tbool
      else if Term.eq_constr c (Lazy.force cZ) ||
              Term.eq_constr c (Lazy.force cTZ) then TZ
      else if Term.eq_constr c (Lazy.force cpositive) ||
              Term.eq_constr c (Lazy.force cTpositive) then Tpositive
      else if Term.eq_constr c (Lazy.force cbitvector) ||
              Term.eq_constr c (Lazy.force cTBV) then
        match args with
        | [s] -> TBV (mk_bvsize s)
        | _ -> assert false
      else if Term.eq_constr c (Lazy.force cfarray) ||
              Term.eq_constr c (Lazy.force cTFArray) then
        match args with
        | ti :: te :: _ -> TFArray (of_coq reify ti, of_coq reify te)
        | _ -> assert false
      else try
        Hashtbl.find reify.tbl t
      with | Not_found ->
        let n = string_of_int (List.length reify.cuts) in

        let compdec_name = Names.id_of_string ("CompDec"^n) in
        let compdec_var = Term.mkVar compdec_name in
        let compdec_type = mklApp cCompDec [| t |]in

        reify.cuts <- (compdec_name, compdec_type) :: reify.cuts;
        
        let ce = mklApp cTyp_compdec [|t; compdec_var|] in
        declare reify t ce

    
    let logic_of_coq reify t = logic (of_coq reify t)
    

    let interp_tbl reify =
      let t = Array.make (reify.count + 1) (Lazy.force cunit_typ_compdec) in
      let set _ = function
        | Tindex it -> t.(it.index) <- it.hval
        | _ -> () in
      Hashtbl.iter set reify.tbl;
      Structures.mkArray (Lazy.force ctyp_compdec, t)


    let to_list reify =
      let set _ t acc = match t with
	| Tindex it -> (it.index,it)::acc
	| _ -> acc in
      Hashtbl.fold set reify.tbl []

    let make_t_i rt = interp_tbl rt


    let interp_t t_i t =
        mklApp cinterp_t [|t_i ; to_coq t|]

    let dec_interp t_i t =
      mklApp cdec_interp [|t_i ; to_coq t|]
        
    let ord_interp t_i t =
      mklApp cord_interp [|t_i ; to_coq t|]
        
    let comp_interp t_i t =
      mklApp ccomp_interp [|t_i ; to_coq t|]
        
    let inh_interp t_i t =
        mklApp cinh_interp [|t_i ; to_coq t|]

    let rec interp t_i = function
      | TZ -> Lazy.force cZ
      | Tbool -> Lazy.force cbool
      | Tpositive -> Lazy.force cpositive
      | TBV n -> mklApp cbitvector [|mkN n|]
      | Tindex c -> mklApp cte_carrier [|c.hval|]
      (* | TFArray _ as t -> interp_t t_i t *)
      | TFArray (ti,te) ->
        mklApp cfarray [| interp t_i ti; interp t_i te;
                          ord_interp t_i ti; inh_interp t_i te |]

    
    let interp_to_coq reify t = interp (make_t_i reify) t

    
  end

(** Operators *)

type cop = 
   | CO_xH
   | CO_Z0
   | CO_BV of bool list

type uop =
   | UO_xO
   | UO_xI
   | UO_Zpos 
   | UO_Zneg
   | UO_Zopp
   | UO_BVbitOf of int * int
   | UO_BVnot of int
   | UO_BVneg of int
   | UO_BVextr of int * int * int
   | UO_BVzextn of int * int
   | UO_BVsextn of int * int

type bop = 
   | BO_Zplus
   | BO_Zminus
   | BO_Zmult
   | BO_Zlt
   | BO_Zle
   | BO_Zge
   | BO_Zgt
   | BO_eq of btype
   | BO_BVand of int
   | BO_BVor of int
   | BO_BVxor of int
   | BO_BVadd of int
   | BO_BVmult of int
   | BO_BVult of int
   | BO_BVslt of int
   | BO_BVconcat of int * int
   | BO_select of btype * btype
   | BO_diffarray of btype * btype


type top =
  | TO_store of btype * btype


type nop =
  | NO_distinct of btype

type op_def = { 
    tparams : btype array; 
    tres : btype; 
    op_val : Term.constr }

type indexed_op = op_def gen_hashed 

let dummy_indexed_op i dom codom =
  {index = i; hval = {tparams = dom; tres = codom; op_val = Term.mkProp}}
  
let indexed_op_index op = op.index

let debruijn_indexed_op i ty =
  { index = i;
    hval = {tparams = [||]; tres = ty; op_val = Term.mkRel i}}

module Op =
  struct 
    let c_to_coq = function
      | CO_xH -> Lazy.force cCO_xH
      | CO_Z0 -> Lazy.force cCO_Z0
      | CO_BV bv -> mklApp cCO_BV [|mk_bv_list bv; mkN (List.length bv)|]

    let c_type_of = function
      | CO_xH -> Tpositive
      | CO_Z0 -> TZ
      | CO_BV bv -> TBV (List.length bv)

    let interp_cop = function
      | CO_xH -> Lazy.force cxH
      | CO_Z0 -> Lazy.force cZ0
      | CO_BV bv -> mklApp cof_bits [|mk_bv_list bv|]

    let u_to_coq = function 
      | UO_xO -> Lazy.force cUO_xO
      | UO_xI -> Lazy.force cUO_xI
      | UO_Zpos -> Lazy.force cUO_Zpos 
      | UO_Zneg -> Lazy.force cUO_Zneg
      | UO_Zopp -> Lazy.force cUO_Zopp
      | UO_BVbitOf (s, i) -> mklApp cUO_BVbitOf [|mkN s; mkNat i|]
      | UO_BVnot s -> mklApp cUO_BVnot [|mkN s|]
      | UO_BVneg s -> mklApp cUO_BVneg [|mkN s|]
      | UO_BVextr (i, n, s) -> mklApp cUO_BVextr [|mkN i; mkN n; mkN s|]
      | UO_BVzextn (s, n) -> mklApp cUO_BVzextn [|mkN s; mkN n|]
      | UO_BVsextn (s, n) -> mklApp cUO_BVsextn [|mkN s; mkN n|]

    let u_type_of = function 
      | UO_xO | UO_xI -> Tpositive
      | UO_Zpos | UO_Zneg | UO_Zopp -> TZ
      | UO_BVbitOf _ -> Tbool
      | UO_BVnot s | UO_BVneg s -> TBV s
      | UO_BVextr (_, n, _) -> TBV n
      | UO_BVzextn (s, n) | UO_BVsextn (s, n) -> TBV (s + n)
          
    let u_type_arg = function 
      | UO_xO | UO_xI | UO_Zpos | UO_Zneg -> Tpositive
      | UO_Zopp -> TZ
      | UO_BVbitOf (s,_) -> TBV s
      | UO_BVnot s | UO_BVneg s -> TBV s
      | UO_BVextr (_, _, s) -> TBV s
      | UO_BVzextn (s, _) | UO_BVsextn (s, _) -> TBV s
      

    let interp_uop = function
      | UO_xO -> Lazy.force cxO
      | UO_xI -> Lazy.force cxI
      | UO_Zpos -> Lazy.force cZpos
      | UO_Zneg -> Lazy.force cZneg
      | UO_Zopp -> Lazy.force copp
      | UO_BVbitOf (_,i) -> mklApp cbitOf [|mkNat i|]
      | UO_BVnot s -> mklApp cbv_not [|mkN s|]
      | UO_BVneg s -> mklApp cbv_neg [|mkN s|]
      | UO_BVextr (i, n, s) -> mklApp cbv_extr [|mkN i; mkN n; mkN s|]
      | UO_BVzextn (s, n) -> mklApp cbv_zextn [|mkN s; mkN n|]
      | UO_BVsextn (s, n) -> mklApp cbv_sextn [|mkN s; mkN n|]

    let eq_tbl = Hashtbl.create 17 
    let select_tbl = Hashtbl.create 17 
    let store_tbl = Hashtbl.create 17 
    let diffarray_tbl = Hashtbl.create 17 
    
    let eq_to_coq t =
      try Hashtbl.find eq_tbl t 
      with Not_found ->
	let op = mklApp cBO_eq [|Btype.to_coq t|] in
	Hashtbl.add eq_tbl t op;
	op

    let select_to_coq ti te =
      try Hashtbl.find select_tbl (ti, te)
      with Not_found ->
        let op = mklApp cBO_select [|Btype.to_coq ti; Btype.to_coq te|] in
        Hashtbl.add select_tbl (ti, te) op;
        op

    let store_to_coq ti te =
      try Hashtbl.find store_tbl (ti, te)
      with Not_found ->
        let op = mklApp cTO_store [|Btype.to_coq ti; Btype.to_coq te|] in
        Hashtbl.add store_tbl (ti, te) op;
        op

    let diffarray_to_coq ti te =
      try Hashtbl.find diffarray_tbl (ti, te)
      with Not_found ->
        let op = mklApp cBO_diffarray [|Btype.to_coq ti; Btype.to_coq te|] in
        Hashtbl.add diffarray_tbl (ti, te) op;
        op

    let b_to_coq = function
      | BO_Zplus -> Lazy.force cBO_Zplus
      | BO_Zminus -> Lazy.force cBO_Zminus
      | BO_Zmult -> Lazy.force cBO_Zmult
      | BO_Zlt -> Lazy.force cBO_Zlt
      | BO_Zle -> Lazy.force cBO_Zle
      | BO_Zge -> Lazy.force cBO_Zge
      | BO_Zgt -> Lazy.force cBO_Zgt
      | BO_eq t -> eq_to_coq t
      | BO_BVand s -> mklApp cBO_BVand [|mkN s|]
      | BO_BVor s -> mklApp cBO_BVor [|mkN s|]
      | BO_BVxor s -> mklApp cBO_BVxor [|mkN s|]
      | BO_BVadd s -> mklApp cBO_BVadd [|mkN s|]
      | BO_BVmult s -> mklApp cBO_BVmult [|mkN s|]
      | BO_BVult s -> mklApp cBO_BVult [|mkN s|]
      | BO_BVslt s -> mklApp cBO_BVslt [|mkN s|]
      | BO_BVconcat (s1, s2) -> mklApp cBO_BVconcat [|mkN s1; mkN s2|]
      | BO_select (ti, te) -> select_to_coq ti te
      | BO_diffarray (ti, te) -> diffarray_to_coq ti te
        
    let b_type_of = function
      | BO_Zplus | BO_Zminus | BO_Zmult -> TZ
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt | BO_eq _
      | BO_BVult _ | BO_BVslt _ -> Tbool
      | BO_BVand s | BO_BVor s | BO_BVxor s | BO_BVadd s | BO_BVmult s -> TBV s
      | BO_BVconcat (s1, s2) -> TBV (s1 + s2)
      | BO_select (_, te) -> te
      | BO_diffarray (ti, _) -> ti

    let b_type_args = function
      | BO_Zplus | BO_Zminus | BO_Zmult 
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt -> (TZ,TZ)
      | BO_eq t -> (t,t)
      | BO_BVand s | BO_BVor s | BO_BVxor s | BO_BVadd s | BO_BVmult s
      | BO_BVult s | BO_BVslt s ->
        (TBV s,TBV s)
      | BO_BVconcat (s1, s2) -> (TBV s1, TBV s2)
      | BO_select (ti, te) -> (TFArray (ti, te), ti)
      | BO_diffarray (ti, te) -> (TFArray (ti, te), TFArray (ti, te))
                                 

    let interp_ieq t_i t =
      mklApp cinterp_eqb [|t_i ; Btype.to_coq t|]

 (*   let veval_t te =
      let env = Global.env () in
      let evd = Evd.from_env env in
      let evd, ty = Typing.type_of env evd te in
      Vnorm.cbv_vm env te ty

    
    let interp_ieq_eval t_i t =
      let te = mklApp cinterp_eqb [|t_i ; Btype.to_coq t|] in
      veval_t te
      *)

    let interp_eqarray t_i ti te =
      mklApp cequalarray
        Btype.[|interp t_i ti; interp t_i te;
                ord_interp t_i ti; comp_interp t_i ti;
                ord_interp t_i te; comp_interp t_i te;
                inh_interp t_i te |]

    let interp_select t_i ti te =
      mklApp cselect
        Btype.[|interp t_i ti; interp t_i te;
                ord_interp t_i ti; comp_interp t_i ti;
                inh_interp t_i te|]

    let interp_diff t_i ti te =
      mklApp cdiff
        Btype.[|interp t_i ti; interp t_i te;
                dec_interp t_i ti; ord_interp t_i ti; comp_interp t_i ti;
                dec_interp t_i te; ord_interp t_i te; comp_interp t_i te;
                inh_interp t_i ti; inh_interp t_i te |]


    let interp_store t_i ti te =
      mklApp cstore
        Btype.[|interp t_i ti; interp t_i te;
                dec_interp t_i ti; ord_interp t_i ti; comp_interp t_i ti;
                ord_interp t_i te; comp_interp t_i te; inh_interp t_i te |]

    
    let interp_eq t_i = function
      | TZ -> Lazy.force ceqbZ
      | Tbool -> Lazy.force ceqb
      | Tpositive -> Lazy.force ceqbP
      | TBV s -> mklApp cbv_eq [|mkN s|]
      | Tindex i -> mklApp ceqb_of_compdec [|mklApp cte_compdec [|i.hval|]|]
      | TFArray (ti, te) -> interp_eqarray t_i ti te

    

    let interp_bop t_i = function
      | BO_Zplus -> Lazy.force cadd
      | BO_Zminus -> Lazy.force csub
      | BO_Zmult -> Lazy.force cmul
      | BO_Zlt -> Lazy.force cltb
      | BO_Zle -> Lazy.force cleb
      | BO_Zge -> Lazy.force cgeb
      | BO_Zgt -> Lazy.force cgtb
      | BO_eq t -> interp_eq t_i t
      | BO_BVand s -> mklApp cbv_and [|mkN s|]
      | BO_BVor s -> mklApp cbv_or [|mkN s|]
      | BO_BVxor s -> mklApp cbv_xor [|mkN s|]
      | BO_BVadd s -> mklApp cbv_add [|mkN s|]
      | BO_BVmult s -> mklApp cbv_mult [|mkN s|]
      | BO_BVult s -> mklApp cbv_ult [|mkN s|]
      | BO_BVslt s -> mklApp cbv_slt [|mkN s|]
      | BO_BVconcat (s1,s2) -> mklApp cbv_concat [|mkN s1; mkN s2|]
      | BO_select (ti, te) -> interp_select t_i ti te
      | BO_diffarray (ti, te) -> interp_diff t_i ti te

    let t_to_coq = function
      | TO_store (ti, te) -> store_to_coq ti te

    let t_type_of = function
      | TO_store (ti, te) -> TFArray (ti, te)

    let t_type_args = function
      | TO_store (ti, te) -> TFArray (ti, te), ti, te

    let interp_top t_i = function
      | TO_store (ti, te) -> interp_store t_i ti te

    
    let n_to_coq = function
      | NO_distinct t -> mklApp cNO_distinct [|Btype.to_coq t|]

    let n_type_of = function
      | NO_distinct _ -> Tbool

    let n_type_args = function
      | NO_distinct ty -> ty


    let interp_nop t_i = function
      | NO_distinct ty ->
        mklApp cdistinct [|Btype.interp t_i ty; interp_eq t_i ty|]

    let i_to_coq i = mkInt i.index

    let i_type_of i = i.hval.tres

    let i_type_args i = i.hval.tparams
	  
    (* reify table *)
    type reify_tbl =
        { mutable count : int;
	          tbl : (Term.constr, indexed_op) Hashtbl.t
	}

    let create () =
      { count = 0;
	tbl =  Hashtbl.create 17 }

    let declare reify op tparams tres =
      assert (not (Hashtbl.mem reify.tbl op));
      let v = { tparams = tparams; tres = tres; op_val = op } in
      let res = {index = reify.count; hval = v } in
      Hashtbl.add reify.tbl op res;
      reify.count <- reify.count + 1;
      res

    let of_coq reify op =
      Hashtbl.find reify.tbl op


    let interp_tbl tval mk_Tval reify =
      let t = Array.make (reify.count + 1) 
	  (mk_Tval [||] Tbool (Lazy.force ctrue))  in
      let set _ v = 
	t.(v.index) <- mk_Tval v.hval.tparams v.hval.tres v.hval.op_val in
      Hashtbl.iter set reify.tbl;
      Structures.mkArray (tval, t)

    let to_list reify =
      let set _ op acc =
        let value = op.hval in
        (op.index,value.tparams,value.tres,op)::acc in
      Hashtbl.fold set reify.tbl []

    let c_equal op1 op2 = match op1, op2 with
      | CO_BV bv1, CO_BV bv2 ->
        (try List.for_all2 (=) bv1 bv2 with
         | Invalid_argument _ -> false)
      | _ -> op1 == op2

    let u_equal op1 op2 =
      match op1,op2 with
      | UO_xO, UO_xO
      | UO_xI, UO_xI
      | UO_Zpos, UO_Zpos
      | UO_Zneg, UO_Zneg
      | UO_Zopp, UO_Zopp -> true
      | UO_BVbitOf (s1,i1), UO_BVbitOf (s2,i2) -> s1 == s2 && i1 == i2
      | UO_BVnot s1, UO_BVnot s2 -> s1 == s2
      | UO_BVneg s1, UO_BVneg s2 -> s1 == s2
      | UO_BVextr (i1, n1, s1) , UO_BVextr (i2, n2, s2) ->
        i1 == i2 && n1 == n2 && s1 == s2
      | UO_BVzextn (s1, n1), UO_BVzextn (s2, n2) -> s1 == s2 && n1 == n2
      | UO_BVsextn (s1, n1), UO_BVsextn (s2, n2) -> s1 == s2 && n1 == n2
      | _ -> false

    let b_equal op1 op2 =
      match op1,op2 with
        | BO_eq t1, BO_eq t2 -> Btype.equal t1 t2
        | BO_BVand n1, BO_BVand n2 -> n1 == n2
        | BO_BVor n1, BO_BVor n2 -> n1 == n2
        | BO_BVxor n1, BO_BVxor n2 -> n1 == n2
        | BO_BVadd n1, BO_BVadd n2 -> n1 == n2
        | BO_BVmult n1, BO_BVmult n2 -> n1 == n2
        | BO_BVult n1, BO_BVult n2 -> n1 == n2
        | BO_BVslt n1, BO_BVslt n2 -> n1 == n2
        | BO_BVconcat (n1,m1), BO_BVconcat (n2,m2) -> n1 == n2 && m1 == m2
        | BO_select (ti1, te1), BO_select (ti2, te2)
        | BO_diffarray (ti1, te1), BO_diffarray (ti2, te2) ->
          Btype.equal ti1 ti2 && Btype.equal te1 te2
        | _ -> op1 == op2

    let t_equal op1 op2 =
      match op1,op2 with
        | TO_store (ti1, te1), TO_store (ti2, te2) ->
          Btype.equal ti1 ti2 && Btype.equal te1 te2

    let n_equal op1 op2 =
      match op1,op2 with
        | NO_distinct t1, NO_distinct t2 -> Btype.equal t1 t2

    let i_equal op1 op2 = op1.index == op2.index




    let logic_of_cop = function
      | CO_xH | CO_Z0 -> SL.singleton LLia
      | CO_BV _ -> SL.singleton LBitvectors

    let logic_of_uop = function
      | UO_xO | UO_xI
      | UO_Zpos | UO_Zneg | UO_Zopp -> SL.singleton LLia
      | UO_BVbitOf _ | UO_BVnot _ | UO_BVneg _
      | UO_BVextr _ | UO_BVzextn _ | UO_BVsextn _ -> SL.singleton LBitvectors

    let logic_of_bop = function
      | BO_Zplus
      | BO_Zminus
      | BO_Zmult
      | BO_Zlt
      | BO_Zle
      | BO_Zge
      | BO_Zgt -> SL.singleton LLia
      | BO_eq ty -> Btype.logic ty
      | BO_BVand _
      | BO_BVor _
      | BO_BVxor _
      | BO_BVadd _
      | BO_BVmult _
      | BO_BVult _
      | BO_BVslt _
      | BO_BVconcat _ -> SL.singleton LBitvectors
      | BO_select (ti, te)
      | BO_diffarray (ti, te) ->
        SL.add LArrays (SL.union (Btype.logic ti) (Btype.logic te))


    let logic_of_top = function
      | TO_store (ti, te) ->
        SL.add LArrays (SL.union (Btype.logic ti) (Btype.logic te))

    let logic_of_nop = function
      | NO_distinct ty -> Btype.logic ty

    
    let logic_of_indexed t =
      Array.fold_left (fun l ty ->
         SL.union (Btype.logic ty) l  
        ) (Btype.logic t.hval.tres) t.hval.tparams


    let logic_ro reify =
      Hashtbl.fold (fun _ op -> SL.union (logic_of_indexed op))
        reify.tbl SL.empty

  end


(** Definition of atoms *)

type atom = 
  | Acop of cop
  | Auop of uop * hatom 
  | Abop of bop * hatom * hatom 
  | Atop of top * hatom * hatom * hatom
  | Anop of nop * hatom array
  | Aapp of indexed_op * hatom array

and hatom = atom gen_hashed

(* let pp_acop = function *)
(*   | CO_xH -> "CO_xH" *)
(*   | CO_Z0 -> "CO_Z0" *)

(* let pp_auop = function *)
(*   | UO_xO -> "UO_xO" *)
(*   | UO_xI -> "UO_xI" *)
(*   | UO_Zpos -> "UO_Zpos" *)
(*   | UO_Zneg -> "UO_Zneg" *)
(*   | UO_Zopp -> "UO_Zopp" *)

(* let pp_abop = function *)
(*   | BO_Zplus -> "BO_Zplus" *)
(*   | BO_Zminus -> "BO_Zminus" *)
(*   | BO_Zmult -> "BO_Zmult" *)
(*   | BO_Zlt -> "BO_Zlt" *)
(*   | BO_Zle -> "BO_Zle" *)
(*   | BO_Zge -> "BO_Zge" *)
(*   | BO_Zgt -> "BO_Zgt" *)
(*   | BO_eq _ -> "(BO_eq ??)" *)

(* let rec pp_atom = function *)
(*   | Acop c -> "(Acop "^(pp_acop c)^")" *)
(*   | Auop (u,b) -> "(Auop "^(pp_auop u)^" "^(pp_atom b.hval)^")" *)
(*   | Abop (b,c,d) -> "(Abop "^(pp_abop b)^" "^(pp_atom c.hval)^" "^(pp_atom d.hval)^")" *)
(*   | Aapp (op,a) -> "(Aapp "^(string_of_int op.index)^" ("^(Array.fold_left (fun acc h -> acc^" "^(pp_atom h.hval)) "" a)^"))" *)

module HashedAtom =
  struct 
    type t = atom

    let equal a b =
      match a, b with
      | Acop opa, Acop opb -> Op.c_equal opa opb
      | Auop(opa,ha), Auop(opb,hb) -> Op.u_equal opa opb && ha.index == hb.index
      | Abop(opa,ha1,ha2), Abop(opb,hb1,hb2) ->
	Op.b_equal opa opb && ha1.index == hb1.index && ha2.index == hb2.index
      | Atop(opa,ha1,ha2,ha3), Atop(opb,hb1,hb2,hb3) ->
	Op.t_equal opa opb && ha1.index == hb1.index &&
         ha2.index == hb2.index && ha3.index == hb3.index
      | Anop (opa,ha), Anop (opb,hb) ->
        let na = Array.length ha in
        let nb = Array.length hb in
        let i = ref (-1) in
        Op.n_equal opa opb && na == nb &&
        Array.fold_left
          (fun b h -> incr i; b && h.index == hb.(!i).index) true ha
      | Aapp (va,ha), Aapp (vb,hb) ->
        let na = Array.length ha in
        let nb = Array.length hb in
        let i = ref (-1) in
        Op.i_equal va vb && na == nb &&
        Array.fold_left
          (fun b h -> incr i; b && h.index == hb.(!i).index) true ha
      | _, _ -> false

    let hash = function
      |	Acop op -> ((Hashtbl.hash op) lsl 3) lxor 1
      | Auop (op,h) ->
          (( (h.index lsl 3) + (Hashtbl.hash op)) lsl 3) lxor 2
      | Abop (op,h1,h2) ->
        (((( (h1.index lsl 2) + h2.index) lsl 3) + Hashtbl.hash op) lsl 3) lxor 3
      | Atop (op,h1,h2,h3) ->
        (((( ((h1.index lsl 2) + h2.index) lsl 3) + h3.index) lsl 4
          + Hashtbl.hash op) lsl 4) lxor 4
      | Anop (op, args) ->
          let hash_args =
            match Array.length args with
            | 0 -> 0
            | 1 -> args.(0).index
            | 2 -> args.(1).index lsl 2 + args.(0).index
            | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index
          in
          (hash_args lsl 5 + (Hashtbl.hash op) lsl 3) lxor 4
      | Aapp (op, args) ->
          let hash_args =
            match Array.length args with
            | 0 -> 0
            | 1 -> args.(0).index
            | 2 -> args.(1).index lsl 2 + args.(0).index
            | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index
          in
          (hash_args lsl 5 + op.index lsl 3) lxor 4


    
  end

module HashAtom = Hashtbl.Make(HashedAtom)

module Atom = 
  struct 

    type t = hatom

    let atom h = h.hval
    let index h = h.index 

    let equal h1 h2 = h1.index == h2.index

    let type_of h =
      match h.hval with
      | Acop op -> Op.c_type_of op
      | Auop (op,_) -> Op.u_type_of op
      | Abop (op,_,_) -> Op.b_type_of op
      | Atop (op,_,_,_) -> Op.t_type_of op
      | Anop (op,_) -> Op.n_type_of op
      | Aapp (op,_) -> Op.i_type_of op

    let is_bool_type h = Btype.equal (type_of h) Tbool
    let is_bv_type h = match type_of h with | TBV _ -> true | _ -> false


    let rec compute_int = function
      | Acop c ->
        (match c with
          | CO_xH -> 1
          | CO_Z0 -> 0
          | CO_BV _ -> assert false)
      | Auop (op,h) ->
        (match op with
          | UO_xO -> 2*(compute_hint h)
          | UO_xI -> 2*(compute_hint h) + 1
          | UO_Zpos -> compute_hint h
          | UO_Zneg -> - (compute_hint h)
          | UO_Zopp | UO_BVbitOf _
          | UO_BVnot _ | UO_BVneg _
          | UO_BVextr _ | UO_BVzextn _ | UO_BVsextn _ -> assert false)
      | _ -> assert false

    and compute_hint h = compute_int (atom h)

    let to_smt_int fmt i =
      let s1 = if i < 0 then "(- " else "" in
      let s2 = if i < 0 then ")" else "" in
      let j = if i < 0 then -i else i in
      Format.fprintf fmt "%s%i%s" s1 j s2


    let rec bv_to_smt fmt = function
      | true :: bv -> Format.fprintf fmt "%a1" bv_to_smt bv
      | false :: bv -> Format.fprintf fmt "%a0" bv_to_smt bv
      | [] -> ()

    
    let rec to_smt fmt h = to_smt_atom fmt (atom h)

    and to_smt_atom fmt = function
      | Acop (CO_BV bv) -> Format.fprintf fmt "#b%a" bv_to_smt bv
      | Acop _ as a -> to_smt_int fmt (compute_int a)
      | Auop (UO_Zopp,h) ->
        Format.fprintf fmt "(- ";
        to_smt fmt h;
        Format.fprintf fmt ")"
      | Auop (UO_BVbitOf (_, i), h) ->
        Format.fprintf fmt "(bitof %d %a)" i to_smt h
      | Auop (UO_BVnot _, h) ->
        Format.fprintf fmt "(bvnot %a)" to_smt h
      | Auop (UO_BVneg _, h) ->
        Format.fprintf fmt "(bvneg %a)" to_smt h
      | Auop (UO_BVextr (i, n, _), h) ->
        Format.fprintf fmt "((_ extract %d %d) %a)" i (i+n) to_smt h
      | Auop (UO_BVzextn (_, n), h) ->
        Format.fprintf fmt "((_ zero_extend %d) %a)" n to_smt h
      | Auop (UO_BVsextn (_, n), h) ->
        Format.fprintf fmt "((_ sign_extend %d) %a)" n to_smt h
      | Auop _ as a -> to_smt_int fmt (compute_int a)
      | Abop (op,h1,h2) -> to_smt_bop fmt op h1 h2
      | Atop (op,h1,h2,h3) -> to_smt_top fmt op h1 h2 h3
      | Anop (op,a) -> to_smt_nop fmt op a
      | Aapp (op,a) ->
        if Array.length a = 0 then (
          Format.fprintf fmt "op_%i" op.index;
        ) else (
          Format.fprintf fmt "(op_%i" op.index;
          Array.iter (fun h -> Format.fprintf fmt " "; to_smt fmt h) a;
          Format.fprintf fmt ")"
        )

    and to_smt_bop fmt op h1 h2 =
      let s = match op with
        | BO_Zplus -> "+"
        | BO_Zminus -> "-"
        | BO_Zmult -> "*"
        | BO_Zlt -> "<"
        | BO_Zle -> "<="
        | BO_Zge -> ">="
        | BO_Zgt -> ">"
        | BO_eq _ -> "="
        | BO_BVand _ -> "bvand"
        | BO_BVor _ -> "bvor"
        | BO_BVxor _ -> "bvxor"
        | BO_BVadd _ -> "bvadd"
        | BO_BVmult _ -> "bvmul"
        | BO_BVult _ -> "bvult"
        | BO_BVslt _ -> "bvslt"
        | BO_BVconcat _ -> "concat"
        | BO_select _ -> "select"
        | BO_diffarray _ -> "diff" (* should not be used in goals *)
      in
      Format.fprintf fmt "(%s %a %a)" s to_smt h1 to_smt h2

    and to_smt_top fmt op h1 h2 h3=
      let s = match op with
        | TO_store _ -> "store"
      in
      Format.fprintf fmt "(%s %a %a %a)" s to_smt h1 to_smt h2 to_smt h3

    and to_smt_nop fmt op a =
      let s = match op with
        | NO_distinct _ -> "distinct" in
      Format.fprintf fmt "(%s" s;
      Array.iter (fun h -> Format.fprintf fmt " "; to_smt fmt h) a;
      Format.fprintf fmt ")"



    exception NotWellTyped of atom

    let check a =
      match a with
      | Acop _ -> ()
      | Auop(op,h) -> 
	if not (Btype.equal (Op.u_type_arg op) (type_of h)) then
	  raise (NotWellTyped a)
      | Abop(op,h1,h2) ->
	let (t1,t2) = Op.b_type_args op in
 	if not (Btype.equal t1 (type_of h1) && Btype.equal t2 (type_of h2))
	then raise (NotWellTyped a)
      | Atop(op,h1,h2,h3) ->
	let (t1,t2,t3) = Op.t_type_args op in
        if not (Btype.equal t1 (type_of h1) &&
                Btype.equal t2 (type_of h2) &&
                Btype.equal t3 (type_of h3))
	then raise (NotWellTyped a)
      | Anop(op,ha) ->
        let ty = Op.n_type_args op in
        Array.iter
          (fun h -> if not (Btype.equal ty (type_of h)) then
              raise (NotWellTyped a)) ha
      | Aapp(op,args) ->
	let tparams = Op.i_type_args op in
	Array.iteri (fun i t -> 
	    if not (Btype.equal t (type_of args.(i))) then
	      raise (NotWellTyped a)) tparams

    type reify_tbl =
      { mutable count : int;
	tbl : hatom HashAtom.t 
      }

    let create () = 
      { count = 0;
	tbl =  HashAtom.create 17 }

    let op_coq_terms = Hashtbl.create 17

    let clear reify =
      Hashtbl.clear op_coq_terms;
      reify.count <- 0;
      HashAtom.clear reify.tbl

    let declare reify a = 
      check a;
      let res = {index = reify.count; hval = a} in
      HashAtom.add reify.tbl a res;
      reify.count <- reify.count + 1;
      res

    let get reify a =
      try HashAtom.find reify.tbl a
      with Not_found -> declare reify a


    (** Given a coq term, build the corresponding atom *)
    type coq_cst =
      | CCxH
      | CCZ0
      | CCBV
      | CCxO
      | CCxI
      | CCZpos
      | CCZneg
      | CCZopp
      | CCBVbitOf
      | CCBVnot
      | CCBVneg
      | CCZplus
      | CCZminus
      | CCZmult
      | CCZlt
      | CCZle
      | CCZge
      | CCZgt
      | CCBVand
      | CCBVor
      | CCBVxor
      | CCBVadd
      | CCBVmult
      | CCBVult
      | CCBVslt
      | CCBVconcat
      | CCBVextr
      | CCBVsextn
      | CCBVzextn
      | CCeqb
      | CCeqbP
      | CCeqbZ
      | CCeqbBV
      | CCeqbA
      | CCselect
      | CCdiff
      | CCstore
      | CCunknown

    let op_tbl () =
      let tbl = Hashtbl.create 29 in
      let add (c1,c2) = Hashtbl.add tbl (Lazy.force c1) c2 in
      List.iter add
	[ cxH,CCxH; cZ0,CCZ0; cof_bits, CCBV;
          cxO,CCxO; cxI,CCxI; cZpos,CCZpos; cZneg,CCZneg; copp,CCZopp;
          cbitOf, CCBVbitOf; cbv_not, CCBVnot; cbv_neg, CCBVneg;
          cbv_extr, CCBVextr; cbv_zextn, CCBVzextn; cbv_sextn, CCBVsextn;
          cadd,CCZplus; csub,CCZminus; cmul,CCZmult; cltb,CCZlt;
          cleb,CCZle; cgeb,CCZge; cgtb,CCZgt;
          cbv_and, CCBVand; cbv_or, CCBVor; cbv_xor, CCBVxor;
          cbv_add, CCBVadd; cbv_mult, CCBVmult;
          cbv_ult, CCBVult; cbv_slt, CCBVslt; cbv_concat, CCBVconcat;
          ceqb,CCeqb; ceqbP,CCeqbP; ceqbZ, CCeqbZ; cbv_eq, CCeqbBV;
          cselect, CCselect; cdiff, CCdiff;
          cstore, CCstore;
          cequalarray, CCeqbA;
        ];
      tbl

    let op_tbl = lazy (op_tbl ())

    


    let get_coq_term_op =
      Hashtbl.find op_coq_terms
    
        
    let of_coq rt ro reify env sigma c =
      let op_tbl = Lazy.force op_tbl in
      let get_cst c =
	try Hashtbl.find op_tbl c with Not_found -> CCunknown in
      let rec mk_hatom h =
	let c, args = Term.decompose_app h in
	match get_cst c with
          | CCxH -> mk_cop CCxH args
          | CCZ0 -> mk_cop CCZ0 args
          | CCBV -> mk_cop CCBV args
          | CCxO -> mk_uop UO_xO args
          | CCxI -> mk_uop UO_xI args
          | CCZpos -> mk_uop UO_Zpos args
          | CCZneg -> mk_uop UO_Zneg args
          | CCZopp -> mk_uop UO_Zopp args
          | CCBVbitOf -> mk_bvbitof args
          | CCBVnot -> mk_bvnot args
          | CCBVneg -> mk_bvneg args
          | CCZplus -> mk_bop BO_Zplus args
          | CCZminus -> mk_bop BO_Zminus args
          | CCZmult -> mk_bop BO_Zmult args
          | CCZlt -> mk_bop BO_Zlt args
          | CCZle -> mk_bop BO_Zle args
          | CCZge -> mk_bop BO_Zge args
          | CCZgt -> mk_bop BO_Zgt args
          | CCBVand -> mk_bop_bvand args
          | CCBVor -> mk_bop_bvor args
          | CCBVxor -> mk_bop_bvxor args
          | CCBVadd -> mk_bop_bvadd args
          | CCBVmult -> mk_bop_bvmult args
          | CCBVult -> mk_bop_bvult args
          | CCBVslt -> mk_bop_bvslt args
          | CCBVconcat -> mk_bop_bvconcat args
          | CCBVextr -> mk_bvextr args
          | CCBVzextn -> mk_bvzextn args
          | CCBVsextn -> mk_bvsextn args
          | CCeqb -> mk_bop (BO_eq Tbool) args
          | CCeqbP -> mk_bop (BO_eq Tpositive) args
          | CCeqbZ -> mk_bop (BO_eq TZ) args
          | CCeqbA -> mk_bop_farray_equal args
          | CCeqbBV -> mk_bop_bveq args
          | CCselect -> mk_bop_select args
          | CCdiff -> mk_bop_diff args
          | CCstore -> mk_top_store args
	  | CCunknown -> mk_unknown c args (Retyping.get_type_of env sigma h)

    
      and mk_cop op args = match op, args with
        | CCxH, [] -> get reify (Acop CO_xH)
        | CCZ0, [] -> get reify (Acop CO_Z0)
        | CCBV, [bs] -> get reify (Acop (CO_BV (mk_bool_list bs)))
        | _ -> assert false
          
    
      and mk_uop op = function
        | [a] -> let h = mk_hatom a in get reify (Auop (op,h))
        | _ -> assert false

      and mk_bvbitof = function
        | [s;n;a] ->
          let h = mk_hatom a in
          get reify (Auop (UO_BVbitOf (mk_bvsize s, mk_nat n), h))
        | _ -> assert false

      and mk_bvnot = function
        | [s;a] ->
          let h = mk_hatom a in
          get reify (Auop (UO_BVnot (mk_bvsize s), h))
        | _ -> assert false

      and mk_bvneg = function
        | [s;a] ->
          let h = mk_hatom a in
          get reify (Auop (UO_BVneg (mk_bvsize s), h))
        | _ -> assert false

      and mk_bvextr = function
        | [i;n;s;a] ->
          let h = mk_hatom a in
          get reify (Auop (UO_BVextr (mk_N i, mk_N n, mk_bvsize s), h))
        | _ -> assert false

      and mk_bvzextn = function
        | [s;n;a] ->
          let h = mk_hatom a in
          get reify (Auop (UO_BVzextn (mk_bvsize s, mk_N n), h))
        | _ -> assert false

      and mk_bvsextn = function
        | [s;n;a] ->
          let h = mk_hatom a in
          get reify (Auop (UO_BVsextn (mk_bvsize s, mk_N n), h))
        | _ -> assert false

      and mk_bop op = function
        | [a1;a2] ->
          let h1 = mk_hatom a1 in
          let h2 = mk_hatom a2 in
          get reify (Abop (op,h1,h2))
        | _ -> assert false

      and mk_top op = function
        | [a1;a2;a3] ->
          let h1 = mk_hatom a1 in
          let h2 = mk_hatom a2 in
          let h3 = mk_hatom a3 in
          get reify (Atop (op,h1,h2,h3))
        | _ -> assert false

      and mk_bop_bvand = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVand s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvor = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVor s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvxor = function
        | [s;a1;a2] ->
          let s' = mk_bvsize s in
          mk_bop (BO_BVxor s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvadd = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVadd s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvmult = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVmult s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvult = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVult s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvslt = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVslt s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvconcat = function
        | [s1;s2;a1;a2] ->
           mk_bop (BO_BVconcat (mk_bvsize s1, mk_bvsize s2)) [a1;a2]
        | _ -> assert false

      and mk_bop_bveq = function
        | [s;a1;a2] ->
          let s' = mk_bvsize s in
          mk_bop (BO_eq (TBV s')) [a1;a2]
        | _ -> assert false

      and mk_bop_select = function
        | [ti;te;_;_;_;a;i] ->
          let ti' = Btype.of_coq rt ti in
          let te' = Btype.of_coq rt te in
          mk_bop (BO_select (ti', te')) [a; i]
        | _ -> assert false

      and mk_bop_diff = function
        | [ti;te;_;_;_;_;_;_;_;_;a;b] ->
          let ti' = Btype.of_coq rt ti in
          let te' = Btype.of_coq rt te in
          mk_bop (BO_diffarray (ti', te')) [a; b]
        | _ -> assert false

      and mk_top_store = function
        | [ti;te;_;_;_;_;_;_;a;i;e] ->
          let ti' = Btype.of_coq rt ti in
          let te' = Btype.of_coq rt te in
          mk_top (TO_store (ti', te')) [a; i; e]
        | _ -> assert false

      and mk_bop_farray_equal = function
        | [ti;te;_;_;_;_;_;a;b] ->
          let ti' = Btype.of_coq rt ti in
          let te' = Btype.of_coq rt te in
          mk_bop (BO_eq (TFArray (ti', te'))) [a; b]
        | _ -> assert false

    
      and mk_unknown c args ty =
        let hargs = Array.of_list (List.map mk_hatom args) in
        let op =
          try Op.of_coq ro c
          with | Not_found ->
            let targs = Array.map type_of hargs in
            let tres = Btype.of_coq rt ty in
            Op.declare ro c targs tres in
        Hashtbl.add op_coq_terms op.index c;
        get reify (Aapp (op,hargs)) in

       mk_hatom c


    let to_coq h = mkInt h.index

    let a_to_coq a =
      match a with
      | Acop op -> mklApp cAcop [|Op.c_to_coq op|]
      | Auop (op,h) -> mklApp cAuop [|Op.u_to_coq op; to_coq h|]
      | Abop (op,h1,h2) -> 
	  mklApp cAbop [|Op.b_to_coq op;to_coq h1; to_coq h2|]
      | Atop (op,h1,h2,h3) -> 
	  mklApp cAtop [|Op.t_to_coq op;to_coq h1; to_coq h2; to_coq h3|]
      | Anop (op,ha) ->
        let cop = Op.n_to_coq op in
        let cargs = Array.fold_right
            (fun h l -> mklApp ccons [|Lazy.force cint; to_coq h; l|])
            ha (mklApp cnil [|Lazy.force cint|]) in
        mklApp cAnop [|cop; cargs|]
      | Aapp (op,args) ->
        let cop = Op.i_to_coq op in
        let cargs = Array.fold_right
            (fun h l -> mklApp ccons [|Lazy.force cint; to_coq h; l|])
            args (mklApp cnil [|Lazy.force cint|]) in
        mklApp cAapp [|cop; cargs|]

    let dft_atom = lazy (mklApp cAcop [| Lazy.force cCO_xH |])

    let to_array reify dft f =
      let t = Array.make (reify.count + 1) dft in
      let set _ h = t.(h.index) <- f h.hval in
      HashAtom.iter set reify.tbl;
      t

    let interp_tbl reify =
      let t = to_array reify (Lazy.force dft_atom) a_to_coq in
      Structures.mkArray (Lazy.force catom, t)


    (** Producing a Coq term corresponding to the interpretation of an atom *)
    let interp_to_coq t_i atom_tbl a =
      let rec interp_atom a =
	let l = index a in
	try Hashtbl.find atom_tbl l
	with Not_found ->
	  let pc =
	    match atom a with
              | Acop c -> Op.interp_cop c
              | Auop (op,h) -> Term.mkApp (Op.interp_uop op, [|interp_atom h|])
              | Abop (op,h1,h2) ->
                Term.mkApp (Op.interp_bop t_i op,
                            [|interp_atom h1; interp_atom h2|])
              | Atop (op,h1,h2,h3) ->
                Term.mkApp (Op.interp_top t_i op,
                            [|interp_atom h1; interp_atom h2; interp_atom h3|])
              | Anop (NO_distinct ty as op,ha) ->
                let cop = Op.interp_nop t_i op in
                let typ = Btype.interp t_i ty in
                let cargs = Array.fold_right (fun h l ->
                    mklApp ccons [|typ; interp_atom h; l|])
                    ha (mklApp cnil [|typ|]) in
                Term.mkApp (cop,[|cargs|])
              | Aapp (op,t) ->
                Term.mkApp (op.hval.op_val, Array.map interp_atom t) in
	  Hashtbl.add atom_tbl l pc;
	  pc in
      interp_atom a


    (* Generation of atoms *)

    let mk_nop op reify a = get reify (Anop (op,a))

    let mk_binop op reify h1 h2 = get reify (Abop (op, h1, h2))

    let mk_terop op reify h1 h2 h3 = get reify (Atop (op, h1, h2, h3))

    let mk_unop op reify h = get reify (Auop (op, h))

    let rec hatom_pos_of_int reify i =
      if i <= 1 then
        get reify (Acop CO_xH)
      else
        if i land 1 = 0
        then mk_unop UO_xO reify (hatom_pos_of_int reify (i lsr 1))
        else mk_unop UO_xI reify (hatom_pos_of_int reify (i lsr 1))

    let hatom_Z_of_int reify i =
      if i = 0 then
        get reify (Acop CO_Z0)
      else
        if i > 0
        then mk_unop UO_Zpos reify (hatom_pos_of_int reify i)
        else mk_unop UO_Zneg reify (hatom_pos_of_int reify (-i))

    let rec hatom_pos_of_bigint reify i =
      if Big_int.le_big_int i Big_int.unit_big_int then
        get reify (Acop CO_xH)
      else
        let (q,r) = Big_int.quomod_big_int i (Big_int.big_int_of_int 2) in
        if Big_int.eq_big_int r Big_int.zero_big_int then
          mk_unop UO_xO reify (hatom_pos_of_bigint reify q)
        else
          mk_unop UO_xI reify (hatom_pos_of_bigint reify q)

    let hatom_Z_of_bigint reify i =
      if Big_int.eq_big_int i Big_int.zero_big_int then
        get reify (Acop CO_Z0)
      else
        if Big_int.gt_big_int i Big_int.zero_big_int then
          mk_unop UO_Zpos reify (hatom_pos_of_bigint reify i)
        else
          mk_unop UO_Zneg reify
            (hatom_pos_of_bigint reify (Big_int.minus_big_int i))

    let mk_eq reify ty h1 h2 =
      let op = BO_eq ty in
      try
        HashAtom.find reify.tbl (Abop (op, h1, h2))
      with
        | Not_found ->
          try
            HashAtom.find reify.tbl (Abop (op, h2, h1))
          with
            | Not_found ->
              declare reify (Abop (op, h1, h2))

    let mk_lt = mk_binop BO_Zlt
    let mk_le = mk_binop BO_Zle
    let mk_gt = mk_binop BO_Zgt
    let mk_ge = mk_binop BO_Zge
    let mk_plus = mk_binop BO_Zplus
    let mk_minus = mk_binop BO_Zminus
    let mk_mult = mk_binop BO_Zmult
    let mk_bvand reify s = mk_binop (BO_BVand s) reify
    let mk_bvor reify s = mk_binop (BO_BVor s) reify
    let mk_bvxor reify s = mk_binop (BO_BVxor s) reify
    let mk_bvadd reify s = mk_binop (BO_BVadd s) reify
    let mk_bvmult reify s = mk_binop (BO_BVmult s) reify
    let mk_bvult reify s = mk_binop (BO_BVult s) reify
    let mk_bvslt reify s = mk_binop (BO_BVslt s) reify
    let mk_bvconcat reify s1 s2 = mk_binop (BO_BVconcat (s1, s2)) reify
    let mk_opp = mk_unop UO_Zopp
    let mk_distinct reify ty = mk_nop (NO_distinct ty) reify
    let mk_bitof reify s i = mk_unop (UO_BVbitOf (s, i)) reify
    let mk_bvnot reify s = mk_unop (UO_BVnot s) reify
    let mk_bvneg reify s = mk_unop (UO_BVneg s) reify
    let mk_bitof reify s i = mk_unop (UO_BVbitOf (s,i)) reify
    let mk_bvconst reify bool_list = get reify (Acop (CO_BV bool_list))
    let mk_select reify ti te = mk_binop (BO_select (ti, te)) reify
    let mk_diffarray reify ti te = mk_binop (BO_diffarray (ti, te)) reify
    let mk_store reify ti te = mk_terop (TO_store (ti, te)) reify
    let mk_bvextr reify ~i ~n ~s = mk_unop (UO_BVextr (i, n, s)) reify
    let mk_bvzextn reify ~s ~n = mk_unop (UO_BVzextn (s, n)) reify
    let mk_bvsextn reify ~s ~n = mk_unop (UO_BVsextn (s, n)) reify


    let rec logic_atom = function
      | Acop c -> Op.logic_of_cop c
      | Auop (u, h) -> SL.union (Op.logic_of_uop u) (logic h)
      | Abop (b, h1, h2) ->
        SL.union (Op.logic_of_bop b) (SL.union (logic h1) (logic h2))
      | Atop (t, h1, h2, h3) -> 
        SL.union (Op.logic_of_top t)
          (SL.union (logic h1) (SL.union (logic h2) (logic h3)))
      | Anop (n, ha) ->
        Array.fold_left (fun l h -> SL.union (logic h) l) (Op.logic_of_nop n) ha
      | Aapp (i, ha) ->
        Array.fold_left (fun l h -> SL.union (logic h) l)
          (Op.logic_of_indexed i) ha

    and logic h = logic_atom h.hval
    
  end


module Form = SmtForm.Make(Atom)
module Trace = SmtTrace.MakeOpt(Form)


(* Interpretation tables *)

let mk_ftype cod dom =
  let typeb = Lazy.force ctype in
  let typea = mklApp clist [|typeb|] in
  let a = Array.fold_right
      (fun bt acc -> mklApp ccons [|typeb; Btype.to_coq bt; acc|])
      cod (mklApp cnil [|typeb|]) in
  let b = Btype.to_coq dom in
  mklApp cpair [|typea;typeb;a;b|]

let make_t_i = Btype.make_t_i
let make_t_func ro t_i =
  Op.interp_tbl (mklApp ctval [|t_i|])
    (fun cod dom value -> mklApp cTval [|t_i; mk_ftype cod dom; value|]) ro

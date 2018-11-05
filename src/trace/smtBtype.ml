(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand    *                                                *)
(*     Benjamin Grégoire *                                                *)
(*     Chantal Keller    *                                                *)
(*     Alain Mebsout     ♯                                                *)
(*     Burak Ekici       ♯                                                *)
(*                                                                        *)
(*     * Inria - École Polytechnique - Université Paris-Sud               *)
(*     ♯ The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtMisc
open CoqTerms

(** Syntaxified version of Coq type *)

type indexed_type = Term.constr gen_hashed

let dummy_indexed_type i = {index = i; hval = Term.mkProp}
let indexed_type_index i = i.index
let indexed_type_hval i = i.hval

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | TFArray of btype * btype
  | Tindex of indexed_type
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

let index_tbl = Hashtbl.create 17

let index_to_coq i =
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
    mutable cuts : (Structures.names_id_t * Term.types) list;
    unsup_tbl : (btype, btype) Hashtbl.t;
  }

let create () =
  let htbl = Hashtbl.create 17 in
  Hashtbl.add htbl (Lazy.force cZ) TZ;
  Hashtbl.add htbl (Lazy.force cbool) Tbool;
  (* Hashtbl.add htbl (Lazy.force cpositive) Tpositive; *)
  { count = 0;
    tbl = htbl;
    cuts = [];
    unsup_tbl = Hashtbl.create 17;
  }


(* Should we give a way to clear it? *)
let op_coq_types = Hashtbl.create 17
let get_coq_type_op = Hashtbl.find op_coq_types


(* let logic_of_coq reify t = logic (of_coq reify t) *)


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

let get_cuts reify = reify.cuts

let declare reify t typ_compdec =
  (* TODO: allows to have only typ_compdec *)
  assert (not (Hashtbl.mem reify.tbl t));
  let res = Tindex {index = reify.count; hval = typ_compdec} in
  Hashtbl.add reify.tbl t res;
  reify.count <- reify.count + 1;
  res

exception Unknown_type of btype

let check_known ty known_logic =
  let l = logic ty in
  if not (SL.subset l known_logic) then raise (Unknown_type ty)
  else ty

let rec compdec_btype reify = function
  | Tbool -> Lazy.force cbool_compdec
  | TZ -> Lazy.force cZ_compdec
  | Tpositive -> Lazy.force cPositive_compdec
  | TBV s -> mklApp cBV_compdec [|mkN s|]
  | TFArray (ti, te) ->
     mklApp cFArray_compdec
       [|interp_to_coq reify ti; interp_to_coq reify te;
         compdec_btype reify ti; compdec_btype reify te|]
  | Tindex i ->
     let c, args = Term.decompose_app i.hval in
     if Term.eq_constr c (Lazy.force cTyp_compdec) then
       match args with
         | [_; tic] -> tic
         | _ -> assert false
     else assert false


let declare_and_compdec reify t ty =
  try Hashtbl.find reify.unsup_tbl ty
  with Not_found ->
    let res =
      declare reify t (mklApp cTyp_compdec [|t; compdec_btype reify ty|])
    in
    Hashtbl.add reify.unsup_tbl ty res;
    res


let rec of_coq reify known_logic t =
  try
    let c, args = Term.decompose_app t in
    if Term.eq_constr c (Lazy.force cbool) ||
         Term.eq_constr c (Lazy.force cTbool) then Tbool
    else if Term.eq_constr c (Lazy.force cZ) ||
              Term.eq_constr c (Lazy.force cTZ) then
      check_known TZ known_logic
    else if Term.eq_constr c (Lazy.force cpositive) ||
              Term.eq_constr c (Lazy.force cTpositive) then
      check_known Tpositive known_logic
    else if Term.eq_constr c (Lazy.force cbitvector) ||
              Term.eq_constr c (Lazy.force cTBV) then
      match args with
        | [s] -> check_known (TBV (mk_bvsize s)) known_logic
        | _ -> assert false
    else if Term.eq_constr c (Lazy.force cfarray) ||
              Term.eq_constr c (Lazy.force cTFArray) then
      match args with
        | ti :: te :: _ ->
           let ty = TFArray (of_coq reify known_logic ti,
                             of_coq reify known_logic te) in
           check_known ty known_logic
        | _ -> assert false
    else
      try Hashtbl.find reify.tbl t
      with Not_found ->
        let n = string_of_int (List.length reify.cuts) in
        let compdec_name = Names.id_of_string ("CompDec"^n) in
        let compdec_var = Term.mkVar compdec_name in
        let compdec_type = mklApp cCompDec [| t |]in
        reify.cuts <- (compdec_name, compdec_type) :: reify.cuts;
        let ce = mklApp cTyp_compdec [|t; compdec_var|] in
        let ty = declare reify t ce in
        (match ty with Tindex h -> Hashtbl.add op_coq_types h.index t | _ -> assert false);
        ty

  with Unknown_type ty ->
    try Hashtbl.find reify.tbl t
    with Not_found -> declare_and_compdec reify t ty

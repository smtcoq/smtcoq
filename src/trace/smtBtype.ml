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


open SmtMisc
open CoqTerms

(** Reified version of Coq type *)

type uninterpreted_type =
  (* Uninterpreted type for which a CompDec is already known
     The constr is of type typ_compdec
   *)
  | CompDec of Structures.constr
  (* Uninterpreted type for which the knowledge of a CompDec is delayed
     until either:
     - one is used
     - we have reached the end of the process and we generate a new one
       via a cut
     The constr is of type Type
   *)
  | Delayed of Structures.constr

type indexed_type = uninterpreted_type gen_hashed

let dummy_indexed_type i = {index = i; hval = Delayed (Structures.mkProp)}
let indexed_type_index i = i.index
let indexed_type_compdec i =
  match i.hval with
    | CompDec compdec -> compdec
    | Delayed _ -> assert false

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | TFArray of btype * btype
  | Tindex of indexed_type

let index_tbl = Hashtbl.create 17

let index_to_coq i =
  try Hashtbl.find index_tbl i
  with Not_found ->
    let interp = mklApp cTindex [|mkInt i|] in
    Hashtbl.add index_tbl i interp;
    interp

let indexed_type_of_int i =
  {index = i; hval = Delayed (index_to_coq i) }

module HashedBtype : Hashtbl.HashedType with type t = btype = struct
  type t = btype

  let rec equal t1 t2 =
    match t1,t2 with
      | Tindex i, Tindex j -> i.index == j.index
      | TBV i, TBV j -> i == j
      | TFArray (ti, te), TFArray (ti', te') -> equal ti ti' && equal te te'
      | _ -> t1 == t2

  let rec hash = function
    | TZ -> 1
    | Tbool -> 2
    | Tpositive -> 3
    | TBV s -> s lxor 4
    | TFArray (t1, t2) -> ((((hash t1) lsl 3) land (hash t2)) lsl 3) lxor 5
    | Tindex i -> (i.index lsl 3) lxor 6
end

let rec to_coq = function
  | TZ -> Lazy.force cTZ
  | Tbool -> Lazy.force cTbool
  | Tpositive -> Lazy.force cTpositive
  | TBV n -> mklApp cTBV [|mkN n|]
  | Tindex i -> index_to_coq i.index
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
    tbl : (Structures.constr, btype) Hashtbl.t;
    mutable cuts : (Structures.id * Structures.types) list;
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

let copy t =
  { count = t.count;
    tbl = Hashtbl.copy t.tbl;
    cuts = t.cuts;
    unsup_tbl = Hashtbl.copy t.unsup_tbl }


(* Should we give a way to clear it? *)
let op_coq_types = Hashtbl.create 17
let get_coq_type_op = Hashtbl.find op_coq_types


(* let logic_of_coq reify t = logic (of_coq reify t) *)


let interp_tbl reify =
  let t = Array.make (reify.count + 1) (Lazy.force cunit_typ_compdec) in
  let set c bt =
    match bt with
      | Tindex it ->
         (match it.hval with
            | CompDec compdec -> t.(it.index) <- compdec; Some bt
            | Delayed ty ->
               let n = string_of_int (List.length reify.cuts) in
               let compdec_name = Structures.mkId ("CompDec"^n) in
               let compdec_var = Structures.mkVar compdec_name in
               let compdec_type = mklApp cCompDec [| ty |] in
               reify.cuts <- (compdec_name, compdec_type) :: reify.cuts;
               let ce = mklApp cTyp_compdec [|ty; compdec_var|] in
               t.(it.index) <- ce;
               Some (Tindex {index = it.index; hval = CompDec ce})
         )
      | _ -> Some bt
  in
  Hashtbl.filter_map_inplace set reify.tbl;
  Structures.mkArray (Lazy.force ctyp_compdec, t)


let to_list reify =
  let set _ t acc = match t with
      | Tindex it -> (it.index,it)::acc
      | _ -> acc in
  Hashtbl.fold set reify.tbl []

let make_t_i rt = interp_tbl rt


(* let interp_t t_i t =
 *   mklApp cinterp_t [|t_i ; to_coq t|] *)

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
  | Tindex c ->
     (match c.hval with
        | CompDec t -> mklApp cte_carrier [|t|]
        | Delayed _ -> assert false
     )
  (* | TFArray _ as t -> interp_t t_i t *)
  | TFArray (ti,te) ->
     mklApp cfarray [| interp t_i ti; interp t_i te;
                       ord_interp t_i ti; inh_interp t_i te |]


let interp_to_coq reify t = interp (make_t_i reify) t

let get_cuts reify = reify.cuts

let declare reify t typ_uninterpreted_type =
  assert (not (Hashtbl.mem reify.tbl t));
  let res = Tindex {index = reify.count; hval = typ_uninterpreted_type} in
  Hashtbl.add reify.tbl t res;
  reify.count <- reify.count + 1;
  res

let declare_compdec reify t compdec =
  let ce = mklApp cTyp_compdec [|t; compdec|] in
  let ty = declare reify t (CompDec ce) in
  (match ty with Tindex h -> Hashtbl.add op_coq_types h.index t | _ -> assert false);
  ty

let declare_delayed reify t delayed =
  let ty = declare reify t (Delayed delayed) in
  (match ty with Tindex h -> Hashtbl.add op_coq_types h.index t | _ -> assert false);
  ty


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
     (match i.hval with
        | CompDec compdec ->
           let c, args = Structures.decompose_app compdec in
           if Structures.eq_constr c (Lazy.force cTyp_compdec) then
             match args with
               | [_; tic] -> tic
               | _ -> assert false
           else assert false
        | _ -> assert false
     )


let declare_and_compdec reify t ty =
  try Hashtbl.find reify.unsup_tbl ty
  with Not_found ->
    let res =
      declare reify t (CompDec (mklApp cTyp_compdec [|t; compdec_btype reify ty|]))
    in
    Hashtbl.add reify.unsup_tbl ty res;
    res



let rec of_coq reify known_logic t =
  try
    let c, args = Structures.decompose_app t in
    if Structures.eq_constr c (Lazy.force cbool) ||
         Structures.eq_constr c (Lazy.force cTbool) then Tbool
    else if Structures.eq_constr c (Lazy.force cZ) ||
              Structures.eq_constr c (Lazy.force cTZ) then
      check_known TZ known_logic
    else if Structures.eq_constr c (Lazy.force cpositive) ||
              Structures.eq_constr c (Lazy.force cTpositive) then
      check_known Tpositive known_logic
    else if Structures.eq_constr c (Lazy.force cbitvector) ||
              Structures.eq_constr c (Lazy.force cTBV) then
      match args with
        | [s] -> check_known (TBV (mk_bvsize s)) known_logic
        | _ -> assert false
    else if Structures.eq_constr c (Lazy.force cfarray) ||
              Structures.eq_constr c (Lazy.force cTFArray) then
      match args with
        | ti :: te :: _ ->
           let ty = TFArray (of_coq reify known_logic ti,
                             of_coq reify known_logic te) in
           check_known ty known_logic
        | _ -> assert false
    else
      try Hashtbl.find reify.tbl t
      with Not_found ->
        declare_delayed reify t t

  with Unknown_type ty ->
    try Hashtbl.find reify.tbl t
    with Not_found -> declare_and_compdec reify t ty


let of_coq_compdec reify t compdec =
  try
    let ty = Hashtbl.find reify.tbl t in
    match ty with
      | Tindex i ->
         (match i.hval with
            | CompDec _ -> ty
            | Delayed _ ->
               Hashtbl.remove reify.tbl t;
               let ce = mklApp cTyp_compdec [|t; compdec|] in
               let res = Tindex {index = i.index; hval = CompDec ce} in
               Hashtbl.add reify.tbl t res;
               res
         )
      | _ -> assert false
  with Not_found ->
    declare_compdec reify t compdec

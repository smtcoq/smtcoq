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


(** Hashing functions on Btypes *)

module HashBtype = Hashtbl.Make(SmtBtype.HashedBtype)

module HashedBtypePair : Hashtbl.HashedType
       with type t = SmtBtype.btype * SmtBtype.btype = struct
  type t = SmtBtype.btype * SmtBtype.btype

  let equal (t1,s1) (t2,s2) =
    SmtBtype.HashedBtype.equal t1 t2 && SmtBtype.HashedBtype.equal s1 s2

  let hash (t,s) =
    ((SmtBtype.HashedBtype.hash t) lsl 3) land (SmtBtype.HashedBtype.hash s)
end

module HashBtypePair = Hashtbl.Make(HashedBtypePair)


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
   | BO_eq of SmtBtype.btype
   | BO_BVand of int
   | BO_BVor of int
   | BO_BVxor of int
   | BO_BVadd of int
   | BO_BVmult of int
   | BO_BVult of int
   | BO_BVslt of int
   | BO_BVconcat of int * int
   | BO_BVshl of int
   | BO_BVshr of int
   | BO_select of SmtBtype.btype * SmtBtype.btype
   | BO_diffarray of SmtBtype.btype * SmtBtype.btype


type top =
  | TO_store of SmtBtype.btype * SmtBtype.btype


type nop =
  | NO_distinct of SmtBtype.btype

type op_def = {
    tparams : SmtBtype.btype array;
    tres : SmtBtype.btype;
    op_val : Structures.constr }

type index = Index of int
           | Rel_name of string

type indexed_op = index * op_def

let destruct s (i, hval) = match i with
    | Index index -> index, hval
    | Rel_name _ -> failwith s

let dummy_indexed_op i dom codom =
  (i, {tparams = dom; tres = codom; op_val = Structures.mkProp})

let indexed_op_index i =
  let index, _ = destruct "destruct on a Rel: called by indexed_op_index" i in
  index

let debruijn_indexed_op i ty =
  (Index i, {tparams = [||]; tres = ty; op_val = Structures.mkRel i})

module Op =
  struct
    let c_to_coq = function
      | CO_xH -> Lazy.force cCO_xH
      | CO_Z0 -> Lazy.force cCO_Z0
      | CO_BV bv -> mklApp cCO_BV [|mk_bv_list bv; mkN (List.length bv)|]

    let c_type_of = function
      | CO_xH -> SmtBtype.Tpositive
      | CO_Z0 -> SmtBtype.TZ
      | CO_BV bv -> SmtBtype.TBV (List.length bv)

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
      | UO_xO | UO_xI -> SmtBtype.Tpositive
      | UO_Zpos | UO_Zneg | UO_Zopp -> SmtBtype.TZ
      | UO_BVbitOf _ -> SmtBtype.Tbool
      | UO_BVnot s | UO_BVneg s -> SmtBtype.TBV s
      | UO_BVextr (_, n, _) -> SmtBtype.TBV n
      | UO_BVzextn (s, n) | UO_BVsextn (s, n) -> SmtBtype.TBV (s + n)

    let u_type_arg = function
      | UO_xO | UO_xI | UO_Zpos | UO_Zneg -> SmtBtype.Tpositive
      | UO_Zopp -> SmtBtype.TZ
      | UO_BVbitOf (s,_) -> SmtBtype.TBV s
      | UO_BVnot s | UO_BVneg s -> SmtBtype.TBV s
      | UO_BVextr (_, _, s) -> SmtBtype.TBV s
      | UO_BVzextn (s, _) | UO_BVsextn (s, _) -> SmtBtype.TBV s


    let interp_uop = function
      | UO_xO -> Lazy.force cxO
      | UO_xI -> Lazy.force cxI
      | UO_Zpos -> Lazy.force cZpos
      | UO_Zneg -> Lazy.force cZneg
      | UO_Zopp -> Lazy.force copp
      | UO_BVbitOf (s,i) -> mklApp cbitOf [|mkN s; mkNat i|]
      | UO_BVnot s -> mklApp cbv_not [|mkN s|]
      | UO_BVneg s -> mklApp cbv_neg [|mkN s|]
      | UO_BVextr (i, n, s) -> mklApp cbv_extr [|mkN i; mkN n; mkN s|]
      | UO_BVzextn (s, n) -> mklApp cbv_zextn [|mkN s; mkN n|]
      | UO_BVsextn (s, n) -> mklApp cbv_sextn [|mkN s; mkN n|]

    let eq_tbl = HashBtype.create 17
    let select_tbl = HashBtypePair.create 17
    let store_tbl = HashBtypePair.create 17
    let diffarray_tbl = HashBtypePair.create 17

    let eq_to_coq t =
      try HashBtype.find eq_tbl t
      with Not_found ->
	let op = mklApp cBO_eq [|SmtBtype.to_coq t|] in
	HashBtype.add eq_tbl t op;
	op

    let select_to_coq ti te =
      try HashBtypePair.find select_tbl (ti, te)
      with Not_found ->
        let op = mklApp cBO_select [|SmtBtype.to_coq ti; SmtBtype.to_coq te|] in
        HashBtypePair.add select_tbl (ti, te) op;
        op

    let store_to_coq ti te =
      try HashBtypePair.find store_tbl (ti, te)
      with Not_found ->
        let op = mklApp cTO_store [|SmtBtype.to_coq ti; SmtBtype.to_coq te|] in
        HashBtypePair.add store_tbl (ti, te) op;
        op

    let diffarray_to_coq ti te =
      try HashBtypePair.find diffarray_tbl (ti, te)
      with Not_found ->
        let op = mklApp cBO_diffarray [|SmtBtype.to_coq ti; SmtBtype.to_coq te|] in
        HashBtypePair.add diffarray_tbl (ti, te) op;
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
      | BO_BVshl s -> mklApp cBO_BVshl [|mkN s|]
      | BO_BVshr s -> mklApp cBO_BVshr [|mkN s|]
      | BO_select (ti, te) -> select_to_coq ti te
      | BO_diffarray (ti, te) -> diffarray_to_coq ti te

    let b_type_of = function
      | BO_Zplus | BO_Zminus | BO_Zmult -> SmtBtype.TZ
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt | BO_eq _
      | BO_BVult _ | BO_BVslt _ -> SmtBtype.Tbool
      | BO_BVand s | BO_BVor s | BO_BVxor s | BO_BVadd s | BO_BVmult s
      | BO_BVshl s | BO_BVshr s -> SmtBtype.TBV s
      | BO_BVconcat (s1, s2) -> SmtBtype.TBV (s1 + s2)
      | BO_select (_, te) -> te
      | BO_diffarray (ti, _) -> ti

    let b_type_args = function
      | BO_Zplus | BO_Zminus | BO_Zmult
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt -> (SmtBtype.TZ,SmtBtype.TZ)
      | BO_eq t -> (t,t)
      | BO_BVand s | BO_BVor s | BO_BVxor s | BO_BVadd s | BO_BVmult s
      | BO_BVult s | BO_BVslt s | BO_BVshl s | BO_BVshr s ->
        (SmtBtype.TBV s,SmtBtype.TBV s)
      | BO_BVconcat (s1, s2) -> (SmtBtype.TBV s1, SmtBtype.TBV s2)
      | BO_select (ti, te) -> (SmtBtype.TFArray (ti, te), ti)
      | BO_diffarray (ti, te) -> (SmtBtype.TFArray (ti, te), SmtBtype.TFArray (ti, te))


    (* let interp_ieq t_i t =
     *   mklApp cinterp_eqb [|t_i ; SmtBtype.to_coq t|] *)

 (*   let veval_t te =
      let env = Global.env () in
      let evd = Evd.from_env env in
      let evd, ty = Typing.type_of env evd te in
      Vnorm.cbv_vm env te ty


    let interp_ieq_eval t_i t =
      let te = mklApp cinterp_eqb [|t_i ; SmtBtype.to_coq t|] in
      veval_t te
      *)

    let interp_eqarray t_i ti te =
      mklApp cequalarray
        [|SmtBtype.interp t_i ti; SmtBtype.interp t_i te;
          SmtBtype.ord_interp t_i ti; SmtBtype.comp_interp t_i ti;
          SmtBtype.ord_interp t_i te; SmtBtype.comp_interp t_i te;
          SmtBtype.inh_interp t_i te |]

    let interp_select t_i ti te =
      mklApp cselect
        [|SmtBtype.interp t_i ti; SmtBtype.interp t_i te;
          SmtBtype.ord_interp t_i ti; SmtBtype.comp_interp t_i ti;
          SmtBtype.inh_interp t_i te|]

    let interp_diff t_i ti te =
      mklApp cdiff
        [|SmtBtype.interp t_i ti; SmtBtype.interp t_i te;
          SmtBtype.dec_interp t_i ti; SmtBtype.ord_interp t_i ti; SmtBtype.comp_interp t_i ti;
          SmtBtype.dec_interp t_i te; SmtBtype.ord_interp t_i te; SmtBtype.comp_interp t_i te;
          SmtBtype.inh_interp t_i ti; SmtBtype.inh_interp t_i te |]


    let interp_store t_i ti te =
      mklApp cstore
        [|SmtBtype.interp t_i ti; SmtBtype.interp t_i te;
          SmtBtype.dec_interp t_i ti; SmtBtype.ord_interp t_i ti; SmtBtype.comp_interp t_i ti;
          SmtBtype.ord_interp t_i te; SmtBtype.comp_interp t_i te; SmtBtype.inh_interp t_i te |]


    let interp_eq t_i = function
      | SmtBtype.TZ -> Lazy.force ceqbZ
      | SmtBtype.Tbool -> Lazy.force ceqb
      | SmtBtype.Tpositive -> Lazy.force ceqbP
      | SmtBtype.TBV s -> mklApp cbv_eq [|mkN s|]
      | SmtBtype.Tindex i ->
         let compdec = SmtBtype.indexed_type_compdec i in
         mklApp ceqb_of_compdec [|mklApp cte_carrier [|compdec|];
                                  mklApp cte_compdec [|compdec|]|]
      | SmtBtype.TFArray (ti, te) -> interp_eqarray t_i ti te



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
      | BO_BVshl s -> mklApp cbv_shl [|mkN s|]
      | BO_BVshr s -> mklApp cbv_shr [|mkN s|]
      | BO_select (ti, te) -> interp_select t_i ti te
      | BO_diffarray (ti, te) -> interp_diff t_i ti te

    let t_to_coq = function
      | TO_store (ti, te) -> store_to_coq ti te

    let t_type_of = function
      | TO_store (ti, te) -> SmtBtype.TFArray (ti, te)

    let t_type_args = function
      | TO_store (ti, te) -> SmtBtype.TFArray (ti, te), ti, te

    let interp_top t_i = function
      | TO_store (ti, te) -> interp_store t_i ti te


    let n_to_coq = function
      | NO_distinct t -> mklApp cNO_distinct [|SmtBtype.to_coq t|]

    let n_type_of = function
      | NO_distinct _ -> SmtBtype.Tbool

    let n_type_args = function
      | NO_distinct ty -> ty

    let interp_nop t_i = function
      | NO_distinct ty ->
        mklApp cdistinct [|SmtBtype.interp t_i ty; interp_eq t_i ty|]

    let i_to_coq i = let index, _ = destruct "destruct on a Rel: called by i_to_coq" i in
                     mkInt index

    let i_type_of (_, hval) = hval.tres

    let i_type_args (_, hval) = hval.tparams

    (* reify table *)
    type reify_tbl =
      { mutable count : int;
	        tbl : (Structures.constr, indexed_op) Hashtbl.t
      }

    let create () =
      { count = 0;
	tbl =  Hashtbl.create 17 }

    let declare reify op tparams tres os =
      assert (not (Hashtbl.mem reify.tbl op));
      let opa = { tparams = tparams; tres = tres; op_val = op } in
      match os with
      | None ->  let res = Index reify.count, opa in
                 Hashtbl.add reify.tbl op res;
                 reify.count <- reify.count + 1;
                 res
      | Some name -> Rel_name name, opa

    let of_coq reify op =
      Hashtbl.find reify.tbl op


    let interp_tbl tval mk_Tval reify =
      let t = Array.make (reify.count + 1)
	        (mk_Tval [||] SmtBtype.Tbool (Lazy.force ctrue)) in
      let set _ op =
        let index, hval = destruct "destruct on a Rel: called by set in interp_tbl" op in
        t.(index) <- mk_Tval hval.tparams hval.tres hval.op_val in
      Hashtbl.iter set reify.tbl;
      Structures.mkArray (tval, t)

    let to_list reify =
      let set _ op acc =
        let index, hval = destruct "destruct on a Rel: called by set in to_list" op in
        (index, hval.tparams, hval.tres, op)::acc in
      Hashtbl.fold set reify.tbl []

    let c_equal op1 op2 = match op1, op2 with
      | CO_BV bv1, CO_BV bv2 ->
        (try List.for_all2 (=) bv1 bv2 with
         | Invalid_argument _ -> false)
      | _ -> op1 == op2

    let c_hash = function
      | CO_xH -> 1
      | CO_Z0 -> 2
      | CO_BV l -> 3 + (List.fold_left (fun acc b -> if b then 2*acc+1 else 2*acc) 0 l)

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

    let u_hash = function
      | UO_xO -> 0
      | UO_xI -> 1
      | UO_Zpos -> 2
      | UO_Zneg -> 3
      | UO_Zopp -> 4
      | UO_BVbitOf (s,n) -> (n land s) lxor 5
      | UO_BVnot s -> s lxor 6
      | UO_BVneg s -> s lxor 7
      | UO_BVextr (s, n0, n1) -> (s land n0 land n1) lxor 8
      | UO_BVzextn (s, n) -> (s land n) lxor 9
      | UO_BVsextn (s, n) -> (s land n) lxor 10

    let b_equal op1 op2 =
      match op1,op2 with
        | BO_eq t1, BO_eq t2 -> SmtBtype.HashedBtype.equal t1 t2
        | BO_BVand n1, BO_BVand n2 -> n1 == n2
        | BO_BVor n1, BO_BVor n2 -> n1 == n2
        | BO_BVxor n1, BO_BVxor n2 -> n1 == n2
        | BO_BVadd n1, BO_BVadd n2 -> n1 == n2
        | BO_BVmult n1, BO_BVmult n2 -> n1 == n2
        | BO_BVult n1, BO_BVult n2 -> n1 == n2
        | BO_BVslt n1, BO_BVslt n2 -> n1 == n2
        | BO_BVconcat (n1,m1), BO_BVconcat (n2,m2) -> n1 == n2 && m1 == m2
        | BO_BVshl n1, BO_BVshl n2 -> n1 == n2
        | BO_BVshr n1, BO_BVshr n2 -> n1 == n2
        | BO_select (ti1, te1), BO_select (ti2, te2)
        | BO_diffarray (ti1, te1), BO_diffarray (ti2, te2) ->
           HashedBtypePair.equal (ti1, te1) (ti2, te2)
        | _ -> op1 == op2

    let b_hash = function
      | BO_Zplus -> 1
      | BO_Zminus -> 2
      | BO_Zmult -> 3
      | BO_Zlt -> 4
      | BO_Zle -> 5
      | BO_Zge -> 6
      | BO_Zgt -> 7
      | BO_eq ty -> ((SmtBtype.HashedBtype.hash ty) lsl 6) lxor 8
      | BO_BVand s -> s lxor 9
      | BO_BVor s -> s lxor 10
      | BO_BVxor s -> s lxor 11
      | BO_BVadd s -> s lxor 12
      | BO_BVmult s -> s lxor 13
      | BO_BVult s -> s lxor 14
      | BO_BVslt s -> s lxor 15
      | BO_BVconcat (s1,s2) -> (s1 land s2) lxor 16
      | BO_BVshl s -> s lxor 17
      | BO_BVshr s -> s lxor 18
      | BO_select (ti, te) -> ((HashedBtypePair.hash (ti, te)) lsl 6) lxor 19
      | BO_diffarray (ti, te) -> ((HashedBtypePair.hash (ti, te)) lsl 6) lxor 20

    let t_equal op1 op2 =
      match op1,op2 with
        | TO_store (ti1, te1), TO_store (ti2, te2) ->
          SmtBtype.HashedBtype.equal ti1 ti2 && SmtBtype.HashedBtype.equal te1 te2

    let t_hash = function
      | TO_store (ti, te) -> HashedBtypePair.hash (ti, te)

    let n_equal op1 op2 =
      match op1,op2 with
      | NO_distinct t1, NO_distinct t2 -> SmtBtype.HashedBtype.equal t1 t2

    let n_hash = function
      | NO_distinct t -> SmtBtype.HashedBtype.hash t

    let i_equal (i1, _) (i2, _) = i1 = i2




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
      | BO_eq ty -> SmtBtype.logic ty
      | BO_BVand _
      | BO_BVor _
      | BO_BVxor _
      | BO_BVadd _
      | BO_BVmult _
      | BO_BVult _
      | BO_BVslt _
      | BO_BVshl _
      | BO_BVshr _
      | BO_BVconcat _ -> SL.singleton LBitvectors
      | BO_select (ti, te)
      | BO_diffarray (ti, te) ->
        SL.add LArrays (SL.union (SmtBtype.logic ti) (SmtBtype.logic te))


    let logic_of_top = function
      | TO_store (ti, te) ->
        SL.add LArrays (SL.union (SmtBtype.logic ti) (SmtBtype.logic te))

    let logic_of_nop = function
      | NO_distinct ty -> SmtBtype.logic ty


    let logic_of_indexed t =
      let (_, hval) = destruct "destruct on a Rel: called by logic_of_indexed" t in
      Array.fold_left (fun l ty ->
         SL.union (SmtBtype.logic ty) l
        ) (SmtBtype.logic hval.tres) hval.tparams


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
      |	Acop op -> ((Op.c_hash op) lsl 3) lxor 1
      | Auop (op,h) ->
         (( (h.index lsl 3) + (Op.u_hash op)) lsl 3) lxor 2
      | Abop (op,h1,h2) ->
        (((( (h1.index lsl 2) + h2.index) lsl 3) + Op.b_hash op) lsl 3) lxor 3
      | Atop (op,h1,h2,h3) ->
        (((( ((h1.index lsl 2) + h2.index) lsl 3) + h3.index) lsl 4
          + Op.t_hash op) lsl 4) lxor 4
      | Anop (op, args) ->
          let hash_args =
            match Array.length args with
            | 0 -> 0
            | 1 -> args.(0).index
            | 2 -> args.(1).index lsl 2 + args.(0).index
            | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index
          in
          (hash_args lsl 5 + (Op.n_hash op) lsl 3) lxor 4
      | Aapp (op, args) ->
         let op_index = try fst (destruct "destruct on a Rel: called by hash" op) with _ -> 0 in
          let hash_args =
            match Array.length args with
            | 0 -> 0
            | 1 -> args.(0).index
            | 2 -> args.(1).index lsl 2 + args.(0).index
            | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index
          in
          (hash_args lsl 5 + op_index lsl 3) lxor 4



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

    let is_bool_type h = SmtBtype.HashedBtype.equal (type_of h) SmtBtype.Tbool
    let is_bv_type h = match type_of h with | SmtBtype.TBV _ -> true | _ -> false


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


    let to_smt_named ?pi:(pi=false) (fmt:Format.formatter) h =
      let rec to_smt fmt h =
        if pi then Format.fprintf fmt "%d:" (index h);
        to_smt_atom (atom h)

      and to_smt_atom = function
        | Acop (CO_BV bv) -> if List.length bv = 0 then Structures.error "Empty bit-vectors are not valid in SMT" else Format.fprintf fmt "#b%a" bv_to_smt bv
        | Acop _ as a -> to_smt_int fmt (compute_int a)
        | Auop (op,h) -> to_smt_uop op h
        | Abop (op,h1,h2) -> to_smt_bop op h1 h2
        | Atop (op,h1,h2,h3) -> to_smt_top op h1 h2 h3
        | Anop (op,a) -> to_smt_nop op a
        | Aapp ((i,op),a) ->
           let op_smt () =
             (match i with
                | Index index -> Format.fprintf fmt "op_%i" index
                | Rel_name name -> Format.fprintf fmt "%s" name);
             if pi then to_smt_op op
           in
           if Array.length a = 0 then (
             op_smt ()
           ) else (
             Format.fprintf fmt "(";
             op_smt ();
             Array.iter (fun h -> Format.fprintf fmt " "; to_smt fmt h) a;
             Format.fprintf fmt ")"
           )

      and to_smt_op {tparams=bta; tres=bt; op_val=t} =
        Format.fprintf fmt "[(";
        Array.iter (fun bt -> SmtBtype.to_smt fmt bt; Format.fprintf fmt " ") bta;
        Format.fprintf fmt ") ( ";
        SmtBtype.to_smt fmt bt;
        Format.fprintf fmt " ) ( %s )]" (Pp.string_of_ppcmds (Structures.pr_constr t))

      and to_smt_uop op h =
        match op with
          | UO_Zpos ->
             Format.fprintf fmt "%a" to_smt h
          | UO_Zneg ->
             Format.fprintf fmt "(- %a)" to_smt h
          | UO_Zopp ->
             Format.fprintf fmt "(- %a)" to_smt h
          | UO_BVbitOf (_, i) ->
             Format.fprintf fmt "(bitof %d %a)" i to_smt h
          | UO_BVnot _ ->
             Format.fprintf fmt "(bvnot %a)" to_smt h
          | UO_BVneg _ ->
             Format.fprintf fmt "(bvneg %a)" to_smt h
          | UO_BVextr (i, n, _) ->
             Format.fprintf fmt "((_ extract %d %d) %a)" (i+n-1) i to_smt h
          | UO_BVzextn (_, n) ->
             Format.fprintf fmt "((_ zero_extend %d) %a)" n to_smt h
          | UO_BVsextn (_, n) ->
             Format.fprintf fmt "((_ sign_extend %d) %a)" n to_smt h
          | _ -> to_smt_int fmt (compute_int (Auop (op, h)))

      and to_smt_bop op h1 h2 =
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
            | BO_BVshl _ -> "bvshl"
            | BO_BVshr _ -> "bvlshr"
            | BO_select _ -> "select"
            | BO_diffarray _ -> "diff" (* should not be used in goals *)
        in
        Format.fprintf fmt "(%s %a %a)" s to_smt h1 to_smt h2

      and to_smt_top op h1 h2 h3=
        let s = match op with
            | TO_store _ -> "store"
        in
        Format.fprintf fmt "(%s %a %a %a)" s to_smt h1 to_smt h2 to_smt h3

      and to_smt_nop op a =
        let s = match op with
            | NO_distinct _ -> "distinct" in
        Format.fprintf fmt "(%s" s;
        Array.iter (fun h -> Format.fprintf fmt " "; to_smt fmt h) a;
        Format.fprintf fmt ")"

      in
      to_smt fmt h

    let to_smt (fmt:Format.formatter) h = to_smt_named fmt h


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
      let res = {index = reify.count; hval = a} in
      HashAtom.add reify.tbl a res;
      reify.count <- reify.count + 1;
      res

    let rec get ?declare:(decl=true) reify a =
      if decl
      then try HashAtom.find reify.tbl a
           with Not_found ->
             (let a = check reify a in
              try HashAtom.find reify.tbl a
              with Not_found ->
                declare reify a)
      else {index = -1; hval = a}

    and check reify a =
      (* Format.eprintf "Checking %a @." to_smt_atom a; *)

      let check_one t h =
        let th = type_of h in
        if SmtBtype.HashedBtype.equal t th then
          h
        else if t == SmtBtype.TZ && th == SmtBtype.Tpositive then
          (* Special case: the SMT solver cannot distinguish Z from
             positive, we have to add the injection back *)
          get reify (Auop(UO_Zpos, h))
        else (
          Format.eprintf "Incorrect type: wanted %a, got %a@."
            SmtBtype.to_smt t SmtBtype.to_smt th;
          failwith (Format.asprintf "Atom %a is not of the expected type" to_smt h)
        )
      in

      let a =
        match a with
          | Acop _ -> a
          | Auop(op,h) ->
             let t = Op.u_type_arg op in
             Auop(op, check_one t h)
          | Abop(op,h1,h2) ->
	     let (t1,t2) = Op.b_type_args op in
             let h1 = check_one t1 h1 in
             let h2 = check_one t2 h2 in
             Abop(op, h1, h2)
          | Atop(op,h1,h2,h3) ->
	     let (t1,t2,t3) = Op.t_type_args op in
             let h1 = check_one t1 h1 in
             let h2 = check_one t2 h2 in
             let h3 = check_one t3 h3 in
             Atop(op, h1, h2, h3)
          | Anop(op,ha) ->
             let ty = Op.n_type_args op in
             Anop(op, Array.map (check_one ty) ha)
          | Aapp(op,args) ->
             let tparams = Op.i_type_args op in
             Aapp(op, Array.mapi (fun i -> check_one tparams.(i)) args)
      in
      a


    (* Identifies two equalities modulo symmetry *)
    let mk_eq_sym reify ?declare:(decl=true) ty h1 h2 =
      let op = BO_eq ty in
      try
        HashAtom.find reify.tbl (Abop (op, h1, h2))
      with Not_found ->
        try
          HashAtom.find reify.tbl (Abop (op, h2, h1))
        with Not_found ->
          get ~declare:decl reify (Abop (op, h1, h2))

    let mk_neg reify ({index = i; hval = a} as ha) =
      try HashAtom.find reify.tbl (Auop (UO_Zopp, ha))
      with Not_found ->
        let na = match a with
          | Auop (UO_Zpos, x) -> Auop (UO_Zneg, x)
          | Auop (UO_Zneg, x) -> Auop (UO_Zpos, x)
          | _ -> failwith "opp not on Z" in
        get reify na

    let rec hash_hatom ra_quant {index = _; hval = a} =
      match a with
      | Acop cop -> get ra_quant a
      | Auop (uop, ha) -> get ra_quant (Auop (uop, hash_hatom ra_quant ha))
      | Abop (bop, ha1, ha2) ->
         let new_ha1 = hash_hatom ra_quant ha1 in
         let new_ha2 = hash_hatom ra_quant ha2 in
         begin match bop with
         | BO_eq ty -> mk_eq_sym ra_quant ty new_ha1 new_ha2
         | _ -> get ra_quant (Abop (bop, new_ha1, new_ha2)) end
      | Atop (top, ha1, ha2, ha3) ->
         let new_ha1 = hash_hatom ra_quant ha1 in
         let new_ha2 = hash_hatom ra_quant ha2 in
         let new_ha3 = hash_hatom ra_quant ha3 in
         get ra_quant (Atop (top, new_ha1, new_ha2, new_ha3))
      | Anop _ -> assert false
      | Aapp (op, arr) -> get ra_quant (Aapp (op, Array.map (hash_hatom ra_quant) arr))

    let copy {count=c; tbl=t} = {count = c; tbl = HashAtom.copy t}

    let print_atoms reify where =
      let oc = open_out where in
      let fmt = Format.formatter_of_out_channel oc in
      let accumulate _ ha acc = ha :: acc in
      let list = HashAtom.fold accumulate reify.tbl [] in
      let compare ha1 ha2 = compare ha1.index ha2.index in
      let slist = List.sort compare list in
      let print ha = Format.fprintf fmt "%i: " ha.index;
                     to_smt fmt ha; Format.fprintf fmt "\n" in
      List.iter print slist;
      Format.fprintf fmt "@.";
      close_out oc


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
      | CCBVshl
      | CCBVshr
      | CCeqb                   (* Equality on bool *)
      | CCeqbP                  (* Equality on positive *)
      | CCeqbZ                  (* Equality on Z *)
      | CCeqbBV                 (* Equality on bit vectors *)
      | CCeqbA                  (* Equality on arrays *)
      | CCeqbU                  (* Equality on uninterpreted types *)
      | CCselect
      | CCdiff
      | CCstore
      | CCunknown
      | CCunknown_deps of int


    let logic_coq_cst = function
      | CCxH
      | CCZ0
      | CCxO
      | CCxI
      | CCZpos
      | CCZneg
      | CCZopp
      | CCZplus
      | CCZminus
      | CCZmult
      | CCZlt
      | CCZle
      | CCZge
      | CCZgt -> SL.singleton LLia

      | CCBV
      | CCBVbitOf
      | CCBVnot
      | CCBVneg
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
      | CCBVshl
      | CCBVshr -> SL.singleton LBitvectors

      | CCselect | CCdiff | CCstore -> SL.singleton LArrays

      | CCeqb -> SL.empty

      (* | CCeqbP | CCeqbZ -> SL.singleton LLia *)
      (* | CCeqbBV -> SL.singleton LBitvectors *)
      (* | CCeqbA -> SL.singleton LArrays *)

      | CCeqbP | CCeqbZ | CCeqbBV | CCeqbA | CCeqbU
      | CCunknown | CCunknown_deps _  -> SL.singleton LUF


    let gobble_of_coq_cst = function
      | CCBV
      | CCBVbitOf
      | CCBVnot
      | CCBVneg
      | CCBVand
      | CCBVor
      | CCBVxor
      | CCBVadd
      | CCBVmult
      | CCBVult
      | CCBVslt
      | CCBVsextn
      | CCBVzextn
      | CCBVshl
      | CCBVshr -> 1

      | CCBVconcat -> 2
      | CCBVextr -> 3

      | CCselect -> 5
      | CCdiff -> 10
      | CCstore -> 8

      | _ -> 0


    let op_tbl () =
      let tbl = Hashtbl.create 40 in
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
          cbv_shl, CCBVshl; cbv_shr, CCBVshr;
          ceqb,CCeqb; ceqbP,CCeqbP; ceqbZ, CCeqbZ; cbv_eq, CCeqbBV; ceqb_of_compdec, CCeqbU;
          cselect, CCselect; cdiff, CCdiff;
          cstore, CCstore;
          cequalarray, CCeqbA;
        ];
      tbl

    let op_tbl = lazy (op_tbl ())


    let split_list_at n l =
      let rec aux acc n l = match n, l with
        | 0, _ -> List.rev acc, l
        | _, [] -> assert false
        | _, x :: l -> aux (x :: acc) (n-1) l
      in
      aux [] n l


    let get_coq_term_op =
      Hashtbl.find op_coq_terms


    exception UnknownUnderForall

    let of_coq ?eqsym:(eqsym=false) rt ro reify known_logic env sigma c =
      let op_tbl = Lazy.force op_tbl in
      let get_cst c =
	try
          let cc = Hashtbl.find op_tbl c in
          if SL.subset (logic_coq_cst cc) known_logic then cc
          else CCunknown_deps (gobble_of_coq_cst cc)
        with Not_found -> CCunknown
      in
      let rec mk_hatom (h : Structures.constr) =
        let c, args = Structures.decompose_app h in
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
        | CCBVshl -> mk_bop_bvshl args
        | CCBVshr -> mk_bop_bvshr args
        | CCeqb -> mk_teq SmtBtype.Tbool args
        | CCeqbP -> mk_teq SmtBtype.Tpositive args
        | CCeqbZ -> mk_teq SmtBtype.TZ args
        | CCeqbA -> mk_bop_farray_equal args
        | CCeqbBV -> mk_bop_bveq args
        | CCeqbU -> mk_bop_ueq args
        | CCselect -> mk_bop_select args
        | CCdiff -> mk_bop_diff args
        | CCstore -> mk_top_store args
	| CCunknown -> mk_unknown c args (Structures.retyping_get_type_of env sigma h)
        | CCunknown_deps gobble ->
          mk_unknown_deps c args (Structures.retyping_get_type_of env sigma h) gobble


      and mk_cop op args = match op, args with
        | CCxH, [] -> get reify (Acop CO_xH)
        | CCZ0, [] -> get reify (Acop CO_Z0)
        | CCBV, [bs] -> get reify (Acop (CO_BV (mk_bool_list bs)))
        | _ -> assert false


      and mk_uop op = function
        | [a] -> let h = mk_hatom a in
          get reify (Auop (op,h))
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

      and mk_teq ty args =
        if eqsym then match args with
                  | [a1; a2] -> let h1 = mk_hatom a1 in
                                let h2 = mk_hatom a2 in
                                mk_eq_sym reify ty h1 h2
                  | _ -> failwith "unexpected number of arguments for mk_teq"
        else mk_bop (BO_eq ty) args

      and mk_bop_ueq args =
        match args with
          | t::compdec::args ->
             let ty = SmtBtype.of_coq_compdec rt t compdec in
             mk_teq ty args
          | _ -> failwith "unexpected number of arguments for mk_bop_ueq"

      and mk_bop op = function
        | [a1;a2] ->
           let h1 = mk_hatom a1 in
           let h2 = mk_hatom a2 in
           get reify (Abop (op,h1,h2))
        | _ -> failwith "unexpected number of arguments for mk_bop"

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

      and mk_bop_bvshl = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVshl s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvshr = function
        | [s;a1;a2] ->
           let s' = mk_bvsize s in
           mk_bop (BO_BVshr s') [a1;a2]
        | _ -> assert false

      and mk_bop_bvconcat = function
        | [s1;s2;a1;a2] ->
           mk_bop (BO_BVconcat (mk_bvsize s1, mk_bvsize s2)) [a1;a2]
        | _ -> assert false

      and mk_bop_bveq = function
        | [s;a1;a2] when SL.mem LBitvectors known_logic ->
          let s' = mk_bvsize s in
          mk_teq (SmtBtype.TBV s') [a1;a2]
        (* We still want to interpret bv equality as uninterpreted
           smtlib2 equality if the solver doesn't support bitvectors *)
        | [s;a1;a2] ->
          let ty = SmtBtype.of_coq rt known_logic (mklApp cbitvector [|s|]) in
          mk_teq ty [a1;a2]
        | _ -> assert false

      and mk_bop_select = function
        | [ti;te;_;_;_;a;i] ->
          let ti' = SmtBtype.of_coq rt known_logic ti in
          let te' = SmtBtype.of_coq rt known_logic te in
          mk_bop (BO_select (ti', te')) [a; i]
        | _ -> assert false

      and mk_bop_diff = function
        | [ti;te;_;_;_;_;_;_;_;_;a;b] ->
          let ti' = SmtBtype.of_coq rt known_logic ti in
          let te' = SmtBtype.of_coq rt known_logic te in
          mk_bop (BO_diffarray (ti', te')) [a; b]
        | _ -> assert false

      and mk_top_store = function
        | [ti;te;_;_;_;_;_;_;a;i;e] ->
          let ti' = SmtBtype.of_coq rt known_logic ti in
          let te' = SmtBtype.of_coq rt known_logic te in
          mk_top (TO_store (ti', te')) [a; i; e]
        | _ -> assert false

      and mk_bop_farray_equal = function
        | [ti;te;_;_;_;_;_;a;b] when SL.mem LArrays known_logic ->
          let ti' = SmtBtype.of_coq rt known_logic ti in
          let te' = SmtBtype.of_coq rt known_logic te in
          mk_teq (SmtBtype.TFArray (ti', te')) [a; b]
        (* We still want to interpret array equality as uninterpreted
           smtlib2 equality if the solver doesn't support arrays *)
        | [ti;te;ord_ti;_;_;_;inh_te;a;b] ->
          let ty = SmtBtype.of_coq rt known_logic
              (mklApp cfarray [|ti; te; ord_ti; inh_te|]) in
          mk_teq ty [a;b]
        | _ -> assert false

      and mk_unknown c args ty =
        let rec collect_types = function
          | [] -> ([],[])
          | x::xs as l ->
             if Constr.iskind (Structures.retyping_get_type_of env sigma x) then
               let (l1, l2) = collect_types xs in
               (x::l1, l2)
             else
               ([], l)
        in
        let (args1, args2) = collect_types args in
        let c, args =
          match args1 with
            | [] -> c, args
            | _ -> Constr.mkApp (c, Array.of_list args1), args2
        in
        let hargs = Array.of_list (List.map mk_hatom args) in
        let op =
          try Op.of_coq ro c
          with | Not_found ->
            let targs = Array.map type_of hargs in
            let tres = SmtBtype.of_coq rt known_logic ty in
            let os = if Structures.isRel c then
                       let i = Structures.destRel c in
                       let n, _ = Structures.destruct_rel_decl (Environ.lookup_rel i env) in
                       Some (Structures.string_of_name n)
                     else if Vars.closed0 c then
                       None
                     else
                       (* Uninterpreted expression depending on a quantified variable.
                          We do not handle it for the moment.
                          We leave for future work to have "dependent" constants.
                        *)
                       raise UnknownUnderForall
            in
            Op.declare ro c targs tres os
        in
        (try
           let (i, _) = destruct "" op in
           Hashtbl.add op_coq_terms i c (* Chantal: I think we should move it to "Not_found" (otherwise it is already in the table) *)
         with | Failure _ -> ());
        get reify (Aapp (op,hargs))

      (* create an uninterpreted symbol for an unsupported symbol but fisrt do
         partial application to its dependent arguments whose number is given by
         [gobble] *)
      and mk_unknown_deps c args ty gobble =
        let deps, args = split_list_at gobble args in
        let c = Structures.mkApp (c, Array.of_list deps) in
        mk_unknown c args ty

      in

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
              | Auop (op,h) -> Structures.mkApp (Op.interp_uop op, [|interp_atom h|])
              | Abop (op,h1,h2) ->
                Structures.mkApp (Op.interp_bop t_i op,
                            [|interp_atom h1; interp_atom h2|])
              | Atop (op,h1,h2,h3) ->
                Structures.mkApp (Op.interp_top t_i op,
                            [|interp_atom h1; interp_atom h2; interp_atom h3|])
              | Anop (NO_distinct ty as op,ha) ->
                let cop = Op.interp_nop t_i op in
                let typ = SmtBtype.interp t_i ty in
                let cargs = Array.fold_right (fun h l ->
                    mklApp ccons [|typ; interp_atom h; l|])
                    ha (mklApp cnil [|typ|]) in
                Structures.mkApp (cop,[|cargs|])
              | Aapp (op,t) ->
                Structures.mkApp ((snd op).op_val, Array.map interp_atom t) in
	  Hashtbl.add atom_tbl l pc;
	  pc in
      interp_atom a


    (* Generation of atoms *)

    let mk_nop ?declare:(decl=true) op reify a = get ~declare:decl reify (Anop (op,a))

    let mk_binop ?declare:(decl=true) op reify h1 h2 = get ~declare:decl reify (Abop (op, h1, h2))

    let mk_terop ?declare:(decl=true) op reify h1 h2 h3 = get ~declare:decl reify (Atop (op, h1, h2, h3))

    let mk_unop ?declare:(decl=true) op reify h = get ~declare:decl reify (Auop (op, h))

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

    let mk_unop ?declare:(decl=true) op reify h = get ~declare:decl reify (Auop (op, h))

    let mk_lt ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zlt ra
    let mk_le ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zle ra
    let mk_gt ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zgt ra
    let mk_ge ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zge ra
    let mk_plus ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zplus ra
    let mk_minus ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zminus ra
    let mk_mult ra ?declare:(decl=true) = mk_binop ~declare:decl BO_Zmult ra
    let mk_bvand reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVand s) reify
    let mk_bvor reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVor s) reify
    let mk_bvxor reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVxor s) reify
    let mk_bvadd reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVadd s) reify
    let mk_bvmult reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVmult s) reify
    let mk_bvult reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVult s) reify
    let mk_bvslt reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVslt s) reify
    let mk_bvconcat reify ?declare:(decl=true) s1 s2 = mk_binop ~declare:decl (BO_BVconcat (s1, s2)) reify
    let mk_opp ra ?declare:(decl=true) = mk_unop ~declare:decl UO_Zopp ra
    let mk_distinct reify ?declare:(decl=true) ty = mk_nop ~declare:decl (NO_distinct ty) reify
    let mk_bitof reify ?declare:(decl=true) s i = mk_unop ~declare:decl (UO_BVbitOf (s, i)) reify
    let mk_bvnot reify ?declare:(decl=true) s = mk_unop ~declare:decl (UO_BVnot s) reify
    let mk_bvneg reify ?declare:(decl=true) s = mk_unop ~declare:decl (UO_BVneg s) reify
    let mk_bvconst reify bool_list = get reify (Acop (CO_BV bool_list))
    let mk_select reify ?declare:(decl=true) ti te = mk_binop ~declare:decl (BO_select (ti, te)) reify
    let mk_diffarray reify ?declare:(decl=true) ti te = mk_binop ~declare:decl (BO_diffarray (ti, te)) reify
    let mk_store reify ?declare:(decl=true) ti te = mk_terop ~declare:decl (TO_store (ti, te)) reify
    let mk_bvextr reify ?declare:(decl=true) ~i ~n ~s = mk_unop ~declare:decl (UO_BVextr (i, n, s)) reify
    let mk_bvzextn reify ?declare:(decl=true) ~s ~n = mk_unop ~declare:decl (UO_BVzextn (s, n)) reify
    let mk_bvsextn reify ?declare:(decl=true) ~s ~n = mk_unop ~declare:decl (UO_BVsextn (s, n)) reify
    let mk_bvshl reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVshl s) reify
    let mk_bvshr reify ?declare:(decl=true) s = mk_binop ~declare:decl (BO_BVshr s) reify


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
      (fun bt acc -> mklApp ccons [|typeb; SmtBtype.to_coq bt; acc|])
      cod (mklApp cnil [|typeb|]) in
  let b = SmtBtype.to_coq dom in
  mklApp cpair [|typea;typeb;a;b|]

let make_t_i = SmtBtype.make_t_i
let make_t_func ro t_i =
  Op.interp_tbl (mklApp ctval [|t_i|])
    (fun cod dom value -> mklApp cTval [|t_i; mk_ftype cod dom; value|]) ro

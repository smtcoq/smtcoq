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

    let equal t1 t2 =
      match t1,t2 with
        | Tindex i, Tindex j -> i.index == j.index
        | _ -> t1 == t2

    let to_coq = function 
      | TZ -> Lazy.force cTZ
      | Tbool -> Lazy.force cTbool
      | Tpositive -> Lazy.force cTpositive
      | TBV _ -> Lazy.force cTBV
      | Tindex i -> index_to_coq i

    let to_smt fmt = function
      | TZ -> Format.fprintf fmt "Int"
      | Tbool -> Format.fprintf fmt "Bool"
      | Tpositive -> Format.fprintf fmt "Int"
      | TBV i -> Format.fprintf fmt "(_ BitVec %i)" i
      | Tindex i -> Format.fprintf fmt "Tindex_%i" i.index

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

    let of_coq reify t =
      try
        Hashtbl.find reify.tbl t
      with | Not_found ->
        let n = string_of_int (List.length reify.cuts) in
        let eq_name = Names.id_of_string ("eq"^n) in
        let eq_var = Term.mkVar eq_name in

        let eq_ty = Term.mkArrow t (Term.mkArrow t (Lazy.force cbool)) in

        let eq = mkName "eq" in
        let x = mkName "x" in
        let y = mkName "y" in
        let req = Term.mkRel 3 in
        let rx = Term.mkRel 2 in
        let ry = Term.mkRel 1 in
        let refl_ty = Term.mkLambda (eq, eq_ty, Term.mkProd (x,t,Term.mkProd (y,t,mklApp creflect [|mklApp ceq [|t;rx;ry|]; Term.mkApp (req, [|rx;ry|])|]))) in

        let pair_ty = mklApp csigT [|eq_ty; refl_ty|] in

        reify.cuts <- (eq_name, pair_ty)::reify.cuts;
        let ce = mklApp ctyp_eqb_of_typ_eqb_param [|t; eq_var|] in
        declare reify t ce

    let interp_tbl reify =
      let t = Array.make (reify.count + 1) (Lazy.force cunit_typ_eqb) in
      let set _ = function 
	| Tindex it -> t.(it.index) <- it.hval
	| _ -> () in
      Hashtbl.iter set reify.tbl;
      Structures.mkArray (Lazy.force ctyp_eqb, t)

    let to_list reify =
      let set _ t acc = match t with
	| Tindex it -> (it.index,it)::acc
	| _ -> acc in
      Hashtbl.fold set reify.tbl []

    let interp_to_coq reify = function
      | TZ -> Lazy.force cZ
      | Tbool -> Lazy.force cbool
      | Tpositive -> Lazy.force cpositive
      | TBV _ -> Lazy.force cbitvector
      | Tindex c -> mklApp cte_carrier [|c.hval|]

  end

(** Operators *)

type cop = 
   | CO_xH
   | CO_Z0

type uop =
   | UO_xO
   | UO_xI
   | UO_Zpos 
   | UO_Zneg
   | UO_Zopp
   | UO_BVbitOf of int

type bop = 
   | BO_Zplus
   | BO_Zminus
   | BO_Zmult
   | BO_Zlt
   | BO_Zle
   | BO_Zge
   | BO_Zgt
   | BO_eq of btype
   | BO_BVand
   | BO_BVor

type nop =
  | NO_distinct of btype

type op_def = { 
    tparams : btype array; 
    tres : btype; 
    op_val : Term.constr }

type indexed_op = op_def gen_hashed 

let dummy_indexed_op i dom codom = {index = i; hval = {tparams = dom; tres = codom; op_val = Term.mkProp}}
let indexed_op_index op = op.index

type op = 
  | Cop of cop
  | Uop of uop
  | Bop of bop
  | Nop of nop
  | Iop of indexed_op

module Op =
  struct 
    let c_to_coq = function
      | CO_xH -> Lazy.force cCO_xH
      | CO_Z0 -> Lazy.force cCO_Z0

    let c_type_of = function
      | CO_xH -> Tpositive
      | CO_Z0 -> TZ

    let interp_cop = function
      | CO_xH -> Lazy.force cxH
      | CO_Z0 -> Lazy.force cZ0

    let u_to_coq = function 
      | UO_xO -> Lazy.force cUO_xO
      | UO_xI -> Lazy.force cUO_xI
      | UO_Zpos -> Lazy.force cUO_Zpos 
      | UO_Zneg -> Lazy.force cUO_Zneg
      | UO_Zopp -> Lazy.force cUO_Zopp
      | UO_BVbitOf i -> mklApp cUO_BVbitOf [|mkNat i|]

    let u_type_of = function 
      | UO_xO | UO_xI -> Tpositive
      | UO_Zpos | UO_Zneg | UO_Zopp -> TZ
      | UO_BVbitOf _ -> Tbool

    let u_type_arg = function 
      | UO_xO | UO_xI | UO_Zpos | UO_Zneg -> Tpositive
      | UO_Zopp -> TZ
      | UO_BVbitOf _ -> TBV (-1)

    let interp_uop = function
      | UO_xO -> Lazy.force cxO
      | UO_xI -> Lazy.force cxI
      | UO_Zpos -> Lazy.force cZpos
      | UO_Zneg -> Lazy.force cZneg
      | UO_Zopp -> Lazy.force copp
      | UO_BVbitOf i -> mklApp cbv_nth [|mkNat i|]

    let eq_tbl = Hashtbl.create 17 

    let eq_to_coq t =
      try Hashtbl.find eq_tbl t 
      with Not_found ->
	let op = mklApp cBO_eq [|Btype.to_coq t|] in
	Hashtbl.add eq_tbl t op;
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
      | BO_BVand -> Lazy.force cBO_BVand
      | BO_BVor -> Lazy.force cBO_BVor

    let b_type_of = function
      | BO_Zplus | BO_Zminus | BO_Zmult -> TZ
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt | BO_eq _ -> Tbool
      | BO_BVand | BO_BVor -> TBV (-1)

    let b_type_args = function
      | BO_Zplus | BO_Zminus | BO_Zmult 
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt -> (TZ,TZ)
      | BO_eq t -> (t,t)
      | BO_BVand | BO_BVor -> (TBV (-1),TBV (-1))

    let interp_eq = function
      | TZ -> Lazy.force ceqbZ
      | Tbool -> Lazy.force ceqb
      | Tpositive -> Lazy.force ceqbP
      | TBV _ -> Lazy.force cbv_eq
      | Tindex i -> mklApp cte_eqb [|i.hval|]

    let interp_bop = function
      | BO_Zplus -> Lazy.force cadd
      | BO_Zminus -> Lazy.force csub
      | BO_Zmult -> Lazy.force cmul
      | BO_Zlt -> Lazy.force cltb
      | BO_Zle -> Lazy.force cleb
      | BO_Zge -> Lazy.force cgeb
      | BO_Zgt -> Lazy.force cgtb
      | BO_eq t -> interp_eq t
      | BO_BVand -> Lazy.force cbv_and
      | BO_BVor -> Lazy.force cbv_or

    let n_to_coq = function
      | NO_distinct t -> mklApp cNO_distinct [|Btype.to_coq t|]

    let n_type_of = function
      | NO_distinct _ -> Tbool

    let n_type_args = function
      | NO_distinct ty -> ty

    let interp_distinct = function
      | TZ -> Lazy.force cZ
      | Tbool -> Lazy.force cbool
      | Tpositive -> Lazy.force cpositive
      | TBV _ -> Lazy.force cbitvector
      | Tindex i -> mklApp cte_carrier [|i.hval|]

    let interp_nop = function
      | NO_distinct ty -> mklApp cdistinct [|interp_distinct ty;interp_eq ty|]

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

    let c_equal op1 op2 = op1 == op2

    let u_equal op1 op2 = op1 == op2

    let b_equal op1 op2 =
      match op1,op2 with
        | BO_eq t1, BO_eq t2 -> Btype.equal t1 t2
        | _ -> op1 == op2

    let n_equal op1 op2 =
      match op1,op2 with
        | NO_distinct t1, NO_distinct t2 -> Btype.equal t1 t2

    let i_equal op1 op2 = op1.index == op2.index

  end


(** Definition of atoms *)

type atom = 
  | Acop of cop
  | Auop of uop * hatom 
  | Abop of bop * hatom * hatom 
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
      | Anop (opa,ha), Anop (opb,hb) ->
        let na = Array.length ha in
        let nb = Array.length hb in
        let i = ref (-1) in
        Op.n_equal opa opb && na == nb && Array.fold_left (fun b h -> incr i; b && h.index == hb.(!i).index) true ha
      | Aapp (va,ha), Aapp (vb,hb) ->
        let na = Array.length ha in
        let nb = Array.length hb in
        let i = ref (-1) in
        Op.i_equal va vb && na == nb && Array.fold_left (fun b h -> incr i; b && h.index == hb.(!i).index) true ha
      | _, _ -> false

    let hash = function
      |	Acop op -> ((Hashtbl.hash op) lsl 3) lxor 1
      | Auop (op,h) ->
          (( (h.index lsl 3) + (Hashtbl.hash op)) lsl 3) lxor 2
      | Abop (op,h1,h2) ->
          (((( (h1.index lsl 2) + h2.index) lsl 3) + Hashtbl.hash op) lsl 3) lxor 3
      | Anop (op, args) ->
          let hash_args =
            match Array.length args with
            | 0 -> 0
            | 1 -> args.(0).index
            | 2 -> args.(1).index lsl 2 + args.(0).index
            | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index in
          (hash_args lsl 5 + (Hashtbl.hash op) lsl 3) lxor 4
      | Aapp (op, args) ->
          let hash_args =
            match Array.length args with
            | 0 -> 0
            | 1 -> args.(0).index
            | 2 -> args.(1).index lsl 2 + args.(0).index
            | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index in
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
      | Anop (op,_) -> Op.n_type_of op
      | Aapp (op,_) -> Op.i_type_of op

    let is_bool_type h = Btype.equal (type_of h) Tbool
    let is_bv_type h = Btype.equal (type_of h) (TBV (-1))


    let rec compute_int = function
      | Acop c ->
        (match c with
          | CO_xH -> 1
          | CO_Z0 -> 0)
      | Auop (op,h) ->
        (match op with
          | UO_xO -> 2*(compute_hint h)
          | UO_xI -> 2*(compute_hint h) + 1
          | UO_Zpos -> compute_hint h
          | UO_Zneg -> - (compute_hint h)
          | UO_Zopp | UO_BVbitOf _ -> assert false)
      | _ -> assert false

    and compute_hint h = compute_int (atom h)

    let to_smt_int fmt i =
      let s1 = if i < 0 then "(- " else "" in
      let s2 = if i < 0 then ")" else "" in
      let j = if i < 0 then -i else i in
      Format.fprintf fmt "%s%i%s" s1 j s2

    let rec to_smt fmt h = to_smt_atom fmt (atom h)

    and to_smt_atom fmt = function
      | Acop _ as a -> to_smt_int fmt (compute_int a)
      | Auop (UO_Zopp,h) ->
        Format.fprintf fmt "(- ";
        to_smt fmt h;
        Format.fprintf fmt ")"
      | Auop _ as a -> to_smt_int fmt (compute_int a)
      | Abop (op,h1,h2) -> to_smt_bop fmt op h1 h2
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
        | BO_BVand -> "bvand"
        | BO_BVor -> "bvor" in
      Format.fprintf fmt "(%s " s;
      to_smt fmt h1;
      Format.fprintf fmt " ";
      to_smt fmt h2;
      Format.fprintf fmt ")"

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
      | Anop(op,ha) ->
        let ty = Op.n_type_args op in
        Array.iter (fun h -> if not (Btype.equal ty (type_of h)) then raise (NotWellTyped a)) ha
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

    let clear reify =
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
      | CCxO
      | CCxI
      | CCZpos
      | CCZneg
      | CCZopp
      | CCBVbitOf
      | CCZplus
      | CCZminus
      | CCZmult
      | CCZlt
      | CCZle
      | CCZge
      | CCZgt
      | CCBVand
      | CCBVor
      | CCeqb
      | CCeqbP
      | CCeqbZ
      | CCeqbBV
      | CCunknown

    let op_tbl () =
      let tbl = Hashtbl.create 29 in
      let add (c1,c2) = Hashtbl.add tbl (Lazy.force c1) c2 in
      List.iter add
	[ cxH,CCxH; cZ0,CCZ0;
          cxO,CCxO; cxI,CCxI; cZpos,CCZpos; cZneg,CCZneg; copp,CCZopp;
          cbv_nth, CCBVbitOf;
          cadd,CCZplus; csub,CCZminus; cmul,CCZmult; cltb,CCZlt;
          cleb,CCZle; cgeb,CCZge; cgtb,CCZgt;
          cbv_and, CCBVand; cbv_or, CCBVor;
          ceqb,CCeqb; ceqbP,CCeqbP; ceqbZ, CCeqbZ; cbv_eq, CCeqbBV
        ];
      tbl

    let op_tbl = lazy (op_tbl ())

    let rec mk_nat n =
      let c, args = Term.decompose_app n in
      if Term.eq_constr c (Lazy.force cO) then
        0
      else if Term.eq_constr c (Lazy.force cS) then
        match args with
          | [n] -> (mk_nat n) + 1
          | _ -> assert false
      else assert false

    let of_coq rt ro reify env sigma c =
      let op_tbl = Lazy.force op_tbl in
      let get_cst c =
	try Hashtbl.find op_tbl c with Not_found -> CCunknown in
      let mk_cop op = get reify (Acop op) in
      let rec mk_hatom h =
	let c, args = Term.decompose_app h in
	match get_cst c with
          | CCxH -> mk_cop CO_xH
          | CCZ0 -> mk_cop CO_Z0
          | CCxO -> mk_uop UO_xO args
          | CCxI -> mk_uop UO_xI args
          | CCZpos -> mk_uop UO_Zpos args
          | CCZneg -> mk_uop UO_Zneg args
          | CCZopp -> mk_uop UO_Zopp args
          | CCBVbitOf -> mk_bvbitof args
          | CCZplus -> mk_bop BO_Zplus args
          | CCZminus -> mk_bop BO_Zminus args
          | CCZmult -> mk_bop BO_Zmult args
          | CCZlt -> mk_bop BO_Zlt args
          | CCZle -> mk_bop BO_Zle args
          | CCZge -> mk_bop BO_Zge args
          | CCZgt -> mk_bop BO_Zgt args
          | CCBVand -> mk_bop BO_BVand args
          | CCBVor -> mk_bop BO_BVor args
          | CCeqb -> mk_bop (BO_eq Tbool) args
          | CCeqbP -> mk_bop (BO_eq Tpositive) args
          | CCeqbZ -> mk_bop (BO_eq TZ) args
          | CCeqbBV -> mk_bop (BO_eq (TBV (-1))) args
	  | CCunknown -> mk_unknown c args (Retyping.get_type_of env sigma h)

      and mk_uop op = function
        | [a] -> let h = mk_hatom a in get reify (Auop (op,h))
        | _ -> assert false

      and mk_bvbitof = function
        | [n;a] -> let h = mk_hatom a in get reify (Auop (UO_BVbitOf (mk_nat n),h))
        | _ -> assert false

      and mk_bop op = function
        | [a1;a2] ->
          let h1 = mk_hatom a1 in
          let h2 = mk_hatom a2 in
          get reify (Abop (op,h1,h2))
        | _ -> assert false

      and mk_unknown c args ty =
        let hargs = Array.of_list (List.map mk_hatom args) in
        let op =
          try Op.of_coq ro c
          with | Not_found ->
            let targs = Array.map type_of hargs in
            let tres = Btype.of_coq rt ty in
            Op.declare ro c targs tres in
        get reify (Aapp (op,hargs)) in

       mk_hatom c


    let to_coq h = mkInt h.index

    let a_to_coq a =
      match a with
      | Acop op -> mklApp cAcop [|Op.c_to_coq op|]
      | Auop (op,h) -> mklApp cAuop [|Op.u_to_coq op; to_coq h|]
      | Abop (op,h1,h2) -> 
	  mklApp cAbop [|Op.b_to_coq op;to_coq h1; to_coq h2|]
      | Anop (op,ha) ->
        let cop = Op.n_to_coq op in
        let cargs = Array.fold_right (fun h l -> mklApp ccons [|Lazy.force cint; to_coq h; l|]) ha (mklApp cnil [|Lazy.force cint|]) in
        mklApp cAnop [|cop; cargs|]
      | Aapp (op,args) ->
        let cop = Op.i_to_coq op in
        let cargs = Array.fold_right (fun h l -> mklApp ccons [|Lazy.force cint; to_coq h; l|]) args (mklApp cnil [|Lazy.force cint|]) in
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
    let interp_to_coq atom_tbl a =
      let rec interp_atom a =
	let l = index a in
	try Hashtbl.find atom_tbl l
	with Not_found ->
	  let pc =
	    match atom a with
              | Acop c -> Op.interp_cop c
              | Auop (op,h) -> Term.mkApp (Op.interp_uop op, [|interp_atom h|])
              | Abop (op,h1,h2) -> Term.mkApp (Op.interp_bop op, [|interp_atom h1; interp_atom h2|])
              | Anop (NO_distinct ty as op,ha) ->
                let cop = Op.interp_nop op in
                let typ = Op.interp_distinct ty in
                let cargs = Array.fold_right (fun h l -> mklApp ccons [|typ; interp_atom h; l|]) ha (mklApp cnil [|typ|]) in
                Term.mkApp (cop,[|cargs|])
              | Aapp (op,t) -> Term.mkApp (op.hval.op_val, Array.map interp_atom t) in
	  Hashtbl.add atom_tbl l pc;
	  pc in
      interp_atom a


    (* Generation of atoms *)

    let mk_nop op reify a = get reify (Anop (op,a))

    let mk_binop op reify h1 h2 = get reify (Abop (op, h1, h2))

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
          mk_unop UO_Zneg reify (hatom_pos_of_bigint reify (Big_int.minus_big_int i))

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
    let mk_opp = mk_unop UO_Zopp
    let mk_distinct reify ty = mk_nop (NO_distinct ty) reify

  end


module Form = SmtForm.Make(Atom)
module Trace = SmtTrace.MakeOpt(Form)


(* Interpretation tables *)

let mk_ftype cod dom =
  let typeb = Lazy.force ctype in
  let typea = mklApp clist [|typeb|] in
  let a = Array.fold_right (fun bt acc -> mklApp ccons [|typeb; Btype.to_coq bt; acc|]) cod (mklApp cnil [|typeb|]) in
  let b = Btype.to_coq dom in
  mklApp cpair [|typea;typeb;a;b|]

let make_t_i rt = Btype.interp_tbl rt
let make_t_func ro t_i = Op.interp_tbl (mklApp ctval [|t_i|]) (fun cod dom value -> mklApp cTval [|t_i; mk_ftype cod dom; value|]) ro

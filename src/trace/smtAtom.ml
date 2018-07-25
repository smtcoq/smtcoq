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
open SmtBtype

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

type bop =
  | BO_Zplus
  | BO_Zminus
  | BO_Zmult
  | BO_Zlt
  | BO_Zle
  | BO_Zge
  | BO_Zgt
  | BO_eq of btype

type nop =
  | NO_distinct of btype

type op_def = {
    tparams : btype array;
    tres : btype;
    op_val : Term.constr
  }

type index = Index of int
           | Rel_name of string

type indexed_op = index * op_def

let destruct s (i, hval) = match i with
  | Index index -> index, hval
  | Rel_name _ -> failwith s

let dummy_indexed_op i dom codom = i, {tparams = dom; tres = codom; op_val = Term.mkProp}
let indexed_op_index i = let index, _ = destruct "destruct on a Rel: called by indexed_op_index" i in
                         index

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

    let u_type_of = function
      | UO_xO | UO_xI -> Tpositive
      | UO_Zpos | UO_Zneg | UO_Zopp -> TZ

    let u_type_arg = function
      | UO_xO | UO_xI | UO_Zpos | UO_Zneg -> Tpositive
      | UO_Zopp -> TZ

    let interp_uop = function
      | UO_xO -> Lazy.force cxO
      | UO_xI -> Lazy.force cxI
      | UO_Zpos -> Lazy.force cZpos
      | UO_Zneg -> Lazy.force cZneg
      | UO_Zopp -> Lazy.force copp

    let eq_tbl = Hashtbl.create 17

    let eq_to_coq t =
      try Hashtbl.find eq_tbl t
      with Not_found ->
	let op = mklApp cBO_eq [|SmtBtype.to_coq t|] in
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

    let b_type_of = function
      | BO_Zplus | BO_Zminus | BO_Zmult -> TZ
      | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt | BO_eq _ -> Tbool

    let b_type_args = function
      | BO_Zplus | BO_Zminus | BO_Zmult
        | BO_Zlt | BO_Zle | BO_Zge | BO_Zgt -> (TZ,TZ)
      | BO_eq t -> (t,t)

    let interp_eq = function
      | TZ -> Lazy.force ceqbZ
      | Tbool -> Lazy.force ceqb
      | Tpositive -> Lazy.force ceqbP
      | Tindex i -> mklApp cte_eqb [|indexed_type_hval i|]

    let interp_bop = function
      | BO_Zplus -> Lazy.force cadd
      | BO_Zminus -> Lazy.force csub
      | BO_Zmult -> Lazy.force cmul
      | BO_Zlt -> Lazy.force cltb
      | BO_Zle -> Lazy.force cleb
      | BO_Zge -> Lazy.force cgeb
      | BO_Zgt -> Lazy.force cgtb
      | BO_eq t -> interp_eq t

    let n_to_coq = function
      | NO_distinct t -> mklApp cNO_distinct [|SmtBtype.to_coq t|]

    let n_type_of = function
      | NO_distinct _ -> Tbool

    let n_type_args = function
      | NO_distinct ty -> ty

    let interp_distinct = function
      | TZ -> Lazy.force cZ
      | Tbool -> Lazy.force cbool
      | Tpositive -> Lazy.force cpositive
      | Tindex i -> mklApp cte_carrier [|indexed_type_hval i|]

    let interp_nop = function
      | NO_distinct ty -> mklApp cdistinct [|interp_distinct ty;interp_eq ty|]

    let i_to_coq i = let index, _ = destruct "destruct on a Rel: called by i_to_coq" i in
                     mkInt index

    let i_type_of (_, hval) = hval.tres

    let i_type_args (_, hval) = hval.tparams

    (* reify table *)
    type reify_tbl =
      { mutable count : int;
	tbl : (Term.constr, indexed_op) Hashtbl.t
      }

    let create () =
      { count = 0;
	tbl =  Hashtbl.create 17 }

    let declare reify op tparams tres os =
      assert (not (Hashtbl.mem reify.tbl op));
      let opa = { tparams = tparams; tres = tres; op_val = op} in
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
	        (mk_Tval [||] Tbool (Lazy.force ctrue)) in
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

    let c_equal op1 op2 = op1 == op2

    let u_equal op1 op2 = op1 == op2

    let b_equal op1 op2 =
      match op1,op2 with
      | BO_eq t1, BO_eq t2 -> SmtBtype.equal t1 t2
      | _ -> op1 == op2

    let n_equal op1 op2 =
      match op1,op2 with
      | NO_distinct t1, NO_distinct t2 -> SmtBtype.equal t1 t2

    let i_equal (i1, _) (i2, _) = i1 = i2

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
         let op_index = try fst (destruct "destruct on a Rel: called by hash" op) with _ -> 0 in
         let hash_args =
           match Array.length args with
           | 0 -> 0
           | 1 -> args.(0).index
           | 2 -> args.(1).index lsl 2 + args.(0).index
           | _ -> args.(2).index lsl 4 + args.(1).index lsl 2 + args.(0).index in
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
      | Anop (op,_) -> Op.n_type_of op
      | Aapp (op,_) -> Op.i_type_of op

    let is_bool_type h = SmtBtype.equal (type_of h) Tbool


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
          | UO_Zopp -> assert false)
      | _ -> assert false

    and compute_hint h = compute_int (atom h)

    let to_string_int i =
      let s1 = if i < 0 then "(- " else "" in
      let s2 = if i < 0 then ")" else "" in
      let j = if i < 0 then -i else i in
      s1 ^ string_of_int j ^ s2

    let to_string ?pi:(pi=false) h =
      let rec to_string h = 
        (if pi then string_of_int (index h) ^":" else "")
        ^ to_string_atom (atom h)

      and to_string_atom = function
        | Acop _ as a -> to_string_int (compute_int a)
        | Auop (UO_Zopp,h) -> 
           "(- " ^
             to_string h ^
               ")"
        | Auop _ as a -> to_string_int (compute_int a)
        | Abop (op,h1,h2) -> to_string_bop op h1 h2
        | Anop (op,a) -> to_string_nop op a
        | Aapp ((i, op), a) ->
           let op_string = begin match i with
                           | Index index -> "op_" ^ string_of_int index
                           | Rel_name name -> name end
                           ^ if pi then to_string_op op else "" in
           if Array.length a = 0 then (
             op_string
           ) else (
             "(" ^ op_string ^
               Array.fold_left (fun acc h -> acc ^ " " ^ to_string h) "" a ^
                 ")"
           )
      and to_string_op {tparams=bta; tres=bt; op_val=t} =
        "[(" ^ Array.fold_left (fun acc bt -> acc ^ SmtBtype.to_string bt ^ " ")
                 " " bta ^ ") ( " ^ SmtBtype.to_string bt ^ " ) ( " ^
          Pp.string_of_ppcmds (Printer.pr_constr t) ^ " )]"

      and to_string_bop op h1 h2 =
        let s = match op with
          | BO_Zplus -> "+"
          | BO_Zminus -> "-"
          | BO_Zmult -> "*"
          | BO_Zlt -> "<"
          | BO_Zle -> "<="
          | BO_Zge -> ">="
          | BO_Zgt -> ">"
          | BO_eq _ -> "=" in
        "(" ^ s ^ " " ^
          to_string h1 ^
            " " ^
              to_string h2 ^
                ")"

      and to_string_nop op a =
        let s = match op with
          | NO_distinct _ -> "distinct" in
        "(" ^ s ^
          Array.fold_left (fun acc h -> acc ^ " " ^ to_string h) "" a ^
            ")" in
      to_string h

    let to_smt fmt t = Format.fprintf fmt "%s@." (to_string t)


    exception NotWellTyped of atom

    let check a =
      match a with
      | Acop _ -> ()
      | Auop(op,h) ->
	 if not (SmtBtype.equal (Op.u_type_arg op) (type_of h))
         then raise (NotWellTyped a)
      | Abop(op,h1,h2) ->
	 let (t1,t2) = Op.b_type_args op in
	 if not (SmtBtype.equal t1 (type_of h1) &&
                   SmtBtype.equal t2 (type_of h2))
	 then raise (NotWellTyped a)
      | Anop(op,ha) ->
         let ty = Op.n_type_args op in
         Array.iter (fun h -> if not (SmtBtype.equal ty (type_of h)) then raise (NotWellTyped a)) ha
      | Aapp(op,args) ->
	 let tparams = Op.i_type_args op in
	 Array.iteri (fun i t ->
	     if not (SmtBtype.equal t (type_of args.(i))) then
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

    let get ?declare:(decl=true) reify a =
      if decl
      then try HashAtom.find reify.tbl a
           with Not_found -> declare reify a
      else {index = -1; hval = a}

    let mk_eq reify decl ty h1 h2 =
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

    let rec hash_hatom ra' {index = _; hval = a} =
      match a with 
      | Acop cop -> get ra' a
      | Auop (uop, ha) -> get ra' (Auop (uop, hash_hatom ra' ha))
      | Abop (bop, ha1, ha2) ->
         let new_ha1 = hash_hatom ra' ha1 in
         let new_ha2 = hash_hatom ra' ha2 in
         begin match bop with
         | BO_eq ty -> mk_eq ra' true ty new_ha1 new_ha2
         | _ -> get ra' (Abop (bop, new_ha1, new_ha2)) end
      | Anop _ -> assert false
      | Aapp (op, arr) -> get ra' (Aapp (op, Array.map (hash_hatom ra') arr))
              
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
      | CCZgt
      | CCeqb
      | CCeqbP
      | CCeqbZ
      | CCunknown

    let op_tbl () =
      let tbl = Hashtbl.create 29 in
      let add (c1,c2) = Hashtbl.add tbl (Lazy.force c1) c2 in
      List.iter add
	[ cxH,CCxH; cZ0,CCZ0;
          cxO,CCxO; cxI,CCxI; cZpos,CCZpos; cZneg,CCZneg; copp,CCZopp;
          cadd,CCZplus; csub,CCZminus; cmul,CCZmult; cltb,CCZlt;
          cleb,CCZle; cgeb,CCZge; cgtb,CCZgt; ceqb,CCeqb; ceqbP,CCeqbP;
          ceqbZ, CCeqbZ
        ];
      tbl

    let op_tbl = lazy (op_tbl ())

    let of_coq ?hash:(h=false) rt ro reify env sigma c =
      let op_tbl = Lazy.force op_tbl in
      let get_cst c =
	try Hashtbl.find op_tbl c with Not_found -> CCunknown in
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
        | CCZplus -> mk_bop BO_Zplus args
        | CCZminus -> mk_bop BO_Zminus args
        | CCZmult -> mk_bop BO_Zmult args
        | CCZlt -> mk_bop BO_Zlt args
        | CCZle -> mk_bop BO_Zle args
        | CCZge -> mk_bop BO_Zge args
        | CCZgt -> mk_bop BO_Zgt args
        | CCeqb -> mk_teq Tbool args
        | CCeqbP -> mk_teq Tpositive args
        | CCeqbZ -> mk_teq TZ args
	| CCunknown -> let ty = Retyping.get_type_of env sigma h in
                       mk_unknown c args ty

      and mk_cop op = get reify (Acop op)

      and mk_uop op = function
        | [a] -> let h = mk_hatom a in get reify (Auop (op,h))
        | _ -> failwith "unexpected number of arguments for mk_uop"

      and mk_teq ty args = 
        if h then match args with    
        | [a1; a2] -> let h1 = mk_hatom a1 in
                      let h2 = mk_hatom a2 in
                      mk_eq reify true ty h1 h2
        | _ -> failwith "unexpected number of arguments for mk_teq"
        else mk_bop (BO_eq ty) args

      and mk_bop op = function
        | [a1;a2] ->
           let h1 = mk_hatom a1 in
           let h2 = mk_hatom a2 in
           get reify (Abop (op,h1,h2))
        | _ -> failwith "unexpected number of arguments for mk_bop"

      and mk_unknown c args ty =
        let hargs = Array.of_list (List.map mk_hatom args) in
        let op = try Op.of_coq ro c
                 with Not_found ->
                   let targs = Array.map type_of hargs in
                   let tres = SmtBtype.of_coq rt ty in
                   let os = if Term.isRel c
                            then let i = Term.destRel c in
                                 let n, _ = Structures.destruct_rel_decl (Environ.lookup_rel i env) in
                                 Some (string_of_name n)
                            else None in
                   Op.declare ro c targs tres os in
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
            | Aapp ((_, hval),t) -> Term.mkApp (hval.op_val, Array.map interp_atom t) in
	  Hashtbl.add atom_tbl l pc;
	  pc in
      interp_atom a


    (* Generation of atoms *)

    let mk_nop op reify ?declare:(decl=true) a = get ~declare:decl reify (Anop (op,a))

    let mk_binop op reify decl h1 h2 = get ~declare:decl reify (Abop (op, h1, h2))

    let mk_unop op reify ?declare:(decl=true) h = get ~declare:decl reify (Auop (op, h))

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

    let mk_unop op reify ?declare:(decl=true) h = get ~declare:decl reify (Auop (op, h))

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
  let a = Array.fold_right (fun bt acc -> mklApp ccons [|typeb; SmtBtype.to_coq bt; acc|]) cod (mklApp cnil [|typeb|]) in
  let b = SmtBtype.to_coq dom in
  mklApp cpair [|typea;typeb;a;b|]

let make_t_i rt = SmtBtype.interp_tbl rt
let make_t_func ro t_i = Op.interp_tbl (mklApp ctval [|t_i|]) (fun cod dom value -> mklApp cTval [|t_i; mk_ftype cod dom; value|]) ro

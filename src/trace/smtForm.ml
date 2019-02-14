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


open Util
open SmtMisc
open CoqTerms
open SmtBtype

module type ATOM =
  sig

    type t
    val index : t -> int

    val equal : t -> t -> bool

    val is_bool_type : t -> bool
    val is_bv_type : t -> bool
    val to_smt : Format.formatter -> t -> unit
    val logic : t -> logic

  end


type fop =
  | Ftrue
  | Ffalse
  | Fand
  | For
  | Fxor
  | Fimp
  | Fiff
  | Fite
  | Fnot2 of int
  | Fforall of (string * btype) list

type ('a,'f) gen_pform =
  | Fatom of 'a
  | Fapp of fop * 'f array
  | FbbT of 'a * 'f list


module type FORM =
  sig
    type hatom
    type t
    type pform = (hatom, t) gen_pform

    val pform_true : pform
    val pform_false : pform

    val equal : t -> t -> bool

    val to_lit : t -> int
    val index : t -> int
    val pform : t -> pform

    val neg : t -> t
    val is_pos : t -> bool
    val is_neg : t -> bool

    val to_smt : ?pi:bool ->
                 (Format.formatter -> hatom -> unit) ->
                 Format.formatter -> t -> unit

    val logic : t -> logic

    (* Building formula from positive formula *)
    exception NotWellTyped of pform
    type reify
    val create : unit -> reify
    val clear : reify -> unit
    val get : ?declare:bool -> reify -> pform -> t

    (** Give a coq term, build the corresponding formula *)
    val of_coq : (Term.constr -> hatom) -> reify -> Term.constr -> t

    val hash_hform : (hatom -> hatom) -> reify -> t -> t
    (** Flattening of [Fand] and [For], removing of [Fnot2]  *)
    val flatten : reify -> t -> t

    (** Turn n-ary [Fand] and [For] into their right-associative
        counter-parts *)
    val right_assoc : reify -> t -> t

    (** Producing Coq terms *)

    val to_coq : t -> Term.constr

    val pform_tbl : reify -> pform array

    val to_array : reify -> 'a -> (pform -> 'a) -> int * 'a array
    val interp_tbl : reify -> Term.constr * Term.constr
    val nvars : reify -> int
    (** Producing a Coq term corresponding to the interpretation
          of a formula *)
    (** [interp_atom] map [hatom] to coq term, it is better if it produce
          shared terms. *)
    val interp_to_coq :
      (hatom -> Term.constr) -> (int, Term.constr) Hashtbl.t ->
      t -> Term.constr
  end

module Make (Atom:ATOM) =
  struct

    type hatom = Atom.t

    type pform = (Atom.t, t) gen_pform

    and hpform = pform gen_hashed

    and t =
      | Pos of hpform
      | Neg of hpform

    let pform_true = Fapp (Ftrue,[||])
    let pform_false = Fapp (Ffalse,[||])

    let equal h1 h2 =
      match h1, h2 with
      | Pos hp1, Pos hp2 -> hp1.index == hp2.index
      | Neg hp1, Neg hp2 -> hp1.index == hp2.index
      | _, _ -> false

    let index = function
      | Pos hp -> hp.index
      | Neg hp -> hp.index

    let to_lit = function
      | Pos hp -> hp.index * 2
      | Neg hp -> hp.index * 2 + 1

    let neg = function
      | Pos hp -> Neg hp
      | Neg hp -> Pos hp

    let is_pos = function
      | Pos _ -> true
      | _ -> false

    let is_neg = function
      | Neg _ -> true
      | _ -> false

    let pform = function
      | Pos hp -> hp.hval
      | Neg hp -> hp.hval


    let rec to_smt ?pi:(pi=false) atom_to_smt fmt = function
      | Pos hp ->
         if pi then Format.fprintf fmt "%s" (string_of_int hp.index ^ ":");
         to_smt_pform atom_to_smt fmt hp.hval
      | Neg hp ->
         if pi then Format.fprintf fmt "%s" (string_of_int hp.index ^ ":");
         Format.fprintf fmt "(not ";
         to_smt_pform atom_to_smt fmt hp.hval;
         Format.fprintf fmt ")"

    and to_smt_pform atom_to_smt fmt = function
      | Fatom a -> atom_to_smt fmt a
      | Fapp (op,args) -> to_smt_op atom_to_smt fmt op args
      (* This is an intermediate object of proofs, it correspond to nothing in SMT *)
      | FbbT (a, l) ->
        Format.fprintf fmt "(bbT %a [" atom_to_smt a;
        let fi = ref true in
        List.iter (fun f -> Format.fprintf fmt "%s%a"
                      (if !fi then "" else "; ")
                      (to_smt atom_to_smt) f; fi := false) l;
        Format.fprintf fmt "])"

    and to_smt_op atom_to_smt fmt op args =
      let (s1,s2) = if ((Array.length args = 0) || (match op with Fnot2 _ -> true | _ -> false)) then ("","") else ("(",")") in
      Format.fprintf fmt "%s" s1;
      (match op with
         | Ftrue -> Format.fprintf fmt "true"
         | Ffalse -> Format.fprintf fmt "false"
         | Fand -> Format.fprintf fmt "and"
         | For -> Format.fprintf fmt "or"
         | Fxor -> Format.fprintf fmt "xor"
         | Fimp -> Format.fprintf fmt "=>"
         | Fiff -> Format.fprintf fmt "="
         | Fite -> Format.fprintf fmt "ite"
         | Fnot2 _ -> ()
         | Fforall l ->
            (Format.fprintf fmt "forall (";
             to_smt_args fmt l;
             Format.fprintf fmt  ")")
      );

      Array.iter (fun h -> Format.fprintf fmt " "; to_smt atom_to_smt fmt h) args;
      Format.fprintf fmt "%s" s2

    and to_smt_args fmt = function
      | [] -> Format.fprintf fmt " "
      | (s, t)::rem ->
         (Format.fprintf fmt " (%s " s;
          SmtBtype.to_smt fmt t;
          Format.fprintf fmt ")";
          to_smt_args fmt rem)

    let rec logic_pform = function
      | Fatom a -> Atom.logic a
      | Fapp (_, args) ->
        Array.fold_left (fun l f ->
            SL.union (logic f) l
          ) SL.empty args
      | FbbT _ -> SL.singleton LBitvectors

    and logic = function
      | Pos hp | Neg hp -> logic_pform hp.hval

    let dumbed_down op =
      let dumbed_down_bt = function
        | Tindex it -> Tindex (dummy_indexed_type (indexed_type_index it))
        | x -> x in
      match op with
      | Fforall l -> Fforall (List.map (fun (x, bt) -> x, dumbed_down_bt bt) l)
      | x -> x


    module HashedForm =
      struct

	type t = pform

	let equal pf1 pf2 =
	  match pf1, pf2 with
	  | Fatom ha1, Fatom ha2 -> Atom.equal ha1 ha2
	  | Fapp(op1,args1), Fapp(op2,args2) ->
	     dumbed_down op1 = dumbed_down op2 &&
	      Array.length args1 == Array.length args2 &&
	      (try
		for i = 0 to Array.length args1 - 1 do
		  if not (equal args1.(i) args2.(i)) then raise Not_found
		done;
		true
	      with Not_found -> false)
          | FbbT(ha1, l1), FbbT(ha2, l2) ->
             (try
                Atom.equal ha1 ha2 &&
                  List.for_all2 (fun i j -> equal i j) l1 l2
              with | Invalid_argument _ -> false)
	  | _, _ -> false

	let hash pf =
	  match pf with
	  | Fatom ha1 -> Atom.index ha1 * 2
	  | Fapp(op, args) ->
	      let hash_args =
		match Array.length args with
		| 0 -> 0
		| 1 -> to_lit args.(0)
		| 2 -> (to_lit args.(1)) lsl 2 + to_lit args.(0)
		| _ ->
		    (to_lit args.(2)) lsl 4 + (to_lit args.(1)) lsl 2 +
		      to_lit args.(0) in
	      (hash_args * 10 + Hashtbl.hash (dumbed_down op)) * 2 + 1
	  | FbbT(ha, l) ->
	      let hash_args =
		match l with
		| [] -> 0
		| [a0] -> to_lit a0
		| [a0;a1] -> (to_lit a1) lsl 2 + to_lit a0
		| a0::a1::a2::_ ->
                   (to_lit a2) lsl 4 + (to_lit a1) lsl 2 + to_lit a0 in
              (hash_args * 10 + Atom.index ha) * 2 + 1
      end

    module HashForm = Hashtbl.Make (HashedForm)

    type reify = {
	mutable count : int;
                tbl : t HashForm.t
      }

    exception NotWellTyped of pform

    let check pf =
      match pf with
      | Fatom ha ->  if not (Atom.is_bool_type ha) then
          raise (Format.eprintf "nwt: %a" (to_smt_pform Atom.to_smt) pf;
                 NotWellTyped pf)
      | Fapp (op, args) ->
	(match op with
	 | Ftrue | Ffalse ->
           if Array.length args <> 0 then
             raise (Format.eprintf "nwt: %a" (to_smt_pform Atom.to_smt) pf;
                    NotWellTyped pf)
	 | Fnot2 _ ->
           if Array.length args <> 1 then
             raise (Format.eprintf "nwt: %a" (to_smt_pform Atom.to_smt) pf;
                    NotWellTyped pf)
	 | Fand | For -> ()
	 | Fxor | Fimp | Fiff ->
           if Array.length args <> 2 then
             raise (Format.eprintf "nwt: %a" (to_smt_pform Atom.to_smt) pf;
                    NotWellTyped pf)

          | Fite ->
            if Array.length args <> 3 then
              raise (Format.eprintf "nwt: %a" (to_smt_pform Atom.to_smt) pf;
                     NotWellTyped pf)

         | Fforall l -> ()
       )

      | FbbT (ha, l) -> if not (Atom.is_bv_type ha) then
          raise (Format.eprintf "nwt: %a" (to_smt_pform Atom.to_smt) pf;
                 NotWellTyped pf)

    let declare reify pf =
      check pf;
      let res = Pos {index = reify.count; hval = pf} in
      HashForm.add reify.tbl pf res;
      reify.count <- reify.count + 1;
      res

    let create () =
      let reify =
	{ count = 0;
	  tbl =  HashForm.create 17 } in
      let _ = declare reify pform_true in
      let _ = declare reify pform_false in
      reify

    let clear r =
      r.count <- 0;
      HashForm.clear r.tbl;
      let _ = declare r pform_true in
      let _ = declare r pform_false in
      ()

    let get ?declare:(decl=true) reify pf =
      if decl then
        try HashForm.find reify.tbl pf
        with Not_found -> declare reify pf
      else Pos {index = -1; hval = pf}

    (** Given a coq term, build the corresponding formula *)
    type coq_cst =
      | CCtrue
      | CCfalse
      | CCnot
      | CCand
      | CCor
      | CCxor
      | CCimp
      | CCiff
      | CCifb
      | CCunknown

    module ConstrHash = struct
      type t = Term.constr
      let equal = Term.eq_constr
      let hash = Term.hash_constr
    end
    module ConstrHashtbl = Hashtbl.Make(ConstrHash)

    let op_tbl () =
      let tbl = ConstrHashtbl.create 29 in
      let add (c1,c2) = ConstrHashtbl.add tbl (Lazy.force c1) c2 in
      List.iter add
	[
	  ctrue,CCtrue; cfalse,CCfalse;
	  candb,CCand; corb,CCor; cxorb,CCxor; cimplb,CCimp; cnegb,CCnot;
          ceqb,CCiff; cifb,CCifb ];
      tbl

    let op_tbl = lazy (op_tbl ())

    let empty_args = [||]

    let of_coq atom_of_coq reify c =
      let op_tbl = Lazy.force op_tbl in
      let get_cst c =
        try ConstrHashtbl.find op_tbl c with Not_found -> CCunknown in
      let rec mk_hform h =
        let c, args = Term.decompose_app h in
        match get_cst c with
          | CCtrue  -> get reify (Fapp(Ftrue,empty_args))
          | CCfalse -> get reify (Fapp(Ffalse,empty_args))
          | CCnot -> mk_fnot 1 args
          | CCand -> mk_fand [] args
          | CCor  -> mk_for [] args
          | CCxor -> op2 (fun l -> Fapp(Fxor,l)) args
          | CCiff -> op2 (fun l -> Fapp(Fiff,l)) args
          | CCimp ->
             (match args with
                | [b1;b2] ->
                   let l1 = mk_hform b1 in
                   let l2 = mk_hform b2 in
                   get reify (Fapp (Fimp, [|l1;l2|]))
                | _ -> Structures.error "SmtForm.Form.of_coq: wrong number of arguments for implb")
          | CCifb ->
             (* We should also be able to reify if then else *)
             begin match args with
               | [b1;b2;b3] ->
                  let l1 = mk_hform b1 in
                  let l2 = mk_hform b2 in
                  let l3 = mk_hform b3 in
                  get reify (Fapp (Fite, [|l1;l2;l3|]))
               | _ -> Structures.error "SmtForm.Form.of_coq: wrong number of arguments for ifb"
             end
          | _ ->
             let a = atom_of_coq h in
             get reify (Fatom a)

      and op2 f args =
        match args with
          | [b1;b2] ->
             let l1 = mk_hform b1 in
             let l2 = mk_hform b2 in
             get reify (f [|l1; l2|])
          | _ ->  Structures.error "SmtForm.Form.of_coq: wrong number of arguments"

      and mk_fnot i args =
        match args with
          | [t] ->
             let c,args = Term.decompose_app t in
             if Term.eq_constr c (Lazy.force cnegb) then
               mk_fnot (i+1) args
             else
               let q,r = i lsr 1 , i land 1 in
               let l = mk_hform t in
               let l = if r = 0 then l else neg l in
               if q = 0 then l
               else get reify (Fapp(Fnot2 q, [|l|]))
          | _ -> Structures.error "SmtForm.Form.mk_hform: wrong number of arguments for negb"

      and mk_fand acc args =
        match args with
          | [t1;t2] ->
             let l2 = mk_hform t2 in
             let c, args = Term.decompose_app t1 in
             if Term.eq_constr c (Lazy.force candb) then
               mk_fand (l2::acc) args
             else
               let l1 = mk_hform t1 in
               get reify (Fapp(Fand, Array.of_list (l1::l2::acc)))
          | _ -> Structures.error "SmtForm.Form.mk_hform: wrong number of arguments for andb"

      and mk_for acc args =
        match args with
          | [t1;t2] ->
             let l2 = mk_hform t2 in
             let c, args = Term.decompose_app t1 in
             if Term.eq_constr c (Lazy.force corb) then
               mk_for (l2::acc) args
             else
               let l1 = mk_hform t1 in
               get reify (Fapp(For, Array.of_list (l1::l2::acc)))
          | _ -> Structures.error "SmtForm.Form.mk_hform: wrong number of arguments for orb" in

      mk_hform c


    let hash_hform hash_hatom rf' hf =
      let rec mk_hform = function
        | Pos hp -> Pos (mk_hpform hp)
        | Neg hp -> Neg (mk_hpform hp)
      and mk_hpform {index = _; hval = hv} =
        let new_hv = match hv with
            | Fatom a -> Fatom (hash_hatom a)
            | Fapp (fop, arr) -> Fapp (fop, Array.map mk_hform arr)
            | FbbT (a, l) -> FbbT (hash_hatom a, List.map mk_hform l)
        in
        match get rf' new_hv with Pos x | Neg x -> x in
      mk_hform hf


    (** Flattening of Fand and For, removing of Fnot2 *)
    let set_sign f f' =
      if is_pos f then f' else neg f'

    let rec flatten reify f =
      match pform f with
      | Fatom _ | FbbT _ -> f
      | Fapp(Fnot2 _,args) -> set_sign f (flatten reify args.(0))
      | Fapp(Fand, args) -> set_sign f (flatten_and reify [] (Array.to_list args))
      | Fapp(For,args) -> set_sign f (flatten_or reify [] (Array.to_list args))
      | Fapp(op,args) ->
         (* TODO change Fimp into For ? *)
	 set_sign f (get reify (Fapp(op, Array.map (flatten reify) args)))

    and flatten_and reify acc args =
      match args with
      | [] -> get reify (Fapp(Fand, Array.of_list (List.rev acc)))
      | a::args ->
	 (* TODO change (not For) and (not Fimp) into Fand *)
	 match pform a with
	 | Fapp(Fand, args') when is_pos a ->
	    let args = Array.fold_right (fun a args -> a::args) args' args in
	    flatten_and reify acc args
	 | _ -> flatten_and reify (flatten reify a :: acc) args

    and flatten_or reify acc args =
      (* TODO change Fimp and (not Fand) into For *)
      match args with
      | [] -> get reify (Fapp(For, Array.of_list (List.rev acc)))
      | a::args ->
	 match pform a with
	 | Fapp(For, args') when is_pos a ->
	    let args = Array.fold_right (fun a args -> a::args) args' args in
	    flatten_or reify acc args
	 | _ -> flatten_or reify (flatten reify a :: acc) args

    let rec right_assoc reify f =
      match pform f with
      | Fapp(Fand, args) when Array.length args > 2 ->
        let a = args.(0) in
        let rargs = Array.sub args 1 (Array.length args - 1) in
        let f' = right_assoc reify (get reify (Fapp (Fand, rargs))) in
        set_sign f (get reify (Fapp (Fand, [|a; f'|])))
      | Fapp(For, args) when Array.length args > 2 ->
        let a = args.(0) in
        let rargs = Array.sub args 1 (Array.length args - 1) in
        let f' = right_assoc reify (get reify (Fapp (For, rargs))) in
        set_sign f (get reify (Fapp (For, [|a; f'|])))
      | _ -> f


    (** Producing Coq terms *)

    let to_coq hf = let i = to_lit hf in
                    if i < 0 then failwith "This formula should'nt be in Coq"
                    else mkInt i

    let args_to_coq args =
      let cargs = Array.make (Array.length args + 1) (mkInt 0) in
      Array.iteri (fun i hf -> cargs.(i) <- to_coq hf) args;
      Structures.mkArray (Lazy.force cint, cargs)

    let pf_to_coq = function
      | Fatom a -> mklApp cFatom [|mkInt (Atom.index a)|]
      | Fapp(op,args) ->
         (match op with
	   | Ftrue -> Lazy.force cFtrue
	   | Ffalse -> Lazy.force cFfalse
	   | Fand -> mklApp cFand [| args_to_coq args|]
	   | For  -> mklApp cFor [| args_to_coq args|]
	   | Fimp -> mklApp cFimp [| args_to_coq args|]
	   | Fxor -> mklApp cFxor (Array.map to_coq args)
	   | Fiff -> mklApp cFiff (Array.map to_coq args)
	   | Fite -> mklApp cFite (Array.map to_coq args)
	   | Fnot2 i -> mklApp cFnot2 [|mkInt i; to_coq args.(0)|]
           | Fforall _ -> failwith "pf_to_coq on forall")
      | FbbT(a, l) -> mklApp cFbbT
         [|mkInt (Atom.index a);
           List.fold_right (fun f l -> mklApp ccons [|Lazy.force cint; to_coq f; l|]) l (mklApp cnil [|Lazy.force cint|])|]

    let pform_tbl reify =
      let t = Array.make reify.count pform_true in
      let set _ h =
	match h with
	| Pos hp -> t.(hp.index) <- hp.hval
	| _ -> assert false in
      HashForm.iter set reify.tbl;
      t

    let to_array reify dft f =
      let t = Array.make (reify.count + 1) dft in
      let set _ h =
	match h with
	| Pos hp -> t.(hp.index) <- f hp.hval
	| _ -> assert false in
      HashForm.iter set reify.tbl;
      (reify.count, t)

    let interp_tbl reify =
      let (i,t) = to_array reify (Lazy.force cFtrue) pf_to_coq in
      (mkInt i, Structures.mkArray (Lazy.force cform, t))

    let nvars reify = reify.count
    (** Producing a Coq term corresponding to the interpretation of a formula *)
    (** [interp_atom] map [Atom.t] to coq term, it is better if it produce
	shared terms. *)
    let interp_to_coq interp_atom form_tbl f =
      let rec interp_form f =
	let l = to_lit f in
	try Hashtbl.find form_tbl l
	with Not_found ->
	      if is_neg f then
	        let pc = interp_form (neg f) in
	        let nc = mklApp cnegb [|pc|] in
	        Hashtbl.add form_tbl l nc;
	        nc
	      else
	        let pc =
	          match pform f with
	            | Fatom a -> interp_atom a
	            | Fapp(op, args) ->
		       (match op with
		          | Ftrue -> Lazy.force ctrue
		          | Ffalse -> Lazy.force cfalse
		          | Fand -> interp_args candb args
		          | For -> interp_args corb args
		          | Fxor -> interp_args cxorb args
		          | Fimp ->
		             let r = ref (interp_form args.(Array.length args - 1)) in
		             for i = Array.length args - 2 downto 0 do
		               r := mklApp cimplb [|interp_form args.(i); !r|]
		             done;
		             !r
		          | Fiff -> interp_args ceqb args
		          | Fite ->
		             (* TODO with if here *)
		             mklApp cifb (Array.map interp_form args)
		          | Fnot2 n ->
		             (let r = ref (interp_form args.(0)) in
		              for _ = 1 to n do
                                r := mklApp cnegb [|!r|]
                              done;
                              !r)
                          | Fforall _ -> failwith "interp_to_coq on forall")
                    | FbbT(a, l) ->
                       mklApp cbv_eq
                         [|mkN (List.length l);
                           interp_atom a;
                           mklApp cof_bits [|List.fold_right (fun f l -> mklApp ccons [|Lazy.force cbool; interp_form f; l|]) l (mklApp cnil [|Lazy.force cbool|])|]|]
                in
	        Hashtbl.add form_tbl l pc;
                pc

      and interp_args op args =
	let r = ref (interp_form args.(0)) in
	  for i = 1 to Array.length args - 1 do
	    r := mklApp op [|!r;interp_form args.(i)|]
	  done;
	  !r in
        interp_form f
end

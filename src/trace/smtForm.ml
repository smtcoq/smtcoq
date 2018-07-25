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

    val to_string : ?pi:bool -> (hatom -> string) -> t -> string
    val to_smt : (hatom -> string) -> Format.formatter ->
                 t -> unit

    (* Building formula from positive formula *)
    exception NotWellTyped of pform
    type reify
    val create : unit -> reify
    val clear : reify -> unit
    val get : ?declare:bool -> reify -> pform -> t

    (** Give a coq term, build the corresponding formula *)
    val of_coq : (Term.constr -> hatom) ->
                 reify -> Term.constr -> t

    val hash_hform : (hatom -> hatom) -> reify -> t -> t
    (** Flattening of [Fand] and [For], removing of [Fnot2]  *)
    val flatten : reify -> t -> t

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

    let rec to_string ?pi:(pi=false) atom_to_string = function
      | Pos hp -> (if pi then string_of_int hp.index ^ ":" else "")
                  ^ to_string_pform atom_to_string hp.hval
      | Neg hp -> (if pi then string_of_int hp.index ^ ":" else "") ^ "(not "
                  ^ to_string_pform atom_to_string hp.hval ^ ")"

    and to_string_pform atom_to_string = function
      | Fatom a -> atom_to_string a
      | Fapp (op,args) -> to_string_op_args atom_to_string op args

    and to_string_op_args atom_to_string op args =
      let (s1,s2) = if Array.length args = 0 then ("","") else ("(",")") in
      s1 ^ to_string_op op ^
        Array.fold_left (fun acc h -> acc ^ " " ^ to_string atom_to_string h) "" args ^ s2

    and to_string_op = function
        | Ftrue -> "true"
        | Ffalse -> "false"
        | Fand -> "and"
        | For -> "or"
        | Fxor -> "xor"
        | Fimp -> "=>"
        | Fiff -> "="
        | Fite -> "ite"
        | Fnot2 _ -> ""
        | Fforall l -> "forall (" ^
                       to_string_args l ^
                       ")"
                                                                                
    and to_string_args = function
      | [] -> " "
      | (s, t)::rest -> " (" ^ s ^ " " ^ SmtBtype.to_string t ^ ")"
                        ^ to_string_args rest

    let dumbed_down op =
      let dumbed_down_bt = function
        | Tindex it -> Tindex (dummy_indexed_type (indexed_type_index it))
        | x -> x in
      match op with
      | Fforall l -> Fforall (List.map (fun (x, bt) -> x, dumbed_down_bt bt) l)
      | x -> x

    let to_smt atom_to_string fmt f =
      Format.fprintf fmt "%s" (to_string atom_to_string f)

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

      end

    module HashForm = Hashtbl.Make (HashedForm)

    type reify = {
	mutable count : int;
        tbl : t HashForm.t
      }

    exception NotWellTyped of pform

    let check pf =
      match pf with
      | Fatom ha ->  if not (Atom.is_bool_type ha) then raise (NotWellTyped pf)
      | Fapp (op, args) ->
	 match op with
	 | Ftrue | Ffalse ->
	    if Array.length args <> 0 then raise (NotWellTyped pf)
	 | Fnot2 _ ->
	    if Array.length args <> 1 then raise (NotWellTyped pf)
	 | Fand | For -> ()
	 | Fxor | Fimp | Fiff ->
	    if Array.length args <> 2 then raise (NotWellTyped pf)
	 | Fite ->
	    if Array.length args <> 3 then raise (NotWellTyped pf)
         | Fforall l -> ()

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
             get reify (Fapp(Fand, Array.of_list  (l1::l2::acc)))
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
          | Fapp (fop, arr) -> Fapp (fop, Array.map mk_hform arr) in
        match get rf' new_hv with Pos x | Neg x -> x in
      mk_hform hf


    (** Flattening of Fand and For, removing of Fnot2 *)
    let set_sign f f' =
      if is_pos f then f' else neg f'

    let rec flatten reify f =
      match pform f with
      | Fatom _ -> f
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

    (** Producing Coq terms *)

    let to_coq hf = mkInt (to_lit hf)

    let args_to_coq args =
      let cargs = Array.make (Array.length args + 1) (mkInt 0) in
      Array.iteri (fun i hf -> cargs.(i) <- to_coq hf) args;
      Structures.mkArray (Lazy.force cint, cargs)

    let pf_to_coq = function
      | Fatom a -> mklApp cFatom [|mkInt (Atom.index a)|]
      | Fapp(op,args) ->
         match op with
	 | Ftrue -> Lazy.force cFtrue
	 | Ffalse -> Lazy.force cFfalse
	 | Fand -> mklApp cFand [| args_to_coq args|]
	 | For  -> mklApp cFor [| args_to_coq args|]
	 | Fimp -> mklApp cFimp [| args_to_coq args|]
	 | Fxor -> mklApp cFxor (Array.map to_coq args)
	 | Fiff -> mklApp cFiff (Array.map to_coq args)
	 | Fite -> mklApp cFite (Array.map to_coq args)
	 | Fnot2 i -> mklApp cFnot2 [|mkInt i; to_coq args.(0)|]
         | Fforall _ -> failwith "pf_to_coq on forall"

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
		     match op with
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
		        let r = ref (interp_form args.(0)) in
		        for i = 1 to n do
                          r := mklApp cnegb [|!r|]
                        done;
                        !r
                     |Fforall _ -> failwith "interp_to_coq on forall" in
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

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
  | Fforall of (string * SmtBtype.btype) list 
 
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
      val to_smt : (hatom -> string) -> Format.formatter -> t -> unit

      (* Building formula from positive formula *)
      exception NotWellTyped of pform
      type reify 
      val create : unit -> reify
      val clear : reify -> unit
      val get : ?declare:bool -> reify -> pform -> t
      
      (** Given a coq term, build the corresponding formula *)  
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

module Make (Atom:ATOM) : FORM with type hatom = Atom.t

	

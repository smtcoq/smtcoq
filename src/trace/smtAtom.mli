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


type indexed_type

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int

type btype =
  | TZ
  | Tbool
  | Tpositive
  | TBV of int
  | Tindex of indexed_type
  | TFArray of btype * btype

module Btype : 
    sig
      
      val equal : btype -> btype -> bool
	  
      val to_coq : btype -> Term.constr

      val to_smt : Format.formatter -> btype -> unit

      type reify_tbl
	  
      val create : unit -> reify_tbl

      val declare : reify_tbl -> Term.constr -> Term.constr -> btype

      val of_coq : reify_tbl -> Term.constr -> btype

      val interp_tbl : reify_tbl -> Term.constr

      val to_list : reify_tbl -> (int * indexed_type) list

      val interp_to_coq : reify_tbl -> btype -> Term.constr

      val get_cuts : reify_tbl -> (Structures.names_id_t * Term.types) list

      val logic : btype -> logic

      val logic_of_coq : reify_tbl -> Term.constr -> logic

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
   | BO_BVshl of int
   | BO_BVshr of int
   | BO_select of btype * btype
   | BO_diffarray of btype * btype

type top =
   | TO_store of btype * btype

type nop =
  | NO_distinct of btype

type indexed_op

val dummy_indexed_op: int -> btype array -> btype -> indexed_op
val indexed_op_index : indexed_op -> int
val debruijn_indexed_op : int -> btype -> indexed_op
  
module Op :
  sig
	  
    type reify_tbl

    val create : unit -> reify_tbl

    val declare : reify_tbl -> Term.constr -> btype array -> btype -> indexed_op

    val of_coq : reify_tbl -> Term.constr -> indexed_op

    val interp_tbl : Term.constr -> 
      (btype array -> btype -> Term.constr -> Term.constr) -> 
      reify_tbl -> Term.constr 

    val to_list : reify_tbl -> (int * (btype array) * btype * indexed_op) list

    val logic_ro : reify_tbl -> logic
    
  end


(** Definition of atoms *)

type hatom 

type atom = 
  | Acop of cop
  | Auop of uop * hatom
  | Abop of bop * hatom * hatom
  | Atop of top * hatom * hatom * hatom
  | Anop of nop * hatom array
  | Aapp of indexed_op * hatom array



module Atom : 
    sig 

      type t = hatom

      val equal : hatom -> hatom -> bool

      val index : hatom -> int

      val atom : hatom -> atom
 
      val type_of : hatom -> btype

      val to_smt : Format.formatter -> t -> unit

      exception NotWellTyped of atom

      type reify_tbl 

      val create : unit -> reify_tbl

      val clear : reify_tbl -> unit

      val get : reify_tbl -> atom -> hatom

      (** Given a coq term, build the corresponding atom *)
      val of_coq : Btype.reify_tbl -> Op.reify_tbl -> reify_tbl ->
        Environ.env -> Evd.evar_map -> Term.constr -> t

      val get_coq_term_op : int -> Term.constr
      
      val to_coq : hatom -> Term.constr

      val to_array : reify_tbl -> 'a -> (atom -> 'a) -> 'a array

      val interp_tbl : reify_tbl -> Term.constr

      val interp_to_coq : Term.constr -> (int, Term.constr) Hashtbl.t ->
	t -> Term.constr

      val logic : t -> logic
      
      (* Generation of atoms *)
      val hatom_Z_of_int : reify_tbl -> int -> hatom
      val hatom_Z_of_bigint : reify_tbl -> Big_int.big_int -> hatom
      val mk_eq : reify_tbl -> btype -> hatom -> hatom -> hatom
      val mk_lt : reify_tbl -> hatom -> hatom -> hatom
      val mk_le : reify_tbl -> hatom -> hatom -> hatom
      val mk_gt : reify_tbl -> hatom -> hatom -> hatom
      val mk_ge : reify_tbl -> hatom -> hatom -> hatom
      val mk_plus : reify_tbl -> hatom -> hatom -> hatom
      val mk_minus : reify_tbl -> hatom -> hatom -> hatom
      val mk_mult : reify_tbl -> hatom -> hatom -> hatom
      val mk_bvand : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvor : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvxor : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvadd : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvmult : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvult : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvslt : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvconcat : reify_tbl -> int -> int -> hatom -> hatom -> hatom
      val mk_opp : reify_tbl -> hatom -> hatom
      val mk_distinct : reify_tbl -> btype -> hatom array -> hatom
      val mk_bitof : reify_tbl -> int -> int -> hatom -> hatom
      val mk_bvnot : reify_tbl -> int -> hatom -> hatom
      val mk_bvneg : reify_tbl -> int -> hatom -> hatom
      val mk_bitof : reify_tbl -> int -> int -> hatom -> hatom
      val mk_bvconst : reify_tbl -> bool list -> hatom
      val mk_bvextr : reify_tbl -> i:int -> n:int -> s:int -> hatom -> hatom
      val mk_bvzextn : reify_tbl -> s:int -> n:int -> hatom -> hatom
      val mk_bvsextn : reify_tbl -> s:int -> n:int -> hatom -> hatom
      val mk_bvshl : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_bvshr : reify_tbl -> int -> hatom -> hatom -> hatom
      val mk_select : reify_tbl -> btype -> btype -> hatom -> hatom -> hatom
      val mk_diffarray : reify_tbl -> btype -> btype -> hatom -> hatom -> hatom
      val mk_store :
        reify_tbl -> btype -> btype -> hatom -> hatom -> hatom -> hatom

    end


module Form : SmtForm.FORM with type hatom = hatom
module Trace : sig
  val share_prefix : Form.t SmtCertif.clause -> int -> unit
end


val make_t_i : Btype.reify_tbl -> Term.constr
val make_t_func : Op.reify_tbl -> Term.constr -> Term.constr

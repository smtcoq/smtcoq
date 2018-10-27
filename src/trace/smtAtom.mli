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

type indexed_op

val dummy_indexed_op: int -> btype array -> btype -> indexed_op
val indexed_op_index : indexed_op -> int

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

  end


(** Definition of atoms *)

type hatom 

type atom = 
  | Acop of cop
  | Auop of uop * hatom 
  | Abop of bop * hatom * hatom 
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
      val of_coq : SmtBtype.reify_tbl -> Op.reify_tbl ->
        reify_tbl -> Environ.env -> Evd.evar_map -> Term.constr -> t

      val to_coq : hatom -> Term.constr

      val to_array : reify_tbl -> 'a -> (atom -> 'a) -> 'a array

      val interp_tbl : reify_tbl -> Term.constr

      val interp_to_coq : (int, Term.constr) Hashtbl.t ->
	t -> Term.constr

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
      val mk_opp : reify_tbl -> hatom -> hatom
      val mk_distinct : reify_tbl -> btype -> hatom array -> hatom

    end


module Form : SmtForm.FORM with type hatom = hatom
module Trace : sig
  val share_prefix : Form.t SmtCertif.clause -> int -> unit
end


val make_t_i : SmtBtype.reify_tbl -> Term.constr
val make_t_func : Op.reify_tbl -> Term.constr -> Term.constr

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


open SmtBtype

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

type index = Index of int
           | Rel_name of string

type indexed_op

val dummy_indexed_op: index -> btype array -> btype -> indexed_op
val indexed_op_index : indexed_op -> int
val debruijn_indexed_op : int -> btype -> indexed_op

module Op :
  sig

    type reify_tbl

    val create : unit -> reify_tbl

    val declare : reify_tbl -> Structures.constr -> btype array ->
                  btype -> string option -> indexed_op

    val of_coq : reify_tbl -> Structures.constr -> indexed_op

    val interp_tbl : Structures.constr ->
      (btype array -> btype -> Structures.constr -> Structures.constr) ->
      reify_tbl -> Structures.constr

    val to_list : reify_tbl -> (int * (btype array) * btype * indexed_op) list

    val logic_ro : reify_tbl -> SmtMisc.logic

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

      val equal : t -> t -> bool

      val index : t -> int

      val atom : t -> atom

      val type_of : t -> btype

      val to_smt : Format.formatter -> t -> unit

      type reify_tbl

      val create : unit -> reify_tbl

      val clear : reify_tbl -> unit

      val get : ?declare:bool -> reify_tbl -> atom -> t

      val mk_neg : reify_tbl -> t -> t

      val hash_hatom : reify_tbl -> t -> t

      (** for debugging purposes **)

      val copy : reify_tbl -> reify_tbl

      val print_atoms : reify_tbl -> string -> unit

      (** Given a coq term, build the corresponding atom *)
      exception UnknownUnderForall
      val of_coq : ?eqsym:bool -> SmtBtype.reify_tbl -> Op.reify_tbl ->
        reify_tbl -> SmtMisc.logic -> Environ.env -> Evd.evar_map -> Structures.constr -> t

      val get_coq_term_op : int -> Structures.constr

      val to_coq : t -> Structures.constr

      val to_array : reify_tbl -> 'a -> (atom -> 'a) -> 'a array

      val interp_tbl : reify_tbl -> Structures.constr

      val interp_to_coq : Structures.constr -> (int, Structures.constr) Hashtbl.t ->
	t -> Structures.constr

      val logic : t -> SmtMisc.logic

      (* Generation of atoms *)
      val hatom_Z_of_int : reify_tbl -> int -> t
      val hatom_Z_of_bigint : reify_tbl -> Big_int.big_int -> t
      val mk_eq_sym : reify_tbl -> ?declare:bool -> btype -> t -> t -> t
      val mk_lt : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_le : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_gt : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_ge : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_plus : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_minus : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_mult : reify_tbl -> ?declare:bool -> t -> t -> t
      val mk_bvand : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvor : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvxor : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvadd : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvmult : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvult : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvslt : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvconcat : reify_tbl -> ?declare:bool -> int -> int -> t -> t -> t
      val mk_opp : reify_tbl -> ?declare:bool -> t -> t
      val mk_distinct : reify_tbl -> ?declare:bool -> btype -> t array -> t
      val mk_bitof : reify_tbl -> ?declare:bool -> int -> int -> t -> t
      val mk_bvnot : reify_tbl -> ?declare:bool -> int -> t -> t
      val mk_bvneg : reify_tbl -> ?declare:bool -> int -> t -> t
      val mk_bvconst : reify_tbl -> bool list -> t
      val mk_bvextr : reify_tbl -> ?declare:bool -> i:int -> n:int -> s:int -> t -> t
      val mk_bvzextn : reify_tbl -> ?declare:bool -> s:int -> n:int -> t -> t
      val mk_bvsextn : reify_tbl -> ?declare:bool -> s:int -> n:int -> t -> t
      val mk_bvshl : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_bvshr : reify_tbl -> ?declare:bool -> int -> t -> t -> t
      val mk_select : reify_tbl -> ?declare:bool -> btype -> btype -> t -> t -> t
      val mk_diffarray : reify_tbl -> ?declare:bool -> btype -> btype -> t -> t -> t
      val mk_store :
        reify_tbl -> ?declare:bool -> btype -> btype -> t -> t -> t -> t

    end


module Form : SmtForm.FORM with type hatom = hatom
module Trace : sig
  val share_prefix : Form.t SmtCertif.clause -> int -> unit
end


val make_t_i : SmtBtype.reify_tbl -> Structures.constr
val make_t_func : Op.reify_tbl -> Structures.constr -> Structures.constr

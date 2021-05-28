(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


val gen_constant : string list list -> string -> CoqInterface.constr lazy_t

(* Int63 *)
val cint : CoqInterface.constr lazy_t
val ceq63 : CoqInterface.constr lazy_t

(* PArray *)
val carray : CoqInterface.constr lazy_t

(* nat *)
val cnat : CoqInterface.constr lazy_t
val cO : CoqInterface.constr lazy_t
val cS : CoqInterface.constr lazy_t

(* Positive *)
val cpositive : CoqInterface.constr lazy_t
val cxI : CoqInterface.constr lazy_t
val cxO : CoqInterface.constr lazy_t
val cxH : CoqInterface.constr lazy_t
val ceqbP : CoqInterface.constr lazy_t

(* N *)
val cN : CoqInterface.constr lazy_t
val cN0 : CoqInterface.constr lazy_t
val cNpos : CoqInterface.constr lazy_t
val cof_nat : CoqInterface.constr lazy_t

(* Z *)
val cZ : CoqInterface.constr lazy_t
val cZ0 : CoqInterface.constr lazy_t
val cZpos : CoqInterface.constr lazy_t
val cZneg : CoqInterface.constr lazy_t
val copp : CoqInterface.constr lazy_t
val cadd : CoqInterface.constr lazy_t
val csub : CoqInterface.constr lazy_t
val cmul : CoqInterface.constr lazy_t
val cltb : CoqInterface.constr lazy_t
val cleb : CoqInterface.constr lazy_t
val cgeb : CoqInterface.constr lazy_t
val cgtb : CoqInterface.constr lazy_t
val ceqbZ : CoqInterface.constr lazy_t

(* Booleans *)
val cbool : CoqInterface.constr lazy_t
val ctrue : CoqInterface.constr lazy_t
val cfalse : CoqInterface.constr lazy_t
val candb : CoqInterface.constr lazy_t
val corb : CoqInterface.constr lazy_t
val cxorb : CoqInterface.constr lazy_t
val cnegb : CoqInterface.constr lazy_t
val cimplb : CoqInterface.constr lazy_t
val ceqb : CoqInterface.constr lazy_t
val cifb : CoqInterface.constr lazy_t
val ciff : CoqInterface.constr lazy_t
val creflect : CoqInterface.constr lazy_t

(* Lists *)
val clist : CoqInterface.constr lazy_t
val cnil : CoqInterface.constr lazy_t
val ccons : CoqInterface.constr lazy_t
val clength : CoqInterface.constr lazy_t

(* Option *)
val coption : CoqInterface.constr lazy_t
val cSome : CoqInterface.constr lazy_t
val cNone : CoqInterface.constr lazy_t

(* Pairs *)
val cpair : CoqInterface.constr lazy_t
val cprod : CoqInterface.constr lazy_t

(* Dependent pairs *)
val csigT : CoqInterface.constr lazy_t

(* Logical Operators *)
val cnot : CoqInterface.constr lazy_t
val ceq : CoqInterface.constr lazy_t
val crefl_equal : CoqInterface.constr lazy_t
val cconj : CoqInterface.constr lazy_t
val cand : CoqInterface.constr lazy_t

(* Bit vectors *)
val cbitvector : CoqInterface.constr lazy_t
val cof_bits : CoqInterface.constr lazy_t
val cbitOf : CoqInterface.constr lazy_t
val cbv_eq : CoqInterface.constr lazy_t
val cbv_not : CoqInterface.constr lazy_t
val cbv_neg : CoqInterface.constr lazy_t
val cbv_and : CoqInterface.constr lazy_t
val cbv_or : CoqInterface.constr lazy_t
val cbv_xor : CoqInterface.constr lazy_t
val cbv_add : CoqInterface.constr lazy_t
val cbv_mult : CoqInterface.constr lazy_t
val cbv_ult : CoqInterface.constr lazy_t
val cbv_slt : CoqInterface.constr lazy_t
val cbv_concat : CoqInterface.constr lazy_t
val cbv_extr : CoqInterface.constr lazy_t
val cbv_zextn : CoqInterface.constr lazy_t
val cbv_sextn : CoqInterface.constr lazy_t
val cbv_shl : CoqInterface.constr lazy_t
val cbv_shr : CoqInterface.constr lazy_t

(* Arrays *)
val cfarray : CoqInterface.constr lazy_t
val cselect : CoqInterface.constr lazy_t
val cstore : CoqInterface.constr lazy_t
val cdiff : CoqInterface.constr lazy_t
val cequalarray : CoqInterface.constr lazy_t

(* OrderedType *)

(* SMT_terms *)
val cState_C_t : CoqInterface.constr lazy_t
val cState_S_t : CoqInterface.constr lazy_t

val cdistinct : CoqInterface.constr lazy_t

val ctype : CoqInterface.constr lazy_t
val cTZ : CoqInterface.constr lazy_t
val cTbool : CoqInterface.constr lazy_t
val cTpositive : CoqInterface.constr lazy_t
val cTBV : CoqInterface.constr lazy_t
val cTFArray : CoqInterface.constr lazy_t
val cTindex : CoqInterface.constr lazy_t

val cinterp_t : CoqInterface.constr lazy_t
val cdec_interp : CoqInterface.constr lazy_t
val cord_interp : CoqInterface.constr lazy_t
val ccomp_interp : CoqInterface.constr lazy_t
val cinh_interp : CoqInterface.constr lazy_t

val cinterp_eqb : CoqInterface.constr lazy_t

val ctyp_compdec : CoqInterface.constr lazy_t
val cTyp_compdec : CoqInterface.constr lazy_t
val cunit_typ_compdec : CoqInterface.constr lazy_t
val cte_carrier : CoqInterface.constr lazy_t
val cte_compdec : CoqInterface.constr lazy_t
val ceqb_of_compdec : CoqInterface.constr lazy_t
val cCompDec : CoqInterface.constr lazy_t

val cbool_compdec : CoqInterface.constr lazy_t
val cZ_compdec : CoqInterface.constr lazy_t
val cPositive_compdec : CoqInterface.constr lazy_t
val cBV_compdec : CoqInterface.constr lazy_t
val cFArray_compdec : CoqInterface.constr lazy_t

val ctval : CoqInterface.constr lazy_t
val cTval : CoqInterface.constr lazy_t

val cCO_xH : CoqInterface.constr lazy_t
val cCO_Z0 : CoqInterface.constr lazy_t
val cCO_BV : CoqInterface.constr lazy_t

val cUO_xO : CoqInterface.constr lazy_t
val cUO_xI : CoqInterface.constr lazy_t
val cUO_Zpos : CoqInterface.constr lazy_t
val cUO_Zneg : CoqInterface.constr lazy_t
val cUO_Zopp : CoqInterface.constr lazy_t
val cUO_BVbitOf : CoqInterface.constr lazy_t
val cUO_BVnot : CoqInterface.constr lazy_t
val cUO_BVneg : CoqInterface.constr lazy_t
val cUO_BVextr : CoqInterface.constr lazy_t
val cUO_BVzextn : CoqInterface.constr lazy_t
val cUO_BVsextn : CoqInterface.constr lazy_t

val cBO_Zplus : CoqInterface.constr lazy_t
val cBO_Zminus : CoqInterface.constr lazy_t
val cBO_Zmult : CoqInterface.constr lazy_t
val cBO_Zlt : CoqInterface.constr lazy_t
val cBO_Zle : CoqInterface.constr lazy_t
val cBO_Zge : CoqInterface.constr lazy_t
val cBO_Zgt : CoqInterface.constr lazy_t
val cBO_eq : CoqInterface.constr lazy_t
val cBO_BVand : CoqInterface.constr lazy_t
val cBO_BVor : CoqInterface.constr lazy_t
val cBO_BVxor : CoqInterface.constr lazy_t
val cBO_BVadd : CoqInterface.constr lazy_t
val cBO_BVmult : CoqInterface.constr lazy_t
val cBO_BVult : CoqInterface.constr lazy_t
val cBO_BVslt : CoqInterface.constr lazy_t
val cBO_BVconcat : CoqInterface.constr lazy_t
val cBO_BVshl : CoqInterface.constr lazy_t
val cBO_BVshr : CoqInterface.constr lazy_t
val cBO_select : CoqInterface.constr lazy_t
val cBO_diffarray : CoqInterface.constr lazy_t

val cTO_store : CoqInterface.constr lazy_t

val cNO_distinct : CoqInterface.constr lazy_t

val catom : CoqInterface.constr lazy_t
val cAcop : CoqInterface.constr lazy_t
val cAuop : CoqInterface.constr lazy_t
val cAbop : CoqInterface.constr lazy_t
val cAtop : CoqInterface.constr lazy_t
val cAnop : CoqInterface.constr lazy_t
val cAapp : CoqInterface.constr lazy_t

val cform : CoqInterface.constr lazy_t
val cFatom : CoqInterface.constr lazy_t
val cFtrue : CoqInterface.constr lazy_t
val cFfalse : CoqInterface.constr lazy_t
val cFnot2 : CoqInterface.constr lazy_t
val cFand : CoqInterface.constr lazy_t
val cFor : CoqInterface.constr lazy_t
val cFxor : CoqInterface.constr lazy_t
val cFimp : CoqInterface.constr lazy_t
val cFiff : CoqInterface.constr lazy_t
val cFite : CoqInterface.constr lazy_t
val cFbbT : CoqInterface.constr lazy_t

val cis_true : CoqInterface.constr lazy_t

val cvalid_sat_checker : CoqInterface.constr lazy_t
val cinterp_var_sat_checker : CoqInterface.constr lazy_t

val make_certif_ops :
           string list list ->
           CoqInterface.constr array option ->
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t * CoqInterface.constr lazy_t *
           CoqInterface.constr lazy_t * CoqInterface.constr lazy_t

(* Some constructions *)
val ceq_refl_true : CoqInterface.constr lazy_t
val eq_refl_true : unit -> CoqInterface.constr
val vm_cast_true_no_check : CoqInterface.constr -> CoqInterface.constr
val vm_cast_true : Environ.env -> CoqInterface.constr -> CoqInterface.constr
val mkNat : int -> CoqInterface.constr
val mkN : int -> CoqInterface.constr
val mk_bv_list : bool list -> CoqInterface.constr

(* Reification *)
val mk_bool : CoqInterface.constr -> bool
val mk_bool_list : CoqInterface.constr -> bool list
val mk_nat : CoqInterface.constr -> int
val mk_N : CoqInterface.constr -> int
val mk_Z : CoqInterface.constr -> int
val mk_bvsize : CoqInterface.constr -> int

(* Switches between constr and OCaml *)
val option_of_constr_option : CoqInterface.constr -> CoqInterface.constr option
val list_of_constr_tuple : CoqInterface.constr -> CoqInterface.constr list

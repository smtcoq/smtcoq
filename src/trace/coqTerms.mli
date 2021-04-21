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


val gen_constant : string list list -> string -> Structures.constr lazy_t

(* Int63 *)
val cint : Structures.constr lazy_t
val ceq63 : Structures.constr lazy_t

(* PArray *)
val carray : Structures.constr lazy_t

(* nat *)
val cnat : Structures.constr lazy_t
val cO : Structures.constr lazy_t
val cS : Structures.constr lazy_t

(* Positive *)
val cpositive : Structures.constr lazy_t
val cxI : Structures.constr lazy_t
val cxO : Structures.constr lazy_t
val cxH : Structures.constr lazy_t
val ceqbP : Structures.constr lazy_t

(* N *)
val cN : Structures.constr lazy_t
val cN0 : Structures.constr lazy_t
val cNpos : Structures.constr lazy_t
val cof_nat : Structures.constr lazy_t

(* Z *)
val cZ : Structures.constr lazy_t
val cZ0 : Structures.constr lazy_t
val cZpos : Structures.constr lazy_t
val cZneg : Structures.constr lazy_t
val copp : Structures.constr lazy_t
val cadd : Structures.constr lazy_t
val csub : Structures.constr lazy_t
val cmul : Structures.constr lazy_t
val cltb : Structures.constr lazy_t
val cleb : Structures.constr lazy_t
val cgeb : Structures.constr lazy_t
val cgtb : Structures.constr lazy_t
val ceqbZ : Structures.constr lazy_t

(* Booleans *)
val cbool : Structures.constr lazy_t
val ctrue : Structures.constr lazy_t
val cfalse : Structures.constr lazy_t
val candb : Structures.constr lazy_t
val corb : Structures.constr lazy_t
val cxorb : Structures.constr lazy_t
val cnegb : Structures.constr lazy_t
val cimplb : Structures.constr lazy_t
val ceqb : Structures.constr lazy_t
val cifb : Structures.constr lazy_t
val ciff : Structures.constr lazy_t
val creflect : Structures.constr lazy_t

(* Lists *)
val clist : Structures.constr lazy_t
val cnil : Structures.constr lazy_t
val ccons : Structures.constr lazy_t
val clength : Structures.constr lazy_t

(* Option *)
val coption : Structures.constr lazy_t
val cSome : Structures.constr lazy_t
val cNone : Structures.constr lazy_t

(* Pairs *)
val cpair : Structures.constr lazy_t
val cprod : Structures.constr lazy_t

(* Dependent pairs *)
val csigT : Structures.constr lazy_t

(* Logical Operators *)
val cnot : Structures.constr lazy_t
val ceq : Structures.constr lazy_t
val crefl_equal : Structures.constr lazy_t
val cconj : Structures.constr lazy_t
val cand : Structures.constr lazy_t

(* Bit vectors *)
val cbitvector : Structures.constr lazy_t
val cof_bits : Structures.constr lazy_t
val cbitOf : Structures.constr lazy_t
val cbv_eq : Structures.constr lazy_t
val cbv_not : Structures.constr lazy_t
val cbv_neg : Structures.constr lazy_t
val cbv_and : Structures.constr lazy_t
val cbv_or : Structures.constr lazy_t
val cbv_xor : Structures.constr lazy_t
val cbv_add : Structures.constr lazy_t
val cbv_mult : Structures.constr lazy_t
val cbv_ult : Structures.constr lazy_t
val cbv_slt : Structures.constr lazy_t
val cbv_concat : Structures.constr lazy_t
val cbv_extr : Structures.constr lazy_t
val cbv_zextn : Structures.constr lazy_t
val cbv_sextn : Structures.constr lazy_t
val cbv_shl : Structures.constr lazy_t
val cbv_shr : Structures.constr lazy_t

(* Arrays *)
val cfarray : Structures.constr lazy_t
val cselect : Structures.constr lazy_t
val cstore : Structures.constr lazy_t
val cdiff : Structures.constr lazy_t
val cequalarray : Structures.constr lazy_t

(* OrderedType *)

(* SMT_terms *)
val cState_C_t : Structures.constr lazy_t
val cState_S_t : Structures.constr lazy_t

val cdistinct : Structures.constr lazy_t

val ctype : Structures.constr lazy_t
val cTZ : Structures.constr lazy_t
val cTbool : Structures.constr lazy_t
val cTpositive : Structures.constr lazy_t
val cTBV : Structures.constr lazy_t
val cTFArray : Structures.constr lazy_t
val cTindex : Structures.constr lazy_t

val cinterp_t : Structures.constr lazy_t
val cdec_interp : Structures.constr lazy_t
val cord_interp : Structures.constr lazy_t
val ccomp_interp : Structures.constr lazy_t
val cinh_interp : Structures.constr lazy_t

val cinterp_eqb : Structures.constr lazy_t

val ctyp_compdec : Structures.constr lazy_t
val cTyp_compdec : Structures.constr lazy_t
val cunit_typ_compdec : Structures.constr lazy_t
val cte_carrier : Structures.constr lazy_t
val cte_compdec : Structures.constr lazy_t
val ceqb_of_compdec : Structures.constr lazy_t
val cCompDec : Structures.constr lazy_t

val cbool_compdec : Structures.constr lazy_t
val cZ_compdec : Structures.constr lazy_t
val cPositive_compdec : Structures.constr lazy_t
val cBV_compdec : Structures.constr lazy_t
val cFArray_compdec : Structures.constr lazy_t

val ctval : Structures.constr lazy_t
val cTval : Structures.constr lazy_t

val cCO_xH : Structures.constr lazy_t
val cCO_Z0 : Structures.constr lazy_t
val cCO_BV : Structures.constr lazy_t

val cUO_xO : Structures.constr lazy_t
val cUO_xI : Structures.constr lazy_t
val cUO_Zpos : Structures.constr lazy_t
val cUO_Zneg : Structures.constr lazy_t
val cUO_Zopp : Structures.constr lazy_t
val cUO_BVbitOf : Structures.constr lazy_t
val cUO_BVnot : Structures.constr lazy_t
val cUO_BVneg : Structures.constr lazy_t
val cUO_BVextr : Structures.constr lazy_t
val cUO_BVzextn : Structures.constr lazy_t
val cUO_BVsextn : Structures.constr lazy_t

val cBO_Zplus : Structures.constr lazy_t
val cBO_Zminus : Structures.constr lazy_t
val cBO_Zmult : Structures.constr lazy_t
val cBO_Zlt : Structures.constr lazy_t
val cBO_Zle : Structures.constr lazy_t
val cBO_Zge : Structures.constr lazy_t
val cBO_Zgt : Structures.constr lazy_t
val cBO_eq : Structures.constr lazy_t
val cBO_BVand : Structures.constr lazy_t
val cBO_BVor : Structures.constr lazy_t
val cBO_BVxor : Structures.constr lazy_t
val cBO_BVadd : Structures.constr lazy_t
val cBO_BVmult : Structures.constr lazy_t
val cBO_BVult : Structures.constr lazy_t
val cBO_BVslt : Structures.constr lazy_t
val cBO_BVconcat : Structures.constr lazy_t
val cBO_BVshl : Structures.constr lazy_t
val cBO_BVshr : Structures.constr lazy_t
val cBO_select : Structures.constr lazy_t
val cBO_diffarray : Structures.constr lazy_t

val cTO_store : Structures.constr lazy_t

val cNO_distinct : Structures.constr lazy_t

val catom : Structures.constr lazy_t
val cAcop : Structures.constr lazy_t
val cAuop : Structures.constr lazy_t
val cAbop : Structures.constr lazy_t
val cAtop : Structures.constr lazy_t
val cAnop : Structures.constr lazy_t
val cAapp : Structures.constr lazy_t

val cform : Structures.constr lazy_t
val cFatom : Structures.constr lazy_t
val cFtrue : Structures.constr lazy_t
val cFfalse : Structures.constr lazy_t
val cFnot2 : Structures.constr lazy_t
val cFand : Structures.constr lazy_t
val cFor : Structures.constr lazy_t
val cFxor : Structures.constr lazy_t
val cFimp : Structures.constr lazy_t
val cFiff : Structures.constr lazy_t
val cFite : Structures.constr lazy_t
val cFbbT : Structures.constr lazy_t

val cis_true : Structures.constr lazy_t

val cvalid_sat_checker : Structures.constr lazy_t
val cinterp_var_sat_checker : Structures.constr lazy_t

val make_certif_ops :
           string list list ->
           Structures.constr array option ->
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t * Structures.constr lazy_t *
           Structures.constr lazy_t * Structures.constr lazy_t

(* Some constructions *)
val ceq_refl_true : Structures.constr lazy_t
val eq_refl_true : unit -> Structures.constr
val vm_cast_true_no_check : Structures.constr -> Structures.constr
val vm_cast_true : Environ.env -> Structures.constr -> Structures.constr
val mkNat : int -> Structures.constr
val mkN : int -> Structures.constr
val mk_bv_list : bool list -> Structures.constr

(* Reification *)
val mk_bool : Structures.constr -> bool
val mk_bool_list : Structures.constr -> bool list
val mk_nat : Structures.constr -> int
val mk_N : Structures.constr -> int
val mk_Z : Structures.constr -> int
val mk_bvsize : Structures.constr -> int

(* Switches between constr and OCaml *)
val option_of_constr_option : Structures.constr -> Structures.constr option
val list_of_constr_tuple : Structures.constr -> Structures.constr list

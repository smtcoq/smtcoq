(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type coqTerm = CoqInterface.constr Evd.MonadR.t

(* Int63 *)
val cint : coqTerm
val ceq63 : coqTerm

(* PArray *)
val carray : coqTerm
val cmake : coqTerm
val cset : coqTerm

(* is_true *)
val cis_true : coqTerm

(* nat *)
val cnat : coqTerm
val cO : coqTerm
val cS : coqTerm

(* Positive *)
val cpositive : coqTerm
val cxI : coqTerm
val cxO : coqTerm
val cxH : coqTerm
val ceqbP : coqTerm

(* N *)
val cN : coqTerm
val cN0 : coqTerm
val cNpos : coqTerm
val cof_nat : coqTerm

(* Z *)
val cZ : coqTerm
val cZ0 : coqTerm
val cZpos : coqTerm
val cZneg : coqTerm
val copp : coqTerm
val cadd : coqTerm
val csub : coqTerm
val cmul : coqTerm
val cltb : coqTerm
val cleb : coqTerm
val cgeb : coqTerm
val cgtb : coqTerm
val ceqbZ : coqTerm

(* Booleans *)
val cbool : coqTerm
val ctrue : coqTerm
val cfalse : coqTerm
val candb : coqTerm
val corb : coqTerm
val cxorb : coqTerm
val cnegb : coqTerm
val cimplb : coqTerm
val ceqb : coqTerm
val cifb : coqTerm
val creflect : coqTerm

(* Lists *)
val clist : coqTerm
val cnil : coqTerm
val ccons : coqTerm
val clength : coqTerm

(* Option *)
val coption : coqTerm
val cSome : coqTerm
val cNone : coqTerm

(* Pairs *)
val cpair : coqTerm
val cprod : coqTerm

(* Dependent pairs *)
val csigT : coqTerm

(* Logical Operators *)
val cnot : coqTerm
val cconj : coqTerm
val cand : coqTerm
val ciff : coqTerm

(* Equality *)
val ceq : coqTerm
val crefl_equal : coqTerm

(* Micromega *)
val micromega_coq_proofTerm : coqTerm

(* Bit vectors *)
val cbitvector : coqTerm
val cof_bits : coqTerm
val cbitOf : coqTerm
val cbv_eq : coqTerm
val cbv_not : coqTerm
val cbv_neg : coqTerm
val cbv_and : coqTerm
val cbv_or : coqTerm
val cbv_xor : coqTerm
val cbv_add : coqTerm
val cbv_mult : coqTerm
val cbv_ult : coqTerm
val cbv_slt : coqTerm
val cbv_concat : coqTerm
val cbv_extr : coqTerm
val cbv_zextn : coqTerm
val cbv_sextn : coqTerm
val cbv_shl : coqTerm
val cbv_shr : coqTerm

(* Arrays *)
val cfarray : coqTerm
val cselect : coqTerm
val cstore : coqTerm
val cdiff : coqTerm
val cequalarray : coqTerm

(* SMTCoq terms *)
val cState_C_t : coqTerm
val cState_S_t : coqTerm

val cdistinct : coqTerm

val ctype : coqTerm
val cTZ : coqTerm
val cTbool : coqTerm
val cTpositive : coqTerm
val cTBV : coqTerm
val cTFArray : coqTerm
val cTindex : coqTerm

val cinterp_t : coqTerm
val cdec_interp : coqTerm
val cord_interp : coqTerm
val ccomp_interp : coqTerm
val cinh_interp : coqTerm

val cinterp_eqb : coqTerm

val ctval : coqTerm
val cTval : coqTerm

val cCO_xH : coqTerm
val cCO_Z0 : coqTerm
val cCO_BV : coqTerm

val cUO_xO : coqTerm
val cUO_xI : coqTerm
val cUO_Zpos : coqTerm
val cUO_Zneg : coqTerm
val cUO_Zopp : coqTerm
val cUO_BVbitOf : coqTerm
val cUO_BVnot : coqTerm
val cUO_BVneg : coqTerm
val cUO_BVextr : coqTerm
val cUO_BVzextn : coqTerm
val cUO_BVsextn : coqTerm

val cBO_Zplus : coqTerm
val cBO_Zminus : coqTerm
val cBO_Zmult : coqTerm
val cBO_Zlt : coqTerm
val cBO_Zle : coqTerm
val cBO_Zge : coqTerm
val cBO_Zgt : coqTerm
val cBO_eq : coqTerm
val cBO_BVand : coqTerm
val cBO_BVor : coqTerm
val cBO_BVxor : coqTerm
val cBO_BVadd : coqTerm
val cBO_BVmult : coqTerm
val cBO_BVult : coqTerm
val cBO_BVslt : coqTerm
val cBO_BVconcat : coqTerm
val cBO_BVshl : coqTerm
val cBO_BVshr : coqTerm
val cBO_select : coqTerm
val cBO_diffarray : coqTerm

val cTO_store : coqTerm

val cNO_distinct : coqTerm

val catom : coqTerm
val cAcop : coqTerm
val cAuop : coqTerm
val cAbop : coqTerm
val cAtop : coqTerm
val cAnop : coqTerm
val cAapp : coqTerm

val cform : coqTerm
val cFatom : coqTerm
val cFtrue : coqTerm
val cFfalse : coqTerm
val cFnot2 : coqTerm
val cFand : coqTerm
val cFor : coqTerm
val cFxor : coqTerm
val cFimp : coqTerm
val cFiff : coqTerm
val cFite : coqTerm
val cFbbT : coqTerm

(* SMTCoq Classes *)
val ctyp_compdec : coqTerm
val cTyp_compdec : coqTerm
val cte_carrier : coqTerm
val cte_compdec : coqTerm
val ceqb_of_compdec : coqTerm
val cCompDec : coqTerm

val cunit_typ_compdec : coqTerm
val cbool_compdec : coqTerm
val cZ_compdec : coqTerm
val cPositive_compdec : coqTerm
val cBV_compdec : coqTerm
val cFArray_compdec : coqTerm

(* SMTCoq Trace *)
type certif_ops =
  (CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr * CoqInterface.constr *
   CoqInterface.constr * CoqInterface.constr) Evd.MonadR.t

val csat_checker_valid : coqTerm
val csat_checker_interp_var : coqTerm
val csat_checker_Certif : coqTerm
val csat_checker_dimacs : coqTerm
val csat_checker_certif : coqTerm
val csat_checker_theorem_checker : coqTerm
val csat_checker_checker : coqTerm
val csat_checker_certif_ops : certif_ops

val ccnf_checker_certif : coqTerm
val ccnf_checker_Certif : coqTerm
val ccnf_checker_checker_b_correct : coqTerm
val ccnf_checker_checker_b : coqTerm
val ccnf_checker_checker_eq_correct : coqTerm
val ccnf_checker_checker_eq : coqTerm
val ccnf_checker_certif_ops : certif_ops

val ceuf_checker_Certif : coqTerm
val ceuf_checker_certif : coqTerm
val ceuf_checker_checker : coqTerm
val ceuf_checker_checker_correct : coqTerm
val ceuf_checker_checker_b_correct : coqTerm
val ceuf_checker_checker_b : coqTerm
val ceuf_checker_checker_eq_correct : coqTerm
val ceuf_checker_checker_eq : coqTerm
val ceuf_checker_checker_debug : coqTerm
val ceuf_checker_name_step : coqTerm
val ceuf_checker_Name_Res : coqTerm
val ceuf_checker_Name_Weaken : coqTerm
val ceuf_checker_Name_ImmFlatten : coqTerm
val ceuf_checker_Name_CTrue : coqTerm
val ceuf_checker_Name_CFalse : coqTerm
val ceuf_checker_Name_BuildDef : coqTerm
val ceuf_checker_Name_BuildDef2 : coqTerm
val ceuf_checker_Name_BuildProj : coqTerm
val ceuf_checker_Name_ImmBuildDef : coqTerm
val ceuf_checker_Name_ImmBuildDef2 : coqTerm
val ceuf_checker_Name_ImmBuildProj : coqTerm
val ceuf_checker_Name_EqTr : coqTerm
val ceuf_checker_Name_EqCgr : coqTerm
val ceuf_checker_Name_EqCgrP : coqTerm
val ceuf_checker_Name_LiaMicromega : coqTerm
val ceuf_checker_Name_LiaDiseq : coqTerm
val ceuf_checker_Name_SplArith : coqTerm
val ceuf_checker_Name_SplDistinctElim : coqTerm
val ceuf_checker_Name_BBVar : coqTerm
val ceuf_checker_Name_BBConst : coqTerm
val ceuf_checker_Name_BBOp : coqTerm
val ceuf_checker_Name_BBNot : coqTerm
val ceuf_checker_Name_BBNeg : coqTerm
val ceuf_checker_Name_BBAdd : coqTerm
val ceuf_checker_Name_BBConcat : coqTerm
val ceuf_checker_Name_BBMul : coqTerm
val ceuf_checker_Name_BBUlt : coqTerm
val ceuf_checker_Name_BBSlt : coqTerm
val ceuf_checker_Name_BBEq : coqTerm
val ceuf_checker_Name_BBDiseq : coqTerm
val ceuf_checker_Name_BBExtract : coqTerm
val ceuf_checker_Name_BBZextend : coqTerm
val ceuf_checker_Name_BBSextend : coqTerm
val ceuf_checker_Name_BBShl : coqTerm
val ceuf_checker_Name_BBShr : coqTerm
val ceuf_checker_Name_RowEq : coqTerm
val ceuf_checker_Name_RowNeq : coqTerm
val ceuf_checker_Name_Ext : coqTerm
val ceuf_checker_Name_Hole : coqTerm
val ceuf_checker_certif_ops : CoqInterface.constr array option -> certif_ops


(* Some constructions *)
val ceq_refl_true : coqTerm
val vm_cast_true_no_check : CoqInterface.constr -> coqTerm
val vm_cast_true : Environ.env -> CoqInterface.constr -> coqTerm
val mkNat : int -> coqTerm
val mkN : int -> coqTerm
val mk_list : coqTerm -> ('a -> coqTerm) -> 'a list -> coqTerm
val mk_bv_list : bool list -> coqTerm
val mkArray : coqTerm * CoqInterface.constr array -> coqTerm

(* Reification *)
val mk_bool : Evd.evar_map -> CoqInterface.constr -> bool
val mk_bool_list : Evd.evar_map -> CoqInterface.constr -> bool list
val mk_nat : Evd.evar_map -> CoqInterface.constr -> int
val mk_N : Evd.evar_map -> CoqInterface.constr -> int
val mk_Z : Evd.evar_map -> CoqInterface.constr -> int
val mk_bvsize : Evd.evar_map -> CoqInterface.constr -> int

(* Switches between constr and OCaml *)
val option_of_constr_option : Evd.evar_map -> CoqInterface.constr -> CoqInterface.constr option
val list_of_constr_tuple : Evd.evar_map -> CoqInterface.constr -> CoqInterface.constr list

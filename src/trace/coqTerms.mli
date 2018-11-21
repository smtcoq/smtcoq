(* Int63 *)
val cint : Term.constr lazy_t
val ceq63 : Term.constr lazy_t

(* PArray *)
val carray : Term.constr lazy_t

(* nat *)
val cnat : Term.constr lazy_t
val cO : Term.constr lazy_t
val cS : Term.constr lazy_t

(* Positive *)
val cpositive : Term.constr lazy_t
val cxI : Term.constr lazy_t
val cxO : Term.constr lazy_t
val cxH : Term.constr lazy_t
val ceqbP : Term.constr lazy_t

(* N *)
val cN : Term.constr lazy_t
val cN0 : Term.constr lazy_t
val cNpos : Term.constr lazy_t
val cof_nat : Term.constr lazy_t

(* Z *)
val cZ : Term.constr lazy_t
val cZ0 : Term.constr lazy_t
val cZpos : Term.constr lazy_t
val cZneg : Term.constr lazy_t
val copp : Term.constr lazy_t
val cadd : Term.constr lazy_t
val csub : Term.constr lazy_t
val cmul : Term.constr lazy_t
val cltb : Term.constr lazy_t
val cleb : Term.constr lazy_t
val cgeb : Term.constr lazy_t
val cgtb : Term.constr lazy_t
val ceqbZ : Term.constr lazy_t

(* Booleans *)
val cbool : Term.constr lazy_t
val ctrue : Term.constr lazy_t
val cfalse : Term.constr lazy_t
val candb : Term.constr lazy_t
val corb : Term.constr lazy_t
val cxorb : Term.constr lazy_t
val cnegb : Term.constr lazy_t
val cimplb : Term.constr lazy_t
val ceqb : Term.constr lazy_t
val cifb : Term.constr lazy_t
val ciff : Term.constr lazy_t
val creflect : Term.constr lazy_t

(* Lists *)
val clist : Term.constr lazy_t
val cnil : Term.constr lazy_t
val ccons : Term.constr lazy_t
val clength : Term.constr lazy_t

(* Option *)
val coption : Term.constr lazy_t
val cSome : Term.constr lazy_t
val cNone : Term.constr lazy_t

(* Pairs *)
val cpair : Term.constr lazy_t

(* Dependent pairs *)
val csigT : Term.constr lazy_t

(* Logical Operators *)
val cnot : Term.constr lazy_t
val ceq : Term.constr lazy_t
val crefl_equal : Term.constr lazy_t
val cconj : Term.constr lazy_t
val cand : Term.constr lazy_t

(* Bit vectors *)
val cbitvector : Term.constr lazy_t
val cof_bits : Term.constr lazy_t
val cbitOf : Term.constr lazy_t
val cbv_eq : Term.constr lazy_t
val cbv_not : Term.constr lazy_t
val cbv_neg : Term.constr lazy_t
val cbv_and : Term.constr lazy_t
val cbv_or : Term.constr lazy_t
val cbv_xor : Term.constr lazy_t
val cbv_add : Term.constr lazy_t
val cbv_mult : Term.constr lazy_t
val cbv_ult : Term.constr lazy_t
val cbv_slt : Term.constr lazy_t
val cbv_concat : Term.constr lazy_t
val cbv_extr : Term.constr lazy_t
val cbv_zextn : Term.constr lazy_t
val cbv_sextn : Term.constr lazy_t
val cbv_shl : Term.constr lazy_t
val cbv_shr : Term.constr lazy_t

(* Arrays *)
val cfarray : Term.constr lazy_t
val cselect : Term.constr lazy_t
val cstore : Term.constr lazy_t
val cdiff : Term.constr lazy_t
val cequalarray : Term.constr lazy_t

(* OrderedType *)

(* SMT_terms *)
val cState_C_t : Term.constr lazy_t

val cdistinct : Term.constr lazy_t

val ctype : Term.constr lazy_t
val cTZ : Term.constr lazy_t
val cTbool : Term.constr lazy_t
val cTpositive : Term.constr lazy_t
val cTBV : Term.constr lazy_t
val cTFArray : Term.constr lazy_t
val cTindex : Term.constr lazy_t

val cinterp_t : Term.constr lazy_t
val cdec_interp : Term.constr lazy_t
val cord_interp : Term.constr lazy_t
val ccomp_interp : Term.constr lazy_t
val cinh_interp : Term.constr lazy_t

val cinterp_eqb : Term.constr lazy_t

val ctyp_compdec : Term.constr lazy_t
val cTyp_compdec : Term.constr lazy_t
val cunit_typ_compdec : Term.constr lazy_t
val cte_carrier : Term.constr lazy_t
val cte_compdec : Term.constr lazy_t
val ceqb_of_compdec : Term.constr lazy_t
val cCompDec : Term.constr lazy_t

val cbool_compdec : Term.constr lazy_t
val cZ_compdec : Term.constr lazy_t
val cPositive_compdec : Term.constr lazy_t
val cBV_compdec : Term.constr lazy_t
val cFArray_compdec : Term.constr lazy_t

val ctval : Term.constr lazy_t
val cTval : Term.constr lazy_t

val cCO_xH : Term.constr lazy_t
val cCO_Z0 : Term.constr lazy_t
val cCO_BV : Term.constr lazy_t

val cUO_xO : Term.constr lazy_t
val cUO_xI : Term.constr lazy_t
val cUO_Zpos : Term.constr lazy_t
val cUO_Zneg : Term.constr lazy_t
val cUO_Zopp : Term.constr lazy_t
val cUO_BVbitOf : Term.constr lazy_t
val cUO_BVnot : Term.constr lazy_t
val cUO_BVneg : Term.constr lazy_t
val cUO_BVextr : Term.constr lazy_t
val cUO_BVzextn : Term.constr lazy_t
val cUO_BVsextn : Term.constr lazy_t

val cBO_Zplus : Term.constr lazy_t
val cBO_Zminus : Term.constr lazy_t
val cBO_Zmult : Term.constr lazy_t
val cBO_Zlt : Term.constr lazy_t
val cBO_Zle : Term.constr lazy_t
val cBO_Zge : Term.constr lazy_t
val cBO_Zgt : Term.constr lazy_t
val cBO_eq : Term.constr lazy_t
val cBO_BVand : Term.constr lazy_t
val cBO_BVor : Term.constr lazy_t
val cBO_BVxor : Term.constr lazy_t
val cBO_BVadd : Term.constr lazy_t
val cBO_BVmult : Term.constr lazy_t
val cBO_BVult : Term.constr lazy_t
val cBO_BVslt : Term.constr lazy_t
val cBO_BVconcat : Term.constr lazy_t
val cBO_BVshl : Term.constr lazy_t
val cBO_BVshr : Term.constr lazy_t
val cBO_select : Term.constr lazy_t
val cBO_diffarray : Term.constr lazy_t

val cTO_store : Term.constr lazy_t

val cNO_distinct : Term.constr lazy_t

val catom : Term.constr lazy_t
val cAcop : Term.constr lazy_t
val cAuop : Term.constr lazy_t
val cAbop : Term.constr lazy_t
val cAtop : Term.constr lazy_t
val cAnop : Term.constr lazy_t
val cAapp : Term.constr lazy_t

val cform : Term.constr lazy_t
val cFatom : Term.constr lazy_t
val cFtrue : Term.constr lazy_t
val cFfalse : Term.constr lazy_t
val cFnot2 : Term.constr lazy_t
val cFand : Term.constr lazy_t
val cFor : Term.constr lazy_t
val cFxor : Term.constr lazy_t
val cFimp : Term.constr lazy_t
val cFiff : Term.constr lazy_t
val cFite : Term.constr lazy_t
val cFbbT : Term.constr lazy_t

val cis_true : Term.constr lazy_t

val cvalid_sat_checker : Term.constr lazy_t
val cinterp_var_sat_checker : Term.constr lazy_t

val make_certif_ops :
           string list list ->
           Term.constr array option ->
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t * Term.constr lazy_t *
           Term.constr lazy_t * Term.constr lazy_t

(* Some constructions *)
val ceq_refl_true : Term.constr lazy_t
val eq_refl_true : unit -> Term.constr
val vm_cast_true : Environ.env -> Term.constr -> Term.constr
val mkNat : int -> Term.constr
val mkN : int -> Term.constr
val mk_bv_list : bool list -> Term.constr

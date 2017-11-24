val gen_constant : string list list -> string -> Term.constr lazy_t
val cint : Term.constr lazy_t
val ceq63 : Term.constr lazy_t
val carray : Term.constr lazy_t
val positive_modules : string list list
val cpositive : Term.constr lazy_t
val cxI : Term.constr lazy_t
val cxO : Term.constr lazy_t
val cxH : Term.constr lazy_t
val ceqbP : Term.constr lazy_t
val z_modules : string list list
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
val bool_modules : string list list
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
val creflect : Term.constr lazy_t
val clist : Term.constr lazy_t
val cnil : Term.constr lazy_t
val ccons : Term.constr lazy_t
val coption : Term.constr lazy_t
val cSome : Term.constr lazy_t
val cNone : Term.constr lazy_t
val cpair : Term.constr lazy_t
val csigT : Term.constr lazy_t
val cnot : Term.constr lazy_t
val ceq : Term.constr lazy_t
val crefl_equal : Term.constr lazy_t
val smt_modules : string list list
val cState_C_t : Term.constr lazy_t
val cdistinct : Term.constr lazy_t
val ctype : Term.constr lazy_t
val cTZ : Term.constr lazy_t
val cTbool : Term.constr lazy_t
val cTpositive : Term.constr lazy_t
val cTindex : Term.constr lazy_t
val ctyp_eqb : Term.constr lazy_t
val cTyp_eqb : Term.constr lazy_t
val cte_carrier : Term.constr lazy_t
val cte_eqb : Term.constr lazy_t
val ctyp_eqb_of_typ_eqb_param : Term.constr lazy_t
val cunit_typ_eqb : Term.constr lazy_t
val ctval : Term.constr lazy_t
val cTval : Term.constr lazy_t
val cCO_xH : Term.constr lazy_t
val cCO_Z0 : Term.constr lazy_t
val cUO_xO : Term.constr lazy_t
val cUO_xI : Term.constr lazy_t
val cUO_Zpos : Term.constr lazy_t
val cUO_Zneg : Term.constr lazy_t
val cUO_Zopp : Term.constr lazy_t
val cBO_Zplus : Term.constr lazy_t
val cBO_Zminus : Term.constr lazy_t
val cBO_Zmult : Term.constr lazy_t
val cBO_Zlt : Term.constr lazy_t
val cBO_Zle : Term.constr lazy_t
val cBO_Zge : Term.constr lazy_t
val cBO_Zgt : Term.constr lazy_t
val cBO_eq : Term.constr lazy_t
val cNO_distinct : Term.constr lazy_t
val catom : Term.constr lazy_t
val cAcop : Term.constr lazy_t
val cAuop : Term.constr lazy_t
val cAbop : Term.constr lazy_t
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
  Term.constr lazy_t
val ceq_refl_true : Term.constr lazy_t
val eq_refl_true : unit -> Term.constr
val vm_cast_true : Term.constr -> Term.constr

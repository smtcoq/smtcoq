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


open SmtMisc


type coqTerm = CoqInterface.constr Evd.MonadR.t

let gc prefix constant sigma =
  Evarutil.new_global sigma (Coqlib.lib_ref (prefix ^ "." ^ constant))


(* Int63 *)
let int63_prefix = "num.int63"
let int63_gc = gc int63_prefix
let cint = int63_gc "type"
let ceq63 = int63_gc "eqb"

(* PArray *)
let array_prefix = "array.array"
let array_gc = gc array_prefix
let carray = array_gc "type"
let cmake = array_gc "make"
let cset = array_gc "set"

(* is_true *)
let cis_true = gc "core.is_true" "is_true"

(* nat *)
let nat_prefix = "num.nat"
let nat_gc = gc nat_prefix
let cnat = nat_gc "type"
let cO = nat_gc "O"
let cS = nat_gc "S"

(* Positive *)
let positive_prefix = "num.pos"
let positive_gc = gc positive_prefix
let cpositive = positive_gc "type"
let cxI = positive_gc "xI"
let cxO = positive_gc "xO"
let cxH = positive_gc "xH"
let ceqbP = positive_gc "eqb"

(* N *)
let n_prefix = "num.N"
let n_gc = gc n_prefix
let cN = n_gc "type"
let cN0 = n_gc "N0"
let cNpos = n_gc "Npos"
let cof_nat = n_gc "of_nat"

(* Z *)
let z_prefix = "num.Z"
let z_gc = gc z_prefix
let cZ = z_gc "type"
let cZ0 = z_gc "Z0"
let cZpos = z_gc "Zpos"
let cZneg = z_gc "Zneg"
let copp = z_gc "opp"
let cadd = z_gc "add"
let csub = z_gc "sub"
let cmul = z_gc "mul"
let cltb = z_gc "ltb"
let cleb = z_gc "leb"
let cgeb = z_gc "geb"
let cgtb = z_gc "gtb"
let ceqbZ = z_gc "eqb"

(* Booleans *)
let bool_prefix = "core.bool"
let bool_gc = gc bool_prefix
let cbool = bool_gc "type"
let ctrue = bool_gc "true"
let cfalse = bool_gc "false"
let candb = bool_gc "andb"
let corb = bool_gc "orb"
let cxorb = bool_gc "xorb"
let cnegb = bool_gc "negb"
let cimplb = bool_gc "implb"
let ceqb = bool_gc "eqb"
let cifb = bool_gc "ifb"
let creflect = bool_gc "reflect"

(* Lists *)
let list_prefix = "core.list"
let list_gc = gc list_prefix
let clist = list_gc "type"
let cnil = list_gc "nil"
let ccons = list_gc "cons"
let clength = list_gc "length"

(* Option *)
let option_prefix = "core.option"
let option_gc = gc option_prefix
let coption = option_gc "type"
let cSome = option_gc "Some"
let cNone = option_gc "None"

(* Pairs *)
let pair_prefix = "core.prod"
let pair_gc = gc pair_prefix
let cpair = pair_gc "intro"
let cprod = pair_gc "type"

(* Dependent pairs *)
let sigT_prefix = "core.sigT"
let sigT_gc = gc sigT_prefix
let csigT = sigT_gc "type"

(* Logical Operators *)
let cnot = gc "core.not" "type"
let cconj = gc "core.and" "conj"
let cand = gc "core.and" "type"
let ciff = gc "core.iff" "type"

(* Equality *)
let eq_prefix = "core.eq"
let eq_gc = gc eq_prefix
let ceq = eq_gc "type"
let crefl_equal = eq_gc "refl"

(* Micromega *)
let micromega_prefix = "micromega.ZMicromega"
let micromega_gc = gc micromega_prefix
let micromega_coq_proofTerm = micromega_gc "ZArithProof"

(* Bit vectors *)
let bv_prefix = "SMTCoq.bva.BVList.BITVECTOR_LIST"
let bv_gc = gc bv_prefix
let cbitvector = bv_gc "bitvector"
let cof_bits = bv_gc "of_bits"
let cbitOf = bv_gc "bitOf"
let cbv_eq = bv_gc "bv_eq"
let cbv_not = bv_gc "bv_not"
let cbv_neg = bv_gc "bv_neg"
let cbv_and = bv_gc "bv_and"
let cbv_or = bv_gc "bv_or"
let cbv_xor = bv_gc "bv_xor"
let cbv_add = bv_gc "bv_add"
let cbv_mult = bv_gc "bv_mult"
let cbv_ult = bv_gc "bv_ult"
let cbv_slt = bv_gc "bv_slt"
let cbv_concat = bv_gc "bv_concat"
let cbv_extr = bv_gc "bv_extr"
let cbv_zextn = bv_gc "bv_zextn"
let cbv_sextn = bv_gc "bv_sextn"
let cbv_shl = bv_gc "bv_shl"
let cbv_shr = bv_gc "bv_shr"

(* Arrays *)
let array_prefix = "SMTCoq.array.FArray"
let array_gc = gc array_prefix
let cfarray = array_gc "farray"
let cselect = array_gc "select"
let cstore = array_gc "store"
let cdiff = array_gc "diff"
let cequalarray = array_gc "equal"

(* SMTCoq terms *)
let state_prefix = "SMTCoq.State"
let state_gc = gc state_prefix
let cState_C_t = state_gc "C.t"
let cState_S_t = state_gc "S.t"

let misc_prefix = "SMTCoq.Misc"
let misc_gc = gc misc_prefix
let cdistinct = misc_gc "distinct"

let terms_prefix = "SMTCoq.SMT_terms"
let terms_gc = gc terms_prefix

let ctype = terms_gc "Typ.type"
let cTZ = terms_gc "Typ.TZ"
let cTbool = terms_gc "Typ.Tbool"
let cTpositive = terms_gc "Typ.Tpositive"
let cTBV = terms_gc "Typ.TBV"
let cTFArray = terms_gc "Typ.TFArray"
let cTindex = terms_gc "Typ.Tindex"

let cinterp_t = terms_gc "Typ.interp"
let cdec_interp = terms_gc "Typ.dec_interp"
let cord_interp = terms_gc "Typ.ord_interp"
let ccomp_interp = terms_gc "Typ.comp_interp"
let cinh_interp = terms_gc "Typ.inh_interp"

let cinterp_eqb = terms_gc "Typ.i_eqb"

let ctval =  terms_gc "Atom.tval"
let cTval =  terms_gc "Atom.Tval"

let cCO_xH = terms_gc "Atom.CO_xH"
let cCO_Z0 = terms_gc "Atom.CO_Z0"
let cCO_BV = terms_gc "Atom.CO_BV"

let cUO_xO = terms_gc "Atom.UO_xO"
let cUO_xI = terms_gc "Atom.UO_xI"
let cUO_Zpos = terms_gc "Atom.UO_Zpos"
let cUO_Zneg = terms_gc "Atom.UO_Zneg"
let cUO_Zopp = terms_gc "Atom.UO_Zopp"
let cUO_BVbitOf = terms_gc "Atom.UO_BVbitOf"
let cUO_BVnot = terms_gc "Atom.UO_BVnot"
let cUO_BVneg = terms_gc "Atom.UO_BVneg"
let cUO_BVextr = terms_gc "Atom.UO_BVextr"
let cUO_BVzextn = terms_gc "Atom.UO_BVzextn"
let cUO_BVsextn = terms_gc "Atom.UO_BVsextn"

let cBO_Zplus = terms_gc "Atom.BO_Zplus"
let cBO_Zminus = terms_gc "Atom.BO_Zminus"
let cBO_Zmult = terms_gc "Atom.BO_Zmult"
let cBO_Zlt = terms_gc "Atom.BO_Zlt"
let cBO_Zle = terms_gc "Atom.BO_Zle"
let cBO_Zge = terms_gc "Atom.BO_Zge"
let cBO_Zgt = terms_gc "Atom.BO_Zgt"
let cBO_eq = terms_gc "Atom.BO_eq"
let cBO_BVand = terms_gc "Atom.BO_BVand"
let cBO_BVor = terms_gc "Atom.BO_BVor"
let cBO_BVxor = terms_gc "Atom.BO_BVxor"
let cBO_BVadd = terms_gc "Atom.BO_BVadd"
let cBO_BVmult = terms_gc "Atom.BO_BVmult"
let cBO_BVult = terms_gc "Atom.BO_BVult"
let cBO_BVslt = terms_gc "Atom.BO_BVslt"
let cBO_BVconcat = terms_gc "Atom.BO_BVconcat"
let cBO_BVshl = terms_gc "Atom.BO_BVshl"
let cBO_BVshr = terms_gc "Atom.BO_BVshr"
let cBO_select = terms_gc "Atom.BO_select"
let cBO_diffarray = terms_gc "Atom.BO_diffarray"

let cTO_store = terms_gc "Atom.TO_store"

let cNO_distinct = terms_gc "Atom.NO_distinct"

let catom = terms_gc "Atom.atom"
let cAcop = terms_gc "Atom.Acop"
let cAuop = terms_gc "Atom.Auop"
let cAbop = terms_gc "Atom.Abop"
let cAtop = terms_gc "Atom.Atop"
let cAnop = terms_gc "Atom.Anop"
let cAapp = terms_gc "Atom.Aapp"

let cform  = terms_gc "Form.form"
let cFatom = terms_gc "Form.Fatom"
let cFtrue = terms_gc "Form.Ftrue"
let cFfalse = terms_gc "Form.Ffalse"
let cFnot2 = terms_gc "Form.Fnot2"
let cFand = terms_gc "Form.Fand"
let cFor = terms_gc "Form.For"
let cFxor = terms_gc "Form.Fxor"
let cFimp = terms_gc "Form.Fimp"
let cFiff = terms_gc "Form.Fiff"
let cFite = terms_gc "Form.Fite"
let cFbbT = terms_gc "Form.FbbT"

(* SMTCoq Classes *)
let classes_prefix = "SMTCoq.classes.SMT_classes"
let classes_gc = gc classes_prefix
let ctyp_compdec = classes_gc "typ_compdec"
let cTyp_compdec = classes_gc "Typ_compdec"
let cte_carrier = classes_gc "te_carrier"
let cte_compdec = classes_gc "te_compdec"
let ceqb_of_compdec = classes_gc "eqb_of_compdec"
let cCompDec = classes_gc "CompDec"

let classesi_prefix = "SMTCoq.classes.SMT_classes_instances"
let classesi_gc = gc classesi_prefix
let cunit_typ_compdec = classesi_gc "unit_typ_compdec"
let cbool_compdec = classesi_gc "bool_compdec"
let cZ_compdec = classesi_gc "Z_compdec"
let cPositive_compdec = classesi_gc "Positive_compdec"
let cBV_compdec = classesi_gc "BV_compdec"
let cFArray_compdec = classesi_gc "FArray_compdec"

(* SMTCoq Trace *)
let sat_checker_prefix = "SMTCoq.Trace.Sat_Checker"
let sat_checker_gc = gc sat_checker_prefix
let csat_checker_valid = sat_checker_gc "valid"
let csat_checker_interp_var = sat_checker_gc "interp_var"
let csat_checker_Certif = sat_checker_gc "Certif"
let csat_checker_dimacs = sat_checker_gc "dimacs"
let csat_checker_certif = sat_checker_gc "certif"
let csat_checker_theorem_checker = sat_checker_gc "theorem_checker"
let csat_checker_checker = sat_checker_gc "checker"

let cnf_checker_prefix = "SMTCoq.Trace.Cnf_Checker"
let cnf_checker_gc = gc cnf_checker_prefix
let ccnf_checker_certif = cnf_checker_gc "certif"
let ccnf_checker_Certif = cnf_checker_gc "Certif"
let ccnf_checker_checker_b_correct = cnf_checker_gc "checker_b_correct"
let ccnf_checker_checker_b = cnf_checker_gc "checker_b"
let ccnf_checker_checker_eq_correct = cnf_checker_gc "checker_eq_correct"
let ccnf_checker_checker_eq = cnf_checker_gc "checker_eq"

let euf_checker_prefix = "SMTCoq.Trace.Euf_Checker"
let euf_checker_gc = gc euf_checker_prefix
let ceuf_checker_Certif = euf_checker_gc "Certif"
let ceuf_checker_certif = euf_checker_gc "certif"
let ceuf_checker_checker = euf_checker_gc "checker"
let ceuf_checker_checker_correct = euf_checker_gc "checker_correct"
let ceuf_checker_checker_b_correct = euf_checker_gc "checker_b_correct"
let ceuf_checker_checker_b = euf_checker_gc "checker_b"
let ceuf_checker_checker_eq_correct = euf_checker_gc "checker_eq_correct"
let ceuf_checker_checker_eq = euf_checker_gc "checker_eq"
let ceuf_checker_checker_debug = euf_checker_gc "checker_debug"
let ceuf_checker_name_step = euf_checker_gc "name_step"
let ceuf_checker_Name_Res = euf_checker_gc "Name_Res"
let ceuf_checker_Name_Weaken = euf_checker_gc "Name_Weaken"
let ceuf_checker_Name_ImmFlatten = euf_checker_gc "Name_ImmFlatten"
let ceuf_checker_Name_CTrue = euf_checker_gc "Name_CTrue"
let ceuf_checker_Name_CFalse = euf_checker_gc "Name_CFalse"
let ceuf_checker_Name_BuildDef = euf_checker_gc "Name_BuildDef"
let ceuf_checker_Name_BuildDef2 = euf_checker_gc "Name_BuildDef2"
let ceuf_checker_Name_BuildProj = euf_checker_gc "Name_BuildProj"
let ceuf_checker_Name_ImmBuildDef = euf_checker_gc "Name_ImmBuildDef"
let ceuf_checker_Name_ImmBuildDef2 = euf_checker_gc "Name_ImmBuildDef2"
let ceuf_checker_Name_ImmBuildProj = euf_checker_gc "Name_ImmBuildProj"
let ceuf_checker_Name_EqTr = euf_checker_gc "Name_EqTr"
let ceuf_checker_Name_EqCgr = euf_checker_gc "Name_EqCgr"
let ceuf_checker_Name_EqCgrP = euf_checker_gc "Name_EqCgrP"
let ceuf_checker_Name_LiaMicromega = euf_checker_gc "Name_LiaMicromega"
let ceuf_checker_Name_LiaDiseq = euf_checker_gc "Name_LiaDiseq"
let ceuf_checker_Name_SplArith = euf_checker_gc "Name_SplArith"
let ceuf_checker_Name_SplDistinctElim = euf_checker_gc "Name_SplDistinctElim"
let ceuf_checker_Name_BBVar = euf_checker_gc "Name_BBVar"
let ceuf_checker_Name_BBConst = euf_checker_gc "Name_BBConst"
let ceuf_checker_Name_BBOp = euf_checker_gc "Name_BBOp"
let ceuf_checker_Name_BBNot = euf_checker_gc "Name_BBNot"
let ceuf_checker_Name_BBNeg = euf_checker_gc "Name_BBNeg"
let ceuf_checker_Name_BBAdd = euf_checker_gc "Name_BBAdd"
let ceuf_checker_Name_BBConcat = euf_checker_gc "Name_BBConcat"
let ceuf_checker_Name_BBMul = euf_checker_gc "Name_BBMul"
let ceuf_checker_Name_BBUlt = euf_checker_gc "Name_BBUlt"
let ceuf_checker_Name_BBSlt = euf_checker_gc "Name_BBSlt"
let ceuf_checker_Name_BBEq = euf_checker_gc "Name_BBEq"
let ceuf_checker_Name_BBDiseq = euf_checker_gc "Name_BBDiseq"
let ceuf_checker_Name_BBExtract = euf_checker_gc "Name_BBExtract"
let ceuf_checker_Name_BBZextend = euf_checker_gc "Name_BBZextend"
let ceuf_checker_Name_BBSextend = euf_checker_gc "Name_BBSextend"
let ceuf_checker_Name_BBShl = euf_checker_gc "Name_BBShl"
let ceuf_checker_Name_BBShr = euf_checker_gc "Name_BBShr"
let ceuf_checker_Name_RowEq = euf_checker_gc "Name_RowEq"
let ceuf_checker_Name_RowNeq = euf_checker_gc "Name_RowNeq"
let ceuf_checker_Name_Ext = euf_checker_gc "Name_Ext"
let ceuf_checker_Name_Hole = euf_checker_gc "Name_Hole"

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
let make_certif_ops prefix args sigma =
  let gc = gc prefix in
  let gen_constant c sigma =
    match args with
      | Some args ->
         let sigma, c = gc c sigma in
         sigma, mklApp c args
      | None -> gc c sigma in
  let sigma, step = gen_constant "step" sigma in
  let sigma, res = gen_constant "Res" sigma in
  let sigma, weaken = gen_constant "Weaken" sigma in
  let sigma, immflatten = gen_constant "ImmFlatten" sigma in
  let sigma, ctrue = gen_constant "CTrue" sigma in
  let sigma, cfalse = gen_constant "CFalse" sigma in
  let sigma, builddef = gen_constant "BuildDef" sigma in
  let sigma, builddef2 = gen_constant "BuildDef2" sigma in
  let sigma, buildproj = gen_constant "BuildProj" sigma in
  let sigma, immbuildproj = gen_constant "ImmBuildProj" sigma in
  let sigma, immbuilddef = gen_constant "ImmBuildDef" sigma in
  let sigma, immbuilddef2 = gen_constant "ImmBuildDef2" sigma in
  let sigma, eqtr = gen_constant "EqTr" sigma in
  let sigma, eqcgr = gen_constant "EqCgr" sigma in
  let sigma, eqcgrp = gen_constant "EqCgrP" sigma in
  let sigma, liamicromega = gen_constant "LiaMicromega" sigma in
  let sigma, liadiseq = gen_constant "LiaDiseq" sigma in
  let sigma, splarith = gen_constant "SplArith" sigma in
  let sigma, spldistinctelim = gen_constant "SplDistinctElim" sigma in
  let sigma, bbvar = gen_constant "BBVar" sigma in
  let sigma, bbconst = gen_constant "BBConst" sigma in
  let sigma, bbop = gen_constant "BBOp" sigma in
  let sigma, bbnot = gen_constant "BBNot" sigma in
  let sigma, bbeq = gen_constant "BBEq" sigma in
  let sigma, bbdiseq = gen_constant "BBDiseq" sigma in
  let sigma, bbneg = gen_constant "BBNeg" sigma in
  let sigma, bbadd = gen_constant "BBAdd" sigma in
  let sigma, bbmul = gen_constant "BBMul" sigma in
  let sigma, bbult = gen_constant "BBUlt" sigma in
  let sigma, bbslt = gen_constant "BBSlt" sigma in
  let sigma, bbconcat = gen_constant "BBConcat" sigma in
  let sigma, bbextract = gen_constant "BBExtract" sigma in
  let sigma, bbzextend = gen_constant "BBZextend" sigma in
  let sigma, bbsextend = gen_constant "BBSextend" sigma in
  let sigma, bbshl = gen_constant "BBShl" sigma in
  let sigma, bbshr = gen_constant "BBShr" sigma in
  let sigma, roweq = gen_constant "RowEq" sigma in
  let sigma, rowneq = gen_constant "RowNeq" sigma in
  let sigma, ext = gen_constant "Ext" sigma in
  let sigma, hole = gen_constant "Hole" sigma in
  let sigma, forallinst = gen_constant "ForallInst" sigma in
  sigma, (step, res, weaken, immflatten, ctrue, cfalse, builddef, builddef2, buildproj, immbuildproj, immbuilddef, immbuilddef2, eqtr, eqcgr, eqcgrp, liamicromega, liadiseq, splarith, spldistinctelim, bbvar, bbconst, bbop, bbnot, bbeq, bbdiseq, bbneg, bbadd, bbmul, bbult, bbslt, bbconcat, bbextract, bbzextend, bbsextend, bbshl, bbshr, roweq, rowneq, ext, hole, forallinst)
 (* (gen_constant "step",
  *  gen_constant "Res", gen_constant "Weaken", gen_constant "ImmFlatten",
  *  gen_constant "CTrue", gen_constant "CFalse",
  *  gen_constant "BuildDef", gen_constant "BuildDef2",
  *  gen_constant "BuildProj",
  *  gen_constant "ImmBuildProj", gen_constant "ImmBuildDef",
  *  gen_constant"ImmBuildDef2",
  *  gen_constant "EqTr", gen_constant "EqCgr", gen_constant "EqCgrP",
  *  gen_constant "LiaMicromega", gen_constant "LiaDiseq",
  *  gen_constant "SplArith", gen_constant "SplDistinctElim",
  *  gen_constant "BBVar", gen_constant "BBConst",
  *  gen_constant "BBOp", gen_constant "BBNot", gen_constant "BBEq",
  *  gen_constant "BBDiseq",
  *  gen_constant "BBNeg", gen_constant "BBAdd", gen_constant "BBMul",
  *  gen_constant "BBUlt", gen_constant "BBSlt", gen_constant "BBConcat",
  *  gen_constant "BBExtract", gen_constant "BBZextend", gen_constant "BBSextend",
  *  gen_constant "BBShl", gen_constant "BBShr",
  *  gen_constant "RowEq", gen_constant "RowNeq", gen_constant "Ext",
  *  gen_constant "Hole", gen_constant "ForallInst") *)
let csat_checker_certif_ops = make_certif_ops sat_checker_prefix None
let ccnf_checker_certif_ops = make_certif_ops cnf_checker_prefix None
let ceuf_checker_certif_ops = make_certif_ops euf_checker_prefix


(** Useful constructions *)

let ceq_refl_true sigma =
  let sigma, cbool = cbool sigma in
  let sigma, ctrue = ctrue sigma in
  let sigma, crefl_equal = crefl_equal sigma in
  sigma, mklApp crefl_equal [|cbool; ctrue|]

let vm_cast_true_no_check t sigma =
  let sigma, ceq_refl_true = ceq_refl_true sigma in
  let sigma, ceq = ceq sigma in
  let sigma, cbool = cbool sigma in
  let sigma, ctrue = ctrue sigma in
  sigma, CoqInterface.mkCast(ceq_refl_true, CoqInterface.vmcast, mklApp ceq [|cbool; t; ctrue|])

(* This version checks convertibility right away instead of delaying it at
   Qed. This allows to report issues to the user as soon as he/she runs one of
   SMTCoq's tactics. *)
let vm_cast_true env t sigma =
  let sigma, ctrue = ctrue sigma in
  try
    let ctrue' = EConstr.to_constr sigma ctrue in
    let t' = EConstr.to_constr sigma t in
    CoqInterface.vm_conv Reduction.CUMUL env ctrue' t';
    vm_cast_true_no_check t sigma
  with Reduction.NotConvertible ->
    CoqInterface.error ("SMTCoq was not able to check the proof certificate.")


(* Compute a nat *)
let mkNat i sigma =
  let sigma, cO = cO sigma in
  let sigma, cS = cS sigma in
  let rec mkNat = function
    | 0 -> cO
    | i -> mklApp cS [|mkNat (i-1)|]
  in
  sigma, mkNat i

(* Compute a positive *)
let mkPositive i sigma =
  let sigma, cxH = cxH sigma in
  let sigma, cxO = cxO sigma in
  let sigma, cxI = cxI sigma in
  let rec mkPositive = function
    | 1 -> cxH
    | i ->
       let c = if (i mod 2) = 0 then cxO else cxI in
       mklApp c [|mkPositive (i / 2)|]
  in
  sigma, mkPositive i

(* Compute a N *)
let mkN i sigma =
  let sigma, cN0 = cN0 sigma in
  let sigma, cNpos = cNpos sigma in
  match i with
    | 0 -> sigma, cN0
    | i ->
       let sigma, r = mkPositive i sigma in
       sigma, mklApp cNpos [|r|]

(* Compute a Boolean *)
let mkBool b sigma =
  match b with
    | true -> ctrue sigma
    | false -> cfalse sigma

(* Compute a list *)
let mk_list ty f l sigma =
  let sigma, ty = ty sigma in
  let sigma, cnil = cnil sigma in
  let sigma, ccons = ccons sigma in
  let rec mk_list sigma = function
    | [] -> sigma, mklApp cnil [|ty|]
    | x::xs ->
       let sigma, x = f x sigma in
       let sigma, xs = mk_list sigma xs in
       sigma, mklApp ccons [|ty; x; xs|]
  in
  mk_list sigma l

(* Compute a Boolean list *)
let mk_bv_list = mk_list cbool mkBool

(* Compute an array *)
let mkArray : coqTerm * CoqInterface.constr array -> coqTerm =
  fun (ty, a) sigma ->
  let sigma, ty = ty sigma in
  let sigma, cset = cset sigma in
  let sigma, cmake = cmake sigma in
  let l = (Array.length a) - 1 in
  sigma, snd (Array.fold_left (fun (i, acc) c ->
                        let acc' =
                          if i = l then
                            acc
                          else
                            mklApp cset [|ty; acc; mkInt i; c|] in
                        (i+1, acc')
                       ) (0, mklApp cmake [|ty; mkInt l; a.(l)|]) a)


(* Reification *)
let mk_bool sigma b =
  let sigma, ctrue = ctrue sigma in
  let sigma, cfalse = cfalse sigma in
  let c, args = CoqInterface.decompose_app sigma b in
  if CoqInterface.eq_constr sigma c ctrue then true
  else if CoqInterface.eq_constr sigma c cfalse then false
  else assert false

let mk_bool_list sigma bs =
  let sigma, cnil = cnil sigma in
  let sigma, ccons = ccons sigma in
  let rec mk_bool_list bs =
    let c, args = CoqInterface.decompose_app sigma bs in
    if CoqInterface.eq_constr sigma c cnil then []
    else if CoqInterface.eq_constr sigma c ccons then
      match args with
        | [_; b; bs] -> mk_bool sigma b :: mk_bool_list bs
        | _ -> assert false
    else assert false
  in
  mk_bool_list bs

let mk_nat sigma n =
  let sigma, cO = cO sigma in
  let sigma, cS = cS sigma in
  let rec mk_nat n =
    let c, args = CoqInterface.decompose_app sigma n in
    if CoqInterface.eq_constr sigma c cO then
      0
    else if CoqInterface.eq_constr sigma c cS then
      match args with
        | [n] -> (mk_nat n) + 1
        | _ -> assert false
    else assert false
  in
  mk_nat n

let mk_positive sigma n =
  let sigma, cxH = cxH sigma in
  let sigma, cxO = cxO sigma in
  let sigma, cxI = cxI sigma in
  let rec mk_positive n =
    let c, args = CoqInterface.decompose_app sigma n in
    if CoqInterface.eq_constr sigma c cxH then
      1
    else if CoqInterface.eq_constr sigma c cxO then
      match args with
        | [n] -> 2 * (mk_positive n)
        | _ -> assert false
    else if CoqInterface.eq_constr sigma c cxI then
      match args with
        | [n] -> 2 * (mk_positive n) + 1
        | _ -> assert false
    else assert false
  in
  mk_positive n

let mk_N sigma n =
  let sigma, cN0 = cN0 sigma in
  let sigma, cNpos = cNpos sigma in
  let c, args = CoqInterface.decompose_app sigma n in
  if CoqInterface.eq_constr sigma c cN0 then
    0
  else if CoqInterface.eq_constr sigma c cNpos then
    match args with
      | [n] -> mk_positive sigma n
      | _ -> assert false
  else assert false

let mk_Z sigma n =
  let sigma, cZ0 = cZ0 sigma in
  let sigma, cZpos = cZpos sigma in
  let sigma, cZneg = cZneg sigma in
  let c, args = CoqInterface.decompose_app sigma n in
  if CoqInterface.eq_constr sigma c cZ0 then 0
  else if CoqInterface.eq_constr sigma c cZpos then
    match args with
    | [n] -> mk_positive sigma n
    | _ -> assert false
  else if CoqInterface.eq_constr sigma c cZneg then
    match args with
    | [n] -> - mk_positive sigma n
    | _ -> assert false
  else assert false


(* size of bivectors are either N.of_nat (length l) or an N *)
let mk_bvsize sigma n =
  let sigma, cof_nat = cof_nat sigma in
  let sigma, clength = clength sigma in
  let c, args = CoqInterface.decompose_app sigma n in
  if CoqInterface.eq_constr sigma c cof_nat then
    match args with
    | [nl] ->
      let c, args = CoqInterface.decompose_app sigma nl in
      if CoqInterface.eq_constr sigma c clength then
        match args with
        | [_; l] -> List.length (mk_bool_list sigma l)
        | _ -> assert false
      else assert false
    | _ -> assert false
  else mk_N sigma n


(** Switches between constr and OCaml *)
(* Transform a option constr into a constr option *)
let option_of_constr_option sigma co =
  let sigma, cSome = cSome sigma in
  let c, args = CoqInterface.decompose_app sigma co in
  if CoqInterface.eq_constr sigma c cSome then
    match args with
      | [_;c] -> Some c
      | _ -> assert false
  else
    None

(* Transform a tuple of constr into a (reversed) list of constr *)
let list_of_constr_tuple sigma =
  let sigma, cpair = cpair sigma in
  let rec list_of_constr_tuple acc t =
    let c, args = CoqInterface.decompose_app sigma t in
    if CoqInterface.eq_constr sigma c cpair then
      match args with
        | [_;_;t1;t2] ->
           let acc' = list_of_constr_tuple acc t1 in
           list_of_constr_tuple acc' t2
        | _ -> assert false
    else
      t::acc
  in
  list_of_constr_tuple []

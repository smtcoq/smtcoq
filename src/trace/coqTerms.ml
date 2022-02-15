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


open SmtMisc


type coqTerm = CoqInterface.constr lazy_t
let gen_constant = CoqInterface.gen_constant


(* Int63 *)
let cint = CoqInterface.cint
let ceq63 = gen_constant CoqInterface.int63_module "eqb"

(* PArray *)
let carray = gen_constant CoqInterface.parray_modules "array"

(* is_true *)
let cis_true = gen_constant CoqInterface.init_modules "is_true"

(* nat *)
let cnat = gen_constant CoqInterface.init_modules "nat"
let cO = gen_constant CoqInterface.init_modules "O"
let cS = gen_constant CoqInterface.init_modules "S"

(* Positive *)
let positive_modules = [["Coq";"Numbers";"BinNums"];
                        ["Coq";"PArith";"BinPosDef";"Pos"]]

let cpositive = gen_constant positive_modules "positive"
let cxI = gen_constant positive_modules "xI"
let cxO = gen_constant positive_modules "xO"
let cxH = gen_constant positive_modules "xH"
let ceqbP = gen_constant positive_modules "eqb"

(* N *)
let n_modules = [["Coq";"NArith";"BinNat";"N"]]

let cN = gen_constant positive_modules "N"
let cN0 = gen_constant positive_modules "N0"
let cNpos = gen_constant positive_modules "Npos"

let cof_nat = gen_constant n_modules "of_nat"


(* Z *)
let z_modules = [["Coq";"Numbers";"BinNums"];
                 ["Coq";"ZArith";"BinInt"];
                 ["Coq";"ZArith";"BinInt";"Z"]]

let cZ = gen_constant z_modules "Z"
let cZ0 = gen_constant z_modules "Z0"
let cZpos = gen_constant z_modules "Zpos"
let cZneg = gen_constant z_modules "Zneg"
let copp = gen_constant z_modules "opp"
let cadd = gen_constant z_modules "add"
let csub = gen_constant z_modules "sub"
let cmul = gen_constant z_modules "mul"
let cltb = gen_constant z_modules "ltb"
let cleb = gen_constant z_modules "leb"
let cgeb = gen_constant z_modules "geb"
let cgtb = gen_constant z_modules "gtb"
let ceqbZ = gen_constant z_modules "eqb"
(* let cZeqbsym = gen_constant z_modules "eqb_sym" *)

(* Booleans *)
let bool_modules = [["Coq";"Bool";"Bool"]]

let cbool = gen_constant CoqInterface.init_modules "bool"
let ctrue = gen_constant CoqInterface.init_modules "true"
let cfalse = gen_constant CoqInterface.init_modules "false"
let candb = gen_constant CoqInterface.init_modules "andb"
let corb = gen_constant CoqInterface.init_modules "orb"
let cxorb = gen_constant CoqInterface.init_modules "xorb"
let cnegb = gen_constant CoqInterface.init_modules "negb"
let cimplb = gen_constant CoqInterface.init_modules "implb"
let ceqb = gen_constant  bool_modules "eqb"
let cifb = gen_constant bool_modules "ifb"
let ciff = gen_constant CoqInterface.init_modules "iff"
let creflect = gen_constant bool_modules "reflect"

(* Lists *)
let clist = gen_constant CoqInterface.init_modules "list"
let cnil = gen_constant CoqInterface.init_modules "nil"
let ccons = gen_constant CoqInterface.init_modules "cons"
let clength = gen_constant CoqInterface.init_modules "length"

(* Option *)
let coption = gen_constant CoqInterface.init_modules "option"
let cSome = gen_constant CoqInterface.init_modules "Some"
let cNone = gen_constant CoqInterface.init_modules "None"

(* Pairs *)
let cpair = gen_constant CoqInterface.init_modules "pair"
let cprod = gen_constant CoqInterface.init_modules "prod"

(* Dependent pairs *)
let csigT = gen_constant CoqInterface.init_modules "sigT"
(* let cprojT1 = gen_constant CoqInterface.init_modules "projT1" *)
(* let cprojT2 = gen_constant CoqInterface.init_modules "projT2" *)
(* let cprojT3 = gen_constant CoqInterface.init_modules "projT3" *)

(* let csigT2 = gen_constant CoqInterface.init_modules "sigT2" *)
(* let csigT_of_sigT2 = gen_constant CoqInterface.init_modules "sigT_of_sigT2" *)

(* Logical Operators *)
let cnot = gen_constant CoqInterface.init_modules "not"
let ceq = gen_constant CoqInterface.init_modules "eq"
let crefl_equal = gen_constant CoqInterface.init_modules "eq_refl"
let cconj = gen_constant CoqInterface.init_modules "conj"
let cand = gen_constant CoqInterface.init_modules "and"

(* Bit vectors *)
let bv_prefix = "SMTCoq.bva.BVList.BITVECTOR_LIST"
let bv_gc = CoqInterface.gen_constant2 bv_prefix
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
let array_gc = CoqInterface.gen_constant2 array_prefix
let cfarray = array_gc "farray"
let cselect = array_gc "select"
let cstore = array_gc "store"
let cdiff = array_gc "diff"
let cequalarray = array_gc "equal"


(* SMT_terms *)
let state_prefix = "SMTCoq.State"
let state_gc = CoqInterface.gen_constant2 state_prefix
let cState_C_t = state_gc "C.t"
let cState_S_t = state_gc "S.t"

let misc_prefix = "SMTCoq.Misc"
let misc_gc = CoqInterface.gen_constant2 misc_prefix
let cdistinct = misc_gc "distinct"

let terms_prefix = "SMTCoq.SMT_terms"
let terms_gc = CoqInterface.gen_constant2 terms_prefix

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

let classes_prefix = "SMTCoq.classes.SMT_classes"
let classes_gc = CoqInterface.gen_constant2 classes_prefix
let ctyp_compdec = classes_gc "typ_compdec"
let cTyp_compdec = classes_gc "Typ_compdec"
let cte_carrier = classes_gc "te_carrier"
let cte_compdec = classes_gc "te_compdec"
let ceqb_of_compdec = classes_gc "eqb_of_compdec"
let cCompDec = classes_gc "CompDec"

let classesi_prefix = "SMTCoq.classes.SMT_classes_instances"
let classesi_gc = CoqInterface.gen_constant2 classesi_prefix
let cunit_typ_compdec = classesi_gc "unit_typ_compdec"
let cbool_compdec = classesi_gc "bool_compdec"
let cZ_compdec = classesi_gc "Z_compdec"
let cPositive_compdec = classesi_gc "Positive_compdec"
let cBV_compdec = classesi_gc "BV_compdec"
let cFArray_compdec = classesi_gc "FArray_compdec"

let sat_checker_prefix = "SMTCoq.Trace.Sat_Checker"
let sat_checker_gc = CoqInterface.gen_constant2 sat_checker_prefix
let csat_checker_valid = sat_checker_gc "valid"
let csat_checker_interp_var = sat_checker_gc "interp_var"
let csat_checker_Certif = sat_checker_gc "Certif"
let csat_checker_dimacs = sat_checker_gc "dimacs"
let csat_checker_certif = sat_checker_gc "certif"
let csat_checker_theorem_checker = sat_checker_gc "theorem_checker"
let csat_checker_checker = sat_checker_gc "checker"

let cnf_checker_prefix = "SMTCoq.Trace.Cnf_Checker"
let cnf_checker_gc = CoqInterface.gen_constant2 cnf_checker_prefix
let ccnf_checker_certif = cnf_checker_gc "certif"
let ccnf_checker_Certif = cnf_checker_gc "Certif"
let ccnf_checker_checker_b_correct = cnf_checker_gc "checker_b_correct"
let ccnf_checker_checker_b = cnf_checker_gc "checker_b"
let ccnf_checker_checker_eq_correct = cnf_checker_gc "checker_eq_correct"
let ccnf_checker_checker_eq = cnf_checker_gc "checker_eq"

let euf_checker_prefix = "SMTCoq.Trace.Euf_Checker"
let euf_checker_gc = CoqInterface.gen_constant2 euf_checker_prefix
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
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm * coqTerm *
  coqTerm * coqTerm
let make_certif_ops prefix args =
  let gc = CoqInterface.gen_constant2 prefix in
  let gen_constant c =
    match args with
      | Some args -> lazy (mklApp (gc c) args)
      | None -> gc c in
 (gen_constant "step",
  gen_constant "Res", gen_constant "Weaken", gen_constant "ImmFlatten",
  gen_constant "CTrue", gen_constant "CFalse",
  gen_constant "BuildDef", gen_constant "BuildDef2",
  gen_constant "BuildProj",
  gen_constant "ImmBuildProj", gen_constant "ImmBuildDef",
  gen_constant"ImmBuildDef2",
  gen_constant "EqTr", gen_constant "EqCgr", gen_constant "EqCgrP",
  gen_constant "LiaMicromega", gen_constant "LiaDiseq",
  gen_constant "SplArith", gen_constant "SplDistinctElim",
  gen_constant "BBVar", gen_constant "BBConst",
  gen_constant "BBOp", gen_constant "BBNot", gen_constant "BBEq",
  gen_constant "BBDiseq",
  gen_constant "BBNeg", gen_constant "BBAdd", gen_constant "BBMul",
  gen_constant "BBUlt", gen_constant "BBSlt", gen_constant "BBConcat",
  gen_constant "BBExtract", gen_constant "BBZextend", gen_constant "BBSextend",
  gen_constant "BBShl", gen_constant "BBShr",
  gen_constant "RowEq", gen_constant "RowNeq", gen_constant "Ext",
  gen_constant "Hole", gen_constant "ForallInst")
let csat_checker_certif_ops = make_certif_ops sat_checker_prefix None
let ccnf_checker_certif_ops = make_certif_ops cnf_checker_prefix None
let ceuf_checker_certif_ops = make_certif_ops euf_checker_prefix


(** Useful constructions *)

let ceq_refl_true =
  lazy (mklApp crefl_equal [|Lazy.force cbool;Lazy.force ctrue|])

let eq_refl_true () = Lazy.force ceq_refl_true

let vm_cast_true_no_check t =
  CoqInterface.mkCast(eq_refl_true (),
              CoqInterface.vmcast,
              mklApp ceq [|Lazy.force cbool; t; Lazy.force ctrue|])

(* This version checks convertibility right away instead of delaying it at
   Qed. This allows to report issues to the user as soon as he/she runs one of
   SMTCoq's tactics. *)
let vm_cast_true env t =
  try
    CoqInterface.vm_conv Reduction.CUMUL env
      (mklApp ceq
         [|Lazy.force cbool; Lazy.force ctrue; Lazy.force ctrue|])
      (mklApp ceq [|Lazy.force cbool; t; Lazy.force ctrue|]);
    vm_cast_true_no_check t
  with Reduction.NotConvertible ->
    CoqInterface.error ("SMTCoq was not able to check the proof certificate.")


(* Compute a nat *)
let rec mkNat = function
  | 0 -> Lazy.force cO
  | i -> mklApp cS [|mkNat (i-1)|]

(* Compute a positive *)
let rec mkPositive = function
  | 1 -> Lazy.force cxH
  | i ->
     let c = if (i mod 2) = 0 then cxO else cxI in
     mklApp c [|mkPositive (i / 2)|]

(* Compute a N *)
let mkN = function
  | 0 -> Lazy.force cN0
  | i -> mklApp cNpos [|mkPositive i|]

(* Compute a Boolean *)
let mkBool = function
  | true -> Lazy.force ctrue
  | false -> Lazy.force cfalse

(* Compute a Boolean list *)
let rec mk_bv_list = function
  | [] -> mklApp cnil [|Lazy.force cbool|]
  | b :: bv ->
    mklApp ccons [|Lazy.force cbool; mkBool b; mk_bv_list bv|]


(* Reification *)
let mk_bool b =
  let c, args = CoqInterface.decompose_app b in
  if CoqInterface.eq_constr c (Lazy.force ctrue) then true
  else if CoqInterface.eq_constr c (Lazy.force cfalse) then false
  else assert false

let rec mk_bool_list bs =
  let c, args = CoqInterface.decompose_app bs in
  if CoqInterface.eq_constr c (Lazy.force cnil) then []
  else if CoqInterface.eq_constr c (Lazy.force ccons) then
    match args with
    | [_; b; bs] -> mk_bool b :: mk_bool_list bs
    | _ -> assert false
  else assert false

let rec mk_nat n =
  let c, args = CoqInterface.decompose_app n in
  if CoqInterface.eq_constr c (Lazy.force cO) then
    0
  else if CoqInterface.eq_constr c (Lazy.force cS) then
    match args with
    | [n] -> (mk_nat n) + 1
    | _ -> assert false
  else assert false

let rec mk_positive n =
  let c, args = CoqInterface.decompose_app n in
  if CoqInterface.eq_constr c (Lazy.force cxH) then
    1
  else if CoqInterface.eq_constr c (Lazy.force cxO) then
    match args with
    | [n] -> 2 * (mk_positive n)
    | _ -> assert false
  else if CoqInterface.eq_constr c (Lazy.force cxI) then
    match args with
    | [n] -> 2 * (mk_positive n) + 1
    | _ -> assert false
  else assert false


let mk_N n =
  let c, args = CoqInterface.decompose_app n in
  if CoqInterface.eq_constr c (Lazy.force cN0) then
    0
  else if CoqInterface.eq_constr c (Lazy.force cNpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else assert false


let mk_Z n =
  let c, args = CoqInterface.decompose_app n in
  if CoqInterface.eq_constr c (Lazy.force cZ0) then 0
  else if CoqInterface.eq_constr c (Lazy.force cZpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else if CoqInterface.eq_constr c (Lazy.force cZneg) then
    match args with
    | [n] -> - mk_positive n
    | _ -> assert false
  else assert false


(* size of bivectors are either N.of_nat (length l) or an N *)
let mk_bvsize n =
  let c, args = CoqInterface.decompose_app n in
  if CoqInterface.eq_constr c (Lazy.force cof_nat) then
    match args with
    | [nl] ->
      let c, args = CoqInterface.decompose_app nl in
      if CoqInterface.eq_constr c (Lazy.force clength) then
        match args with
        | [_; l] -> List.length (mk_bool_list l)
        | _ -> assert false
      else assert false
    | _ -> assert false
  else mk_N n

(** Switches between constr and OCaml *)
(* Transform a option constr into a constr option *)
let option_of_constr_option co =
  let c, args = CoqInterface.decompose_app co in
  if c = Lazy.force cSome then
    match args with
      | [_;c] -> Some c
      | _ -> assert false
  else
    None

(* Transform a tuple of constr into a (reversed) list of constr *)
let list_of_constr_tuple =
  let rec list_of_constr_tuple acc t =
    let c, args = CoqInterface.decompose_app t in
    if c = Lazy.force cpair then
      match args with
        | [_;_;t1;t2] ->
           let acc' = list_of_constr_tuple acc t1 in
           list_of_constr_tuple acc' t2
        | _ -> assert false
    else
      t::acc
  in
  list_of_constr_tuple []

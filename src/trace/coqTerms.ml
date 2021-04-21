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


open SmtMisc


let gen_constant = Structures.gen_constant


(* Int63 *)
let cint = Structures.cint
let ceq63 = gen_constant Structures.int63_modules "eqb"

(* PArray *)
let carray = gen_constant Structures.parray_modules "array"

(* is_true *)
let cis_true = gen_constant Structures.init_modules "is_true"

(* nat *)
let cnat = gen_constant Structures.init_modules "nat"
let cO = gen_constant Structures.init_modules "O"
let cS = gen_constant Structures.init_modules "S"

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

let cbool = gen_constant Structures.init_modules "bool"
let ctrue = gen_constant Structures.init_modules "true"
let cfalse = gen_constant Structures.init_modules "false"
let candb = gen_constant Structures.init_modules "andb"
let corb = gen_constant Structures.init_modules "orb"
let cxorb = gen_constant Structures.init_modules "xorb"
let cnegb = gen_constant Structures.init_modules "negb"
let cimplb = gen_constant Structures.init_modules "implb"
let ceqb = gen_constant  bool_modules "eqb"
let cifb = gen_constant bool_modules "ifb"
let ciff = gen_constant Structures.init_modules "iff"
let creflect = gen_constant bool_modules "reflect"

(* Lists *)
let clist = gen_constant Structures.init_modules "list"
let cnil = gen_constant Structures.init_modules "nil"
let ccons = gen_constant Structures.init_modules "cons"
let clength = gen_constant Structures.init_modules "length"

(* Option *)
let coption = gen_constant Structures.init_modules "option"
let cSome = gen_constant Structures.init_modules "Some"
let cNone = gen_constant Structures.init_modules "None"

(* Pairs *)
let cpair = gen_constant Structures.init_modules "pair"
let cprod = gen_constant Structures.init_modules "prod"

(* Dependent pairs *)
let csigT = gen_constant Structures.init_modules "sigT"
(* let cprojT1 = gen_constant Structures.init_modules "projT1" *)
(* let cprojT2 = gen_constant Structures.init_modules "projT2" *)
(* let cprojT3 = gen_constant Structures.init_modules "projT3" *)

(* let csigT2 = gen_constant Structures.init_modules "sigT2" *)
(* let csigT_of_sigT2 = gen_constant Structures.init_modules "sigT_of_sigT2" *)

(* Logical Operators *)
let cnot = gen_constant Structures.init_modules "not"
let ceq = gen_constant Structures.init_modules "eq"
let crefl_equal = gen_constant Structures.init_modules "eq_refl"
let cconj = gen_constant Structures.init_modules "conj"
let cand = gen_constant Structures.init_modules "and"

(* Bit vectors *)
let bv_modules = [["SMTCoq";"bva";"BVList";"BITVECTOR_LIST"]]
let cbitvector = gen_constant bv_modules "bitvector"
let cof_bits = gen_constant bv_modules "of_bits"
(* let c_of_bits = gen_constant bv_modules "_of_bits" *)
let cbitOf = gen_constant bv_modules "bitOf"
let cbv_eq = gen_constant bv_modules "bv_eq"
let cbv_not = gen_constant bv_modules "bv_not"
let cbv_neg = gen_constant bv_modules "bv_neg"
let cbv_and = gen_constant bv_modules "bv_and"
let cbv_or = gen_constant bv_modules "bv_or"
let cbv_xor = gen_constant bv_modules "bv_xor"
let cbv_add = gen_constant bv_modules "bv_add"
let cbv_mult = gen_constant bv_modules "bv_mult"
let cbv_ult = gen_constant bv_modules "bv_ult"
let cbv_slt = gen_constant bv_modules "bv_slt"
let cbv_concat = gen_constant bv_modules "bv_concat"
let cbv_extr = gen_constant bv_modules "bv_extr"
let cbv_zextn = gen_constant bv_modules "bv_zextn"
let cbv_sextn = gen_constant bv_modules "bv_sextn"
let cbv_shl = gen_constant bv_modules "bv_shl"
let cbv_shr = gen_constant bv_modules "bv_shr"


(* Arrays *)
let array_modules = [["SMTCoq";"array";"FArray"]]
let cfarray = gen_constant array_modules "FArray.farray"
let cselect = gen_constant array_modules "select"
let cstore = gen_constant array_modules "store"
let cdiff = gen_constant array_modules "diff"
let cequalarray = gen_constant array_modules "FArray.equal"

(* OrderedType *)
(* let cOrderedTypeCompare =
 *   gen_constant [["Coq";"Structures";"OrderedType"]] "Compare" *)

(* SMT_terms *)
let smt_modules = [ ["SMTCoq";"Misc"];
		    ["SMTCoq";"State"];
		    ["SMTCoq";"SMT_terms"];
		    ["SMTCoq";"SMT_terms";"Typ"];
		    ["SMTCoq";"SMT_terms";"Form"];
		    ["SMTCoq";"SMT_terms";"Atom"]
		  ]

let cState_C_t = gen_constant [["SMTCoq";"State";"C"]] "t"
let cState_S_t = gen_constant [["SMTCoq";"State";"S"]] "t"

let cdistinct = gen_constant smt_modules "distinct"

let ctype = gen_constant smt_modules "type"
let cTZ = gen_constant smt_modules "TZ"
let cTbool = gen_constant smt_modules "Tbool"
let cTpositive = gen_constant smt_modules "Tpositive"
let cTBV = gen_constant smt_modules "TBV"
let cTFArray = gen_constant smt_modules "TFArray"
let cTindex = gen_constant smt_modules "Tindex"

(* let ct_i = gen_constant smt_modules "t_i" *)
let cinterp_t = gen_constant smt_modules "Typ.interp"
let cdec_interp = gen_constant smt_modules "dec_interp"
let cord_interp = gen_constant smt_modules "ord_interp"
let ccomp_interp = gen_constant smt_modules "comp_interp"
let cinh_interp = gen_constant smt_modules "inh_interp"

let cinterp_eqb = gen_constant smt_modules "i_eqb"
(* let cinterp_eqb_eqb = gen_constant smt_modules "i_eqb_eqb" *)

let classes_modules = [["SMTCoq";"classes";"SMT_classes"];
                       ["SMTCoq";"classes";"SMT_classes_instances"]]

let ctyp_compdec = gen_constant classes_modules "typ_compdec"
let cTyp_compdec = gen_constant classes_modules "Typ_compdec"
(* let ctyp_compdec_from = gen_constant classes_modules "typ_compdec_from" *)
let cunit_typ_compdec = gen_constant classes_modules "unit_typ_compdec"
let cte_carrier = gen_constant classes_modules "te_carrier"
let cte_compdec = gen_constant classes_modules "te_compdec"
let ceqb_of_compdec = gen_constant classes_modules "eqb_of_compdec"
let cCompDec = gen_constant classes_modules "CompDec"

let cbool_compdec = gen_constant classes_modules "bool_compdec"
let cZ_compdec = gen_constant classes_modules "Z_compdec"
let cPositive_compdec = gen_constant classes_modules "Positive_compdec"
let cBV_compdec = gen_constant classes_modules "BV_compdec"
let cFArray_compdec = gen_constant classes_modules "FArray_compdec"

let ctval =  gen_constant smt_modules "tval"
let cTval =  gen_constant smt_modules "Tval"

let cCO_xH = gen_constant smt_modules "CO_xH"
let cCO_Z0 = gen_constant smt_modules "CO_Z0"
let cCO_BV = gen_constant smt_modules "CO_BV"

let cUO_xO = gen_constant smt_modules "UO_xO"
let cUO_xI = gen_constant smt_modules "UO_xI"
let cUO_Zpos = gen_constant smt_modules "UO_Zpos"
let cUO_Zneg = gen_constant smt_modules "UO_Zneg"
let cUO_Zopp = gen_constant smt_modules "UO_Zopp"
let cUO_BVbitOf = gen_constant smt_modules "UO_BVbitOf"
let cUO_BVnot = gen_constant smt_modules "UO_BVnot"
let cUO_BVneg = gen_constant smt_modules "UO_BVneg"
let cUO_BVextr = gen_constant smt_modules "UO_BVextr"
let cUO_BVzextn = gen_constant smt_modules "UO_BVzextn"
let cUO_BVsextn = gen_constant smt_modules "UO_BVsextn"

let cBO_Zplus = gen_constant smt_modules "BO_Zplus"
let cBO_Zminus = gen_constant smt_modules "BO_Zminus"
let cBO_Zmult = gen_constant smt_modules "BO_Zmult"
let cBO_Zlt = gen_constant smt_modules "BO_Zlt"
let cBO_Zle = gen_constant smt_modules "BO_Zle"
let cBO_Zge = gen_constant smt_modules "BO_Zge"
let cBO_Zgt = gen_constant smt_modules "BO_Zgt"
let cBO_eq = gen_constant smt_modules "BO_eq"
let cBO_BVand = gen_constant smt_modules "BO_BVand"
let cBO_BVor = gen_constant smt_modules "BO_BVor"
let cBO_BVxor = gen_constant smt_modules "BO_BVxor"
let cBO_BVadd = gen_constant smt_modules "BO_BVadd"
let cBO_BVmult = gen_constant smt_modules "BO_BVmult"
let cBO_BVult = gen_constant smt_modules "BO_BVult"
let cBO_BVslt = gen_constant smt_modules "BO_BVslt"
let cBO_BVconcat = gen_constant smt_modules "BO_BVconcat"
let cBO_BVshl = gen_constant smt_modules "BO_BVshl"
let cBO_BVshr = gen_constant smt_modules "BO_BVshr"
let cBO_select = gen_constant smt_modules "BO_select"
let cBO_diffarray = gen_constant smt_modules "BO_diffarray"

let cTO_store = gen_constant smt_modules "TO_store"

let cNO_distinct = gen_constant smt_modules "NO_distinct"

let catom = gen_constant smt_modules "atom"
let cAcop = gen_constant smt_modules "Acop"
let cAuop = gen_constant smt_modules "Auop"
let cAbop = gen_constant smt_modules "Abop"
let cAtop = gen_constant smt_modules "Atop"
let cAnop = gen_constant smt_modules "Anop"
let cAapp = gen_constant smt_modules "Aapp"

let cform  = gen_constant smt_modules "form"
let cFatom = gen_constant smt_modules "Fatom"
let cFtrue = gen_constant smt_modules "Ftrue"
let cFfalse = gen_constant smt_modules "Ffalse"
let cFnot2 = gen_constant smt_modules "Fnot2"
let cFand = gen_constant smt_modules "Fand"
let cFor = gen_constant smt_modules "For"
let cFxor = gen_constant smt_modules "Fxor"
let cFimp = gen_constant smt_modules "Fimp"
let cFiff = gen_constant smt_modules "Fiff"
let cFite = gen_constant smt_modules "Fite"
let cFbbT = gen_constant smt_modules "FbbT"

let cvalid_sat_checker = gen_constant [["SMTCoq";"Trace";"Sat_Checker"]] "valid"
let cinterp_var_sat_checker = gen_constant [["SMTCoq";"Trace";"Sat_Checker"]] "interp_var"

let make_certif_ops modules args =
  let gen_constant c =
    match args with
      | Some args -> lazy (mklApp (gen_constant modules c) args)
      | None -> gen_constant modules c in
 (gen_constant "step",
  gen_constant "Res", gen_constant "Weaken", gen_constant "ImmFlatten",
  gen_constant "CTrue", gen_constant "CFalse",
  gen_constant "BuildDef", gen_constant "BuildDef2",
  gen_constant "BuildProj",
  gen_constant "ImmBuildProj", gen_constant"ImmBuildDef",
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


(** Useful constructions *)

let ceq_refl_true =
  lazy (mklApp crefl_equal [|Lazy.force cbool;Lazy.force ctrue|])

let eq_refl_true () = Lazy.force ceq_refl_true

let vm_cast_true_no_check t =
  Structures.mkCast(eq_refl_true (),
              Structures.vmcast,
              mklApp ceq [|Lazy.force cbool; t; Lazy.force ctrue|])

(* This version checks convertibility right away instead of delaying it at
   Qed. This allows to report issues to the user as soon as he/she runs one of
   SMTCoq's tactics. *)
let vm_cast_true env t =
  try
    Structures.vm_conv Reduction.CUMUL env
      (mklApp ceq
         [|Lazy.force cbool; Lazy.force ctrue; Lazy.force ctrue|])
      (mklApp ceq [|Lazy.force cbool; t; Lazy.force ctrue|]);
    vm_cast_true_no_check t
  with Reduction.NotConvertible ->
    Structures.error ("SMTCoq was not able to check the proof certificate.")


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
  let c, args = Structures.decompose_app b in
  if Structures.eq_constr c (Lazy.force ctrue) then true
  else if Structures.eq_constr c (Lazy.force cfalse) then false
  else assert false

let rec mk_bool_list bs =
  let c, args = Structures.decompose_app bs in
  if Structures.eq_constr c (Lazy.force cnil) then []
  else if Structures.eq_constr c (Lazy.force ccons) then
    match args with
    | [_; b; bs] -> mk_bool b :: mk_bool_list bs
    | _ -> assert false
  else assert false

let rec mk_nat n =
  let c, args = Structures.decompose_app n in
  if Structures.eq_constr c (Lazy.force cO) then
    0
  else if Structures.eq_constr c (Lazy.force cS) then
    match args with
    | [n] -> (mk_nat n) + 1
    | _ -> assert false
  else assert false

let rec mk_positive n =
  let c, args = Structures.decompose_app n in
  if Structures.eq_constr c (Lazy.force cxH) then
    1
  else if Structures.eq_constr c (Lazy.force cxO) then
    match args with
    | [n] -> 2 * (mk_positive n)
    | _ -> assert false
  else if Structures.eq_constr c (Lazy.force cxI) then
    match args with
    | [n] -> 2 * (mk_positive n) + 1
    | _ -> assert false
  else assert false


let mk_N n =
  let c, args = Structures.decompose_app n in
  if Structures.eq_constr c (Lazy.force cN0) then
    0
  else if Structures.eq_constr c (Lazy.force cNpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else assert false


let mk_Z n =
  let c, args = Structures.decompose_app n in
  if Structures.eq_constr c (Lazy.force cZ0) then 0
  else if Structures.eq_constr c (Lazy.force cZpos) then
    match args with
    | [n] -> mk_positive n
    | _ -> assert false
  else if Structures.eq_constr c (Lazy.force cZneg) then
    match args with
    | [n] -> - mk_positive n
    | _ -> assert false
  else assert false


(* size of bivectors are either N.of_nat (length l) or an N *)
let mk_bvsize n =
  let c, args = Structures.decompose_app n in
  if Structures.eq_constr c (Lazy.force cof_nat) then
    match args with
    | [nl] ->
      let c, args = Structures.decompose_app nl in
      if Structures.eq_constr c (Lazy.force clength) then
        match args with
        | [_; l] -> List.length (mk_bool_list l)
        | _ -> assert false
      else assert false
    | _ -> assert false
  else mk_N n

(** Switches between constr and OCaml *)
(* Transform a option constr into a constr option *)
let option_of_constr_option co =
  let c, args = Structures.decompose_app co in
  if c = Lazy.force cSome then
    match args with
      | [_;c] -> Some c
      | _ -> assert false
  else
    None

(* Transform a tuple of constr into a (reversed) list of constr *)
let list_of_constr_tuple =
  let rec list_of_constr_tuple acc t =
    let c, args = Structures.decompose_app t in
    if c = Lazy.force cpair then
      match args with
        | [_;_;t;l] -> list_of_constr_tuple (l::acc) t
        | _ -> assert false
    else
      t::acc
  in
  list_of_constr_tuple []

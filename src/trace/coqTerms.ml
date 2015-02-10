(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Coqlib

let gen_constant modules constant = lazy (gen_constant_in_modules "SMT" modules constant)

(* Int63 *)
let cint = Structures.cint
let ceq63 = gen_constant Structures.int63_modules "eqb"

(* PArray *)
let carray = gen_constant Structures.parray_modules "array"

(* Positive *)
let positive_modules = [["Coq";"Numbers";"BinNums"];
                        ["Coq";"PArith";"BinPosDef";"Pos"]]

let cpositive = gen_constant positive_modules "positive"
let cxI = gen_constant positive_modules "xI"
let cxO = gen_constant positive_modules "xO"
let cxH = gen_constant positive_modules "xH"
let ceqbP = gen_constant positive_modules "eqb"

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
(* Je ne comprends pas pourquoi ça fonctionne avec Zeq_bool et pas avec
   Z.eqb *)
(* let ceqbZ = gen_constant z_modules "eqb" *)
let ceqbZ = gen_constant [["Coq";"ZArith";"Zbool"]] "Zeq_bool"

(* Booleans *)
let bool_modules = [["Coq";"Bool";"Bool"]]

let cbool = gen_constant init_modules "bool"
let ctrue = gen_constant init_modules "true"
let cfalse = gen_constant init_modules "false"
let candb = gen_constant init_modules "andb"
let corb = gen_constant init_modules "orb"
let cxorb = gen_constant init_modules "xorb"
let cnegb = gen_constant init_modules "negb"
let cimplb = gen_constant init_modules "implb"
let ceqb = gen_constant  bool_modules "eqb"
let cifb = gen_constant bool_modules "ifb"
let creflect = gen_constant bool_modules "reflect"

(* Lists *)
let clist = gen_constant init_modules "list"
let cnil = gen_constant init_modules "nil"
let ccons = gen_constant init_modules "cons"


(* Option *)
let coption = gen_constant init_modules "option"
let cSome = gen_constant init_modules "Some"
let cNone = gen_constant init_modules "None"

(* Pairs *)
let cpair = gen_constant init_modules "pair"

(* Logical Operators *)
let cnot = gen_constant init_modules "not"
let ceq = gen_constant init_modules "eq"
let crefl_equal = gen_constant init_modules "eq_refl"

(* SMT_terms *)

let smt_modules = [ ["SMTCoq";"Misc"];
		    ["SMTCoq";"State"];
		    ["SMTCoq";"SMT_terms"];
		    ["SMTCoq";"SMT_terms";"Typ"];
		    ["SMTCoq";"SMT_terms";"Form"];
		    ["SMTCoq";"SMT_terms";"Atom"]
		  ]

let cdistinct = gen_constant smt_modules "distinct"

let ctype = gen_constant smt_modules "type"
let cTZ = gen_constant smt_modules "TZ"
let cTbool = gen_constant smt_modules "Tbool"
let cTpositive = gen_constant smt_modules "Tpositive"
let cTindex = gen_constant smt_modules "Tindex"

let ctyp_eqb = gen_constant smt_modules "typ_eqb"
let cTyp_eqb = gen_constant smt_modules "Typ_eqb"
let cte_carrier = gen_constant smt_modules "te_carrier"
let cte_eqb = gen_constant smt_modules "te_eqb"
let cunit_typ_eqb = gen_constant smt_modules "unit_typ_eqb"

let ctval =  gen_constant smt_modules "tval"
let cTval =  gen_constant smt_modules "Tval"

let cCO_xH = gen_constant smt_modules "CO_xH"
let cCO_Z0 = gen_constant smt_modules "CO_Z0"

let cUO_xO = gen_constant smt_modules "UO_xO"
let cUO_xI = gen_constant smt_modules "UO_xI"
let cUO_Zpos = gen_constant smt_modules "UO_Zpos"
let cUO_Zneg = gen_constant smt_modules "UO_Zneg"
let cUO_Zopp = gen_constant smt_modules "UO_Zopp"

let cBO_Zplus = gen_constant smt_modules "BO_Zplus"
let cBO_Zminus = gen_constant smt_modules "BO_Zminus"
let cBO_Zmult = gen_constant smt_modules "BO_Zmult"
let cBO_Zlt = gen_constant smt_modules "BO_Zlt"
let cBO_Zle = gen_constant smt_modules "BO_Zle"
let cBO_Zge = gen_constant smt_modules "BO_Zge"
let cBO_Zgt = gen_constant smt_modules "BO_Zgt"
let cBO_eq = gen_constant smt_modules "BO_eq"

let cNO_distinct = gen_constant smt_modules "NO_distinct"

let catom = gen_constant smt_modules "atom"
let cAcop = gen_constant smt_modules "Acop"
let cAuop = gen_constant smt_modules "Auop"
let cAbop = gen_constant smt_modules "Abop"
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

let cis_true = gen_constant smt_modules "is_true"

let make_certif_ops modules = 
 (gen_constant modules "step", 
  gen_constant modules "Res", gen_constant modules "ImmFlatten", 
  gen_constant modules "CTrue", gen_constant modules "CFalse", 
  gen_constant modules "BuildDef", gen_constant modules "BuildDef2", 
  gen_constant modules "BuildProj", 
  gen_constant modules "ImmBuildProj", gen_constant modules"ImmBuildDef", 
  gen_constant modules"ImmBuildDef2",
  gen_constant modules "EqTr", gen_constant modules "EqCgr", gen_constant modules "EqCgrP", 
  gen_constant modules "LiaMicromega", gen_constant modules "LiaDiseq", gen_constant modules "SplArith", gen_constant modules "SplDistinctElim")
  

(** Useful construction *)

let ceq_refl_true = 
  lazy (SmtMisc.mklApp crefl_equal [|Lazy.force cbool;Lazy.force ctrue|])

let eq_refl_true () = Lazy.force ceq_refl_true

let vm_cast_true t = 
  Term.mkCast(eq_refl_true (),
	      Term.VMcast, 
	      SmtMisc.mklApp ceq [|Lazy.force cbool; t; Lazy.force ctrue|])

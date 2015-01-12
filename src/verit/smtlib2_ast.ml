(**************************************************************************)
(*                                                                        *)
(*     SMTCoq, originally belong to The Alt-ergo theorem prover           *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Smtlib2_util

type loc = Lexing.position * Lexing.position

type specconstant =
  | SpecConstsDec of loc * string
  | SpecConstNum of loc * string
  | SpecConstString of loc * string
  | SpecConstsHex of loc * string
  | SpecConstsBinary of loc * string

type symbol =
  | Symbol of loc * string
  | SymbolWithOr of loc * string

type sexpr =
  | SexprSpecConst of loc * specconstant
  | SexprSymbol of loc * symbol
  | SexprKeyword of loc * string
  | SexprInParen of loc * (loc * sexpr list)

type attributevalue =
  | AttributeValSpecConst of loc * specconstant
  | AttributeValSymbol of loc * symbol
  | AttributeValSexpr of loc * (loc * sexpr list)

type attribute =
  | AttributeKeyword of loc * string
  | AttributeKeywordValue of loc * string * attributevalue

type an_option = AnOptionAttribute of loc * attribute

type infoflag = InfoFlagKeyword of loc * string

type identifier =
  | IdSymbol of loc * symbol
  | IdUnderscoreSymNum of loc * symbol * (loc * string list)

type sort =
  | SortIdentifier of loc * identifier
  | SortIdSortMulti of loc * identifier * (loc * sort list)

type qualidentifier =
  | QualIdentifierId of loc * identifier
  | QualIdentifierAs of loc * identifier * sort

type sortedvar =
  | SortedVarSymSort of loc * symbol * sort

type varbinding = VarBindingSymTerm of loc * symbol * term

and term =
  | TermSpecConst of loc * specconstant
  | TermQualIdentifier of loc * qualidentifier
  | TermQualIdTerm of loc * qualidentifier * (loc * term list)
  | TermLetTerm of loc * (loc * varbinding list) * term
  | TermForAllTerm of loc * (loc * sortedvar list) * term
  | TermExistsTerm of loc * (loc * sortedvar list) * term
  | TermExclimationPt of loc * term * (loc * attribute list)

type command =
  | CSetLogic of loc * symbol
  | CSetOption of loc * an_option
  | CSetInfo of loc * attribute
  | CDeclareSort of loc * symbol * string
  | CDefineSort of loc * symbol * (loc * symbol list) * sort
  | CDeclareFun of loc * symbol * (loc * sort list) * sort
  | CDefineFun of loc * symbol * (loc * sortedvar list) * sort * term
  | CPush of loc * string
  | CPop of loc * string
  | CAssert of loc * term
  | CCheckSat of loc
  | CGetAssert of loc
  | CGetProof of loc
  | CGetUnsatCore of loc
  | CGetValue of loc * (loc * term list)
  | CGetAssign of loc
  | CGetOption of loc * string
  | CGetInfo of loc * infoflag
  | CExit of loc

type commands = Commands of loc * (loc * command list)


(* loc stands for pos (position) and extradata *)

let loc_an_option = function
  | AnOptionAttribute(d,_) -> d

let loc_attribute = function
  | AttributeKeyword(d,_) -> d
  | AttributeKeywordValue(d,_,_) -> d

let loc_attributevalue = function
  | AttributeValSpecConst(d,_) -> d
  | AttributeValSymbol(d,_) -> d
  | AttributeValSexpr(d,_) -> d

let loc_command = function
  | CSetLogic(d,_) -> d
  | CSetOption(d,_) -> d
  | CSetInfo(d,_) -> d
  | CDeclareSort(d,_,_) -> d
  | CDefineSort(d,_,_,_) -> d
  | CDeclareFun(d,_,_,_) -> d
  | CDefineFun(d,_,_,_,_) -> d
  | CPush(d,_) -> d
  | CPop(d,_) -> d
  | CAssert(d,_) -> d
  | CCheckSat(d) -> d
  | CGetAssert(d) -> d
  | CGetProof(d) -> d
  | CGetUnsatCore(d) -> d
  | CGetValue(d,_) -> d
  | CGetAssign(d) -> d
  | CGetOption(d,_) -> d
  | CGetInfo(d,_) -> d
  | CExit(d) -> d

let loc_commands = function
  | Commands(d,_) -> d

let loc_identifier = function
  | IdSymbol(d,_) -> d
  | IdUnderscoreSymNum(d,_,_) -> d

let loc_infoflag = function
  | InfoFlagKeyword(d,_) -> d

let loc_qualidentifier = function
  | QualIdentifierId(d,_) -> d
  | QualIdentifierAs(d,_,_) -> d

let loc_sexpr = function
  | SexprSpecConst(d,_) -> d
  | SexprSymbol(d,_) -> d
  | SexprKeyword(d,_) -> d
  | SexprInParen(d,_) -> d

let loc_sort = function
  | SortIdentifier(d,_) -> d
  | SortIdSortMulti(d,_,_) -> d

let loc_sortedvar = function
  | SortedVarSymSort(d,_,_) -> d

let loc_specconstant = function
  | SpecConstsDec(d,_) -> d
  | SpecConstNum(d,_) -> d
  | SpecConstString(d,_) -> d
  | SpecConstsHex(d,_) -> d
  | SpecConstsBinary(d,_) -> d

let loc_symbol = function
  | Symbol(d,_) -> d
  | SymbolWithOr(d,_) -> d

let loc_term = function
  | TermSpecConst(d,_) -> d
  | TermQualIdentifier(d,_) -> d
  | TermQualIdTerm(d,_,_) -> d
  | TermLetTerm(d,_,_) -> d
  | TermForAllTerm(d,_,_) -> d
  | TermExistsTerm(d,_,_) -> d
  | TermExclimationPt(d,_,_) -> d

let loc_varbinding = function
  | VarBindingSymTerm(d,_,_) -> d

let loc_couple = fst

let loc_of e = loc_commands e;;

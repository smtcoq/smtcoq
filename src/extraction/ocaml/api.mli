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


open Smtcoq_plugin


(** SMT-LIB2 sorts and function symbols **)
type sort = string
type funsym = string * sort list * sort


(** SMT-LIB2 terms and formulas **)
type expr =
  (* Variables and applied functions and predicates *)
  | EFun of funsym * expr list

  (* False *)
  | EFalse
  (* Negation *)
  | ENeg of expr

  (* Equality *)
  | EEq of expr * expr
  (* Distinct *)
  | EDistinct of expr list

  (* Integer constants *)
  | EInt of int
  | EBigInt of Big_int.big_int
  (* Addition *)
  | EAdd of expr * expr
  (* Unary substraction *)
  | EOpp of expr
  (* Binary substraction *)
  | EMinus of expr * expr
  (* Multiplication *)
  | EMult of expr * expr
  (* Less than *)
  | ELt of expr * expr
  (* Less or equal *)
  | ELe of expr * expr
  (* Greater than *)
  | EGt of expr * expr
  (* Greater or equal *)
  | EGe of expr * expr


(** SMT-LIB2 commands **)
(*** Sort declarations ***)
type sorts = sort list

(*** Function symbols declarations ***)
type funsyms = funsym list

(*** Assertions ***)
type assertions = expr array

(*** Commands ***)
type smtlib2 = sorts * funsyms * assertions


(** Certificate **)
type node =
  | CAssert of int
  | CFalse
  | CResolution of certif list
and certif = string * node


(** The API checker **)
val checker : smtlib2 -> certif -> bool


(** Pretty-printers **)
val pp_sort : Format.formatter -> sort -> unit
val pp_funsym : Format.formatter -> funsym -> unit
val pp_expr : Format.formatter -> expr -> unit

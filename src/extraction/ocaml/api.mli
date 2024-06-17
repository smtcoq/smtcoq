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

  (* True *)
  | ETrue
  (* False *)
  | EFalse
  (* Negation *)
  | ENeg of expr
  (* N-ary and *)
  | EAnd of expr list
  (* Binary and *)
  | EBAnd of expr * expr
  (* N-ary or *)
  | EOr of expr list
  (* Binary or *)
  | EBor of expr * expr
  (* Xor *)
  | EXor of expr * expr
  (* -> *)
  | EImp of expr * expr

  (* Equality *)
  | EEq of expr * expr
  (* Distinct (applies to terms only) *)
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


(** Certificate
    It implements parts of the Alethe format as presented in
      https://verit.loria.fr/documentation/alethe-spec.pdf
    See in particular the description of the rules starting p.26

    Numbers in comments indicate the number of the rule in the document,
    and we keep the names.

    Note that the rule not_not is useless as SMTCoq reasons modulo
    double negation.

    It implements an additional rule: weakening.

    Warning: make sure not to produce clauses containing both a formula
    and its negation (even modulo double negation), as it is considered
    trivial by SMTCoq. It may be a cause of failure.
 **)
type node =
  (* 0. Given a proof of the clause {f1 ... fn} and formulas b1 ... bm,
        proves the clause {f1 ... fn b1 ... bm}
   *)
  | Cweakening of certif * expr list

  (* 1. Refer to an assertion by its index *)
  | Cassume of int

  (* 3. Proves the clause {(true)} *)
  | Ctrue

  (* 4. Proves the clause {(not false)} *)
  | Cfalse

  (* 6 & 7. Resolution of two or more clauses *)
  | Cresolution of certif list

  (* 12. Proves the given clause in the theory of Linear Integer Arithmetic *)
  | Clia_generic of expr list

  (* 23. Given a term t, proves the clause {(= t t)} *)
  | Ceq_reflexive of expr

  (* 24. Given the terms t1 ... tn,
         proves the clause {(not (= t1 t2)) ... (not (= t{n-1} tn)) (= t1 tn)}
   *)
  | Ceq_transitive of expr list

  (* 25. Given a function symbol f, the terms t1 ... tn, and the terms u1 ... un,
         proves the clause
           {(not (= t1 u1)) ... (not (= tn un)) (= f(t1, ..., tn) f(u1, ..., un))}
   *)
  | Ceq_congruent of funsym * expr list * expr list

  (* 26. Given a predicate symbol P, the terms t1 ... tn, and the terms u1 ... un,
         proves the clause
           {(not (= t1 u1)) ... (not (= tn un)) (= P(t1, ..., tn) P(u1, ..., un))}
   *)
  | Ceq_congruent_pred of funsym * expr list * expr list

  (* 28. Given a proof of the clause {(and f1 ... fn)} and a non-negative integer k,
         proves the clause {fk}
   *)
  | Cand of certif * int

  (* 29. Given a proof of the clause {(not (or f1 ... fn))} and a non-negative integer k,
         proves the clause {(not fk)}
   *)
  | Cnot_or of certif * int

  (* 30. Given a proof of the clause {(or f1 ... fn)},
         proves the clause {f1 ... fn}
   *)
  | Cor of certif

  (* 31. Given a proof of the clause {(not (and f1 ... fn))},
         proves the clause {(not f1) ... (not fn)}
   *)
  | Cnot_and of certif

  (* 32. Given a proof of the clause {(xor a b)},
         proves the clause {a b}
   *)
  | Cxor1 of certif

  (* 33. Given a proof of the clause {(xor a b)},
         proves the clause {(not a) (not b)}
   *)
  | Cxor2 of certif

  (* 34. Given a proof of the clause {(not (xor a b))},
         proves the clause {a (not b)}
   *)
  | Cnot_xor1 of certif

  (* 35. Given a proof of the clause {(not (xor a b))},
         proves the clause {(not a) b}
   *)
  | Cnot_xor2 of certif

  (* 36. Given a proof of the clause {(-> a b)},
         proves the clause {(not a) b}
   *)
  | Cimplies of certif

  (* 37. Given a proof of the clause {(not (-> a b))},
         proves the clause {a}
   *)
  | Cnot_implies1 of certif

  (* 38. Given a proof of the clause {(not (-> a b))},
         proves the clause {(not b)}
   *)
  | Cnot_implies2 of certif

  (* 39. Given a proof of the clause {(= a b)},
         proves the clause {(not a) b}
   *)
  | Cequiv1 of certif

  (* 40. Given a proof of the clause {(= a b)},
         proves the clause {a (not b)}
   *)
  | Cequiv2 of certif

  (* 41. Given a proof of the clause {(not (= a b))},
         proves the clause {a b}
   *)
  | Cnot_equiv1 of certif

  (* 42. Given a proof of the clause {(not (= a b))},
         proves the clause {(not a) (not b)}
   *)
  | Cnot_equiv2 of certif

  (* 43. Given the formulas f1 ... fn and a non-negative integer k,
         proves the clause {(not (and f1 ... fn)) fk}
   *)
  | Cand_pos of expr list * int

  (* 44. Given the formulas f1 ... fn,
         proves the clause {(and f1 ... fn) (not f1) ... (not fn)}
   *)
  | Cand_neg of expr list

  (* 45. Given the formulas f1 ... fn,
         proves the clause {(not (or f1 ... fn)) f1 ... fn}
   *)
  | Cor_pos of expr list

  (* 46. Given the formulas f1 ... fn and a non-negative integer k,
         proves the clause {(or f1 ... fn) (not fk)}
   *)
  | Cor_neg of expr list * int

  (* 47. Given the formulas a and b,
         proves the clause {(not (xor a b)) a b}
   *)
  | Cxor_pos1 of expr * expr

  (* 48. Given the formulas a and b,
         proves the clause {(not (xor a b)) (not a) (not b)}
   *)
  | Cxor_pos2 of expr * expr

  (* 49. Given the formulas a and b,
         proves the clause {(xor a b) a (not b)}
   *)
  | Cxor_neg1 of expr * expr

  (* 50. Given the formulas a and b,
         proves the clause {(xor a b) (not a) b}
   *)
  | Cxor_neg2 of expr * expr

  (* 51. Given the formulas a and b,
         proves the clause {(not (implies a b)) (not a) b}
   *)
  | Cimplies_pos of expr * expr

  (* 52. Given the formulas a and b,
         proves the clause {(implies a b) a}
   *)
  | Cimplies_neg1 of expr * expr

  (* 53. Given the formulas a and b,
         proves the clause {(implies a b) (not b)}
   *)
  | Cimplies_neg2 of expr * expr

  (* 54. Given the formulas a and b,
         proves the clause {(not (= a b)) a (not b)}
   *)
  | Cequiv_pos1 of expr * expr

  (* 55. Given the formulas a and b,
         proves the clause {(not (= a b)) (not a) b}
   *)
  | Cequiv_pos2 of expr * expr

  (* 56. Given the formulas a and b,
         proves the clause {(= a b) (not a) (not b)}
   *)
  | Cequiv_neg1 of expr * expr

  (* 57. Given the formulas a and b,
         proves the clause {(= a b) a b}
   *)
  | Cequiv_neg2 of expr * expr

and certif = string * node


(** The API checker **)
val checker : smtlib2 -> certif -> bool


(** Pretty-printers **)
val pp_sort : Format.formatter -> sort -> unit
val pp_funsym : Format.formatter -> funsym -> unit
val pp_expr : Format.formatter -> expr -> unit

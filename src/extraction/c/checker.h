/**************************************************************************/
/*                                                                        */
/*     SMTCoq                                                             */
/*     Copyright (C) 2011 - 2024                                          */
/*                                                                        */
/*     See file "AUTHORS" for the list of authors                         */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/


#ifndef _CHECKER_H_
#define _CHECKER_H_

#include <caml/mlvalues.h>

#include "types.h"


/** Sorts of first-order logic **/

SORT sort(char* s);


/** Function symbols of first-order logic **/

FUNSYM funsym(char* name, size_t arity, const SORT* domain, SORT codomain);


/** Terms and formulas of first-order logic **/

/* Variables and applied functions and predicates */
EXPR efun(FUNSYM fun, const EXPR* args);

/* true */
EXPR etrue();

/* false */
EXPR efalse();

/* not */
EXPR eneg(EXPR a);

/* N-ary and */
EXPR eand(size_t nb, const EXPR* a);

/* Binary and */
EXPR eband(EXPR a, EXPR b);

/* N-ary or */
EXPR eor(size_t nb, const EXPR* a);

/* Binary or */
EXPR ebor(EXPR a, EXPR b);

/* xor */
EXPR exor(EXPR a, EXPR b);

/* -> */
EXPR eimp(EXPR a, EXPR b);

/* = */
EXPR eeq(EXPR a, EXPR b);

/* distinct */
EXPR edistinct(size_t nb, const EXPR* d);

/* Integer constants */
EXPR eint(int i);

/* + */
EXPR eadd(EXPR a, EXPR b);

/* Unary - */
EXPR eopp(EXPR a);

/* Binary - */
EXPR eminus(EXPR a, EXPR b);

/* * */
EXPR emult(EXPR a, EXPR b);

/* < */
EXPR elt(EXPR a, EXPR b);

/* <= */
EXPR ele(EXPR a, EXPR b);

/* > */
EXPR egt(EXPR a, EXPR b);

/* >= */
EXPR ege(EXPR a, EXPR b);


/** Certificates
    It implements parts of the Alethe format as presented in
      https://verit.loria.fr/documentation/alethe-spec.pdf
    See in particular the description of the rules starting p.26

    Numbers in comments indicate the number of the rule in the document,
    and we keep the names.

    The first parameter of each rule is a name given to the step, to be
    used with the debugging checker

    Note that the rule not_not is useless as SMTCoq reasons modulo
    double negation.

    It implements an additional rule: weakening.

    Warning: make sure not to produce clauses containing both a formula
    and its negation (even modulo double negation), as it is considered
    trivial by SMTCoq. It may be a cause of failure.
**/

/* 0. Given a proof of the clause {f1 ... fn} and formulas b1 ... bm,
      proves the clause {f1 ... fn b1 ... bm}
*/
CERTIF cweakening(char* name, CERTIF c, size_t m, const EXPR* bs);

/* 1. Refer to an assertion by its index */
CERTIF cassume(char* name, size_t num);

/* 3. Proves the clause; {(true)} */
CERTIF ctrue(char* name);

/* 4. Proves the clause {(not false)} */
CERTIF cfalse(char* name);

/* 6 & 7. Resolution of two or more clauses */
CERTIF cresolution(char* name, size_t nb, const CERTIF* premisses);

/* 12. Proves the given clause in the theory of Linear Integer Arithmetic */
CERTIF clia_generic(char* name, size_t nb, const EXPR* l);

/* 23. Given a term t, proves the clause {(= t t)}
       Applies only to terms.
*/
CERTIF ceq_reflexive(char* name, EXPR t);

/* 24. Given the terms t1 ... tn,
       proves the clause {(not (= t1 t2)) ... (not (= t{n-1} tn)) (= t1 tn)}
       Applies only to terms.
*/
CERTIF ceq_transitive(char* name, size_t n, const EXPR* ts);

/* 25. Given a function symbol f, the terms t1 ... tn, and the terms u1 ... un,
       proves the clause
         {(not (= t1 u1)) ... (not (= tn un)) (= f(t1, ..., tn) f(u1, ..., un))}
       n is given by the arity of f
*/
CERTIF ceq_congruent(char* name, FUNSYM f, const EXPR* ts, const EXPR* us);

/* 26. Given a predicate symbol P, the terms t1 ... tn, and the terms u1 ... un,
       proves the clause
         {(not (= t1 u1)) ... (not (= tn un)) (= P(t1, ..., tn) P(u1, ..., un))}
       n is given by the arity of P
*/
CERTIF ceq_congruent_pred(char* name, FUNSYM p, const EXPR* ts, const EXPR* us);

/* 26b. A small variant
        Given a predicate symbol P, the terms t1 ... tn, and the terms u1 ... un,
        proves the clause
          {(not (= t1 u1)) ... (not (= tn un)) (not P(t1, ..., tn)) P(u1, ..., un)}
       n is given by the arity of P
*/
CERTIF ceq_congruent_pred_b(char* name, FUNSYM p, const EXPR* ts, const EXPR* us);

/* 28. Given a proof of the clause {(and f1 ... fn)} and a non-negative integer k,
       proves the clause {fk}
*/
CERTIF cand(char* name, CERTIF c, int k);

/* 29. Given a proof of the clause {(not (or f1 ... fn))} and a non-negative integer k,
       proves the clause {(not fk)}
*/
CERTIF cnot_or(char* name, CERTIF c, int k);

/* 30. Given a proof of the clause {(or f1 ... fn)},
       proves the clause {f1 ... fn}
*/
CERTIF cor(char* name, CERTIF c);

/* 31. Given a proof of the clause {(not (and f1 ... fn))},
       proves the clause {(not f1) ... (not fn)}
*/
CERTIF cnot_and(char* name, CERTIF c);

/* 32. Given a proof of the clause {(xor a b)},
       proves the clause {a b}
*/
CERTIF cxor1(char* name, CERTIF c);

/* 33. Given a proof of the clause {(xor a b)},
       proves the clause {(not a) (not b)}
*/
CERTIF cxor2(char* name, CERTIF c);

/* 34. Given a proof of the clause {(not (xor a b))},
       proves the clause {a (not b)}
*/
CERTIF cnot_xor1(char* name, CERTIF c);

/* 35. Given a proof of the clause {(not (xor a b))},
       proves the clause {(not a) b}
*/
CERTIF cnot_xor2(char* name, CERTIF c);

/* 36. Given a proof of the clause {(-> a b)},
       proves the clause {(not a) b}
*/
CERTIF cimplies(char* name, CERTIF c);

/* 37. Given a proof of the clause {(not (-> a b))},
       proves the clause {a}
*/
CERTIF cnot_implies1(char* name, CERTIF c);

/* 38. Given a proof of the clause {(not (-> a b))},
       proves the clause {(not b)}
*/
CERTIF cnot_implies2(char* name, CERTIF c);

/* 39. Given a proof of the clause {(= a b)},
       proves the clause {(not a) b}
*/
CERTIF cequiv1(char* name, CERTIF c);

/* 40. Given a proof of the clause {(= a b)},
       proves the clause {a (not b)}
*/
CERTIF cequiv2(char* name, CERTIF c);

/* 41. Given a proof of the clause {(not (= a b))},
       proves the clause {a b}
*/
CERTIF cnot_equiv1(char* name, CERTIF c);

/* 42. Given a proof of the clause {(not (= a b))},
       proves the clause {(not a) (not b)}
*/
CERTIF cnot_equiv2(char* name, CERTIF c);

/* 43. Given the formulas f1 ... fn and a non-negative integer k,
       proves the clause {(not (and f1 ... fn)) fk}
*/
CERTIF cand_pos(char* name, size_t n, const EXPR* fs, int k);

/* 44. Given the formulas f1 ... fn,
       proves the clause {(and f1 ... fn) (not f1) ... (not fn)}
*/
CERTIF cand_neg(char* name, size_t n, const EXPR* fs);

/* 45. Given the formulas f1 ... fn,
       proves the clause {(not (or f1 ... fn)) f1 ... fn}
*/
CERTIF cor_pos(char* name, size_t n, const EXPR* fs);

/* 46. Given the formulas f1 ... fn and a non-negative integer k,
       proves the clause {(or f1 ... fn) (not fk)}
*/
CERTIF cor_neg(char* name, size_t n, const EXPR* fs, int k);

/* 47. Given the formulas a and b,
       proves the clause {(not (xor a b)) a b}
*/
CERTIF cxor_pos1(char* name, EXPR a, EXPR b);

/* 48. Given the formulas a and b,
       proves the clause {(not (xor a b)) (not a) (not b)}
*/
CERTIF cxor_pos2(char* name, EXPR a, EXPR b);

/* 49. Given the formulas a and b,
       proves the clause {(xor a b) a (not b)}
*/
CERTIF cxor_neg1(char* name, EXPR a, EXPR b);

/* 50. Given the formulas a and b,
       proves the clause {(xor a b) (not a) b}
*/
CERTIF cxor_neg2(char* name, EXPR a, EXPR b);

/* 51. Given the formulas a and b,
       proves the clause {(not (implies a b)) (not a) b}
*/
CERTIF cimplies_pos(char* name, EXPR a, EXPR b);

/* 52. Given the formulas a and b,
       proves the clause {(implies a b) a}
*/
CERTIF cimplies_neg1(char* name, EXPR a, EXPR b);

/* 53. Given the formulas a and b,
       proves the clause {(implies a b) (not b)}
*/
CERTIF cimplies_neg2(char* name, EXPR a, EXPR b);

/* 54. Given the formulas a and b,
       proves the clause {(not (= a b)) a (not b)}
*/
CERTIF cequiv_pos1(char* name, EXPR a, EXPR b);

/* 55. Given the formulas a and b,
       proves the clause {(not (= a b)) (not a) b}
*/
CERTIF cequiv_pos2(char* name, EXPR a, EXPR b);

/* 56. Given the formulas a and b,
       proves the clause {(= a b) (not a) (not b)}
*/
CERTIF cequiv_neg1(char* name, EXPR a, EXPR b);

/* 57. Given the formulas a and b,
       proves the clause {(= a b) a b}
*/
CERTIF cequiv_neg2(char* name, EXPR a, EXPR b);


/** SMT-LIB2 commands and proof checker, imperative **/

void start_smt2();
void declare_sort(SORT s);
void declare_fun(FUNSYM f);
void assertf(EXPR f);

int check_proof(CERTIF proof);
void debug_check_proof(CERTIF proof);


/** SMT-LIB2 commands and proof checker, functional **/

SORTS sorts(size_t nb, SORT* data);
FUNSYMS funsyms(size_t nb, FUNSYM* data);
ASSERTIONS assertions(size_t nb, EXPR* data);
SMTLIB2 smtlib2(SORTS s, FUNSYMS f, ASSERTIONS a);

int checker(SMTLIB2 smt, CERTIF proof);
void debug_checker(SMTLIB2 smt, CERTIF proof);


#endif

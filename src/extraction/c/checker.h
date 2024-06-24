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


/**
 * @file checker.h
 * @author Chantal Keller
 * @date 24 Jun 2024
 * @brief C API for SMTCoq
 *
 * This documentation details all the functions to use the C API for
 * SMTCoq
 * @see https://smtcoq.github.io/capi
 */


#ifndef _CHECKER_H_
#define _CHECKER_H_

#include <caml/mlvalues.h>

#include "types.h"


/** @defgroup sort Defining sorts of first-order logic
 *  Defining sorts of first-order logic.
 *  @{
 */

/**
 * @brief Defining a sort of first-order logic.
 *
 * This function defines a sort in first-order logic, either interpreted
 * if @p s is @c "Bool" or @c "Int", or uninterpreted otherwise.
 * @param s The name of the sort.
 * @return The corresponding sort.
 */
SORT sort(char* s);

/** @} */ // end of sort


/** @defgroup funsym Defining function and predicate symbols of first-order logic
 *  Defining function and predicate symbols of first-order logic.
 *  @{
 */

/**
 * @brief Defining a function or predicate symbol of first-order logic.
 *
 * This function defines an uninterpreted function or predicate symbol.
 * @param name The name of the symbol.
 * @param arity The arity of the symbol.
 * @param domain The (possibly empty) pointer to the list of the sorts
 * corresponding to the domain of the symbol.
 * @param codomain The sort corresponding to the codomain of the symbol.
 * @return The corresponding function or predicate symbol.
 */
FUNSYM funsym(char* name, size_t arity, const SORT* domain, SORT codomain);

/** @} */ // end of funsym


/** @defgroup expr Defining terms and formulas of first-order logic
 *  Defining terms and formulas of first-order logic.
 *  @{
 */

/**
 * @brief Variables and applied functions and predicates.
 *
 * This function applies an uninterpreted function or predicate symbol
 * to 0 or more arguments.
 * @param fun The function or predicate symbol
 * @param args The (possibly empty) pointer to the list of arguments. It
 * should be of the same length as the arity of the function or
 * predicate symbol.
 * @return The corresponding expression.
 */
EXPR efun(FUNSYM fun, const EXPR* args);

/**
 * @brief The @c true expression.
 *
 * This function create the @c true Boolean expression.
 * @return The corresponding expression.
 */
EXPR etrue();

/**
 * @brief The @c false expression.
 *
 * This function create the @c false Boolean expression.
 * @return The corresponding expression.
 */
EXPR efalse();

/**
 * @brief Negation.
 *
 * This function negates the Boolean expression @p a.
 * @param a The expression to negate
 * @return The corresponding expression.
 */
EXPR enot(EXPR a);

/**
 * @brief N-ary conjunction
 *
 * This function creates the conjunction of the @p nb Boolean
 * expressions in @p a.
 * @param nb The number of expressions.
 * @param a A pointer to the list of expressions.
 * @return The corresponding expression.
 */
EXPR eand(size_t nb, const EXPR* a);

/**
 * @brief N-ary disjunction
 *
 * This function creates the disjunction of the @p nb Boolean
 * expressions in @p a.
 * @param nb The number of expressions.
 * @param a A pointer to the list of expressions.
 * @return The corresponding expression.
 */
EXPR eor(size_t nb, const EXPR* a);

/**
 * @brief Xor
 *
 * This function creates the exclusive or of the two Boolean expressions
 * @p a and @p b.
 * @param a The left-hand side of the exclusive or.
 * @param b The right-hand side of the exclusive or.
 * @return The corresponding expression.
 */
EXPR exor(EXPR a, EXPR b);

/**
 * @brief Implication
 *
 * This function creates the implication of the two Boolean expressions
 * @p a and @p b.
 * @param a The left-hand side of the implication.
 * @param b The right-hand side of the implication.
 * @return The corresponding expression.
 */
EXPR eimp(EXPR a, EXPR b);

/**
 * @brief Equality
 *
 * This function creates the implication of the two expressions (of any
 * type) @p a and @p b.
 * @param a The left-hand side of the equality.
 * @param b The right-hand side of the equality.
 * @return The corresponding expression.
 */
EXPR eeq(EXPR a, EXPR b);

/**
 * @brief Distinct
 *
 * This function expresses the fact that all the elements in @p d are
 * pairwise distinct.
 * @param nb The number of expressions.
 * @param d A pointer to the list of expressions.
 * @return The corresponding expression.
 */
EXPR edistinct(size_t nb, const EXPR* d);

/**
 * @brief Integer constants
 *
 * This function injects an integer constant into expressions.
 * @param i The constant.
 * @return The corresponding expression.
 */
EXPR eint(int i);

/**
 * @brief Addition
 *
 * This function creates the addition of the two integer expressions @p
 * a and @p b.
 * @param a The left-hand side of the addition.
 * @param b The right-hand side of the addition.
 * @return The corresponding expression.
 */
EXPR eadd(EXPR a, EXPR b);

/**
 * @brief Unary minus
 *
 * This function creates the opposite of the integer expression @p a.
 * @param a The expression that we take the opposite of.
 * @return The corresponding expression.
 */
EXPR eopp(EXPR a);

/**
 * @brief Binary subtraction
 *
 * This function creates the subtraction of the two integer expressions
 * @p a and @p b.
 * @param a The left-hand side of the subtraction.
 * @param b The right-hand side of the subtraction.
 * @return The corresponding expression.
 */
EXPR eminus(EXPR a, EXPR b);

/**
 * @brief Binary multiplication
 *
 * This function creates the multiplication of the two integer
 * expressions @p a and @p b.
 * @param a The left-hand side of the multiplication.
 * @param b The right-hand side of the multiplication.
 * @return The corresponding expression.
 */
EXPR emult(EXPR a, EXPR b);

/**
 * @brief Less than
 *
 * This function creates the comparison that the integer expressions @p
 * a is stricly smaller than the integer expression @p b.
 * @param a The left-hand side of less than.
 * @param b The right-hand side of less than.
 * @return The corresponding expression.
 */
EXPR elt(EXPR a, EXPR b);

/**
 * @brief Less or equal
 *
 * This function creates the comparison that the integer expressions @p
 * a is smaller or equal than the integer expression @p b.
 * @param a The left-hand side of less or equal.
 * @param b The right-hand side of less or equal.
 * @return The corresponding expression.
 */
EXPR ele(EXPR a, EXPR b);

/**
 * @brief Greater than
 *
 * This function creates the comparison that the integer expressions @p
 * a is stricly greater than the integer expression @p b.
 * @param a The left-hand side of greater than.
 * @param b The right-hand side of greater than.
 * @return The corresponding expression.
 */
EXPR egt(EXPR a, EXPR b);

/**
 * @brief Greater or equal
 *
 * This function creates the comparison that the integer expressions @p
 * a is greater or equal than the integer expression @p b.
 * @param a The left-hand side of greater or equal.
 * @param b The right-hand side of greater or equal.
 * @return The corresponding expression.
 */
EXPR ege(EXPR a, EXPR b);

/** @} */ // end of expr


/** @defgroup certif Defining proof certificates of unsatisfiability
 *
 *  Our certificate format implements parts of the Alethe format.
 *  @see https://verit.loria.fr/documentation/alethe-spec.pdf
 *  @see See in particular the description of the rules starting p.26.
 *
 *  Some missing aspects are:
 *  - the context is not supported
 *  - some rules are not supported
 *
 *  Some additional aspects are:
 *  - the rule @c not_not is useless as SMTCoq reasons module double
 *    negation
 *  - it implements an additional rule: weakening.
 *
 *  Each rule has the same name as in the document (with an additional
 *  @c c at the beginning), and the documentation refers to the number
 *  of the rule in the document.
 *
 *  The first parameter of each rule is a name given to the step, to be
 *  used with the debugging checker. All names must be unique.
 *
 *  @warning Make sure not to produce clauses containing both a formula
 *  and its negation (even modulo double negation), as it is considered
 *  trivial by SMTCoq. It may be a cause of failure.
 *  @{
**/

/**
 * @brief @c weakening rule (additional)
 *
 * Given a proof of the clause <tt>{f1 ... fn}</tt>
 * and a possibly larger clause <tt>{f1 ... fn b[n+1] ... bm}</tt>,
 * proves the clause <tt>{f1 ... fn b[n+1] ... bm}</tt>
 *
 * The order does not matter.
 * The initial clause may contain the additional literals <tt>not false</tt>
 * and @c true as well.
 * @param name The unique name given to the proof step.
 * @param c The proof of @c {f1 ... fn}.
 * @param m The number of literals in the final clause
 * <tt>{f1 ... fn b[n+1] ... bm}</tt>.
 * @param bs A pointer to the list of literals in the final clause.
 * @return The corresponding certificate.
 */
CERTIF cweakening(char* name, CERTIF c, size_t m, const EXPR* bs);

/**
 * @brief @c assume rule (number 1 in Alethe)
 *
 * Refer to an assertion by its index, in the order they were given.
 *
 * The first assertion has index 0.
 * @param name The unique name given to the proof step.
 * @param num The index of the assertion.
 * @return The corresponding certificate.
 */
CERTIF cassume(char* name, size_t num);

/**
 * @brief @c true rule (number 3 in Alethe)
 *
 * Proves the clause <tt>{true}.</tt>
 *
 * @param name The unique name given to the proof step.
 * @return The corresponding certificate.
 */
CERTIF ctrue(char* name);

/**
 * @brief @c false rule (number 4 in Alethe)
 *
 * Proves the clause <tt>{(not false)}.</tt>
 *
 * @param name The unique name given to the proof step.
 * @return The corresponding certificate.
 */
CERTIF cfalse(char* name);

/**
 * @brief @c th_resolution and @c resolution rules (number 6 and 7 in Alethe)
 *
 * Resolution of two or more clauses.
 *
 * @param name The unique name given to the proof step.
 * @param nb The number of clauses to be resolved.
 * @param premisses The proof of the clauses to be resolved.
 * @return The corresponding certificate.
 */
CERTIF cresolution(char* name, size_t nb, const CERTIF* premisses);

/**
 * @brief @c lia_generic rule (number 12 in Alethe)
 *
 * Proves the given clause in the theory of linear integer arithmetic.
 *
 * @param name The unique name given to the proof step.
 * @param nb The number of literals in the clause.
 * @param l A pointer to the literals of the clause.
 * @return The corresponding certificate.
 */
CERTIF clia_generic(char* name, size_t nb, const EXPR* l);

/**
 * @brief @c eq_reflexive rule (number 23 in Alethe)
 *
 * Given a term @c t, proves the clause <tt>{(= t t)}</tt>.
 *
 * @warning Applies only to a non-Boolean term.
 *
 * @param name The unique name given to the proof step.
 * @param t The term.
 * @return The corresponding certificate.
 */
CERTIF ceq_reflexive(char* name, EXPR t);

/**
 * @brief @c eq_transitive rule (number 24 in Alethe)
 *
 * Given the terms <tt>t1 ... tn</tt>,
 * proves the clause <tt>{(not (= t1 t2)) ... (not (= t{n-1} tn)) (= t1 tn)}</tt>
 *
 * @warning The @c tis must be non-Boolean terms.
 *
 * @param name The unique name given to the proof step.
 * @param n The number of terms.
 * @param ts A pointer to the list of terms.
 * @return The corresponding certificate.
 */
CERTIF ceq_transitive(char* name, size_t n, const EXPR* ts);

/**
 * @brief @c eq_congruent rule (number 25 in Alethe)
 *
 * Proves the clause
 * <tt>{(not (= t1 u1)) ... (not (= tn un)) (= f(t1, ..., tn) f(u1, ..., un))}</tt>
 *
 * @warning The @c tis and @c uis must be non-Boolean terms, and the
 * codomain of @c f must not be @c Bool.
 *
 * @param name The unique name given to the proof step.
 * @param n The number of literals in the final clause.
 * @param clause A pointer to the list of literals in the final clause.
 * @return The corresponding certificate.
 */
CERTIF ceq_congruent(char* name, size_t n, const EXPR* clause);

/**
 * @brief @c eq_congruent_pred rule (number 26 in Alethe)
 *
 * Proves the clause
 * <tt>{(not (= t1 u1)) ... (not (= tn un)) (= P(t1, ..., tn) P(u1, ..., un))}</tt>
 *
 * @warning The @c tis and @c uis must be non-Boolean terms, and the
 * codomain of @c P must be @c Bool.
 *
 * @param name The unique name given to the proof step.
 * @param n The number of literals in the final clause.
 * @param clause A pointer to the list of literals in the final clause.
 * @return The corresponding certificate.
 */
CERTIF ceq_congruent_pred(char* name, size_t n, const EXPR* clause);

/**
 * @brief @c eq_congruent_pred_b rule (a small variant of the previous one)
 *
 * Proves the clause
 * <tt>{(not (= t1 u1)) ... (not (= tn un)) (not P(t1, ..., tn)) P(u1, ..., un)}</tt>
 *
 * @warning The @c tis and @c uis must be non-Boolean terms, and the
 * codomain of @c P must be @c Bool.
 *
 * @param name The unique name given to the proof step.
 * @param n The number of literals in the final clause.
 * @param clause A pointer to the list of literals in the final clause.
 * @return The corresponding certificate.
 */
CERTIF ceq_congruent_pred_b(char* name, size_t n, const EXPR* clause);

/**
 * @brief @c and rule (number 28 in Alethe)
 *
 * Given a proof of the clause <tt>{(and f1 ... fn)}</tt> and a
 * non-negative integer @c k, proves the clause <tt>{fk}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(and f1 ... fn)}</tt>.
 * @param k An integer between @c 1 and @c n.
 * @return The corresponding certificate.
 */
CERTIF cand(char* name, CERTIF c, int k);

/**
 * @brief @c not_or rule (number 29 in Alethe)
 *
 * Given a proof of the clause <tt>{(not (or f1 ... fn))}</tt> and a
 * non-negative integer @c k, proves the clause <tt>{(not fk)}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(not (or f1 ... fn))}</tt>.
 * @param k An integer between @c 1 and @c n.
 * @return The corresponding certificate.
 */
CERTIF cnot_or(char* name, CERTIF c, int k);

/**
 * @brief @c or rule (number 30 in Alethe)
 *
 * Given a proof of the clause <tt>{(or f1 ... fn)}</tt>,
 * proves the clause <tt>{f1 ... fn}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(or f1 ... fn)}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cor(char* name, CERTIF c);

/**
 * @brief @c not_and rule (number 31 in Alethe)
 *
 * Given a proof of the clause <tt>{(not (and f1 ... fn))}</tt>,
 * proves the clause <tt>{(not f1) ... (not fn)}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(not (and f1 ... fn))}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cnot_and(char* name, CERTIF c);

/**
 * @brief @c xor1 rule (number 32 in Alethe)
 *
 * Given a proof of the clause <tt>{(xor a b)}</tt>,
 * proves the clause <tt>{a b}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(xor a b)}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cxor1(char* name, CERTIF c);

/**
 * @brief @c xor2 rule (number 33 in Alethe)
 *
 * Given a proof of the clause <tt>{(xor a b)}</tt>,
 * proves the clause <tt>{(not a) (not b)}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(xor a b)}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cxor2(char* name, CERTIF c);

/**
 * @brief @c not_xor1 rule (number 34 in Alethe)
 *
 * Given a proof of the clause <tt>{(not (xor a b))}</tt>,
 * proves the clause <tt>{a (not b)}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(not (xor a b))}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cnot_xor1(char* name, CERTIF c);

/**
 * @brief @c not_xor2 rule (number 35 in Alethe)
 *
 * Given a proof of the clause <tt>{(not (xor a b))}</tt>,
 * proves the clause <tt>{(not a) b}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(not (xor a b))}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cnot_xor2(char* name, CERTIF c);

/**
 * @brief @c implies rule (number 36 in Alethe)
 *
 * Given a proof of the clause <tt>{(=> a b)}</tt>,
 * proves the clause <tt>{(not a) b}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(=> a b)}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cimplies(char* name, CERTIF c);

/**
 * @brief @c not_implies1 rule (number 37 in Alethe)
 *
 * Given a proof of the clause <tt>{(not (=> a b))}</tt>,
 * proves the clause <tt>{a}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(not (=> a b))}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cnot_implies1(char* name, CERTIF c);

/**
 * @brief @c not_implies2 rule (number 38 in Alethe)
 *
 * Given a proof of the clause <tt>{(not (=> a b))}</tt>,
 * proves the clause <tt>{(not b)}</tt>.
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(not (=> a b))}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cnot_implies2(char* name, CERTIF c);

/**
 * @brief @c equiv1 rule (number 39 in Alethe)
 *
 * Given a proof of the clause <tt>{(= a b)}</tt>,
 * proves the clause <tt>{(not a) b}</tt>.
 *
 * @warning @c a and @c b must be Boolean expressions
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(= a b)}</tt>.
 * @return The corresponding certificate.
 */
CERTIF cequiv1(char* name, CERTIF c);


/**
 * @brief @c equiv2 rule (number 39 in Alethe)
 *
 * Given a proof of the clause <tt>{(= a b)}</tt>,
 * proves the clause <tt>{a (not b)}</tt>.
 *
 * @warning @c a and @c b must be Boolean expressions
 *
 * @param name The unique name given to the proof step.
 * @param c The proof of <tt>{(= a b)}</tt>.
 * @return The corresponding certificate.
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

/** @} */ // end of certif


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

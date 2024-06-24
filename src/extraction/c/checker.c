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


#include <string.h>
#include <stdio.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/callback.h>

#include "types.h"
#include "checker.h"


/** Utils **/

/* String as a value */
value value_string(char* s) {
  return caml_alloc_initialized_string(strlen(s), s);
}


/* Lists and arrays of values */

value value_list(size_t nb, const value* elem) {
  if (nb == 0) {
    return Val_int(0);
  } else {
    value next = value_list(nb-1, elem+1);
    value res = caml_alloc(2, 0);
    Store_field(res, 0, *elem);
    Store_field(res, 1, next);
    return res;
  }
}

value value_array(size_t nb, const value* elem) {
  value res = caml_alloc(nb, 0);
  for (int i = 0; i < nb; i++) {
    Store_field(res, i, *(elem+i));
  }
  return res;
}


/** Sorts of first-order logic **/

SORT sort(char* s) {
  return value_string(s);
}

/* Booleans */
SORT bool() {
  return sort("Bool");
}

/* Integers */
SORT integer() {
  return sort("Int");
}


/** Function symbols of first-order logic **/

FUNSYM funsym(char* name, size_t arity, const SORT* domain, SORT codomain) {
  CAMLparam1(codomain);
  CAMLlocal2(res, d);
  res = caml_alloc(3, 0);
  Store_field(res, 0, value_string(name));
  d = value_list(arity, domain);
  Store_field(res, 1, d);
  Store_field(res, 2, codomain);
  FUNSYM f = {res, arity};
  CAMLreturnT(FUNSYM, f);
}


/** Terms and formulas of first-order logic **/

#define ETRUE      0
#define EFALSE     1

#define EFUN       0
#define ENOT       1
#define EAND       2
#define EOR        3
#define EXOR       4
#define EIMP       5
#define EEQ        6
#define EDISTINCT  7
#define EINT       8
#define EADD      10
#define EOPP      11
#define EMINUS    12
#define EMULT     13
#define ELT       14
#define ELE       15
#define EGT       16
#define EGE       17

/* Variables and applied functions and predicates */
EXPR efun(FUNSYM fun, const EXPR* args) {
  value res = caml_alloc(2, EFUN);
  Store_field(res, 0, fun.fval);
  value a = value_list(fun.arity, args);
  Store_field(res, 1, a);
  return res;
}

/* true */
EXPR etrue() {
  value res = Val_int(ETRUE);
  return res;
}

/* false */
EXPR efalse() {
  value res = Val_int(EFALSE);
  return res;
}

/* not */
EXPR enot(EXPR a) {
  CAMLparam1(a);
  CAMLlocal1(res);
  res = caml_alloc(1, ENOT);
  Store_field(res, 0, a);
  CAMLreturn(res);
}

/* N-ary and */
EXPR eand(size_t nb, const EXPR* a) {
  value res = caml_alloc(1, EAND);
  value r = value_list(nb, a);
  Store_field(res, 0, r);
  return res;
}

/* N-ary or */
EXPR eor(size_t nb, const EXPR* a) {
  value res = caml_alloc(1, EOR);
  value r = value_list(nb, a);
  Store_field(res, 0, r);
  return res;
}

/* xor */
EXPR exor(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EXOR);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* => */
EXPR eimp(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EIMP);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* = */
EXPR eeq(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EEQ);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* distinct */
EXPR edistinct(size_t nb, const EXPR* d) {
  value res = caml_alloc(1, EDISTINCT);
  value a = value_list(nb, d);
  Store_field(res, 0, a);
  return res;
}

/* Integer constants */
EXPR eint(int i) {
  value res = caml_alloc(1, EINT);
  Store_field(res, 0, Val_int(i));
  return res;
}

/* + */
EXPR eadd(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EADD);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* Unary - */
EXPR eopp(EXPR a) {
  CAMLparam1(a);
  CAMLlocal1(res);
  res = caml_alloc(1, EOPP);
  Store_field(res, 0, a);
  CAMLreturn(res);
}

/* Binary - */
EXPR eminus(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EMINUS);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* * */
EXPR emult(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EMULT);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* < */
EXPR elt(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, ELT);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* <= */
EXPR ele(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, ELE);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* > */
EXPR egt(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EGT);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* >= */
EXPR ege(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EGE);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}


/** Certificates **/

CERTIF certif(char* name, value node) {
  CAMLparam1(node);
  CAMLlocal1(res);
  res = caml_alloc(2, 0);
  Store_field(res, 0, value_string(name));
  Store_field(res, 1, node);
  CAMLreturn(res);
}

#define CTRUE                 0
#define CFALSE                1

#define CWEAKENING            0
#define CASSUME               1
#define CRESOLUTION           2
#define CLIA_GENERIC          3
#define CEQ_REFLEXIVE         4
#define CEQ_TRANSITIVE        5
#define CEQ_CONGRUENT         6
#define CEQ_CONGRUENT_PRED    7
#define CEQ_CONGRUENT_PRED_B  8
#define CAND                  9
#define CNOT_OR              10
#define COR                  11
#define CNOT_AND             12
#define CXOR1                13
#define CXOR2                14
#define CNOT_XOR1            15
#define CNOT_XOR2            16
#define CIMPLIES             17
#define CNOT_IMPLIES1        18
#define CNOT_IMPLIES2        19
#define CEQUIV1              20
#define CEQUIV2              21
#define CNOT_EQUIV1          22
#define CNOT_EQUIV2          23
#define CAND_POS             24
#define CAND_NEG             25
#define COR_POS              26
#define COR_NEG              27
#define CXOR_POS1            28
#define CXOR_POS2            29
#define CXOR_NEG1            30
#define CXOR_NEG2            31
#define CIMPLIES_POS         32
#define CIMPLIES_NEG1        33
#define CIMPLIES_NEG2        34
#define CEQUIV_POS1          35
#define CEQUIV_POS2          36
#define CEQUIV_NEG1          37
#define CEQUIV_NEG2          38


/* 0. Given a proof of the clause {f1 ... fn}
        and a possibly larger clause {f1 ... fn b1 ... bm},
      proves the clause {f1 ... fn b1 ... bm}
      The order does not matter
      The initial clause may contain the additional literals
        `not false` and `true` as well
*/
CERTIF cweakening(char* name, CERTIF c, size_t m, const EXPR* bs) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(2, CWEAKENING);
  Store_field(node, 0, c);
  Store_field(node, 1, value_list(m, bs));
  CAMLreturn(certif(name, node));
}

/* 1. Refer to an assertion by its index */
CERTIF cassume(char* name, size_t num) {
  value node = caml_alloc(1, CASSUME);
  Store_field(node, 0, Val_int(num));
  return certif(name, node);
}

/* 3. Proves the clause {(true)} */
CERTIF ctrue(char* name) {
  value node = Val_int(CTRUE);
  return certif(name, node);
}

/* 4. Proves the clause {(not false)} */
CERTIF cfalse(char* name) {
  value node = Val_int(CFALSE);
  return certif(name, node);
}

/* 6 & 7. Resolution of two or more clauses */
CERTIF cresolution(char* name, size_t nb, const CERTIF* premisses) {
  value node = caml_alloc(1, CRESOLUTION);
  Store_field(node, 0, value_list(nb, premisses));
  return certif(name, node);
}

/* 12. Proves the given clause in the theory of Linear Integer Arithmetic */
CERTIF clia_generic(char* name, size_t nb, const EXPR* l) {
  value node = caml_alloc(1, CLIA_GENERIC);
  Store_field(node, 0, value_list(nb, l));
  return certif(name, node);
}

/* 23. Given a term t, proves the clause {(= t t)}
       Applies only to a non-Boolean term.
*/
CERTIF ceq_reflexive(char* name, EXPR t) {
  CAMLparam1(t);
  CAMLlocal1(node);
  node = caml_alloc(1, CEQ_REFLEXIVE);
  Store_field(node, 0, t);
  CAMLreturn(certif(name, node));
}

/* 24. Given the terms t1 ... tn,
         proves the clause {(not (= t1 t2)) ... (not (= t{n-1} tn)) (= t1 tn)}
       The tis must be non-Boolean terms.
*/
CERTIF ceq_transitive(char* name, size_t n, const EXPR* ts) {
  value node = caml_alloc(1, CEQ_TRANSITIVE);
  Store_field(node, 0, value_list(n, ts));
  return certif(name, node);
}

/* 25. Proves the clause
         {(not (= t1 u1)) ... (not (= tn un)) (= f(t1, ..., tn) f(u1, ..., un))}
       The tis and uis must be non-Boolean terms, and the codomain of f must not be Bool.
*/
CERTIF ceq_congruent(char* name, size_t n, const EXPR* clause) {
  value node = caml_alloc(1, CEQ_CONGRUENT);
  Store_field(node, 0, value_list(n, clause));
  return certif(name, node);
}

/* 26. Proves the clause
         {(not (= t1 u1)) ... (not (= tn un)) (= P(t1, ..., tn) P(u1, ..., un))}
       The tis and uis must be non-Boolean terms, and the codomain of P must be Bool.
*/
CERTIF ceq_congruent_pred(char* name, size_t n, const EXPR* clause) {
  value node = caml_alloc(1, CEQ_CONGRUENT_PRED);
  Store_field(node, 0, value_list(n, clause));
  return certif(name, node);
}

/* 26b. A small variant
        Proves the clause
          {(not (= t1 u1)) ... (not (= tn un)) (not P(t1, ..., tn)) P(u1, ..., un)}
       The tis and uis must be non-Boolean terms, and the codomain of P must be Bool.
*/
CERTIF ceq_congruent_pred_b(char* name, size_t n, const EXPR* clause) {
  value node = caml_alloc(1, CEQ_CONGRUENT_PRED_B);
  Store_field(node, 0, value_list(n, clause));
  return certif(name, node);
}

/* 28. Given a proof of the clause {(and f1 ... fn)} and a non-negative integer k,
       proves the clause {fk}
*/
CERTIF cand(char* name, CERTIF c, int k) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(2, CAND);
  Store_field(node, 0, c);
  Store_field(node, 1, Val_int(k));
  CAMLreturn(certif(name, node));
}

/* 29. Given a proof of the clause {(not (or f1 ... fn))} and a non-negative integer k,
       proves the clause {(not fk)}
*/
CERTIF cnot_or(char* name, CERTIF c, int k) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(2, CNOT_OR);
  Store_field(node, 0, c);
  Store_field(node, 1, Val_int(k));
  CAMLreturn(certif(name, node));
}

/* 30. Given a proof of the clause {(or f1 ... fn)},
       proves the clause {f1 ... fn}
*/
CERTIF cor(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, COR);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 31. Given a proof of the clause {(not (and f1 ... fn))},
       proves the clause {(not f1) ... (not fn)}
*/
CERTIF cnot_and(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_AND);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 32. Given a proof of the clause {(xor a b)},
       proves the clause {a b}
*/
CERTIF cxor1(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CXOR1);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 33. Given a proof of the clause {(xor a b)},
       proves the clause {(not a) (not b)}
*/
CERTIF cxor2(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CXOR2);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 34. Given a proof of the clause {(not (xor a b))},
       proves the clause {a (not b)}
*/
CERTIF cnot_xor1(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_XOR1);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 35. Given a proof of the clause {(not (xor a b))},
       proves the clause {(not a) b}
*/
CERTIF cnot_xor2(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_XOR2);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 36. Given a proof of the clause {(=> a b)},
       proves the clause {(not a) b}
*/
CERTIF cimplies(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CIMPLIES);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 37. Given a proof of the clause {(not (=> a b))},
       proves the clause {a}
*/
CERTIF cnot_implies1(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_IMPLIES1);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 38. Given a proof of the clause {(not (=> a b))},
       proves the clause {(not b)}
*/
CERTIF cnot_implies2(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_IMPLIES2);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 39. Given a proof of the clause {(= a b)},
       proves the clause {(not a) b}
*/
CERTIF cequiv1(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CEQUIV1);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 40. Given a proof of the clause {(= a b)},
       proves the clause {a (not b)}
*/
CERTIF cequiv2(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CEQUIV2);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 41. Given a proof of the clause {(not (= a b))},
       proves the clause {a b}
*/
CERTIF cnot_equiv1(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_EQUIV1);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 42. Given a proof of the clause {(not (= a b))},
       proves the clause {(not a) (not b)}
*/
CERTIF cnot_equiv2(char* name, CERTIF c) {
  CAMLparam1(c);
  CAMLlocal1(node);
  node = caml_alloc(1, CNOT_EQUIV2);
  Store_field(node, 0, c);
  CAMLreturn(certif(name, node));
}

/* 43. Given the formulas f1 ... fn and a non-negative integer k,
       proves the clause {(not (and f1 ... fn)) fk}
*/
CERTIF cand_pos(char* name, size_t n, const EXPR* fs, int k) {
  value node = caml_alloc(2, CAND_POS);
  Store_field(node, 0, value_list(n, fs));
  Store_field(node, 1, Val_int(k));
  return certif(name, node);
}

/* 44. Given the formulas f1 ... fn,
       proves the clause {(and f1 ... fn) (not f1) ... (not fn)}
*/
CERTIF cand_neg(char* name, size_t n, const EXPR* fs) {
  value node = caml_alloc(1, CAND_NEG);
  Store_field(node, 0, value_list(n, fs));
  return certif(name, node);
}

/* 45. Given the formulas f1 ... fn,
       proves the clause {(not (or f1 ... fn)) f1 ... fn}
*/
CERTIF cor_pos(char* name, size_t n, const EXPR* fs) {
  value node = caml_alloc(1, COR_POS);
  Store_field(node, 0, value_list(n, fs));
  return certif(name, node);
}

/* 46. Given the formulas f1 ... fn and a non-negative integer k,
       proves the clause {(or f1 ... fn) (not fk)}
*/
CERTIF cor_neg(char* name, size_t n, const EXPR* fs, int k) {
  value node = caml_alloc(2, COR_NEG);
  Store_field(node, 0, value_list(n, fs));
  Store_field(node, 1, Val_int(k));
  return certif(name, node);
}

/* 47. Given the formulas a and b,
       proves the clause {(not (xor a b)) a b}
*/
CERTIF cxor_pos1(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CXOR_POS1);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 48. Given the formulas a and b,
       proves the clause {(not (xor a b)) (not a) (not b)}
*/
CERTIF cxor_pos2(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CXOR_POS2);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 49. Given the formulas a and b,
       proves the clause {(xor a b) a (not b)}
*/
CERTIF cxor_neg1(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CXOR_NEG1);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 50. Given the formulas a and b,
       proves the clause {(xor a b) (not a) b}
*/
CERTIF cxor_neg2(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CXOR_NEG2);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 51. Given the formulas a and b,
       proves the clause {(not (implies a b)) (not a) b}
*/
CERTIF cimplies_pos(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CIMPLIES_POS);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 52. Given the formulas a and b,
       proves the clause {(implies a b) a}
*/
CERTIF cimplies_neg1(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CIMPLIES_NEG1);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 53. Given the formulas a and b,
       proves the clause {(implies a b) (not b)}
*/
CERTIF cimplies_neg2(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CIMPLIES_NEG2);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 54. Given the formulas a and b,
       proves the clause {(not (= a b)) a (not b)}
*/
CERTIF cequiv_pos1(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CEQUIV_POS1);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 55. Given the formulas a and b,
       proves the clause {(not (= a b)) (not a) b}
*/
CERTIF cequiv_pos2(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CEQUIV_POS2);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 56. Given the formulas a and b,
       proves the clause {(= a b) (not a) (not b)}
*/
CERTIF cequiv_neg1(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CEQUIV_NEG1);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}

/* 57. Given the formulas a and b,
       proves the clause {(= a b) a b}
*/
CERTIF cequiv_neg2(char* name, EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(node);
  node = caml_alloc(2, CEQUIV_NEG2);
  Store_field(node, 0, a);
  Store_field(node, 1, b);
  CAMLreturn(certif(name, node));
}


/** The checkers **/

int checker(SMTLIB2 smt, CERTIF proof) {
  CAMLparam2(smt, proof);
  CAMLlocal1(v);

  // Get the OCaml function
  static const value * checker_closure = NULL;
  if (checker_closure == NULL)
    checker_closure = caml_named_value("checker");

  // Call the OCaml function
  v = caml_callback2(*checker_closure, smt, proof);
  int b = Bool_val(Field(v, 0));
  char* s = strdup(String_val(Field(v, 1)));

  if (strlen(s) == 0) {
    CAMLreturnT(int, b);
  } else {
    printf("%s\n", s);
    exit(1);
  }
}


void debug_checker(SMTLIB2 smt, CERTIF proof) {
  CAMLparam2(smt, proof);

  // Get the OCaml function
  static const value * debug_checker_closure = NULL;
  if (debug_checker_closure == NULL)
    debug_checker_closure = caml_named_value("debug_checker_string");

  // Call the OCaml function
  char* str = strdup(String_val(caml_callback2(*debug_checker_closure, smt, proof)));
  printf(str);
  CAMLreturn0;
}


/** SMT-LIB2 commands, functional **/

SORTS sorts(size_t nb, SORT* data) {
  return value_list(nb, data);
}

FUNSYMS funsyms(size_t nb, FUNSYM* data) {
  value d[nb];
  for (int i = 0; i < nb; i++) {
    d[i] = (data+i)->fval;
  }
  return value_list(nb, d);
}

ASSERTIONS assertions(size_t nb, EXPR* data) {
  return value_array(nb, data);
}

SMTLIB2 smtlib2(SORTS s, FUNSYMS f, ASSERTIONS a) {
  CAMLparam3(s, f, a);
  CAMLlocal1(res);
  res = caml_alloc(3, 0);
  Store_field(res, 0, s);
  Store_field(res, 1, f);
  Store_field(res, 2, a);
  CAMLreturn(res);
}


/** SMT-LIB2 commands, imperative **/

typedef struct ICOMMANDS_t {
  size_t nb_sorts;
  size_t log2_nb_sorts;
  SORT* sorts;
  size_t nb_funsyms;
  size_t log2_nb_funsyms;
  FUNSYM* funsyms;
  size_t nb_asserts;
  size_t log2_nb_asserts;
  EXPR* asserts;
} ICOMMANDS;

ICOMMANDS icommands;

void reset_commands() {
  /* free(icommands.sorts); */
  /* free(icommands.funsyms); */
  /* free(icommands.asserts); */
}

void start_smt2() {
  icommands.nb_sorts = 0;
  icommands.log2_nb_sorts = 0;
  icommands.nb_funsyms = 0;
  icommands.log2_nb_funsyms = 0;
  icommands.nb_asserts = 0;
  icommands.log2_nb_asserts = 0;
}

void declare_sort(SORT s) {
  CAMLparam1(s);
  if (icommands.nb_sorts == 0) {
    icommands.sorts = (SORT*) malloc(sizeof(SORT));
    if (icommands.sorts) *icommands.sorts = s;
  } else if (icommands.nb_sorts == (1 << icommands.log2_nb_sorts)) {
    icommands.log2_nb_sorts++;
    size_t size = 1 << icommands.log2_nb_sorts;
    icommands.sorts = realloc(icommands.sorts, size*sizeof(SORT));
    if (icommands.sorts) *(icommands.sorts + icommands.nb_sorts) = s;
  } else {
    *(icommands.sorts + icommands.nb_sorts) = s;
  }
  icommands.nb_sorts++;
  CAMLreturn0;
}

void declare_fun(FUNSYM f) {
  if (icommands.nb_funsyms == 0) {
    icommands.funsyms = (FUNSYM*) malloc(sizeof(FUNSYM));
    if (icommands.funsyms) *icommands.funsyms = f;
  } else if (icommands.nb_funsyms == (1 << icommands.log2_nb_funsyms)) {
    icommands.log2_nb_funsyms++;
    size_t size = 1 << icommands.log2_nb_funsyms;
    icommands.funsyms = realloc(icommands.funsyms, size*sizeof(FUNSYM));
    if (icommands.funsyms) *(icommands.funsyms + icommands.nb_funsyms) = f;
  } else {
    *(icommands.funsyms + icommands.nb_funsyms) = f;
  }
  icommands.nb_funsyms++;
}

void assertf(EXPR f) {
  CAMLparam1(f);
  if (icommands.nb_asserts == 0) {
    icommands.asserts = (EXPR*) malloc(sizeof(EXPR));
    if (icommands.asserts) *icommands.asserts = f;
  } else if (icommands.nb_asserts == (1 << icommands.log2_nb_asserts)) {
    icommands.log2_nb_asserts++;
    size_t size = 1 << icommands.log2_nb_asserts;
    icommands.asserts = realloc(icommands.asserts, size*sizeof(EXPR));
    if (icommands.asserts) *(icommands.asserts + icommands.nb_asserts) = f;
  } else {
    *(icommands.asserts + icommands.nb_asserts) = f;
  }
  icommands.nb_asserts++;
  CAMLreturn0;
}

int check_proof(CERTIF proof) {
  CAMLparam1(proof);
  CAMLlocal4(s, f, a, smt);
  s = sorts     (icommands.nb_sorts,   icommands.sorts);
  f = funsyms   (icommands.nb_funsyms, icommands.funsyms);
  a = assertions(icommands.nb_asserts, icommands.asserts);
  smt = smtlib2(s, f, a);
  int res = checker(smt, proof);
  reset_commands();
  CAMLreturnT(int, res);
}

void debug_check_proof(CERTIF proof) {
  CAMLparam1(proof);
  CAMLlocal4(s, f, a, smt);
  s = sorts     (icommands.nb_sorts,   icommands.sorts);
  f = funsyms   (icommands.nb_funsyms, icommands.funsyms);
  a = assertions(icommands.nb_asserts, icommands.asserts);
  smt = smtlib2(s, f, a);
  debug_checker(smt, proof);
  /* TODO: find why it fails */
  /* reset_commands(); */
  CAMLreturn0;
}

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


#include <stdio.h>
#include <assert.h>

#include <caml/callback.h>


#include "c/types.h"
#include "c/checker.h"


/** Incorrect proofs **/

int testIF00() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cfalse("t1"), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testIFD00() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cfalse("t1"), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int testII00() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testIID00() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}

int testIF01() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF proof = cfalse("t1");

  // Proof checking
  return checker(smt, proof);
}

void testIFD01() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF proof = cfalse("t1");

  // Proof checking
  debug_checker(smt, proof);
}

int testII01() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF proof = cfalse("t1");

  // Proof checking
  return check_proof(proof);
}

void testIID01() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF proof = cfalse("t1");

  // Proof checking
  debug_check_proof(proof);
}

/** Proofs of unsatisfiability of ⊥ **/

int testCF00() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testCFD00() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int testCI00() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testCID00() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}

int testCF01() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testCFD01() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int testCI01() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testCID01() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}


/** Proofs of unsatisfiability of `a ∧ ¬a` **/

int testCF02() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, enot(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cassume("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testCFD02() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, enot(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cassume("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int testCI02() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(enot(a));

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cassume("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testCID02() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(enot(a));

  // Proof
  CERTIF r[2] = {cassume("t1", 0), cassume("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}

int testCF03() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, enot(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassume("t1", 1), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testCFD03() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, enot(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassume("t1", 1), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int testCI03() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(enot(a));

  // Proof
  CERTIF r[2] = {cassume("t1", 1), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testCID03() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(enot(a));

  // Proof
  CERTIF r[2] = {cassume("t1", 1), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}


/** Unit tests **/

int testWeakening() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a  = efun(fa, NULL);
  EXPR b  = efun(fb, NULL);
  EXPR na  = enot(a);
  EXPR nb  = enot(b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(a);
  assertf(na);
  assertf(nb);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  EXPR t4b[2] = {a, b};
  CERTIF t4 = cweakening("t4", t1, 2, t4b);
  CERTIF t6b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t6b);

  // Proof checking
  return check_proof(t5);
}

int testTrue() {

  // SMT-LIB2 problem
  start_smt2();
  assertf(enot(etrue()));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = ctrue("t2");
  CERTIF t3b[2] = {t1, t2};
  CERTIF t3 = cresolution("t3", 2, t3b);

  // Proof checking
  return check_proof(t3);
}

int testFalse() {

  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cfalse("t2");
  CERTIF t3b[2] = {t1, t2};
  CERTIF t3 = cresolution("t3", 2, t3b);

  // Proof checking
  return check_proof(t3);
}

int testEq_reflexive() {
  // Expressions
  SORT u = sort("U");
  FUNSYM fa = funsym ("a", 0, NULL, u);
  EXPR a = efun(fa, NULL);
  EXPR aa = eeq(a, a);

  // SMT-LIB2 problem
  start_smt2();
  declare_sort(u);
  declare_fun(fa);
  assertf(enot(aa));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = ceq_reflexive("t2", a);
  CERTIF f3b[2] = {t1, t2};
  CERTIF t3 = cresolution("t3", 2, f3b);

  // Proof checking
  return check_proof(t3);
}

int testEq_transitive() {
  // Expressions
  SORT u = sort("U");
  FUNSYM fa = funsym ("a", 0, NULL, u);
  FUNSYM fb = funsym ("b", 0, NULL, u);
  FUNSYM fc = funsym ("c", 0, NULL, u);
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR c = efun(fc, NULL);
  EXPR ab = eeq(a, b);
  EXPR bc = eeq(b, c);
  EXPR ac = eeq(a, c);

  // SMT-LIB2 problem
  start_smt2();
  declare_sort(u);
  declare_fun(fa);
  declare_fun(fb);
  declare_fun(fc);
  assertf(ab);
  assertf(bc);
  assertf(enot(ac));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  EXPR t4b[3] = {a, b, c};
  CERTIF t4 = ceq_transitive("t4", 3, t4b);
  CERTIF t5b[4] = {t4, t1, t2, t3};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEq_congruent() {
  // Expressions
  SORT u = sort("U");
  SORT i = sort("Int");
  SORT fdom[2] = {i, u};
  FUNSYM f = funsym ("f", 2, fdom, u);
  FUNSYM fa1 = funsym ("a1", 0, NULL, i);
  FUNSYM fa2 = funsym ("a2", 0, NULL, u);
  FUNSYM fb1 = funsym ("b1", 0, NULL, i);
  FUNSYM fb2 = funsym ("b2", 0, NULL, u);
  EXPR a1 = efun(fa1, NULL);
  EXPR a2 = efun(fa2, NULL);
  EXPR b1 = efun(fb1, NULL);
  EXPR b2 = efun(fb2, NULL);
  EXPR aa[2] = {a1, a2};
  EXPR f1 = efun(f, aa);
  EXPR bb[2] = {b1, b2};
  EXPR f2 = efun(f, bb);
  EXPR ab1 = eeq(a1, b1);
  EXPR ab2 = eeq(a2, b2);
  EXPR f12 = eeq(f1, f2);

  // SMT-LIB2 problem
  start_smt2();
  declare_sort(u);
  declare_fun(f);
  declare_fun(fa1);
  declare_fun(fa2);
  declare_fun(fb1);
  declare_fun(fb2);
  assertf(ab1);
  assertf(ab2);
  assertf(enot(f12));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  EXPR t4b[3] = {enot(ab1), f12, enot(ab2)};
  CERTIF t4 = ceq_congruent("t4", 3, t4b);
  CERTIF t5b[4] = {t4, t1, t2, t3};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEq_congruent2() {
  // Expressions
  SORT i = sort("Int");
  FUNSYM fa1 = funsym ("a1", 0, NULL, i);
  FUNSYM fa2 = funsym ("a2", 0, NULL, i);
  FUNSYM fb1 = funsym ("b1", 0, NULL, i);
  FUNSYM fb2 = funsym ("b2", 0, NULL, i);
  EXPR a1 = efun(fa1, NULL);
  EXPR a2 = efun(fa2, NULL);
  EXPR b1 = efun(fb1, NULL);
  EXPR b2 = efun(fb2, NULL);
  EXPR f1 = emult(a1, a2);
  EXPR f2 = emult(b1, b2);
  EXPR ab1 = eeq(a1, b1);
  EXPR ab2 = eeq(a2, b2);
  EXPR f12 = eeq(f1, f2);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa1);
  declare_fun(fa2);
  declare_fun(fb1);
  declare_fun(fb2);
  assertf(ab1);
  assertf(ab2);
  assertf(enot(f12));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  EXPR t4b[3] = {enot(ab1), f12, enot(ab2)};
  CERTIF t4 = ceq_congruent("t4", 3, t4b);
  CERTIF t5b[4] = {t4, t1, t2, t3};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEq_congruent_pred() {
  // Expressions
  SORT u = sort("U");
  SORT i = sort("Int");
  SORT b = sort("Bool");
  SORT pdom[2] = {i, u};
  FUNSYM p = funsym ("p", 2, pdom, b);
  FUNSYM fa1 = funsym ("a1", 0, NULL, i);
  FUNSYM fa2 = funsym ("a2", 0, NULL, u);
  FUNSYM fb1 = funsym ("b1", 0, NULL, i);
  FUNSYM fb2 = funsym ("b2", 0, NULL, u);
  EXPR a1 = efun(fa1, NULL);
  EXPR a2 = efun(fa2, NULL);
  EXPR b1 = efun(fb1, NULL);
  EXPR b2 = efun(fb2, NULL);
  EXPR aa[2] = {a1, a2};
  EXPR p1 = efun(p, aa);
  EXPR bb[2] = {b1, b2};
  EXPR p2 = efun(p, bb);
  EXPR ab1 = eeq(a1, b1);
  EXPR ab2 = eeq(a2, b2);
  EXPR f12 = eeq(p1, p2);

  // SMT-LIB2 problem
  start_smt2();
  declare_sort(u);
  declare_fun(p);
  declare_fun(fa1);
  declare_fun(fa2);
  declare_fun(fb1);
  declare_fun(fb2);
  assertf(ab1);
  assertf(ab2);
  assertf(enot(f12));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  EXPR t4b[3] = {enot(ab1), enot(ab2), f12};
  CERTIF t4 = ceq_congruent_pred("t4", 3, t4b);
  CERTIF t5b[4] = {t4, t1, t2, t3};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEq_congruent_pred2() {
  // Expressions
  SORT i = sort("Int");
  FUNSYM fa1 = funsym ("a1", 0, NULL, i);
  FUNSYM fa2 = funsym ("a2", 0, NULL, i);
  FUNSYM fb1 = funsym ("b1", 0, NULL, i);
  FUNSYM fb2 = funsym ("b2", 0, NULL, i);
  EXPR a1 = efun(fa1, NULL);
  EXPR a2 = efun(fa2, NULL);
  EXPR b1 = efun(fb1, NULL);
  EXPR b2 = efun(fb2, NULL);
  EXPR p1 = ege(a1, a2);
  EXPR p2 = ege(b1, b2);
  EXPR ab1 = eeq(a1, b1);
  EXPR ab2 = eeq(a2, b2);
  EXPR f12 = eeq(p1, p2);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa1);
  declare_fun(fa2);
  declare_fun(fb1);
  declare_fun(fb2);
  assertf(ab1);
  assertf(ab2);
  assertf(enot(f12));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  EXPR t4b[3] = {enot(ab1), enot(ab2), f12};
  CERTIF t4 = ceq_congruent_pred("t4", 3, t4b);
  CERTIF t5b[4] = {t4, t1, t2, t3};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEq_congruent_pred_b() {
  // Expressions
  SORT u = sort("U");
  SORT i = sort("Int");
  SORT b = sort("Bool");
  SORT pdom[2] = {i, u};
  FUNSYM p = funsym ("p", 2, pdom, b);
  FUNSYM fa1 = funsym ("a1", 0, NULL, i);
  FUNSYM fa2 = funsym ("a2", 0, NULL, u);
  FUNSYM fb1 = funsym ("b1", 0, NULL, i);
  FUNSYM fb2 = funsym ("b2", 0, NULL, u);
  EXPR a1 = efun(fa1, NULL);
  EXPR a2 = efun(fa2, NULL);
  EXPR b1 = efun(fb1, NULL);
  EXPR b2 = efun(fb2, NULL);
  EXPR aa[2] = {a1, a2};
  EXPR p1 = efun(p, aa);
  EXPR bb[2] = {b1, b2};
  EXPR p2 = efun(p, bb);
  EXPR ab1 = eeq(a1, b1);
  EXPR ab2 = eeq(a2, b2);

  // SMT-LIB2 problem
  start_smt2();
  declare_sort(u);
  declare_fun(p);
  declare_fun(fa1);
  declare_fun(fa2);
  declare_fun(fb1);
  declare_fun(fb2);
  assertf(ab1);
  assertf(ab2);
  assertf(p1);
  assertf(enot(p2));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cassume("t4", 3);
  EXPR t5b[4] = {enot(ab1), enot(ab2), enot(p1), p2};
  CERTIF t5 = ceq_congruent_pred_b("t5", 4, t5b);
  CERTIF t6b[5] = {t5, t1, t2, t3, t4};
  CERTIF t6 = cresolution("t6", 5, t6b);

  // Proof checking
  return check_proof(t6);
}

int testEq_congruent_pred_b2() {
  // Expressions
  SORT i = sort("Int");
  FUNSYM fa1 = funsym ("a1", 0, NULL, i);
  FUNSYM fa2 = funsym ("a2", 0, NULL, i);
  FUNSYM fb1 = funsym ("b1", 0, NULL, i);
  FUNSYM fb2 = funsym ("b2", 0, NULL, i);
  EXPR a1 = efun(fa1, NULL);
  EXPR a2 = efun(fa2, NULL);
  EXPR b1 = efun(fb1, NULL);
  EXPR b2 = efun(fb2, NULL);
  EXPR p1 = elt(a1, a2);
  EXPR p2 = elt(b1, b2);
  EXPR ab1 = eeq(a1, b1);
  EXPR ab2 = eeq(a2, b2);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa1);
  declare_fun(fa2);
  declare_fun(fb1);
  declare_fun(fb2);
  assertf(ab1);
  assertf(ab2);
  assertf(p1);
  assertf(enot(p2));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cassume("t4", 3);
  EXPR t5b[4] = {enot(ab1), enot(ab2), enot(p1), p2};
  CERTIF t5 = ceq_congruent_pred_b("t5", 4, t5b);
  CERTIF t6b[5] = {t5, t1, t2, t3, t4};
  CERTIF t6 = cresolution("t6", 5, t6b);

  // Proof checking
  return check_proof(t6);
}

int testAnd() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR abb[2] = {a, b};
  EXPR ab = eand(2, abb);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cand("t3", t1, 1);
  CERTIF t4b[2] = {t2, t3};
  CERTIF t4 = cresolution("t4", 2, t4b);

  // Proof checking
  return check_proof(t4);
}

int testNot_or() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR abb[2] = {a, b};
  EXPR ab = eor(2, abb);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cnot_or("t3", t1, 1);
  CERTIF t4b[2] = {t2, t3};
  CERTIF t4 = cresolution("t4", 2, t4b);

  // Proof checking
  return check_proof(t4);
}

int testOr() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR abb[2] = {a, b};
  EXPR ab = eor(2, abb);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cor("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testNot_and() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR abb[2] = {a, b};
  EXPR ab = eand(2, abb);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cnot_and("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testXor1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cxor1("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testXor2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(a);
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cxor2("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testNot_xor1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(enot(a));
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cnot_xor1("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testNot_xor2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cnot_xor2("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testImplies() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eimp(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(a);
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cimplies("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testNot_implies1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eimp(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(enot(a));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cnot_implies1("t3", t1);
  CERTIF t4b[2] = {t2, t3};
  CERTIF t4 = cresolution("t4", 2, t4b);

  // Proof checking
  return check_proof(t4);
}

int testNot_implies2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eimp(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cnot_implies2("t3", t1);
  CERTIF t4b[2] = {t2, t3};
  CERTIF t4 = cresolution("t4", 2, t4b);

  // Proof checking
  return check_proof(t4);
}

int testEquiv1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(a);
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cequiv1("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEquiv2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cequiv2("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testNot_equiv1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(enot(a));
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cnot_equiv1("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testNot_equiv2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cnot_equiv2("t4", t1);
  CERTIF t5b[3] = {t4, t2, t3};
  CERTIF t5 = cresolution("t5", 3, t5b);

  // Proof checking
  return check_proof(t5);
}

int testAnd_pos() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR aa[2] = {a, b};
  EXPR ab = eand(2, aa);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3b[2] = {a, b};
  CERTIF t3 = cand_pos("t3", 2, t3b, 1);
  CERTIF t4b[3] = {t3, t2, t1};
  CERTIF t4 = cresolution("t4", 3, t4b);

  // Proof checking
  return check_proof(t4);
}

int testAnd_neg() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR aa[2] = {a, b};
  EXPR ab = eand(2, aa);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4b[2] = {a, b};
  CERTIF t4 = cand_neg("t4", 2, t4b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testOr_pos() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR aa[2] = {a, b};
  EXPR ab = eor(2, aa);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4b[2] = {a, b};
  CERTIF t4 = cor_pos("t4", 2, t4b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testOr_neg() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR aa[2] = {a, b};
  EXPR ab = eor(2, aa);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3b[2] = {a, b};
  CERTIF t3 = cor_neg("t3", 2, t3b, 1);
  CERTIF t4b[3] = {t3, t2, t1};
  CERTIF t4 = cresolution("t4", 3, t4b);

  // Proof checking
  return check_proof(t4);
}

int testXor_pos1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cxor_pos1("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testXor_pos2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(a);
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cxor_pos2("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testXor_neg1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(enot(a));
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cxor_neg1("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testXor_neg2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = exor(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cxor_neg2("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testImplies_pos() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eimp(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(a);
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cimplies_pos("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testImplies_neg1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eimp(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(enot(a));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cimplies_neg1("t3", a, b);
  CERTIF t4b[3] = {t3, t2, t1};
  CERTIF t4 = cresolution("t4", 3, t4b);

  // Proof checking
  return check_proof(t4);
}

int testImplies_neg2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eimp(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cimplies_neg2("t3", a, b);
  CERTIF t4b[3] = {t3, t2, t1};
  CERTIF t4 = cresolution("t4", 3, t4b);

  // Proof checking
  return check_proof(t4);
}

int testEquiv_pos1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(enot(a));
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cequiv_pos1("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEquiv_pos2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(ab);
  assertf(a);
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cequiv_pos2("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEquiv_neg1() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(a);
  assertf(b);

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cequiv_neg1("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}

int testEquiv_neg2() {
  // Expressions
  FUNSYM fa = funsym ("a", 0, NULL, sort("Bool"));
  FUNSYM fb = funsym ("b", 0, NULL, sort("Bool"));
  EXPR a = efun(fa, NULL);
  EXPR b = efun(fb, NULL);
  EXPR ab = eeq(a, b);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fa);
  declare_fun(fb);
  assertf(enot(ab));
  assertf(enot(a));
  assertf(enot(b));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cassume("t2", 1);
  CERTIF t3 = cassume("t3", 2);
  CERTIF t4 = cequiv_neg2("t4", a, b);
  CERTIF t5b[4] = {t4, t3, t2, t1};
  CERTIF t5 = cresolution("t5", 4, t5b);

  // Proof checking
  return check_proof(t5);
}


/** unit-tests/lia6.vtlog **/
int test_lia6 () {
  // Expressions
  FUNSYM fx = funsym("x", 0, NULL, sort("Int"));
  EXPR x = efun(fx, NULL);
  EXPR e4 = eminus(x, eint(3));
  EXPR e5 = ele(eint(7), e4);
  EXPR e3 = ele(e4, eint(7));
  EXPR e2b[2] = {e3, e5};
  EXPR e2 = eand(2, e2b);
  EXPR e6 = ege(x, eint(10));
  EXPR e1 = eimp(e2, e6);

  // SMT-LIB2 problem
  start_smt2();
  declare_fun(fx);
  assertf(enot(e1));

  // Proof
  CERTIF t1 = cassume("t1", 0);
  CERTIF t2 = cnot_implies1("t2", t1);
  CERTIF t3 = cand("t3", t2, 2);
  CERTIF t4 = cnot_implies2("t4", t1);
  EXPR t5b[2] = {e6, enot(e5)};
  CERTIF t5 = clia_generic("t5", 2, t5b);
  CERTIF t6b[3] = {t5, t3, t4};
  CERTIF t6 = cresolution("t6", 3, t6b);

  // Proof checking
  return check_proof(t6);
}


/** Error when terms are ill-typed **/

int testTF00() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Int"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, enot(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassume("t1", 1), cassume("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}


/** Main program **/

int main(int argc, char ** argv)
{
  // Initialize OCaml code
  caml_startup(argv);

  // Run tests
  assert(!testIF00());
  assert(!testII00());
  assert(!testIF01());
  assert(!testII01());
  assert(testCF00());
  assert(testCI00());
  assert(testCF01());
  assert(testCI01());
  assert(testCF02());
  assert(testCI02());
  assert(testCF03());
  assert(testCI03());
  assert(testWeakening());
  assert(testTrue());
  assert(testFalse());
  assert(testEq_reflexive());
  assert(testEq_transitive());
  assert(testEq_congruent());
  assert(testEq_congruent2());
  assert(testEq_congruent_pred());
  assert(testEq_congruent_pred2());
  assert(testEq_congruent_pred_b());
  assert(testEq_congruent_pred_b2());
  assert(testAnd());
  assert(testNot_or());
  assert(testOr());
  assert(testNot_and());
  assert(testXor1());
  assert(testXor2());
  assert(testNot_xor1());
  assert(testNot_xor2());
  assert(testImplies());
  assert(testNot_implies1());
  assert(testNot_implies2());
  assert(testEquiv1());
  assert(testEquiv2());
  assert(testNot_equiv1());
  assert(testNot_equiv2());
  assert(testAnd_pos());
  assert(testAnd_neg());
  assert(testOr_pos());
  assert(testOr_neg());
  assert(testXor_pos1());
  assert(testXor_pos2());
  assert(testXor_neg1());
  assert(testXor_neg2());
  assert(testImplies_pos());
  assert(testImplies_neg1());
  assert(testImplies_neg2());
  assert(testEquiv_pos1());
  assert(testEquiv_pos2());
  assert(testEquiv_neg1());
  assert(testEquiv_neg2());
  assert(test_lia6());
  printf("All tests suceeded\n");
  /* printf("Now testing the debugging checker:\n"); */
  /* printf("testIFD00:\n"); */
  /* testIFD00(); */
  /* printf("testIID00:\n"); */
  /* testIID00(); */
  /* printf("testIFD01:\n"); */
  /* testIFD01(); */
  /* printf("testIID01:\n"); */
  /* testIID01(); */
  /* printf("testCFD00:\n"); */
  /* testCFD00(); */
  /* printf("testCID00:\n"); */
  /* testCID00(); */
  /* printf("testCFD01:\n"); */
  /* testCFD01(); */
  /* printf("testCID01:\n"); */
  /* testCID01(); */
  /* printf("testCFD02:\n"); */
  /* testCFD02(); */
  /* printf("testCID02:\n"); */
  /* testCID02(); */
  /* printf("testCFD03:\n"); */
  /* testCFD03(); */
  /* printf("testCID03:\n"); */
  /* testCID03(); */
  /* printf("Now testing when terms are ill-typed (exits with error code 1):\n"); */
  /* testTF00(); */

  return 0;
}

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

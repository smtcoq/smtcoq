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

int test00() {
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

void testd00() {
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

int test00b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testd00b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}

int test01() {
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

int test01b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF proof = cfalse("t1");

  // Proof checking
  return check_proof(proof);
}

void testd01() {
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

void testd01b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF proof = cfalse("t1");

  // Proof checking
  debug_check_proof(proof);
}

/** Proofs of unsatisfiability of ⊥ **/

int test02() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testd02() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int test02b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testd02b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cfalse("t2")};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}

int test03() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testd03() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYMS f = funsyms(0, NULL);
  EXPR ff = efalse();
  ASSERTIONS a = assertions(1, &ff);
  SMTLIB2 smt = smtlib2(s, f, a);

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int test03b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testd03b() {
  // SMT-LIB2 problem
  start_smt2();
  assertf(efalse());

  // Proof
  CERTIF r[2] = {cfalse("t1"), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}


/** Proofs of unsatisfiability of `a ∧ ¬a` **/

int test04() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, eneg(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cassert("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testd04() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, eneg(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cassert("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int test04b() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(eneg(a));

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cassert("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testd04b() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(eneg(a));

  // Proof
  CERTIF r[2] = {cassert("t1", 0), cassert("t2", 1)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}

int test05() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, eneg(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassert("t1", 1), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return checker(smt, proof);
}

void testd05() {
  // SMT-LIB2 problem
  SORTS s = sorts(0, NULL);
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  FUNSYMS f = funsyms(1, &fa);
  EXPR a = efun(fa, NULL);
  EXPR as[2] = {a, eneg(a)};
  ASSERTIONS ass = assertions(2, as);
  SMTLIB2 smt = smtlib2(s, f, ass);

  // Proof
  CERTIF r[2] = {cassert("t1", 1), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_checker(smt, proof);
}

int test05b() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(eneg(a));

  // Proof
  CERTIF r[2] = {cassert("t1", 1), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  return check_proof(proof);
}

void testd05b() {
  // SMT-LIB2 problem
  start_smt2();
  FUNSYM fa = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(fa);
  EXPR a = efun(fa, NULL);
  assertf(a);
  assertf(eneg(a));

  // Proof
  CERTIF r[2] = {cassert("t1", 1), cassert("t2", 0)};
  CERTIF proof = cresolution("t3", 2, r);

  // Proof checking
  debug_check_proof(proof);
}


/** Main program **/

int main(int argc, char ** argv)
{
  // Initialize OCaml code
  caml_startup(argv);

  // Run tests
  assert(!test00());
  assert(!test00b());
  assert(!test01());
  assert(!test01b());
  assert(test02());
  assert(test02b());
  assert(test03());
  assert(test03b());
  assert(test04());
  assert(test04b());
  assert(test05());
  assert(test05b());
  printf("All tests suceeded\nNow testing the debugging checker:\n");
  printf("test00:\n");
  testd00();
  printf("test00b:\n");
  testd00b();
  printf("test01:\n");
  testd01();
  printf("test01b:\n");
  testd01b();
  printf("test02:\n");
  testd02();
  printf("test02b:\n");
  testd02b();
  printf("test03:\n");
  testd03();
  printf("test03b:\n");
  testd03b();
  printf("test04:\n");
  testd04();
  printf("test04b:\n");
  testd04b();
  printf("test05:\n");
  testd05();
  printf("test05b:\n");
  testd05b();

  return 0;
}

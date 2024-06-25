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


int main(int argc, char ** argv)
{
  // The main should always start with this command
  // (more explanations later)
  caml_startup(argv);

  // We state the problem, in a way similar to SMT-LIB2 <https://smt-lib.org>
  // Start
  start_smt2();

  // `asymb` is a function symbol with name "a", empty domain (`0` and
  // `NULL`), and codomain in the sort `Bool`
  FUNSYM asymb = funsym("a", 0, NULL, sort("Bool"));
  declare_fun(asymb);

  // From this function symbol, we can define our expression `a ∧ ¬a`
  // First, `a` is the application of `asym` to an empty list
  EXPR a = efun(asymb, NULL);

  // Then, let's build the expression `a ∧ ¬a`. `¬` is defined by the
  // unary `enot` function, and ∧ by the n-ary `eand` function.
  EXPR args[2] = {a, enot(a)};
  EXPR anota = eand(2, args);

  // Finally, let's assert this formula in our problem
  assertf(anota);

  // We can now build a proof of unsatisfiability, step by step
  // The proof format is a subset of the Alethe format
  //   <https://verit.loria.fr/documentation/alethe-spec.pdf>
  // All the possible steps take as a first argument a name, that can be
  // useful for debugging (more explanations later)
  // First, let's get back our assertion, which is labeled `0` as it is
  // the first (and only) one we declared
  CERTIF step1 = cassume("step1", 0);   // Proves the clause `a ∧ ¬a`

  // Then, let's break the ∧ in two, from step1
  CERTIF step2 = cand("step2", step1, 1);   // Proves the clause `a`
  CERTIF step3 = cand("step3", step1, 2);   // Proves the clause `¬a`

  // Finally, we can resolve these two clauses to obtain the empty
  // clause, which witnesses that our assertion was unsatisfiable
  CERTIF clauses[2] = {step2, step3};
  CERTIF step4 = cresolution("step4", 2, clauses);   // Proves the empty clause

  // Let's us now call the certified checker, which should return `true`
  assert(check_proof(step4));

  printf("Example successful\n");

  return 0;
}

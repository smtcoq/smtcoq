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


/** Certificates **/

/* In all the smart constructors, the first parameter is a name given to
   the step, used for debugging */

/* Refer to an assertion */
CERTIF cassert(char* name, size_t num);

/* Proof of the clause {(not false)} */
CERTIF cfalse(char* name);

/* Resolution chain */
CERTIF cresolution(char* name, size_t nb, const CERTIF* premisses);


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

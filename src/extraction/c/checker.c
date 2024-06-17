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
#define ENEG       1
#define EAND       2
#define EBAND      3
#define EOR        4
#define EBOR       5
#define EXOR       6
#define EIMP       7
#define EEQ        8
#define EDISTINCT  9
#define EINT      10
#define EADD      12
#define EOPP      13
#define EMINUS    14
#define EMULT     15
#define ELT       16
#define ELE       17
#define EGT       18
#define EGE       19

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
EXPR eneg(EXPR a) {
  CAMLparam1(a);
  CAMLlocal1(res);
  res = caml_alloc(1, ENEG);
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

/* Binary and */
EXPR eband(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EBAND);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
}

/* N-ary or */
EXPR eor(size_t nb, const EXPR* a) {
  value res = caml_alloc(1, EOR);
  value r = value_list(nb, a);
  Store_field(res, 0, r);
  return res;
}

/* Binary or */
EXPR ebor(EXPR a, EXPR b) {
  CAMLparam2(a, b);
  CAMLlocal1(res);
  res = caml_alloc(2, EBOR);
  Store_field(res, 0, a);
  Store_field(res, 1, b);
  CAMLreturn(res);
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

/* -> */
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

#define CFALSE 0

#define CASSERT 0
#define CRESOLUTION 1

/* Refer to an assertion */
CERTIF cassert(char* name, size_t num) {
  value node = caml_alloc(1, CASSERT);
  Store_field(node, 0, Val_int(num));
  return certif(name, node);
}

/* Proof of the clause {(not false)} */
CERTIF cfalse(char* name) {
  value node = Val_int(CFALSE);
  return certif(name, node);
}

/* Resolution chain */
CERTIF cresolution(char* name, size_t nb, const CERTIF* premisses) {
  value node = caml_alloc(1, CRESOLUTION);
  value p = value_list(nb, premisses);
  Store_field(node, 0, p);
  return certif(name, node);
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
  free(icommands.sorts);
  free(icommands.funsyms);
  free(icommands.asserts);
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

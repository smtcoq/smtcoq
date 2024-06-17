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


#ifndef _TYPES_H_
#define _TYPES_H_

#include <caml/mlvalues.h>


/** Sorts of first-order logic **/

typedef value SORT;


/** Function symbols of first-order logic **/

typedef struct FUNSYM_t {
  value fval;
  size_t arity;
} FUNSYM;


/** Terms and formulas of first-order logic **/

typedef value EXPR;


/** SMT-LIB2 commands, functional **/

typedef value SORTS;
typedef value FUNSYMS;
typedef value ASSERTIONS;
typedef value SMTLIB2;


/** Certificates **/

typedef value CERTIF;


#endif

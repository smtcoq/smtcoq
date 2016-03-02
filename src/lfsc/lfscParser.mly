/**************************************************************************/
/*                                                                        */
/*     SMTCoq                                                             */
/*     Copyright (C) 2011 - 2016                                          */
/*                                                                        */
/*     Michaël Armand                                                     */
/*     Benjamin Grégoire                                                  */
/*     Chantal Keller                                                     */
/*                                                                        */
/*     Inria - École Polytechnique - MSR-Inria Joint Lab                  */
/*     Université Paris-Sud                                               */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/

%{
  open SmtAtom
  open SmtForm
  open LfscSyntax
%}


/* To be completed */

/*
  definition of the tokens
*/

%token EOL UNSAT CHECK
%token LPAR RPAR
%token <string> ANY

/* return type of the parser: FIXME */
%type <unit> certif
%start certif


%%

certif:
   | UNSAT LPAR CHECK ANY RPAR EOL                         { () }

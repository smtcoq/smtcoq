/**************************************************************************/
/*                                                                        */
/*     SMTCoq                                                             */
/*     Copyright (C) 2011 - 2016                                          */
/*                                                                        */
/*     Michaël Armand                                                     */
/*     Benjamin Grégoire                                                  */
/*     Chantal Keller                                                     */
/*                                                                        */
/*     Inria - École Polytechnique - Université Paris-Sud                 */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/


%{
  open SmtAtom
  open SmtForm
  open VeritSyntax
%}


/*
  définition des lexèmes
*/

%token EOL SAT
%token COLON SHARP
%token LPAR RPAR
%token NOT XOR ITE EQ LT LEQ GT GEQ PLUS MINUS MULT OPP LET DIST
%token INPU DEEP TRUE FALS ANDP ANDN ORP ORN XORP1 XORP2 XORN1 XORN2 IMPP IMPN1 IMPN2 EQUP1 EQUP2 EQUN1 EQUN2 ITEP1 ITEP2 ITEN1 ITEN2 EQRE EQTR EQCO EQCP DLGE LAGE LATA DLDE LADE FINS EINS SKEA SKAA QNTS QNTM RESO AND NOR OR NAND XOR1 XOR2 NXOR1 NXOR2 IMP NIMP1 NIMP2 EQU1 EQU2 NEQU1 NEQU2 ITE1 ITE2 NITE1 NITE2 TPAL TLAP TPLE TPNE TPDE TPSA TPIE TPMA TPBR TPBE TPSC TPPP TPQT TPQS TPSK SUBP
%token <int> INT
%token <Big_int.big_int> BIGINT
%token <string> VAR BINDVAR

/* type de "retour" du parseur : une clause */
%type <int> line
%start line


%%

line:
  | SAT                                                    { raise Sat }
  | INT COLON LPAR typ clause                   RPAR EOL   { mk_clause ($1,$4,$5,[]) }
  | INT COLON LPAR typ clause clause_ids_params RPAR EOL   { mk_clause ($1,$4,$5,$6) }
;

typ:
  | INPU                                                   { Inpu  }
  | DEEP                                                   { Deep  }
  | TRUE                                                   { True  }
  | FALS                                                   { Fals  }
  | ANDP                                                   { Andp  }
  | ANDN                                                   { Andn  }
  | ORP                                                    { Orp   }
  | ORN                                                    { Orn   }
  | XORP1                                                  { Xorp1 }
  | XORP2                                                  { Xorp2 }
  | XORN1                                                  { Xorn1 }
  | XORN2                                                  { Xorn2 }
  | IMPP                                                   { Impp  }
  | IMPN1                                                  { Impn1 }
  | IMPN2                                                  { Impn2 }
  | EQUP1                                                  { Equp1 }
  | EQUP2                                                  { Equp2 }
  | EQUN1                                                  { Equn1 }
  | EQUN2                                                  { Equn2 }
  | ITEP1                                                  { Itep1 }
  | ITEP2                                                  { Itep2 }
  | ITEN1                                                  { Iten1 }
  | ITEN2                                                  { Iten2 }
  | EQRE                                                   { Eqre  }
  | EQTR                                                   { Eqtr  }
  | EQCO                                                   { Eqco  }
  | EQCP                                                   { Eqcp  }
  | DLGE                                                   { Dlge  }
  | LAGE                                                   { Lage  }
  | LATA                                                   { Lata  }
  | DLDE                                                   { Dlde  }
  | LADE                                                   { Lade  }
  | FINS                                                   { Fins  }
  | EINS                                                   { Eins  }
  | SKEA                                                   { Skea  }
  | SKAA                                                   { Skaa  }
  | QNTS                                                   { Qnts  }
  | QNTM                                                   { Qntm  }
  | RESO                                                   { Reso  }
  | AND                                                    { And   }
  | NOR                                                    { Nor   }
  | OR                                                     { Or    }
  | NAND                                                   { Nand  }
  | XOR1                                                   { Xor1  }
  | XOR2                                                   { Xor2  }
  | NXOR1                                                  { Nxor1 }
  | NXOR2                                                  { Nxor2 }
  | IMP                                                    { Imp   }
  | NIMP1                                                  { Nimp1 }
  | NIMP2                                                  { Nimp2 }
  | EQU1                                                   { Equ1  }
  | EQU2                                                   { Equ2  }
  | NEQU1                                                  { Nequ1 }
  | NEQU2                                                  { Nequ2 }
  | ITE1                                                   { Ite1  }
  | ITE2                                                   { Ite2  }
  | NITE1                                                  { Nite1 }
  | NITE2                                                  { Nite2 }
  | TPAL                                                   { Tpal  }
  | TLAP                                                   { Tlap  }
  | TPLE                                                   { Tple  }
  | TPNE                                                   { Tpne  }
  | TPDE                                                   { Tpde  }
  | TPSA                                                   { Tpsa  }
  | TPIE                                                   { Tpie  }
  | TPMA                                                   { Tpma  }
  | TPBR                                                   { Tpbr  }
  | TPBE                                                   { Tpbe  }
  | TPSC                                                   { Tpsc  }
  | TPPP                                                   { Tppp  }
  | TPQT                                                   { Tpqt  }
  | TPQS                                                   { Tpqs  }
  | TPSK                                                   { Tpsk  }
  | SUBP                                                   { Subp  }
;

clause:
  | LPAR          RPAR                                     { [] }
  | LPAR lit_list RPAR                                     { $2 }
;

lit_list:
  | lit                                                    { [$1] }
  | lit lit_list                                           { $1::$2 }
;

lit:   /* returns a SmtAtom.Form.t */
  | name_term                                              { lit_of_atom_form_lit rf $1 }
  | LPAR NOT lit RPAR                                      { Form.neg $3 }
;

name_term:   /* returns a SmtAtom.Form.pform or a SmtAtom.hatom */
  | SHARP INT                                              { get_solver $2 }
  | SHARP INT COLON LPAR term RPAR                         { let res = $5 in add_solver $2 res; res }
  | TRUE                                                   { Form Form.pform_true }
  | FALS                                                   { Form Form.pform_false }
  | VAR                                                    { Atom (Atom.get ra (Aapp (get_fun $1,[||]))) }
  | BINDVAR                                                { Hashtbl.find hlets $1 }
  | INT                                                    { Atom (Atom.hatom_Z_of_int ra $1) }
  | BIGINT                                                 { Atom (Atom.hatom_Z_of_bigint ra $1) }
;

term:   /* returns a SmtAtom.Form.pform or a SmtAtom.hatom */
  | LPAR term RPAR                                         { $2 }

  /* Formulae */
  | TRUE                                                   { Form Form.pform_true }
  | FALS                                                   { Form Form.pform_false }
  | AND lit_list                                           { Form (Fapp (Fand, Array.of_list $2)) }
  | OR lit_list                                            { Form (Fapp (For, Array.of_list $2)) }
  | IMP lit_list                                           { Form (Fapp (Fimp, Array.of_list $2)) }
  | XOR lit_list                                           { Form (Fapp (Fxor, Array.of_list $2)) }
  | ITE lit_list                                           { Form (Fapp (Fite, Array.of_list $2)) }

  /* Atoms */
  | INT                                                    { Atom (Atom.hatom_Z_of_int ra $1) }
  | BIGINT                                                 { Atom (Atom.hatom_Z_of_bigint ra $1) }
  | LT name_term name_term                                 { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_lt ra h1 h2) | _,_ -> assert false }
  | LEQ name_term name_term                                { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_le ra h1 h2) | _,_ -> assert false }
  | GT name_term name_term                                 { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_gt ra h1 h2) | _,_ -> assert false }
  | GEQ name_term name_term                                { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_ge ra h1 h2) | _,_ -> assert false }
  | PLUS name_term name_term                               { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_plus ra h1 h2) | _,_ -> assert false }
  | MULT name_term name_term                               { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_mult ra h1 h2) | _,_ -> assert false }
  | MINUS name_term name_term                              { match $2,$3 with |Atom h1, Atom h2 -> Atom (Atom.mk_minus ra h1 h2) | _,_ -> assert false }
  | MINUS name_term                                        { match $2 with | Atom h -> Atom (Atom.mk_opp ra h) | _ -> assert false }
  | OPP name_term                                          { match $2 with | Atom h -> Atom (Atom.mk_opp ra h) | _ -> assert false }
  | DIST args                                              { let a = Array.of_list $2 in Atom (Atom.mk_distinct ra (Atom.type_of a.(0)) a) }
  | VAR                                                    { Atom (Atom.get ra (Aapp (get_fun $1, [||]))) }
  | VAR args                                               { Atom (Atom.get ra (Aapp (get_fun $1, Array.of_list $2))) }

  /* Both */
  | EQ name_term name_term                                 { let t1 = $2 in let t2 = $3 in match t1,t2 with | Atom h1, Atom h2 when (match Atom.type_of h1 with | Tbool -> false | _ -> true) -> Atom (Atom.mk_eq ra (Atom.type_of h1) h1 h2) | _, _ -> Form (Fapp (Fiff, [|lit_of_atom_form_lit rf t1; lit_of_atom_form_lit rf t2|])) }
  | LET LPAR bindlist RPAR name_term                       { $3; $5 }
  | BINDVAR                                                { Hashtbl.find hlets $1 }
;

bindlist:
  | LPAR BINDVAR name_term RPAR                            { Hashtbl.add hlets $2 $3 }
  | LPAR BINDVAR lit RPAR                                  { Hashtbl.add hlets $2 (Lit $3) }
  | LPAR BINDVAR name_term RPAR bindlist                   { Hashtbl.add hlets $2 $3; $5 }
  | LPAR BINDVAR lit RPAR bindlist                         { Hashtbl.add hlets $2 (Lit $3); $5 }

args:
  | name_term                                              { match $1 with Atom h -> [h] | _ -> assert false }
  | name_term args                                         { match $1 with Atom h -> h::$2 | _ -> assert false }
;

clause_ids_params:
  | int_list                                               { $1 }
;

int_list:
  | INT                                                    { [$1] }
  | INT int_list                                           { let x1 = $1 in let x2 = $2 in x1::x2 }
;

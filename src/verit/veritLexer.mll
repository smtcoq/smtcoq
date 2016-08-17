(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


{
  open VeritParser
  exception Eof

  let typ_table = Hashtbl.create 53
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add typ_table kwd tok)
      [ "input", INPU;
        "deep_res", DEEP;
        "true", TRUE;
        "false", FALS;
        "and_pos", ANDP;
        "and_neg", ANDN;
        "or_pos", ORP;
        "or_neg", ORN;
        "xor_pos1", XORP1;
        "xor_pos2", XORP2;
        "xor_neg1", XORN1;
        "xor_neg2", XORN2;
        "implies_pos", IMPP;
        "implies_neg1", IMPN1;
        "implies_neg2", IMPN2;
        "equiv_pos1", EQUP1;
        "equiv_pos2", EQUP2;
        "equiv_neg1", EQUN1;
        "equiv_neg2", EQUN2;
        "ite_pos1", ITEP1;
        "ite_pos2", ITEP2;
        "ite_neg1", ITEN1;
        "ite_neg2", ITEN2;
        "eq_reflexive", EQRE;
        "eq_transitive", EQTR;
        "eq_congruent", EQCO;
        "eq_congruent_pred", EQCP;
        "dl_generic", DLGE;
        "lia_generic", LAGE;
        "la_generic", LAGE;
        "la_tautology", LATA;
        "dl_disequality", DLDE;
        "la_disequality", LADE;
        "forall_inst", FINS;
        "exists_inst", EINS;
        "skolem_ex_ax", SKEA;
        "skolem_all_ax", SKAA;
        "qnt_simplify_ax", QNTS;
        "qnt_merge_ax", QNTM;
        "resolution", RESO;
        "weaken", WEAK;
        "and", AND;
        "not_or", NOR;
        "or", OR;
        "not_and", NAND;
        "xor1", XOR1;
        "xor2", XOR2;
        "not_xor1", NXOR1;
        "not_xor2", NXOR2;
        "implies", IMP;
        "not_implies1", NIMP1;
        "not_implies2", NIMP2;
        "equiv1", EQU1;
        "equiv2", EQU2;
        "not_equiv1", NEQU1;
        "not_equiv2", NEQU2;
        "ite1", ITE1;
        "ite2", ITE2;
        "not_ite1", NITE1;
        "not_ite2", NITE2;
        "tmp_alphaconv", TPAL;
        "tmp_LA_pre", TLAP;
        "tmp_let_elim", TPLE;
        "tmp_nary_elim", TPNE;
        "tmp_distinct_elim", TPDE;
        "tmp_simp_arith", TPSA;
        "tmp_ite_elim", TPIE;
        "tmp_macrosubst", TPMA;
        "tmp_betared", TPBR;
        "tmp_bfun_elim", TPBE;
        "tmp_sk_connector", TPSC;
        "tmp_pm_process", TPPP;
        "tmp_qnt_tidy", TPQT;
        "tmp_qnt_simplify", TPQS;
        "tmp_skolemize", TPSK;
        "subproof", SUBP;
        "flatten", FLAT;
        "hole", HOLE;
        "bbvar", BBVA;
        "bbconst", BBCONST;
        "bbeq", BBEQ;
        "bbop", BBOP;
        "bbnot", BBNOT;
        "bbneg", BBNEG;
        "bbadd", BBADD;
        "bbmul", BBMUL;
        "bbult", BBULT;
        "bbslt", BBSLT;
        "bbconcat", BBCONC;
        "bvand", BVAND;
        "bvor", BVOR;
        "bvxor", BVXOR;
        "bvadd", BVADD;
        "bvmul", BVMUL;
        "bvult", BVULT;
        "bvslt", BVSLT;
        "not", NOT;
        "xor", XOR;
        "ite", ITE;
        "let", LET;
        "distinct", DIST;
        "bbT", BBT;
        "bitof", BITOF;
        "bvnot", BVNOT;
        "bvneg", BVNEG;
        "concat", BVCONC;
        "select", SELECT;
        "diff", DIFF;
        "store", STORE;
        "row1", ROW1;
        "row2", ROW2;
        "ext", EXTE;
      ]
}


let digit = [ '0'-'9' ]
let bit = [ '0'-'1' ]
let bitvector = '#' 'b' bit+
let alpha = [ 'a'-'z' 'A' - 'Z' ]
let blank = [' ' '\t']
let newline = ['\n' '\r']
let var = alpha (alpha|digit|'_')*
let bindvar = '?' var+
let int = '-'? digit+


rule token = parse
  | blank +                    { token lexbuf }
  | newline +                  { EOL }

  | ":"                        { COLON }
  | "#" (int as i)             { SHARPINT (int_of_string i) }

  | "("                        { LPAR }
  | ")"                        { RPAR }

  | "["                        { LBRACKET }
  | "]"                        { RBRACKET }

  | "="                        { EQ }
  | "<"                        { LT }
  | "<="                       { LEQ }
  | ">"                        { GT }
  | ">="                       { GEQ }
  | "+"                        { PLUS }
  | "-"                        { MINUS }
  | "~"                        { OPP }
  | "*"                        { MULT }
  | "=>"                       { IMP }

  | "Formula is Satisfiable"   { SAT }

  | (int as i)                 { try INT (int_of_string i)
	                         with _ -> 
                                   BIGINT (Big_int.big_int_of_string i) }
  | bitvector as bv            { BITV bv }
  | var                        { let v = Lexing.lexeme lexbuf in
                                 try Hashtbl.find typ_table v with
                                   | Not_found -> VAR v }
  | bindvar as v               { BINDVAR v }

  | eof                        { raise Eof }

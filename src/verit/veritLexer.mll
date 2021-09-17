{
(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


  open VeritParser
  exception Eof

  let typ_table = Hashtbl.create 53
  let _ =
    List.iter (fun (kwd, tok) -> Hashtbl.add typ_table kwd tok)
      [
      (* SMTLIB formulas *)
        "true", TRUE;
        "false", FALSE;
        "not", NOT;
        "=>", IMPLIES;
        "and", AND;
        "or", OR;
        "xor", XOR;

      (*Basic proof rules*)
        "assume", ASSUME;
        (*true*)
        (*false*)
        "not_not", NOTNOT;

      (* Resolution rules and clause simplifications *)
        "th_resolution", THRESO;
        "resolution", RESO;
        "tautology", TAUT;
        "contraction", CONT;

      (* Equality and congruence reasoning *)
        "refl", REFL;
        "trans", TRANS;
        "cong", CONG;
        "eq_reflexive", EQRE;
        "eq_transitive", EQTR;
        "eq_congruent", EQCO;
        "eq_congruent_pred", EQCP;

      (* Clausification of Boolean operators *)
        (*and*)
        "not_or", NOTOR;
        (*or*)
        "not_and", NOTAND;
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

      (* Clausification of ITE *)
        "ite1", ITE1;
        "ite2", ITE2;
        "ite_pos1", ITEP1;
        "ite_pos2", ITEP2;
        "ite_neg1", ITEN1;
        "ite_neg2", ITEN2;
        "not_ite1", NITE1;
        "not_ite2", NITE2;

      (* Simplifications on Boolean operators *)
        "connective_def", CONNDEF;
        "and_simplify", ANDSIMP;
        "or_simplify", ORSIMP;
        "not_simplify", NOTSIMP;
        "implies_simplify", IMPSIMP;
        "equiv_simplify", EQSIMP;
        "bool_simplify", BOOLSIMP;
        "ac_simp", ACSIMP;

      (* Simplifications on ITE operators *)
        "ite_simplify", ITESIMP;

      (* Simplifications on equalities *)
        "eq_simplify", EQUALSIMP;
      ]
}

(*
let digit = [ '0'-'9' ]
let bit = [ '0'-'1' ]
let bitvector = '#' 'b' bit+
let alpha = [ 'a'-'z' 'A' - 'Z' ]
let blank = [' ' '\t']
let newline = ['\n' '\r']
let var = alpha (alpha|digit|'_')*
let atvar = '@' var
let bindvar = '?' var+
let int = '-'? digit+
*)
let lf = '\010'
let lf_cr = ['\010' '\013']
let dos_newline = "\013\010"
let blank = [' ' '\009' '\012']
let wspace = ['\009' '\010' '\013' '\032']
let printable_char = ['\032'-'\126' '\128'-'\255']
let digit = ['0'-'9']
let non_zero_digit = ['1'-'9']
let hexdigit = digit | ['a'-'f' 'A'-'F']
let bindigit = ['0'-'1']
let letter = ['a'-'z' 'A'-'Z']
let spl = [ '+' '-' '/' '*' '=' '%' '?' '!' '.' '$' '_' '~' '&' '^' '<' '>' '@']
let int = '-'? digit+

let simple_symbol = (letter | spl) (letter | digit | spl)*
let symbol = simple_symbol | '|' (wspace | printable_char # ['|' '\\'])* '|'
let numeral = '0' | non_zero_digit digit*
let decimal = numeral '.' '0'* numeral
let hexadecimal = '#' 'x' hexdigit+
let binary = '#' 'b' bindigit+
let qstring = '"' (wspace | printable_char)* '"'
let spec_constant = numeral | decimal | hexadecimal | binary | qstring
let index = numeral | symbol
let isymbol = '(' '_' symbol index+ ')'
let keyword = ':' simple_symbol

rule token = parse
  | blank +                   { token lexbuf }
  | lf | dos_newline          { EOL }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | ":" { COLON }
  | "!" { BANG }
  | ":rule" { COLRULE }
  | ":step" { COLSTEP }
  | ":args" { COLARGS }
  | ":premises" { COLPREMISES }
  | "assume" { ASSUME }
  | "step" { STEP }
  | "anchor" { ANCHOR }
  | "define_fun" { DEFINEFUN }
  | "cl" { CL }
  | "as" { ASTOK }
  | "choice" { CHOICE }
  | "let" { LET }
  | "forall" { FORALL }
  | "exists" { EXISTS }
  | "match" { MATCH }
  | "Formula is Satisfiable" { SAT }
  | "=" { EQ }
  | spec_constant   { let s = Lexing.lexeme lexbuf in 
                      SPECCONST s }
  | keyword         { let k = Lexing.lexeme lexbuf in 
                      try Hashtbl.find typ_table k with
                      | Not_found -> KEYWORD k }
  | symbol          { let s = Lexing.lexeme lexbuf in 
                      try Hashtbl.find typ_table s with
                      | Not_found -> SYMBOL s }
  | isymbol         { let i = Lexing.lexeme lexbuf in 
                      ISYMBOL i }
  | (int as i)      { try INT (int_of_string i)
	                    with _ -> 
                        BIGINT (Big_int.big_int_of_string i) }
  | eof             { raise Eof }

%{
(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


  open SmtBtype
  open SmtAtom
  open SmtForm
  open VeritSyntax

  let symbol_to_id s = 
    let l = (String.length s) - 1 in
    int_of_string (String.sub s 1 l)

(*  let parse_bv s =
    let l = ref [] in
    for i = 2 to String.length s - 1 do
      match s.[i] with
      | '0' -> l := false :: !l
      | '1' -> l := true :: !l
      | _ -> assert false
    done;
    !l*)

%}


/*
  définition des lexèmes
*/

%token <string> SYMBOL
%token <string> ISYMBOL
%token <string> SPECCONST
%token <string> KEYWORD
%token <string> STRING
%token <int> INT
%token <Big_int.big_int> BIGINT

%token LPAREN RPAREN EOF EOL COLON BANG
%token COLRULE COLSTEP COLARGS COLPREMISES SAT
%token ASSUME STEP ANCHOR DEFINEFUN CL ASTOK CHOICE
%token LET FORALL EXISTS MATCH

%token TRUE FALSE NOT IMPLIES AND OR XOR
%token NOTNOT
%token THRESO RESO TAUT CONT
%token REFL TRANS CONG EQRE EQTR EQCO EQCP
%token NOTOR NOTAND XOR1 XOR2 NXOR1 NXOR2 IMP NIMP1 NIMP2
%token EQU1 EQU2 NEQU1 NEQU2 ANDP ANDN ORP ORN
%token XORP1 XORP2 XORN1 XORN2 IMPP IMPN1 IMPN2
%token EQUP1 EQUP2 EQUN1 EQUN2
%token ITE1 ITE2 ITEP1 ITEP2 ITEN1 ITEN2 NITE1 NITE2
%token CONNDEF ANDSIMP ORSIMP NOTSIMP IMPSIMP
%token EQSIMP BOOLSIMP ACSIMP
%token ITESIMP
%token EQUALSIMP

%type <int> line
%start line

%%

line:
  | SAT EOL { raise Sat }
  | LPAREN ASSUME SYMBOL lit_list RPAREN EOL
    { let id = symbol_to_id $3 in
      let _, l = list_dec $4 in
      mk_clause (id, Assume, l, []) }
  | LPAREN STEP SYMBOL clause COLRULE rulename RPAREN EOL
    { let id = symbol_to_id $3 in
      mk_clause (id, $6, $4, []) }
  | LPAREN STEP SYMBOL clause COLRULE rulename COLPREMISES LPAREN symbol_list RPAREN RPAREN EOL
    { let id = symbol_to_id $3 in
      mk_clause (id, $6, $4, $9) }
  | LPAREN STEP SYMBOL clause COLRULE rulename COLPREMISES LPAREN symbol_list RPAREN
      COLARGS LPAREN int_list RPAREN RPAREN EOL
    { let id = symbol_to_id $3 in
      mk_clause (id, $6, $4, ($9 @ $13)) }
  | LPAREN STEP SYMBOL clause COLRULE rulename COLARGS LPAREN int_list RPAREN RPAREN EOL
    { let id = symbol_to_id $3 in
      mk_clause (id, $6, $4, $9) }
  /*| LPAREN ANCHOR COLSTEP SYMBOL RPAREN { "" }
  | LPAREN ANCHOR COLSTEP SYMBOL COLARGS proof_args RPAREN { "" }
  | LPAREN DEFINEFUN function_def RPAREN { "" }*/
;

symbol_list:
  | SYMBOL { [symbol_to_id $1] }
  | SYMBOL symbol_list { (symbol_to_id $1)::$2 }
;

int_list:
  | INT { [$1] }
  | INT int_list { $1::$2 }
;
/*
  | SAT                                                    { raise Sat }
  | INT COLON LPAR typ clause                   RPAR EOL   { mk_clause ($1,$4,$5,[]) }
  | INT COLON LPAR typ clause clause_ids_params RPAR EOL   { mk_clause ($1,$4,$5,$6) }
  | INT COLON LPAR TPQT LPAR SHARPINT COLON LPAR forall_decl RPAR RPAR INT RPAR EOL { add_solver $6 $9; add_ref $6 $1; mk_clause ($1, Tpqt, [], [$12]) }
  | INT COLON LPAR FINS LPAR SHARPINT COLON LPAR OR LPAR NOT SHARPINT RPAR lit RPAR RPAR RPAR EOL
  { mk_clause ($1, Fins, [snd $14], [get_ref $12]) }
;*/

/*sexpr:
  | SYMBOL { "" }
  | KEYWORD { "" }
  | LPAREN sexpr* RPAREN { "" }
;

attr_val:
  | SPECCONST { "" }
  | SYMBOL { "" }
  | LPAREN sexpr* RPAREN { "" }
;

attr:
  | KEYWORD { "" }
  | KEYWORD attr_val { "" }
;*/

/*ident:
  | SYMBOL { "" }
  | ISYMBOL { "" }
;

sort:
  | ident { "" }
  | ident sort+ { "" }
;*/

/*qual_id:
  | ident { "" }
  | LPAREN AS ident sort RPAREN { "" }
;

var_binding:
  | LPAREN SYMBOL term RPAREN { "" }
;

sorted_var:
  | LPAREN SYMBOL term RPAREN { "" }
;*/
 
/*pattern:
  | SYMBOL { "" }
  | LPAREN SYMBOL SYMBOL+ RPAREN { "" }
;*/

/*match_case:
  | LPAREN pattern term RPAREN { "" }
;*/

clause:
  | LPAREN CL RPAREN { [] }
  | LPAREN CL lit_list RPAREN  { let _, l = list_dec $3 in l }
;

lit_list:
  | lit                                                    { [$1] }
  | lit lit_list                                           { $1::$2 }
;

lit:   /* returns a SmtAtom.Form.t option */
  | term                                              
  { let decl, t = $1 in decl, Form.lit_of_atom_form_lit rf (decl, t) }
  | LPAREN NOT lit RPAREN                                      { apply_dec Form.neg $3 }
;

term: /* term will produce many shift/reduce conflicts */
  | TRUE                        { true, Form.Form Form.pform_true }
  | FALSE                       { true, Form.Form Form.pform_false }
  /*| LPAREN NOT term RPAREN      { apply_dec Form.neg $3 }*/
  | LPAREN IMPLIES lit_list RPAREN 
    { apply_dec (fun x -> Form.Form (Fapp (Fimp, Array.of_list x))) 
                (list_dec $3) }
  | LPAREN AND lit_list RPAREN 
    { apply_dec (fun x -> Form.Form (Fapp (Fand, Array.of_list x))) 
                (list_dec $3) }
  | LPAREN OR lit_list RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (For, Array.of_list x))) 
                (list_dec $3) }
  | LPAREN XOR lit_list RPAREN
    { apply_dec (fun x -> Form.Form (Fapp (Fxor, Array.of_list x))) 
                (list_dec $3) }
  /*| SPECCONST { "" }
  | qual_id { "" }
  | LPAREN qual_id term+ RPAREN { "" }
  | LPAREN LET LPAREN var_binding+ RPAREN term RPAREN { "" }
  | LPAREN FORALL LPAREN sorted_var+ RPAREN term RPAREN { "" }
  | LPAREN EXISTS LPAREN sorted_var+ RPAREN term RPAREN { "" }
  | LPAREN MATCH term LPAREN match_case+ RPAREN RPAREN { "" }
  | LPAREN BANG term attr+ RPAREN { "" }*/
;

/*function_def:
  | SYMBOL LPAREN sorted_var* RPAREN sort term { "" }
;*/

rulename: 
  | ASSUME { Assume } /* Inpu */
  | TRUE { True }
  | FALSE { Fals }
/*  | NOTNOT { Notnot }
  | THRESO { Threso } */ 
  | RESO { Reso }
/*  | TAUT { Taut }
  | CONT { Cont }
  | REFL { Refl }
  | TRANS { Trans }
  | CONG { Cong } */
  | EQRE { Eqre }
  | EQTR { Eqtr }
  | EQCO { Eqco }
  | EQCP { Eqcp }
  | AND { And }
  | NOTOR { Nor }
  | OR { Or }
  | NOTAND { Nand }
  | XOR1 { Xor1 }
  | XOR2 { Xor2 }
  | NXOR1 { Nxor1 }
  | NXOR2 { Nxor2 }
  | IMP { Imp }
  | NIMP1 { Nimp1 }
  | NIMP2 { Nimp2 }
  | EQU1 { Equ1 }
  | EQU2 { Equ2 }
  | NEQU1 { Nequ1 }
  | NEQU2 { Nequ2 }
  | ANDP { Andp }
  | ANDN { Andn }
  | ORP { Orp }
  | ORN { Orn }
  | XORP1 { Xorp1 }
  | XORP2 { Xorp2 }
  | XORN1 { Xorn1 }
  | XORN2 { Xorn2 }
  | IMPP { Impp }
  | IMPN1 { Impn1 }
  | IMPN2 { Impn2 }
  | EQUP1 { Equp1 }
  | EQUP2 { Equp2 }
  | EQUN1 { Equn1 }
  | EQUN2 { Equn2 }
  | ITE1 { Ite1 }
  | ITE2 { Ite2 }
  | ITEP1 { Itep1 }
  | ITEP2 { Itep2 }
  | ITEN1 { Iten1 }
  | ITEN2 { Iten2 }
  | NITE1 { Nite1 }
  | NITE2 { Nite2 }
/*  | CONNDEF { Conndef }
  | ANDSIMP { Andsimp }
  | ORSIMP { Orsimp }
  | NOTSIMP { Notsimp }
  | IMPSIMP { Impsimp }
  | EQSIMP { Eqsimp }
  | BOOLSIMP { Boolsimp }
  | ACSIMP { Acsimp }
  | ITESIMP { Itesimp }
  | EQUALSIMP { Equalsimp } */
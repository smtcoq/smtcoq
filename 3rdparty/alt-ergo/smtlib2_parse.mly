/**************************************************************************/
/*                                                                        */
/*     SMTCoq, originally belong to The Alt-ergo theorem prover           */
/*     Copyright (C) 2006-2010                                            */
/*                                                                        */
/*     Sylvain Conchon                                                    */
/*     Evelyne Contejean                                                  */
/*     Stephane Lescuyer                                                  */
/*     Mohamed Iguernelala                                                */
/*     Alain Mebsout                                                      */
/*                                                                        */
/*     CNRS - INRIA - Universite Paris Sud                                */
/*                                                                        */
/*   This file is distributed under the terms of the CeCILL-C licence     */
/*                                                                        */
/**************************************************************************/


%{
   open Smtlib2_ast

   let loc () = symbol_start_pos (), symbol_end_pos ()

%}

%start main
%start term
%start sort

/* general */
%token EXCLIMATIONPT
%token UNDERSCORE
%token AS
%token EXISTS
%token FORALL
%token LET

/* commands */
%token SETLOGIC
%token SETOPTION
%token SETINFO
%token DECLARESORT
%token DEFINESORT
%token DECLAREFUN
%token DEFINEFUN
%token PUSH
%token POP
%token ASSERT
%token CHECKSAT
%token GETASSERT
%token GETPROOF
%token GETUNSATCORE
%token GETVALUE
%token GETASSIGN
%token GETOPTION
%token GETINFO
%token EXIT

/* Other tokens */
%token LPAREN
%token RPAREN
%token EOF

%token <string> NUMERAL
%token <string> DECIMAL
%token <string> HEXADECIMAL
%token <string> BINARY
%token <string> STRINGLIT
%token <string> ASCIIWOR
%token <string> KEYWORD
%token <string> SYMBOL


%type <Smtlib2_ast.commands option> main
%type <Smtlib2_ast.an_option> an_option
%type <Smtlib2_ast.attribute> attribute
%type <Smtlib2_ast.attributevalue> attributevalue
%type <Smtlib2_ast.command> command
%type <Smtlib2_ast.commands> commands
%type <Smtlib2_ast.identifier> identifier
%type <Smtlib2_ast.infoflag> infoflag
%type <Smtlib2_ast.qualidentifier> qualidentifier
%type <Smtlib2_ast.sexpr> sexpr
%type <Smtlib2_ast.sort> sort
%type <Smtlib2_ast.sortedvar> sortedvar
%type <Smtlib2_ast.specconstant> specconstant
%type <Smtlib2_ast.symbol> symbol
%type <Smtlib2_ast.term> term
%type <Smtlib2_ast.varbinding> varbinding

/* %type <Smtlib2_ast.attributevalsexpr_attributevalue_sexpr5> attributevalsexpr_attributevalue_sexpr5 */
/* %type <Smtlib2_ast.commanddeclarefun_command_sort13> commanddeclarefun_command_sort13 */
/* %type <Smtlib2_ast.commanddefinefun_command_sortedvar15> commanddefinefun_command_sortedvar15 */
/* %type <Smtlib2_ast.commanddefinesort_command_symbol11> commanddefinesort_command_symbol11 */
/* %type <Smtlib2_ast.commandgetvalue_command_term24> commandgetvalue_command_term24 */
/* %type <Smtlib2_ast.commands_commands_command30> commands_commands_command30 */
/* %type <Smtlib2_ast.sexprinparen_sexpr_sexpr41> sexprinparen_sexpr_sexpr41 */
/* %type <Smtlib2_ast.sortidsortmulti_sort_sort44> sortidsortmulti_sort_sort44 */
/* %type <Smtlib2_ast.termexclimationpt_term_attribute64> termexclimationpt_term_attribute64 */
/* %type <Smtlib2_ast.termexiststerm_term_sortedvar62> termexiststerm_term_sortedvar62 */
/* %type <Smtlib2_ast.termforallterm_term_sortedvar60> termforallterm_term_sortedvar60 */
/* %type <Smtlib2_ast.termletterm_term_varbinding58> termletterm_term_varbinding58 */
/* %type <Smtlib2_ast.termqualidterm_term_term56> termqualidterm_term_term56 */
/* %type <Smtlib2_ast.idunderscoresymnum_identifier_numeral33> idunderscoresymnum_identifier_numeral33 */
%%

main:
| commands { Some($1) }
| EOF { None }
;

an_option:
| attribute { AnOptionAttribute(loc_attribute $1, $1) }
;

attribute:
| KEYWORD { AttributeKeyword(loc (), $1) }
| KEYWORD attributevalue { AttributeKeywordValue(loc (), $1, $2) }
;

sexpr_list:
/*sexprinparen_sexpr_sexpr41:*/
/*attributevalsexpr_attributevalue_sexpr5:*/
| { (loc (), []) }
| sexpr sexpr_list { let (_, l1) = $2 in (loc_sexpr $1, ($1)::(l1)) }
;

attributevalue:
| specconstant { AttributeValSpecConst(loc_specconstant $1, $1) }
| symbol { AttributeValSymbol(loc_symbol $1, $1) }
| LPAREN sexpr_list RPAREN { AttributeValSexpr(loc (), $2) }
;

symbol_list: /*commanddefinesort_command_symbol11:*/
| { (loc (), []) }
| symbol symbol_list { let (_, l1) = $2 in (loc_symbol $1, ($1)::(l1)) }
;

sort_list0: /*commanddeclarefun_command_sort13:*/
| { (loc (), []) }
| sort sort_list0 { let (_, l1) = $2 in (loc_sort $1, ($1)::(l1)) }
;

sortedvar_list: /*commanddefinefun_command_sortedvar15:*/
| { (loc (), []) }
| sortedvar sortedvar_list
    { let (_, l1) = $2 in (loc_sortedvar $1, ($1)::(l1)) }
;

command:
| LPAREN SETLOGIC symbol RPAREN
    { CSetLogic(loc (), $3) }
| LPAREN SETOPTION an_option RPAREN
    { CSetOption(loc (), $3) }
| LPAREN SETINFO attribute RPAREN
    { CSetInfo(loc (), $3) }
| LPAREN DECLARESORT symbol NUMERAL RPAREN
    { CDeclareSort(loc (), $3, $4) }
| LPAREN DEFINESORT symbol LPAREN symbol_list RPAREN sort RPAREN
    { CDefineSort(loc (), $3, $5, $7) }
| LPAREN DECLAREFUN symbol LPAREN sort_list0 RPAREN sort RPAREN
    { CDeclareFun(loc (), $3, $5, $7) }
| LPAREN DEFINEFUN symbol LPAREN sortedvar_list RPAREN sort term RPAREN
    { CDefineFun(loc (), $3, $5, $7, $8) }
| LPAREN PUSH NUMERAL RPAREN
    { CPush(loc (), $3) }
| LPAREN POP NUMERAL RPAREN
    { CPop(loc (), $3) }
| LPAREN ASSERT term RPAREN
    { CAssert(loc (), $3) }
| LPAREN CHECKSAT RPAREN
    { CCheckSat(loc ()) }
| LPAREN GETASSERT RPAREN
    { CGetAssert(loc ()) }
| LPAREN GETPROOF RPAREN
    { CGetProof(loc ()) }
| LPAREN GETUNSATCORE RPAREN
    { CGetUnsatCore(loc ()) }
| LPAREN GETVALUE LPAREN term_list1 RPAREN RPAREN
    { CGetValue(loc (), $4) }
| LPAREN GETASSIGN RPAREN
    { CGetAssign(loc ()) }
| LPAREN GETOPTION KEYWORD RPAREN
    { CGetOption(loc (), $3) }
| LPAREN GETINFO infoflag RPAREN
    { CGetInfo(loc (), $3) }
| LPAREN EXIT RPAREN
    { CExit(loc ()) }
;


command_list: /*commands_commands_command30:*/
| { (loc (), []) }
| command command_list { let (_, l1) = $2 in (loc_command $1, ($1)::(l1)) }
;

commands:
| command_list { Commands(loc_couple $1, $1) }
;

numeral_list: /*idunderscoresymnum_identifier_numeral33:*/
| NUMERAL { (loc (), ($1)::[]) }
| NUMERAL numeral_list { let (_, l1) = $2 in (loc (), ($1)::(l1)) }
;

identifier:
| symbol { IdSymbol(loc_symbol $1, $1) }
| LPAREN UNDERSCORE symbol numeral_list RPAREN
    { IdUnderscoreSymNum(loc (), $3, $4) }
;

infoflag:
| KEYWORD { InfoFlagKeyword(loc (), $1) }
;

qualidentifier:
| identifier { QualIdentifierId(loc_identifier $1, $1) }
| LPAREN AS identifier sort RPAREN { QualIdentifierAs(loc (), $3, $4) }
;

sexpr:
| specconstant { SexprSpecConst(loc_specconstant $1, $1) }
| symbol { SexprSymbol(loc_symbol $1, $1) }
| KEYWORD { SexprKeyword(loc (), $1) }
| LPAREN sexpr_list RPAREN { SexprInParen(loc (), $2) }
;


sort_list1: /*sortidsortmulti_sort_sort44:*/
| sort { (loc_sort $1, ($1)::[]) }
| sort sort_list1 { let (_, l1) = $2 in (loc_sort $1, ($1)::(l1)) }
;

sort:
| identifier { SortIdentifier(loc_identifier $1, $1) }
| LPAREN identifier sort_list1 RPAREN { SortIdSortMulti(loc (), $2, $3) }
;

sortedvar:
| LPAREN symbol sort RPAREN { SortedVarSymSort(loc (), $2, $3) }
;

specconstant:
| DECIMAL { SpecConstsDec(loc (), $1) }
| NUMERAL { SpecConstNum(loc (), $1) }
| STRINGLIT { SpecConstString(loc (), $1) }
| HEXADECIMAL { SpecConstsHex(loc (), $1) }
| BINARY { SpecConstsBinary(loc (), $1) }
;

symbol:
| SYMBOL { Symbol(loc (), $1) }
| ASCIIWOR { SymbolWithOr(loc (), $1) }
;

term_list1:
/*termqualidterm_term_term56:*/
/*commandgetvalue_command_term24:*/
| term { (loc_term $1, ($1)::[]) }
| term term_list1 { let (_, l1) = $2 in (loc_term $1, ($1)::(l1)) }
;

varbinding_list1: /*termletterm_term_varbinding58:*/
| varbinding { (loc_varbinding $1, ($1)::[]) }
| varbinding varbinding_list1
    { let (_, l1) = $2 in (loc_varbinding $1, ($1)::(l1)) }
;

sortedvar_list1:
/*termforallterm_term_sortedvar60:*/
/*termexiststerm_term_sortedvar62:*/
| sortedvar { (loc_sortedvar $1, ($1)::[]) }
| sortedvar sortedvar_list1
    { let (_, l1) = $2 in (loc_sortedvar $1, ($1)::(l1)) }
;

attribute_list1: /*termexclimationpt_term_attribute64:*/
| attribute { (loc_attribute $1, ($1)::[]) }
| attribute attribute_list1
    { let (_, l1) = $2 in (loc_attribute $1, ($1)::(l1)) }
;

term:
| specconstant
    { TermSpecConst(loc_specconstant $1, $1) }
| qualidentifier
    { TermQualIdentifier(loc_qualidentifier $1, $1) }
| LPAREN qualidentifier term_list1 RPAREN
    { TermQualIdTerm(loc (), $2, $3) }
| LPAREN LET LPAREN varbinding_list1 RPAREN term RPAREN
    { TermLetTerm(loc (), $4, $6) }
| LPAREN FORALL LPAREN sortedvar_list1 RPAREN term RPAREN
    { TermForAllTerm(loc (), $4, $6) }
| LPAREN EXISTS LPAREN sortedvar_list1 RPAREN term RPAREN
    { TermExistsTerm(loc (), $4, $6) }
| LPAREN EXCLIMATIONPT term attribute_list1 RPAREN
    { TermExclimationPt(loc (), $3, $4) }
;

varbinding:
| LPAREN symbol term RPAREN { VarBindingSymTerm(loc (), $2, $3) }
;

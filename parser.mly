%{
  (* Parser: Grammar Specification for Parsing S-expressions *)

open Ast
open Lexing
open Format

let parse_failure what =
  let pos = Parsing.symbol_start_pos () in
  let msg =
    Printf.sprintf "Sexplib.Parser: failed to parse line %d char %d: %s"
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol) what in
  failwith msg

%}

%token <string> STRING
%token <Big_int.big_int> INT
%token LPAREN RPAREN EOF HASH_SEMI
%token LAMBDA PI BIGLAMBDA COLON
%token CHECK DEFINE DECLARE
%token MPQ MPZ HOLE TYPE KIND
%token SC

%start proof
%type <Ast.proof> proof

%start one_command
%type <Ast.command> one_command

%start sexp
%type <Type.t> sexp

%start sexp_opt
%type <Type.t option> sexp_opt

%start sexps
%type <Type.t list> sexps

%start rev_sexps
%type <Type.t list> rev_sexps

%%
sexp:
| sexp_comments sexp_but_no_comment { $2 }
| sexp_but_no_comment { $1 }

sexp_but_no_comment
  : STRING { Type.Atom $1 }
  | LPAREN RPAREN { Type.List [] }
  | LPAREN rev_sexps_aux RPAREN { Type.List (List.rev $2) }
  | error { parse_failure "sexp" }

sexp_comment
  : HASH_SEMI sexp_but_no_comment { () }
  | HASH_SEMI sexp_comments sexp_but_no_comment { () }

sexp_comments
  : sexp_comment { () }
  | sexp_comments sexp_comment { () }

sexp_opt
  : sexp_but_no_comment { Some $1 }
  | sexp_comments sexp_but_no_comment { Some $2 }
  | EOF { None }
  | sexp_comments EOF { None }

rev_sexps_aux
  : sexp_but_no_comment { [$1] }
  | sexp_comment { [] }
  | rev_sexps_aux sexp_but_no_comment { $2 :: $1 }
  | rev_sexps_aux sexp_comment { $1 }

rev_sexps
  : rev_sexps_aux EOF { $1 }
  | EOF { [] }

sexps
  : rev_sexps_aux EOF { List.rev $1 }
  | EOF { [] }
;

term_list:
  | term { [$1]}
  | term term_list { $1 :: $2 }
;

binding:
  | STRING term {
    let s = mk_symbol $1 $2 in
    register_symbol s;
    s
  }
;

untyped_sym:
  | STRING {
    let s = mk_symbol $1 (mk_hole_hole ()) in
    register_symbol s;
    s
  }
;


term:
  | TYPE { lfsc_type }
  | KIND { kind }
  | MPQ { mpq }
  | MPZ { mpz }
  | INT { mk_mpz $1 }
  | STRING { mk_const $1 }
  | HOLE { mk_hole_hole () }
  | LPAREN term term_list RPAREN { mk_app $2 $3 }
  | LPAREN LAMBDA untyped_sym term RPAREN
    { let s = $3  in
      let t = $4 in
      let r = mk_lambda s t in
      remove_symbol s;
      r
    }
  | LPAREN LAMBDA HOLE term RPAREN
    { let s = mk_symbol_hole (mk_hole_hole ()) in
      let t = $4 in
      mk_lambda s t }
  | LPAREN BIGLAMBDA binding term RPAREN
    { let s = $3 in
      let t = $4 in
      let r = mk_lambda s t in
      remove_symbol s;
      r
    }
  | LPAREN BIGLAMBDA HOLE term term RPAREN
    { let t = $5 in
      let s = mk_symbol_hole $4 in
      mk_lambda s t }
  | LPAREN PI STRING
    LPAREN SC sexp_but_no_comment sexp_but_no_comment RPAREN term RPAREN
    { $9 }
  | LPAREN PI HOLE
    LPAREN SC sexp_but_no_comment sexp_but_no_comment RPAREN term RPAREN
    { $9 }
  | LPAREN PI binding term RPAREN
    { let s = $3 in
      let t = $4 in
      let r = mk_pi s t in
      remove_symbol s;
      r
    }
  | LPAREN PI HOLE term term RPAREN
    { let s = mk_symbol_hole $4 in
      let t = $5 in
      mk_pi s t }
  | LPAREN COLON term term RPAREN
    { mk_ascr $3 $4 }
;

command:
  | LPAREN CHECK term RPAREN {
    mk_check $3;
    Check $3 }
  | LPAREN DEFINE STRING term RPAREN {
    mk_define $3 $4;
    Define ($3, $4) }
  | LPAREN DECLARE STRING term RPAREN {
    mk_declare $3 $4;
    let d = Declare ($3, $4) in
    (* printf "\n%a\n@." print_command d; *)
    d
  }
;

one_command:
  | command EOF { $1 }
;

command_list:
  | { [] }
  | command command_list { $1 :: $2 }
;


proof:
  | command_list EOF { $1 }
;

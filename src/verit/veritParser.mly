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



  let parse_bv s =
    let l = ref [] in
    for i = 2 to String.length s - 1 do
      match s.[i] with
      | '0' -> l := false :: !l
      | '1' -> l := true :: !l
      | _ -> assert false
    done;
    !l

%}


/*
  définition des lexèmes
*/

%token EOL SAT
%token COLON
%token LPAR RPAR LBRACKET RBRACKET
%token NOT XOR ITE EQ LT LEQ GT GEQ PLUS MINUS MULT OPP LET DIST BBT BITOF BVAND BVOR BVXOR BVADD BVMUL BVULT BVSLT BVULE BVSLE BVCONC BVEXTR BVZEXT BVSEXT BVNOT BVNEG SELECT STORE DIFF BVSHL BVSHR
%token TBOOL TINT
%token<int> TINDEX
%token INPU DEEP TRUE FALS ANDP ANDN ORP ORN XORP1 XORP2 XORN1 XORN2 IMPP IMPN1 IMPN2 EQUP1 EQUP2 EQUN1 EQUN2 ITEP1 ITEP2 ITEN1 ITEN2 EQRE EQTR EQCO EQCP DLGE LAGE LATA DLDE LADE FINS EINS SKEA SKAA QNTS QNTM RESO WEAK AND NOR OR NAND XOR1 XOR2 NXOR1 NXOR2 IMP NIMP1 NIMP2 EQU1 EQU2 NEQU1 NEQU2 ITE1 ITE2 NITE1 NITE2 TPAL TLAP TPLE TPNE TPDE TPSA TPIE TPMA TPBR TPBE TPSC TPPP TPQT TPQS TPSK SUBP FLAT HOLE FORALL BBVA BBCONST BBEXTR BBZEXT BBSEXT BBEQ BBDIS BBOP BBADD BBMUL BBULT BBSLT BBNOT BBNEG BBCONC ROW1 ROW2 EXTE BBSHL BBSHR
%token <int> INT SHARPINT
%token <Big_int.big_int> BIGINT
%token <string> VAR BINDVAR ATVAR BITV

/* return type of the parser: a clause (given a state) */
%type <VeritSyntax.verit_state -> State.smtlib_state -> SmtCertif.clause_id> line
%start line

/* Types of non-terminals */
%type <VeritSyntax.typ> typ
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> SmtAtom.Form.t list> clause
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> (bool * SmtAtom.Form.t) list> lit_list
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> bool * SmtAtom.Form.t> lit
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> bool * SmtAtom.Form.t> nlit
%type <string> var_atvar
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> bool * Form.atom_form_lit> name_term
%type <SmtBtype.btype> tvar
%type <VeritSyntax.quant_state -> (string * SmtBtype.btype) list> var_decl_list
%type <VeritSyntax.verit_state -> State.smtlib_state -> bool * SmtAtom.Form.atom_form_lit> forall_decl
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> bool * Form.atom_form_lit> term
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> bool * Form.atom_form_lit> blit
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> unit> bindlist
%type <VeritSyntax.verit_state -> State.smtlib_state -> VeritSyntax.quant_state -> (bool * Atom.t) list> args
%type <int list> clause_ids_params
%type <int list> int_list


%%

line:
  | SAT                                                    { fun _ _ -> raise Sat }
  | INT COLON LPAR typ clause                   RPAR EOL   { fun st stl -> mk_clause ($1,$4,$5 st stl (VeritSyntax.create_quant_state ()),[]) st }  /* The clause should not contain quantified variables */
  | INT COLON LPAR typ clause clause_ids_params RPAR EOL   { fun st stl -> mk_clause ($1,$4,$5 st stl (VeritSyntax.create_quant_state ()),$6) st }  /* The clause should not contain quantified variables */
  | INT COLON LPAR TPQT LPAR SHARPINT COLON LPAR forall_decl RPAR RPAR INT RPAR EOL { fun st stl -> add_solver $6 ($9 st stl) st; add_ref $6 $1 st; mk_clause ($1, Tpqt, [], [$12]) st }
  | INT COLON LPAR FINS LPAR SHARPINT COLON LPAR OR LPAR NOT SHARPINT RPAR lit RPAR RPAR RPAR EOL  /* "forall_inst" rule. The literal should not contain quantified variables */
  { fun st stl ->
    let qst = VeritSyntax.create_quant_state () in
    let l = $14 st stl qst in
    let cl = get_ref $12 st in
    mk_clause ($1, Fins, [snd l], [cl]) st }
;

typ:
  | TPBR                                                   { Tpbr  }
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
  | EINS                                                   { Eins  }
  | SKEA                                                   { Skea  }
  | SKAA                                                   { Skaa  }
  | QNTS                                                   { Qnts  }
  | QNTM                                                   { Qntm  }
  | RESO                                                   { Reso  }
  | WEAK                                                   { Weak  }
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
  | TPBE                                                   { Tpbe  }
  | TPSC                                                   { Tpsc  }
  | TPPP                                                   { Tppp  }
  | TPQS                                                   { Tpqs  }
  | TPSK                                                   { Tpsk  }
  | SUBP                                                   { Subp  }
  | FLAT                                                   { Flat  }
  | HOLE                                                   { Hole  }
  | BBVA                                                   { Bbva  }
  | BBCONST                                                { Bbconst }
  | BBEQ                                                   { Bbeq  }
  | BBDIS                                                  { Bbdis }
  | BBOP                                                   { Bbop  }
  | BBADD                                                  { Bbadd }
  | BBMUL                                                  { Bbmul }
  | BBULT                                                  { Bbult }
  | BBSLT                                                  { Bbslt }
  | BBNOT                                                  { Bbnot }
  | BBNEG                                                  { Bbneg }
  | BBCONC                                                 { Bbconc }
  | BBEXTR                                                 { Bbextr }
  | BBZEXT                                                 { Bbzext }
  | BBSEXT                                                 { Bbsext }
  | BBSHL                                                  { Bbshl }
  | BBSHR                                                  { Bbshr }
  | ROW1                                                   { Row1  }
  | ROW2                                                   { Row2  }
  | EXTE                                                   { Exte  }
;

clause:
  | LPAR          RPAR                                     { fun _ _ _ -> [] }
  | LPAR lit_list RPAR                                     { fun st stl qst -> let _, l = list_dec ($2 st stl qst) in l }
;

lit_list:
  | lit                                                    { fun st stl qst -> [$1 st stl qst] }
  | lit lit_list                                           { fun st stl qst -> let l1 = $1 st stl qst in let l2 = $2 st stl qst in l1::l2 }
;

lit:   /* returns a SmtAtom.Form.t (given a state) */
  | name_term                                              { fun st stl qst -> let (decl, t) = $1 st stl qst in (decl, Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) (decl, t)) }
  | LPAR NOT lit RPAR                                      { fun st stl qst -> apply_dec Form.neg ($3 st stl qst) }
;

nlit:
  | LPAR NOT lit RPAR                                      { fun st stl qst -> apply_dec Form.neg ($3 st stl qst) }
;

var_atvar:
  | VAR			                                   { $1 }
  | ATVAR			                           { $1 }
;

name_term:   /* returns a bool * (SmtAtom.Form.pform or a SmtAtom.hatom) (given a state), the boolean indicates if we should declare the term or not */
  | SHARPINT                                               { fun st _ _ -> get_solver $1 st }
  | SHARPINT COLON LPAR term RPAR                          { fun st stl qst -> let res = $4 st stl qst in add_solver $1 res st; res }
  | BITV                                                   { fun st _ _ -> true, Form.Atom (Atom.mk_bvconst (VeritSyntax.get_atom_tbl_to_add st) (parse_bv $1)) }
  | TRUE                                                   { fun _ _ _ -> true, Form.Form Form.pform_true }
  | FALS                                                   { fun _ _ _ -> true, Form.Form Form.pform_false }
  | var_atvar						   { fun st stl qst -> let x = $1 in match find_opt_qvar x qst with
    					                   | Some bt -> false, Form.Atom (Atom.get ~declare:false (VeritSyntax.get_atom_tbl_to_add st) (Aapp (dummy_indexed_op (Rel_name x) [||] bt, [||])))
							   | None -> true, Form.Atom (Atom.get (VeritSyntax.get_atom_tbl_to_add st) (Aapp (State.get_fun stl $1, [||]))) }
  | BINDVAR                                                { fun st _ _ -> true, VeritSyntax.get_hlet $1 st }
  | INT                                                    { fun st _ _ -> true, Form.Atom (Atom.hatom_Z_of_int (VeritSyntax.get_atom_tbl_to_add st) $1) }
  | BIGINT                                                 { fun st _ _ -> true, Form.Atom (Atom.hatom_Z_of_bigint (VeritSyntax.get_atom_tbl_to_add st) $1) }
;

tvar:
  | TINT						   { TZ }
  | TBOOL						   { Tbool }
  | TINDEX                                                 { Tindex (indexed_type_of_int $1) }
;

var_decl_list:
  | LPAR var_atvar tvar RPAR				   { fun qst -> let () = add_qvar $2 $3 qst in [($2, $3)] }
  | LPAR var_atvar tvar RPAR var_decl_list		   { fun qst -> let () = add_qvar $2 $3 qst in let r5 = $5 qst in ($2, $3)::r5 }
;

forall_decl:
  | FORALL LPAR var_decl_list RPAR blit		   { fun st stl -> let qst = VeritSyntax.create_quant_state () in
                                                               let ff = $3 qst in
                                                               false, Form.Form (Fapp (Fforall ff, [|Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) ($5 st stl qst)|])) }
;

term:   /* returns a bool * (SmtAtom.Form.pform or SmtAtom.hatom), the boolean indicates if we should declare the term or not */
  | LPAR term RPAR                                         { fun st stl qst -> $2 st stl qst }

  /* Formulae */
  | TRUE                                                   { fun _ _ _ -> true, Form.Form Form.pform_true }
  | FALS                                                   { fun _ _ _ -> true, Form.Form Form.pform_false }
  | AND lit_list                                           { fun st stl qst -> apply_dec (fun x -> Form.Form (Fapp (Fand, Array.of_list x))) (list_dec ($2 st stl qst)) }
  | OR lit_list                                            { fun st stl qst -> apply_dec (fun x -> Form.Form (Fapp (For, Array.of_list x))) (list_dec ($2 st stl qst)) }
  | IMP lit_list                                           { fun st stl qst -> apply_dec (fun x -> Form.Form (Fapp (Fimp, Array.of_list x))) (list_dec ($2 st stl qst)) }
  | XOR lit_list                                           { fun st stl qst -> apply_dec (fun x -> Form.Form (Fapp (Fxor, Array.of_list x))) (list_dec ($2 st stl qst)) }
  | ITE lit_list                                           { fun st stl qst -> apply_dec (fun x -> Form.Form (Fapp (Fite, Array.of_list x))) (list_dec ($2 st stl qst)) }
  | forall_decl                                            { fun st stl _ -> $1 st stl }
  | BBT name_term LBRACKET lit_list RBRACKET               { fun st stl qst -> let (decl, t) = $2 st stl qst in let (decll, l) = list_dec ($4 st stl qst) in (decl && decll, match t with | Form.Atom a -> Form.Form (FbbT (a, l)) | _ -> assert false) }

  /* Atoms */
  | INT                                                    { fun st _ _ -> true, Form.Atom (Atom.hatom_Z_of_int (VeritSyntax.get_atom_tbl_to_add st) $1) }
  | BIGINT                                                 { fun st _ _ -> true, Form.Atom (Atom.hatom_Z_of_bigint (VeritSyntax.get_atom_tbl_to_add st) $1) }
  | BITV                                                   { fun st _ _ -> true, Form.Atom (Atom.mk_bvconst (VeritSyntax.get_atom_tbl_to_add st) (parse_bv $1)) }
  | LT name_term name_term                                 { fun st stl qst -> apply_bdec_atom (Atom.mk_lt (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst) }
  | LEQ name_term name_term                                { fun st stl qst -> apply_bdec_atom (Atom.mk_le (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst) }
  | GT name_term name_term                                 { fun st stl qst -> apply_bdec_atom (Atom.mk_gt (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst) }
  | GEQ name_term name_term                                { fun st stl qst -> apply_bdec_atom (Atom.mk_ge (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst) }
  | PLUS name_term name_term                               { fun st stl qst -> apply_bdec_atom (Atom.mk_plus (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst) }
  | MULT name_term name_term                               { fun st stl qst -> apply_bdec_atom (Atom.mk_mult (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst) }
  | MINUS name_term name_term                              { fun st stl qst -> apply_bdec_atom (Atom.mk_minus (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) ($3 st stl qst)}
  | MINUS name_term                                        { fun st stl qst -> apply_dec_atom (fun ?declare:d a -> Atom.mk_neg (VeritSyntax.get_atom_tbl_to_add st) a) ($2 st stl qst) }
  | OPP name_term                                          { fun st stl qst -> apply_dec_atom (Atom.mk_opp (VeritSyntax.get_atom_tbl_to_add st)) ($2 st stl qst) }
  | DIST args                                              { fun st stl qst -> let da, la = list_dec ($2 st stl qst) in
    	 						     let a = Array.of_list la in
                                                             da, Form.Atom (Atom.mk_distinct (VeritSyntax.get_atom_tbl_to_add st) ~declare:da (Atom.type_of a.(0)) a) }
  | BITOF INT name_term                                    { fun st stl qst -> apply_dec_atom (fun ?declare:(d=true) h -> match Atom.type_of h with TBV s -> Atom.mk_bitof (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s $2 h | _ -> assert false) ($3 st stl qst) }
  | BVNOT name_term                                        { fun st stl qst -> apply_dec_atom (fun ?declare:(d=true) h -> match Atom.type_of h with TBV s -> Atom.mk_bvnot (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h | _ -> assert false) ($2 st stl qst) }
  | BVAND name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvand (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVOR name_term name_term                               { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvor (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVXOR name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvxor (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVNEG name_term                                        { fun st stl qst -> apply_dec_atom (fun ?declare:(d=true) h -> match Atom.type_of h with TBV s -> Atom.mk_bvneg (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h | _ -> assert false) ($2 st stl qst) }
  | BVADD name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvadd (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVMUL name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvmult (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVULT name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvult (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVSLT name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvslt (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVULE name_term name_term                              { fun st stl qst -> let (decl,_) as a = apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvult (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) in (decl, Form.Lit (Form.neg (Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) a))) }
  | BVSLE name_term name_term                              { fun st stl qst -> let (decl,_) as a = apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvslt (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) in (decl, Form.Lit (Form.neg (Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) a))) }
  | BVSHL name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvshl (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVSHR name_term name_term                              { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TBV s -> Atom.mk_bvshr (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVCONC name_term name_term                             { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1, Atom.type_of h2 with TBV s1, TBV s2 -> Atom.mk_bvconcat (VeritSyntax.get_atom_tbl_to_add st) ~declare:d s1 s2 h1 h2 | _, _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | BVEXTR INT INT name_term                               { fun st stl qst -> let j, i = $2, $3 in apply_dec_atom (fun ?declare:(d=true) h -> match Atom.type_of h with TBV s -> Atom.mk_bvextr (VeritSyntax.get_atom_tbl_to_add st) ~declare:d ~s ~i ~n:(j-i+1) h | _ -> assert false) ($4 st stl qst) }
  | BVZEXT INT name_term                                   { fun st stl qst -> let n = $2 in apply_dec_atom (fun ?declare:(d=true) h -> match Atom.type_of h with TBV s -> Atom.mk_bvzextn (VeritSyntax.get_atom_tbl_to_add st) ~declare:d ~s ~n h | _ -> assert false) ($3 st stl qst) }
  | BVSEXT INT name_term                                   { fun st stl qst -> let n = $2 in apply_dec_atom (fun ?declare:(d=true) h -> match Atom.type_of h with TBV s -> Atom.mk_bvsextn (VeritSyntax.get_atom_tbl_to_add st) ~declare:d ~s ~n h | _ -> assert false) ($3 st stl qst) }
  | SELECT name_term name_term                             { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TFArray (ti, te) -> Atom.mk_select (VeritSyntax.get_atom_tbl_to_add st) ~declare:d ti te h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | DIFF name_term name_term                               { fun st stl qst -> apply_bdec_atom (fun ?declare:(d=true) h1 h2 -> match Atom.type_of h1 with TFArray (ti, te) -> Atom.mk_diffarray (VeritSyntax.get_atom_tbl_to_add st) ~declare:d ti te h1 h2 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) }
  | STORE name_term name_term name_term                    { fun st stl qst -> apply_tdec_atom (fun ?declare:(d=true) h1 h2 h3 -> match Atom.type_of h1 with TFArray (ti, te) -> Atom.mk_store (VeritSyntax.get_atom_tbl_to_add st) ~declare:d ti te h1 h2 h3 | _ -> assert false) ($2 st stl qst) ($3 st stl qst) ($4 st stl qst) }
  | VAR                                                    { fun st stl qst -> let x = $1 in match find_opt_qvar x qst with | Some bt -> false, Form.Atom (Atom.get ~declare:false (VeritSyntax.get_atom_tbl_to_add st) (Aapp (dummy_indexed_op (Rel_name x) [||] bt, [||]))) | None -> true, Form.Atom (Atom.get (VeritSyntax.get_atom_tbl_to_add st) (Aapp (State.get_fun stl x, [||]))) }
  | VAR args                                               { fun st stl qst -> let f = $1 in let a = $2 st stl qst in match find_opt_qvar f qst with | Some bt -> let op = dummy_indexed_op (Rel_name f) [||] bt in false, Form.Atom (Atom.get ~declare:false (VeritSyntax.get_atom_tbl_to_add st) (Aapp (op, Array.of_list (snd (list_dec a))))) | None -> let dl, l = list_dec a in dl, Form.Atom (Atom.get (VeritSyntax.get_atom_tbl_to_add st) ~declare:dl (Aapp (State.get_fun stl f, Array.of_list l))) }

  /* Both */
  | EQ name_term name_term                                 { fun st stl qst -> let t1 = ($2 st stl qst) in let t2 = ($3 st stl qst) in match t1,t2 with | (decl1, Form.Atom h1), (decl2, Form.Atom h2) when (match Atom.type_of h1 with | SmtBtype.Tbool -> false | _ -> true) -> let decl = decl1 && decl2 in decl, Form.Atom (Atom.mk_eq (VeritSyntax.get_atom_tbl_to_add st) ~declare:decl (Atom.type_of h1) h1 h2) | (decl1, t1), (decl2, t2) -> decl1 && decl2, Form.Form (Fapp (Fiff, [|Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) (decl1, t1); Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) (decl2, t2)|])) }
  | EQ nlit lit                                            { fun st stl qst -> match ($2 st stl qst), ($3 st stl qst) with (decl1, t1), (decl2, t2) -> decl1 && decl2, Form.Form (Fapp (Fiff, [|t1; t2|])) }
  | EQ name_term nlit                                      { fun st stl qst -> match ($2 st stl qst), ($3 st stl qst) with (decl1, t1), (decl2, t2) -> decl1 && decl2, Form.Form (Fapp (Fiff, [|Form.lit_of_atom_form_lit (VeritSyntax.get_form_tbl_to_add st) (decl1, t1); t2|])) }
  | LET LPAR bindlist RPAR name_term                       { fun st stl qst -> $3 st stl qst; $5 st stl qst }
  | BINDVAR                                                { fun st _ _ -> true, VeritSyntax.get_hlet $1 st }
;

blit:
  | name_term                                              { fun st stl qst -> $1 st stl qst }
  | LPAR NOT lit RPAR                                      { fun st stl qst -> apply_dec (fun l -> Form.Lit (Form.neg l)) ($3 st stl qst) }
;

bindlist:
  | LPAR BINDVAR blit RPAR	                           { fun st stl qst -> VeritSyntax.add_hlet $2 (snd ($3 st stl qst)) st }
  | LPAR BINDVAR blit RPAR bindlist                        { fun st stl qst -> VeritSyntax.add_hlet $2 (snd ($3 st stl qst)) st; $5 st stl qst }

args:
  | name_term                                              { fun st stl qst -> match $1 st stl qst with decl, Form.Atom h -> [(decl, h)] | _ -> assert false }
  | name_term args                                         { fun st stl qst -> match $1 st stl qst with decl, Form.Atom h -> (decl, h)::($2 st stl qst) | _ -> assert false }
;

clause_ids_params:
  | int_list                                               { $1 }
;

int_list:
  | INT                                                    { [$1] }
  | INT int_list                                           { let x1 = $1 in let x2 = $2 in x1::x2 }
;

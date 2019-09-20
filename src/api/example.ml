(*
  Building and checking the following proof:

             _________________
    y = z    y ≠ z ∨ f y = f z
    __________________________     _________________________________
              f y = f z            f x ≠ f y ∨ f y ≠ f z ∨ f x = f z
              ______________________________________________________
                             f x ≠ f y ∨ f x = f z                      f x = f y
                             ____________________________________________________
                                                f x = f z                            f x ≠ f z
                                                ______________________________________________
                                                                      ■

  where f : a -> b, a and b being uninterpreted types
*)


let _ =

(* Clear some datastructures
   Note: some parts should be remove from VeritSyntax *)
SmtTrace.clear ();
VeritSyntax.clear ();


(* Uninterpreted types: based on trace/smtBtype.mli;
   see smtlib2/smtlib2_genConstr.ml for use *)
let rt = SmtBtype.create () in
let a = Smtlib2_genConstr.declare_sort_from_name rt "a" in
let b = Smtlib2_genConstr.declare_sort_from_name rt "b" in


(* Uninterpreted variables and functions: based on trace/smtAtom.mli, module Op;
   see smtlib2/smtlib2_genConstr.ml for use *)
let ro = SmtAtom.Op.create () in
let x = Smtlib2_genConstr.declare_fun_from_name rt ro "x" [] a in
let y = Smtlib2_genConstr.declare_fun_from_name rt ro "y" [] a in
let z = Smtlib2_genConstr.declare_fun_from_name rt ro "z" [] a in
let f = Smtlib2_genConstr.declare_fun_from_name rt ro "f" [a] b in


(* Atoms and formulae: one way is to first build them as SMT terms
   in 3rdparty/smtlib2_ast.ml (using a dummy location since it does not
   come from a file) ... *)
let dl =
  let d = { Lexing.pos_fname = ""; Lexing.pos_lnum = 0; Lexing.pos_bol = 0; Lexing.pos_cnum = 0 } in
  (d, d)
in
let id_x = Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "x"))) in
let id_y = Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "y"))) in
let id_z = Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "z"))) in
let id_f = Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "f"))) in
let id_eq = Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "="))) in
let smt_x = Smtlib2_ast.TermQualIdentifier (dl, id_x) in
let smt_y = Smtlib2_ast.TermQualIdentifier (dl, id_y) in
let smt_z = Smtlib2_ast.TermQualIdentifier (dl, id_z) in
let smt_fx = Smtlib2_ast.TermQualIdTerm (dl, id_f, (dl, [smt_x])) in
let smt_fy = Smtlib2_ast.TermQualIdTerm (dl, id_f, (dl, [smt_y])) in
let smt_fz = Smtlib2_ast.TermQualIdTerm (dl, id_f, (dl, [smt_z])) in
let smt_y_eq_z = Smtlib2_ast.TermQualIdTerm (dl, id_eq, (dl, [smt_y; smt_z])) in
let smt_fy_eq_fz = Smtlib2_ast.TermQualIdTerm (dl, id_eq, (dl, [smt_fy; smt_fz])) in
let smt_fx_eq_fy = Smtlib2_ast.TermQualIdTerm (dl, id_eq, (dl, [smt_fx; smt_fy])) in
let smt_fx_eq_fz = Smtlib2_ast.TermQualIdTerm (dl, id_eq, (dl, [smt_fx; smt_fz])) in

(* ... then build the SMTCoq counterpart *)
let module Atom = SmtAtom.Atom in
let module Form = SmtAtom.Form in
let ra = VeritSyntax.ra in
let rf = VeritSyntax.rf in
let y_eq_z = Smtlib2_genConstr.make_root ra rf smt_y_eq_z in
let fx_eq_fy = Smtlib2_genConstr.make_root ra rf smt_fx_eq_fy in
let fy_eq_fz = Smtlib2_genConstr.make_root ra rf smt_fy_eq_fz in
let fx_eq_fz = Smtlib2_genConstr.make_root ra rf smt_fx_eq_fz in
let fx_neq_fz = Form.neg fx_eq_fz in


(* Certificate: input clauses *)
let root1 = SmtTrace.mkRootV [y_eq_z] in
let root2 = SmtTrace.mkRootV [fx_eq_fy] in
let root3 = SmtTrace.mkRootV [fx_neq_fz] in

(* Certificate: congruence *)
let congr = SmtTrace.mkOther (SmtCertif.EqCgr (fy_eq_fz, [Some y_eq_z])) None in

(* Certificate: transitivity *)
let trans = SmtTrace.mkOther (SmtCertif.EqTr (fx_eq_fz, [fx_eq_fy; fy_eq_fz])) None in

(* Certificate: resolution chain *)
let confl = SmtTrace.mkRes root1 congr [trans; root2; root3] in

(* Certificate: doubly linked list *)
SmtTrace.link root1 root2;
SmtTrace.link root2 root3;
SmtTrace.link root3 congr;
SmtTrace.link congr trans;
SmtTrace.link trans confl;

(* Allocation *)
SmtTrace.select confl;
SmtTrace.occur confl;
let max_id = SmtTrace.alloc root1 in

(* Export to Coq *)
let () = SmtCommands.checker (rt, ro, ra, rf, [y_eq_z; fx_eq_fy; fx_neq_fz], max_id, confl) in




print_endline "it compiles"

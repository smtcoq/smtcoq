(*
  Building and checking the following proof:

    y = z
  _________
  f y = f z    f x = f y
  ______________________
         f x = f z               f x ≠ f z
         _________________________________
                       ■

  where f : a -> b where a and b are uninterpreted types
*)


let _ =

(* Start from empty tables
   Note: this should be removed from VeritSyntax during the next
   clean-up... *)
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


(* Atoms and formulae: the simplest is to first build them as SMT terms
   in 3rdparty/smtlib2_ast.ml (using a dummy location since it does not
   come from a file) ... *)
let dl =
  let d = { Lexing.pos_fname = ""; Lexing.pos_lnum = 0; Lexing.pos_bol = 0; Lexing.pos_cnum = 0 } in
  (d, d)
in
let smt_x = Smtlib2_ast.TermQualIdentifier (dl, Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "x")))) in

(* (\* ... then to build the SMTCoq counterpart *\)
 * let Atom = SmtAtom.Atom
 * let Form = SmtForm.Make(Atom)
 * let ra = Atom.create ()
 * let rf = Atom.create ()
 * let y_equals_x = Smtlib2_genConstr.make_root ra rf
 *                    (Smtlib2_ast.TermQualIdentifier (dl, Smtlib2_ast.QualIdentifierId (dl, Smtlib2_ast.IdSymbol (dl, Smtlib2_ast.Symbol (dl, "x"))))) *)



print_endline "it compiles"

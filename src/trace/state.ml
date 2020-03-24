(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2020                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtAtom


(* The state shared by pre-processors, SMT-LIB parsers and printers, containing:
   - type_tbl : uninterpreted sorts
   - op_tbl : uninterpreted function symbols
   - atom_tbl_to_add : hash-consed atoms to be added in the deep embedding
   - form_tbl_to_add : hash-consed formulas to be added in the deep embedding
   - atom_tbl_no_add : hash-consed atoms no to be added in the deep embedding (for quantifiers)
   - form_tbl_no_add : hash-consed formulas no to be added in the deep embedding (for quantifiers)
   - trace_state : the state of the optimizer
   - type_names : the names of uninterpreted sorts
   - op_names : the names of uninterpreted function symbols
 *)

type type_tbl = SmtBtype.reify_tbl
type op_tbl = SmtAtom.Op.reify_tbl
type atom_tbl_to_add = SmtAtom.Atom.reify_tbl
type form_tbl_to_add = SmtAtom.Form.reify
type atom_tbl_no_add = SmtAtom.Atom.reify_tbl
type form_tbl_no_add = SmtAtom.Form.reify

type smt_state =
  { type_tbl : type_tbl;
    op_tbl : op_tbl;
    atom_tbl_to_add : atom_tbl_to_add;
    form_tbl_to_add : form_tbl_to_add;
    atom_tbl_no_add : atom_tbl_no_add;
    form_tbl_no_add : form_tbl_no_add;
    trace_state : SmtTrace.trace_state;
    type_names : (string, SmtBtype.btype) Hashtbl.t;
    op_names : (string, SmtAtom.indexed_op) Hashtbl.t
  }

let get_type_tbl st = st.type_tbl
let get_op_tbl st = st.op_tbl
let get_atom_tbl_to_add st = st.atom_tbl_to_add
let get_form_tbl_to_add st = st.form_tbl_to_add
let get_atom_tbl_no_add st = st.atom_tbl_no_add
let get_form_tbl_no_add st = st.form_tbl_no_add
let get_trace_state st = st.trace_state

(* Names of uninterpreted sorts *)
let get_btype st id =
  let btypes = st.type_names in
  try Hashtbl.find btypes id
  with | Not_found -> failwith ("State.get_btype : sort symbol \""^id^"\" not found\n")

let add_btype st id cl =
  let btypes = st.type_names in
  Hashtbl.add btypes id cl

(* Names of uninterpreted function symbols *)
let get_fun st id =
  let funs = st.op_names in
  try Hashtbl.find funs id
  with | Not_found -> failwith ("State.get_fun : function symbol \""^id^"\" not found\n")

let add_fun st id cl =
  let funs = st.op_names in
  Hashtbl.add funs id cl

let remove_fun st id =
  let funs = st.op_names in
  Hashtbl.remove funs id

let create_smt_state () : smt_state =
  { type_tbl = SmtBtype.create ();
    op_tbl = SmtAtom.Op.create ();
    atom_tbl_to_add = Atom.create ();
    form_tbl_to_add = Form.create ();
    atom_tbl_no_add = Atom.create ();
    form_tbl_no_add = Form.create ();
    trace_state = SmtTrace.create_trace_state ();
    type_names = Hashtbl.create 17;
    op_names = Hashtbl.create 17
  }

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(** Sharing of coq Int *)
let cInt_tbl = Hashtbl.create 17 

let mkInt i = 
  try Hashtbl.find cInt_tbl i 
  with Not_found ->
    let ci = Term.mkInt (Uint63.of_int i) in
    Hashtbl.add cInt_tbl i ci;
    ci

(** Generic representation of shared object *)
type 'a gen_hashed = { index : int; hval : 'a }

(** Functions over constr *)

let mklApp f args = Term.mkApp (Lazy.force f, args)

(* TODO : Set -> Type *)
let coqtype = lazy Term.mkSet

let declare_new_type t =
  Command.declare_assumption false (Decl_kinds.Local,Decl_kinds.Definitional) (Lazy.force coqtype) [] false None (Pp.dummy_loc,t);
  Term.mkVar t

let declare_new_variable v constr_t =
  Command.declare_assumption false (Decl_kinds.Local,Decl_kinds.Definitional) constr_t [] false None (Pp.dummy_loc,v);
  Term.mkVar v

let mkName s =
  let id = Names.id_of_string s in
  Names.Name id

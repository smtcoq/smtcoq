(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type constr_expr = Constrexpr.constr_expr
let ppconstr_modular_constr_pr = Ppconstr.modular_constr_pr
let constrextern_extern_constr = Constrextern.extern_constr

let evd_univ_entry evd = Evd.univ_entry ~poly:false evd

(* TODO: when switching to econstr, may have universe constraints *)
let empty_named_universes_entry =
  UState.univ_entry ~poly:false UState.empty

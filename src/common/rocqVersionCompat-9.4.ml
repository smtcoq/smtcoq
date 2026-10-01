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
let ppconstr_modular_constr_pr = Ppconstr.modular_constr_pr ~flags:(Ppconstr.current_flags())
let constrextern_extern_constr = Constrextern.extern_constr ~flags:(PrintingFlags.current())

let evd_univ_entry evd = Evd.univ_entry ~poly:PolyFlags.default evd

(* TODO: when switching to econstr, may have universe constraints *)
let empty_named_universes_entry =
  UState.univ_entry ~poly:PolyFlags.default UState.empty

let hash_constr = Termops.ConstrData.hash

module Summary = struct
  module Ref = struct
    type 'a t = 'a Summary.Ref.t
    let get = Summary.Ref.get
    let set = Summary.Ref.set
    let (!) = Summary.Ref.(!)
    let (:=) = Summary.Ref.(:=)
  end
  let ref ~name v = Summary.ref ~name v
end

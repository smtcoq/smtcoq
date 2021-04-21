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


(** Sharing of coq Int *)
let cInt_tbl = Hashtbl.create 17 

let mkInt i = 
  try Hashtbl.find cInt_tbl i 
  with Not_found ->
    let ci = Structures.mkInt i in
    Hashtbl.add cInt_tbl i ci;
    ci

(** Generic representation of shared object *)
type 'a gen_hashed = { index : int; hval : 'a }


(** Functions over constr *)
let mklApp f args = Structures.mkApp (Lazy.force f, args)

let string_of_name_def d n = try Structures.string_of_name n with | _ -> d

let string_coq_constr t =
  let rec fix rf x = rf (fix rf) x in
  let pr = fix
      Ppconstr.modular_constr_pr Pp.mt Structures.ppconstr_lsimpleconstr in
  Pp.string_of_ppcmds (pr (Structures.constrextern_extern_constr t))


(** Logics *)

type logic_item =
  | LUF
  | LLia
  | LBitvectors
  | LArrays

module SL = Set.Make (struct
    type t = logic_item
    let compare = Stdlib.compare
  end)

type logic = SL.t


(** Utils *)
let rec filter_map f = function
  | [] -> []
  | x::xs -> match f x with Some x -> x::(filter_map f xs) | None -> filter_map f xs

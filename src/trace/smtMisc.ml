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

let mklApp = Structures.mklApp

(* TODO : Set -> Type *)
let declare_new_type = Structures.declare_new_type
let declare_new_variable = Structures.declare_new_variable

let mkName s =
  let id = Structures.names_id_of_string s in
  Names.Name id


let string_coq_constr t =
  let rec fix rf x = rf (fix rf) x in
  let pr = fix
      Ppconstr.modular_constr_pr Pp.mt Structures.ppconstr_lsimpleconstr in
  Pp.string_of_ppcmds (pr (Structures.constrextern_extern_constr t))


let string_of_name = function
    Names.Name id -> Structures.names_string_of_id id
  | _ -> failwith "unnamed rel"


(** Logics *)

type logic_item =
  | LUF
  | LLia
  | LBitvectors
  | LArrays

module SL = Set.Make (struct
    type t = logic_item
    let compare = Pervasives.compare
  end)

type logic = SL.t

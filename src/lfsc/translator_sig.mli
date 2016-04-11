(**************************************************************************)
(*                                                                        *)
(*                            LFSCtoSmtCoq                                *)
(*                                                                        *)
(*                         Copyright (C) 2016                             *)
(*          by the Board of Trustees of the University of Iowa            *)
(*                                                                        *)
(*                    Alain Mebsout and Burak Ekici                       *)
(*                       The University of Iowa                           *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Ast
open Format

type rule =
  | Reso
  | Weak
  | Or
  | Orp
  | Imp
  | Impp
  | Nand
  | Andn
  | Nimp1
  | Nimp2
  | Impn1
  | Impn2
  | Nor
  | Orn
  | And
  | Andp
  | Eqtr
  | Eqcp
  | Eqco
  | Eqre
    


module type S = sig

  type lit

  type clause = lit list

  
  val to_clause : term -> clause


  val print_clause : formatter -> clause -> unit


  val register_clause_id : clause -> int -> unit


  val mk_clause : ?reuse:bool -> rule -> clause -> int list -> int


  val mk_clause_cl : ?reuse:bool -> rule -> term list -> int list -> int

  
  val mk_input : string -> term -> unit
    

  val register_prop_abstr : term -> term -> unit


  val get_clause_id : clause -> int


  val get_input_id : string -> int


  val clear : unit -> unit

  
end

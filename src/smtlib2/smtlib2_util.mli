(**************************************************************************)
(*                                                                        *)
(*     SMTCoq, originally belong to The Alt-ergo theorem prover           *)
(*     Copyright (C) 2006-2010                                            *)
(*                                                                        *)
(*     Sylvain Conchon                                                    *)
(*     Evelyne Contejean                                                  *)
(*     Stephane Lescuyer                                                  *)
(*     Mohamed Iguernelala                                                *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type extradata = unit
val initial_data : unit -> unit
val file : string ref
val line : int ref
type pos = int
val string_of_pos : int -> string
val cur_pd : unit -> int * unit
type pd = pos * extradata

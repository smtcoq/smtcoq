(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


val mkInt : int -> ExtrNative.uint
val mkArray : 'a array -> 'a ExtrNative.parray
val make_roots :
  SatAtom.Form.t SmtCertif.clause ->
  'a SmtCertif.clause -> ExtrNative.uint ExtrNative.parray ExtrNative.parray
val to_coq :
  'a ->
  'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n * 'o * 'p *
  'q * 'r * 's * 't ->
  'u SmtCertif.clause ->
  Sat_checker.Sat_Checker.step ExtrNative.parray ExtrNative.parray *
  'u SmtCertif.clause
val checker : string -> string -> bool

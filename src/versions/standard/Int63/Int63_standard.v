(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*       from the Int63 library of native-coq                             *)
(*       by Benjamin Gregoire and Laurent Thery                           *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(** Naive software representation of Int63. To improve. Anyway, if you
    want efficiency, rather use native-coq. **)

Require Export Cyclic63.
Require Export Ring63.
Require Export Int63Native.
Require Export Int63Op.
Require Export Int63Axioms.
Require Export Int63Properties.

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


(** Glue with the Int31 library of standard coq, which is linked to
    native integers during VM computations.

    CAUTION: The name "Int63" is given for compatibility reasons, but
    int31 is used. **)

Require Export Ring31.
Require Export Int63Native.
Require Export Int63Op.
Require Export Int63Axioms.
Require Export Int63Properties.

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*     Burak Ekici                                                        *)
(*     Alain Mebsout                                                      *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*     The University of Iowa                                             *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import
        Bool ZArith BVList Logic BVList FArray
        SMT_classes SMT_classes_instances SMT_terms PropToBool BoolToProp.
Import BVList.BITVECTOR_LIST. 

Declare ML Module "smtcoq_plugin".

Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.


Ltac zchaff := prop2bool; zchaff_bool.
Ltac verit := prop2bool; verit_bool.
Ltac cvc4 := prop2bool; cvc4_bool.


Ltac smt := try prop2bool; 
            repeat 
              match goal with
                | [ |- context[ CompDec ?t ] ] => try assumption
                | [ |- _ : bool] => verit
                | [ |- _ : bool] => try (cvc4; verit)
              end;
            try bool2prop.


(*Ltac smt := (prop2bool; try verit; cvc4_bool; try verit_bool; bool2prop).*)

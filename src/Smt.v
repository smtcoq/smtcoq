(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     * Alain Mebsout                                                    *)
(*     * Burak Ekici                                                      *)
(*                                                                        *)
(*     * The University of Iowa                                           *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import
        SMTCoq Bool ZArith BVList Logic BVList FArray
        SMT_classes SMT_classes_instances SMT_terms PropToBool BoolToProp.
Import BVList.BITVECTOR_LIST. 


Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.

Ltac smt := prop2bool; 
            repeat 
              match goal with
                | [ |- context[ CompDec ?t ] ] => try assumption
                | [ |- _ : bool] => verit
                | [ |- _ : bool] => try (cvc4; verit)
              end;
            try bool2prop.
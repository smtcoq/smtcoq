(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


From SMTCoq Require Import SMTCoq.
From Stdlib Require Import Bool Uint63 ZArith.

Local Open Scope Z_scope.


Section BV.

  Import BVList.BITVECTOR_LIST.
  Local Open Scope bv_scope.

  Goal forall (a b: bitvector 8),
    #b|1|0|0|0|0|0|0|0| = a ->
    #b|1|0|0|0|0|0|0|0| = b -> (bv_mult a b) =  #b|0|0|0|0|0|0|0|0|.
  Proof using. smt. Qed.

End BV.


Section PR.

  (* TODO: Slowness *)
  (* (* Pigeon hole: 4 holes, 5 pigeons *) *)
  (* Goal forall x11 x12 x13 x14 x15 x21 x22 x23 x24 x25 x31 x32 x33 x34 x35 x41 x42 x43 x44 x45, ( *)
  (*   (orb (negb x11) (negb x21)) && *)
  (*   (orb (negb x11) (negb x31)) && *)
  (*   (orb (negb x11) (negb x41)) && *)
  (*   (orb (negb x21) (negb x31)) && *)
  (*   (orb (negb x21) (negb x41)) && *)
  (*   (orb (negb x31) (negb x41)) && *)

  (*   (orb (negb x12) (negb x22)) && *)
  (*   (orb (negb x12) (negb x32)) && *)
  (*   (orb (negb x12) (negb x42)) && *)
  (*   (orb (negb x22) (negb x32)) && *)
  (*   (orb (negb x22) (negb x42)) && *)
  (*   (orb (negb x32) (negb x42)) && *)

  (*   (orb (negb x13) (negb x23)) && *)
  (*   (orb (negb x13) (negb x33)) && *)
  (*   (orb (negb x13) (negb x43)) && *)
  (*   (orb (negb x23) (negb x33)) && *)
  (*   (orb (negb x23) (negb x43)) && *)
  (*   (orb (negb x33) (negb x43)) && *)

  (*   (orb (negb x14) (negb x24)) && *)
  (*   (orb (negb x14) (negb x34)) && *)
  (*   (orb (negb x14) (negb x44)) && *)
  (*   (orb (negb x24) (negb x34)) && *)
  (*   (orb (negb x24) (negb x44)) && *)
  (*   (orb (negb x34) (negb x44)) && *)

  (*   (orb (negb x15) (negb x25)) && *)
  (*   (orb (negb x15) (negb x35)) && *)
  (*   (orb (negb x15) (negb x45)) && *)
  (*   (orb (negb x25) (negb x35)) && *)
  (*   (orb (negb x25) (negb x45)) && *)
  (*   (orb (negb x35) (negb x45)) && *)


  (*   (orb (negb x11) (negb x12)) && *)
  (*   (orb (negb x11) (negb x13)) && *)
  (*   (orb (negb x11) (negb x14)) && *)
  (*   (orb (negb x11) (negb x15)) && *)
  (*   (orb (negb x12) (negb x13)) && *)
  (*   (orb (negb x12) (negb x14)) && *)
  (*   (orb (negb x12) (negb x15)) && *)
  (*   (orb (negb x13) (negb x14)) && *)
  (*   (orb (negb x13) (negb x15)) && *)
  (*   (orb (negb x14) (negb x15)) && *)

  (*   (orb (negb x21) (negb x22)) && *)
  (*   (orb (negb x21) (negb x23)) && *)
  (*   (orb (negb x21) (negb x24)) && *)
  (*   (orb (negb x21) (negb x25)) && *)
  (*   (orb (negb x22) (negb x23)) && *)
  (*   (orb (negb x22) (negb x24)) && *)
  (*   (orb (negb x22) (negb x25)) && *)
  (*   (orb (negb x23) (negb x24)) && *)
  (*   (orb (negb x23) (negb x25)) && *)
  (*   (orb (negb x24) (negb x25)) && *)

  (*   (orb (negb x31) (negb x32)) && *)
  (*   (orb (negb x31) (negb x33)) && *)
  (*   (orb (negb x31) (negb x34)) && *)
  (*   (orb (negb x31) (negb x35)) && *)
  (*   (orb (negb x32) (negb x33)) && *)
  (*   (orb (negb x32) (negb x34)) && *)
  (*   (orb (negb x32) (negb x35)) && *)
  (*   (orb (negb x33) (negb x34)) && *)
  (*   (orb (negb x33) (negb x35)) && *)
  (*   (orb (negb x34) (negb x35)) && *)

  (*   (orb (negb x41) (negb x42)) && *)
  (*   (orb (negb x41) (negb x43)) && *)
  (*   (orb (negb x41) (negb x44)) && *)
  (*   (orb (negb x41) (negb x45)) && *)
  (*   (orb (negb x42) (negb x43)) && *)
  (*   (orb (negb x42) (negb x44)) && *)
  (*   (orb (negb x42) (negb x45)) && *)
  (*   (orb (negb x43) (negb x44)) && *)
  (*   (orb (negb x43) (negb x45)) && *)
  (*   (orb (negb x44) (negb x45)) && *)


  (*   (orb (orb (orb x11 x21) x31) x41) && *)
  (*   (orb (orb (orb x12 x22) x32) x42) && *)
  (*   (orb (orb (orb x13 x23) x33) x43) && *)
  (*   (orb (orb (orb x14 x24) x34) x44) && *)
  (*   (orb (orb (orb x15 x25) x35) x45)) = false. *)
  (* Proof using. *)
  (*   smt. *)
  (* Qed. *)

End PR.

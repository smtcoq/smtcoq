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


Add Rec LoadPath "../src" as SMTCoq.

Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith Logic.

Local Open Scope Z_scope.


Section BV.

Import BVList.BITVECTOR_LIST.
Local Open Scope bv_scope.

  Goal forall (x y : bitvector 4),
    bv_eq x #b|0|0|0|1| = true ->
 (* bv_eq y #b|0|0|0|1| = true -> *)
    bv_and x y = #b|0|0|0|1|.
  Proof using. (* Fail smt. *) Fail abduce 3. Abort.

  Goal forall (x y : bitvector 4),
(* bv_eq y #b|0|0|0|1| = true -> *)
   bv_mult x y = x.
  Proof using. (* Fail smt. *) Fail abduce 3. Abort.

  Goal forall (x y : bitvector 4),
 (* bv_eq y #b|0|0|0|0| = true -> *)
    bv_mult x y = #b|0|0|0|0|.
  Proof using. (* Fail smt. *) Fail abduce 3. Abort.

  Goal forall (x y z : bitvector 4),
    bv_ultP x y ->
 (* bv_ultP y z -> *)
    bv_ultP x z.
  Proof using. (* Fail smt. *) Fail abduce 3. Abort.

End BV.


Section EUF.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         (* y = x -> *) (f x) = (f y).
  Proof using. (* Fail smt. *) Fail abduce 1. Abort.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         (* x = (y + 1) -> *) (f y) = (f (x - 1)).
  Proof using. (* Fail smt. *) Fail abduce 1. Abort.

  Goal forall
         (x y: Z)
         (f: Z -> Z),
         (* x = (y + 1) -> *) (f (y + 1)) = (f x).
  Proof using. (* Fail smt. *) Fail abduce 1. Abort.

End EUF.


Section LIA.

  Goal forall (x y: Z), (*(x >= y) ->*) (y < x) \/ (x = y).
  Proof using. (* Fail smt. *) Fail abduce 1. Abort.

  Goal forall (x y z : Z), 0 <= y ->
       (* 0 <= x + z -> *) 0 <= x + y + z.
  Proof using. (* Fail smt. *) Fail abduce 3. Abort.

  Goal forall (a b c d : Z), a <= c ->
  (* b <= d -> *) a + b <= c + d.
  Proof using. (* Fail smt. *) Fail abduce 3. Abort.

End LIA.


Section PR.

  Goal forall (a b c d : bool), (implb a b) && (implb c d)
       -> (*a && c ->*) b && d.
  Proof using. (* Fail smt. *) Fail abduce 4. Abort.

End PR.


(*
   Local Variables:
   coq-load-path: ((rec "../src" "SMTCoq"))
   End:
*)

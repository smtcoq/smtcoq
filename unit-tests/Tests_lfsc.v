Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.


(* LFSC vernacular commands *)

Section Checker_Sat1.
  Lfsc_Checker "sat1.smt2" "sat1.lfsc".
End Checker_Sat1.

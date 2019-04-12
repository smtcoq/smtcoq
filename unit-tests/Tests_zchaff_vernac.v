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


Add Rec LoadPath "../src" as SMTCoq.

Require Import SMTCoq.
Require Import Bool PArray Int63 List ZArith.

Local Open Scope int63_scope.


(* zChaff vernacular commands *)

Time Zchaff_Checker "sat1.cnf" "sat1.zlog".
Time Zchaff_Checker "sat2.cnf" "sat2.zlog".
Time Zchaff_Checker "sat3.cnf" "sat3.zlog".
Time Zchaff_Checker "sat5.cnf" "sat5.zlog".
Time Zchaff_Checker "sat6.cnf" "sat6.zlog".
Time Zchaff_Checker "sat7.cnf" "sat7.zlog".
Time Zchaff_Checker "hole4.cnf" "hole4.zlog".
(* Time Zchaff_Checker "cmu-bmc-barrel6.cnf" "cmu-bmc-barrel6.zlog". *)
(* Time Zchaff_Checker "velev-sss-1.0-05.cnf" "velev-sss-1.0-05.zlog". *)


Time Zchaff_Theorem sat1 "sat1.cnf" "sat1.zlog".
Time Zchaff_Theorem sat2 "sat2.cnf" "sat2.zlog".
Time Zchaff_Theorem sat3 "sat3.cnf" "sat3.zlog".
Time Zchaff_Theorem sat5 "sat5.cnf" "sat5.zlog".
Time Zchaff_Theorem sat6 "sat6.cnf" "sat6.zlog".
Time Zchaff_Theorem sat7 "sat7.cnf" "sat7.zlog".
Time Zchaff_Theorem hole4 "hole4.cnf" "hole4.zlog".


Parse_certif_zchaff d1 t1 "sat1.cnf" "sat1.zlog".
Compute Sat_Checker.checker d1 t1.

Parse_certif_zchaff d2 t2 "sat2.cnf" "sat2.zlog".
Compute Sat_Checker.checker d2 t2.

Parse_certif_zchaff d3 t3 "sat3.cnf" "sat3.zlog".
Compute Sat_Checker.checker d3 t3.

Parse_certif_zchaff d5 t5 "sat5.cnf" "sat5.zlog".
Compute Sat_Checker.checker d5 t5.

Parse_certif_zchaff d6 t6 "sat6.cnf" "sat6.zlog".
Compute Sat_Checker.checker d6 t6.

Parse_certif_zchaff d7 t7 "sat7.cnf" "sat7.zlog".
Compute Sat_Checker.checker d7 t7.

Parse_certif_zchaff dhole4 thole4 "hole4.cnf" "hole4.zlog".
Compute Sat_Checker.checker dhole4 thole4.

(* Parse_certif_zchaff dcmubmcbarrel6 tcmubmcbarrel6 "cmu-bmc-barrel6.cnf" "cmu-bmc-barrel6.zlog". *)
(* Compute Sat_Checker.checker dcmubmcbarrel6 tcmubmcbarrel6. *)

(* Parse_certif_zchaff dvelevsss1005 tvelevsss1005 "velev-sss-1.0-05.cnf" "velev-sss-1.0-05.zlog". *)
(* Compute Sat_Checker.checker dvelevsss1005 tvelevsss1005. *)

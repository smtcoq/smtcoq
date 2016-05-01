(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - Université Paris-Sud                 *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtForm

type used = int

type clause_id  = int

type 'hform rule =
  (* Weakening *)
  | Weaken of 'hform clause * 'hform list
     (*  * weaken          : {a_1 ... a_n} --> {a_1 ... a_n b_1 ... b_n} *)

  (* Simplification *)
  | ImmFlatten of 'hform clause * 'hform 

  (* CNF Transformations *)
  | True       
     (*  * true             : {true} 
     *)
  | False 
     (* * false             : {(not false)} 
     *)
  | BuildDef of 'hform (* the first literal of the clause *)       
     (*  * and_neg          : {(and a_1 ... a_n) (not a_1) ... (not a_n)}
         * or_pos           : {(not (or a_1 ... a_n)) a_1 ... a_n} 
         * implies_pos      : {(not (implies a b)) (not a) b}
         * xor_pos1         : {(not (xor a b)) a b}
         * xor_neg1         : {(xor a b) a (not b)}
         * equiv_pos1       : {(not (iff a b)) a (not b)}
         * equiv_neg1       : {(iff a b) (not a) (not b)}
         * ite_pos1         : {(not (if_then_else a b c)) a c}
         * ite_neg1         : {(if_then_else a b c) a (not c)}
     *)
  | BuildDef2 of 'hform (* the first literal of the clause *) 
     (* * xor_pos2          : {(not (xor a b)) (not a) (not b)}
        * xor_neg2          : {(xor a b) (not a) b}
        * equiv_pos2        : {(not (iff a b)) (not a) b}
        * equiv_neg2        : {(iff a b) a b}
        * ite_pos2          : {(not (if_then_else a b c)) (not a) b}
        * ite_neg2          : {(if_then_else a b c) (not a) (not b)}

     *)
  | BuildProj of 'hform * int 
     (*  * or_neg           : {(or a_1 ... a_n) (not a_i)}
         * and_pos          : {(not (and a_1 ... a_n)) a_i} 
         * implies_neg1     : {(implies a b) a}
         * implies_neg2     : {(implies a b) (not b)}
     *)

  (* Immediate CNF transformation : CNF transformation + Reso *)
  | ImmBuildDef of 'hform clause 
     (* * not_and           : {(not (and a_1 ... a_n))} --> {(not a_1) ... (not a_n)}
        * or                : {(or a_1 ... a_n)} --> {a_1 ... a_n}
        * implies           : {(implies a b)} --> {(not a) b}
        * xor1              : {(xor a b)} --> {a b}
        * not_xor1          : {(not (xor a b))} --> {a (not b)}
        * equiv2            : {(iff a b)} --> {a (not b)}
        * not_equiv2        : {(not (iff a b))} --> {(not a) (not b)}
        * ite1              : {(if_then_else a b c)} --> {a c}
        * not_ite1          : {(not (if_then_else a b c))} --> {a (not c)}
     *)
  | ImmBuildDef2 of 'hform clause
     (* * xor2              : {(xor a b)} --> {(not a) (not b)}
        * not_xor2          : {(not (xor a b))} --> {(not a) b}
        * equiv1            : {(iff a b)} --> {(not a) b}
        * not_equiv1        : {(not (iff a b))} --> {a b}
        * ite2              : {(if_then_else a b c)} --> {(not a) b}
        * not_ite2          : {(not (if_then_else a b c))} --> {(not a) (not b)}
     *)
  | ImmBuildProj of 'hform clause * int
     (*  * and               : {(and a_1 ... a_n)} --> {a_i} 
         * not_or            : {(not (or a_1 ... a_n))} --> {(not a_i)}
         * not_implies1      : {(not (implies a b))} --> {a}
         * not_implies2      : {(not (implies a b))} --> {(not b)}
     *)

  (* Equality *)
  | EqTr of 'hform * 'hform list
    (*  * eq_reflexive     : {(= x x)}
        * eq_transitive    : {(not (= x_1 x_2)) ... (not (= x_{n-1} x_n)) (= x_1 x_n)}
    *)
  | EqCgr of 'hform * ('hform option) list
    (*  * eq_congruent     : {(not (= x_1 y_1)) ... (not (= x_n y_n)) 
                                   (= (f x_1 ... x_n) (f y_1 ... y_n))}
    *)
  | EqCgrP of 'hform * 'hform * ('hform option) list
    (*  * eq_congruent_pred : {(not (= x_1 y_1)) ... (not (= x_n y_n)) 
                                   (not (p x_1 ... x_n)) (p y_1 ... y_n)}
    *)

  (* Linear arithmetic *)
  | LiaMicromega of 'hform list * Certificate.Mc.zArithProof list
  | LiaDiseq of 'hform

  (* Arithmetic simplifications *)
  | SplArith of 'hform clause * 'hform * Certificate.Mc.zArithProof list

  (* Elimination of operators *)
  | SplDistinctElim of 'hform clause * 'hform

  (* Possibility to introduce "holes" in proofs (that should be filled in Coq) *)
  | Hole of ('hform clause) list * 'hform list

and 'hform clause = {
            id    : clause_id;
    mutable kind  : 'hform clause_kind;
    mutable pos   : int option;
    mutable used  : used;
    mutable prev  : 'hform clause option;
    mutable next  : 'hform clause option;
            value : 'hform list option
              (* This field should be defined for rules which can create atoms :
                 EqTr, EqCgr, EqCgrP, Lia, Dlde, Lra *)
}

and 'hform clause_kind =
  | Root
  | Same of 'hform clause
  | Res of 'hform resolution
  | Other of 'hform rule

and 'hform resolution = {
  mutable rc1   : 'hform clause;
  mutable rc2   : 'hform clause;
  mutable rtail : 'hform clause list}

let used_clauses r =
  match r with
  | ImmBuildProj (c, _) | ImmBuildDef c | ImmBuildDef2 c
  | Weaken (c,_) | ImmFlatten (c,_)  | SplArith (c,_,_) | SplDistinctElim (c,_) -> [c]
  | Hole (cs, _) -> cs
  | True | False | BuildDef _ | BuildDef2 _ | BuildProj _
  | EqTr _ | EqCgr _ | EqCgrP _
  | LiaMicromega _ | LiaDiseq _ -> []

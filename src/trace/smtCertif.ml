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
  | LiaMicromega of 'hform list * Structures.Micromega_plugin_Certificate.Mc.zArithProof list
  | LiaDiseq of 'hform

  (* Arithmetic simplifications *)
  | SplArith of 'hform clause * 'hform * Structures.Micromega_plugin_Certificate.Mc.zArithProof list

  (* Elimination of operators *)
  | SplDistinctElim of 'hform clause * 'hform

  (* Possibility to introduce "holes" in proofs (that should be filled in Coq) *)
  | Hole of ('hform clause) list * 'hform list
  | Forall_inst of 'hform clause * 'hform
  | Qf_lemma of 'hform clause * 'hform

and 'hform clause = {
    mutable id    : clause_id;
    mutable kind  : 'hform clause_kind;
    mutable pos   : int option;
    mutable used  : used;
    mutable prev  : 'hform clause option;
    mutable next  : 'hform clause option;
    mutable value : 'hform list option
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
  | ImmFlatten (c,_)  | SplArith (c,_,_) | SplDistinctElim (c,_)
  | Forall_inst (c, _) | Qf_lemma (c, _) -> [c]
  | Hole (cs, _) -> cs
  | True | False | BuildDef _ | BuildDef2 _ | BuildProj _
  | EqTr _ | EqCgr _ | EqCgrP _
  | LiaMicromega _ | LiaDiseq _ -> []

(* For debugging certif processing purposes : <add_scertif> <select> <occur> <alloc> *)
let to_string r =
  match r with
            Root -> "Root"
          | Same c -> "Same(" ^ string_of_int (c.id) ^ ")"
          | Res r ->
             let id1 = string_of_int r.rc1.id in
             let id2 = string_of_int r.rc2.id in
             let rest_ids = List.fold_left (fun str rc -> str ^ "; " ^ string_of_int rc.id) "" r.rtail in
             "Res [" ^ id1 ^ "; " ^ id2 ^ rest_ids ^"]"
          | Other x -> "Other(" ^
                         begin match x with
                         | True -> "True"
                         | False -> "False"
                         | BuildDef _ -> "BuildDef"
                         | BuildDef2 _ -> "BuildDef2"
                         | BuildProj _ -> "BuildProj"
                         | EqTr _ -> "EqTr"
                         | EqCgr _ -> "EqCgr"
                         | EqCgrP _ -> "EqCgrP"
                         | LiaMicromega _ -> "LiaMicromega"
                         | LiaDiseq _ -> "LiaDiseq"
                         | Qf_lemma _ -> "Qf_lemma"
                                         
                         | Hole _ -> "Hole"

                         | ImmFlatten _ -> "ImmFlatten"
                         | ImmBuildDef _ -> "ImmBuildDef"
                         | ImmBuildDef2 _ -> "ImmBuildDef2"
                         | ImmBuildProj _ -> "ImmBuildProj"
                         | SplArith _ -> "SplArith"
                         | SplDistinctElim _ -> "SplDistinctElim"
                         | Forall_inst _ -> "Forall_inst"  end ^ ")"



(* To use <print_certif>, pass, as first and second argument, <Form.to_smt> and <Atom.to_string> *)
let print_certif form_to_smt atom_to_string c where=
  let rec start c =
    match c.prev with
    | None -> c
    | Some c -> start c in
  let r = ref (start c) in
  let out_channel = open_out where in
  let fmt = Format.formatter_of_out_channel out_channel in
  let continue = ref true in
  while !continue do
    let kind = to_string (!r.kind) in
    let id = !r.id in
    let pos = match !r.pos with
      | None -> "None"
      | Some p -> string_of_int p in
    let used = !r.used in
    Format.fprintf fmt "id:%i kind:%s pos:%s used:%i value:" id kind pos used;
    begin match !r.value with
    | None -> Format.fprintf fmt "None"
    | Some l -> List.iter (fun f -> form_to_smt atom_to_string fmt f;
                                    Format.fprintf fmt " ") l end;
    Format.fprintf fmt "\n";
    match !r.next with
    | None -> continue := false
    | Some n -> r := n 
  done;
  Format.fprintf fmt "@."; close_out out_channel

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Bool.
Require Import List.
Require Import Int63.
Require Import PArray.
Require Import BoolEq.
Require Import NZParity.

Add LoadPath ".." as SMTCoq.

Require Import Misc State.
Require Import SMT_terms.


Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Section Checker.

  Import Atom.


  Variable t_form : PArray.array form.
  Variable t_atom : PArray.array atom.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).

  Variable s : S.t.


  Definition atom_to_int (a : atom) :=
    match a with
    | Acop (CO_int i) => i
    | Auop (UO_index i) a => i
    | _ => 0%int63
    end.

  Fixpoint clean {A:Type} (l:list A) := 
    match l with 
    | nil => nil
    | a::nil => a::nil
    | a::b::c => a::(clean c)
    end.

(*TODO : remplace egalité booléène par equivalent*)
 Definition check_BuildDefInt lits :=
  let n := PArray.length lits in
  if (n == Int63Op.digits + 1)&&(Lit.is_pos (lits.[0]))
  then (
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Abop b h1 h2 => 
        match (b,get_atom h1,get_atom h2) with
        | (BO_eq Tint,Acop (CO_int x),Acop (CO_int y)) => 
          let fonction_map i l := if i == 0 then l else (if Lit.is_pos l then Lit.neg l else l) in
          let test_correct i0 l :=
            if i0 == 0
            then true
            else (
              match get_form (Lit.blit l) with
              | Fiff l1 l2 =>
                match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
                | (Fatom a1,Fatom a2) =>
                  match (get_atom a1,get_atom a2) with
                  | (Auop (UO_index x) j,Auop (UO_index y) k) => (j == i0-1)&&(k == j)
                  | _ => false
                  end
                | _ => false
                end
              | _ => false
              end
                 )
          in
          if forallbi (fun i l => test_correct i l) lits
          then PArray.to_list (PArray.mapi fonction_map lits)
          else C._true
        | _ => C._true
        end
      | _ => C._true
      end
    | _ => C._true
    end
       )
  else C._true
  .


Definition check_BuildProjInt lits i :=
  let n := PArray.length lits in
  if (n == Int63Op.digits + 1)&&(i < Int63Op.digits)
  then (
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Abop b h1 h2 => 
        match (b,get_atom h1,get_atom h2) with
        | (BO_eq Tint,Acop (CO_int x),Acop (CO_int y)) => 
          let fonction_map i l := if i == 0 then l else (if Lit.is_pos l then l else Lit.neg l) in
          let test_correct i0 l :=
            if i0 == 0
            then true
            else (
              match get_form (Lit.blit l) with
              | Fiff l1 l2 =>
                match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
                | (Fatom a1,Fatom a2) =>
                  match (get_atom a1,get_atom a2) with
                  | (Auop (UO_index x) j,Auop (UO_index y) k) => (j == i0-1)&&(k == j)
                  | _ => false
                  end
                | _ => false
                end
              | _ => false
              end
                 )
          in
          if test_correct i (lits.[i+1]) 
          then (fonction_map i (lits.[i+1]))::(Lit.nlit (Lit.blit (lits.[0])))::nil
          else C._true
        | _ => C._true
        end
      | _ => C._true
      end
    | _ => C._true
    end
       )
  else C._true
  .

 
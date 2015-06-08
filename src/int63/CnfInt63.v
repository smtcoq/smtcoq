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

  Fixpoint clean A (l:list A) := 
    match l with 
    | nil => nil
    | a::nil => a::nil
    | a::b::c => a::(clean c)
    end.

  Definition check_BuildDefint l a :=
    let n := PArray.length a in
    if n == 126
    then (
      match (a.[0],a.[1]) with
      | (Auop (UO_index i1) j1,Auop (UO_index i2) j2) =>
        let x := atom_to_int (a.[0]) in
        let y := atom_to_int (a.[1]) in

        let f := fun i u => 
          match (u,is_even i) with
          |(Auop (UO_index x) j,true) => j == (i/2)
          |(Auop (UO_index y) j,false) => j == ((i-1)/2)
          | _ => false
          end
        in
        if forallbi f a
        then (
          match (get_form Lit.blit l) with
          | Fatom (Abop (BO_eq atom) h1 h2) =>
          | _ => C._true
          end
             )
        else C._true
      | _ => C._true
      end
         )
    else C._true
    .
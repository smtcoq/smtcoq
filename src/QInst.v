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


Require Import Bool ZArith.
Require Import State SMT_classes.


(** Handling quantifiers with veriT **)

(* verit silently transforms an <implb a b> into a <or (not a) b> when
 instantiating a quantified theorem with <implb> *)
Lemma impl_split a b:
  implb a b = true -> orb (negb a) b = true.
Proof.
  intro H.
  destruct a; destruct b; trivial.
(* alternatively we could do <now verit_base H.> but it forces us to have veriT
   installed when we compile SMTCoq. *)
Qed.

Hint Resolve impl_split : smtcoq_core.

(** verit silently transforms an <implb (a || b) c> into a <or (not a) c>
   or into a <or (not b) c> when instantiating such a quantified theorem *)
Lemma impl_or_split_right a b c:
  implb (a || b) c = true -> negb b || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma impl_or_split_left a b c:
  implb (a || b) c = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

(** same for Boolean equivalence, modulo symmetry *)
Lemma eqb_sym_or_split_right a b c:
  Bool.eqb c (a || b) = true -> negb b || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_sym_or_split_left a b c:
  Bool.eqb c (a || b) = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_or_split_right a b c:
  Bool.eqb (a || b) c = true -> negb b || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_or_split_left a b c:
  Bool.eqb (a || b) c = true -> negb a || c = true.
Proof.
  intro H.
  destruct a; destruct c; intuition.
Qed.

Lemma eqb_or_split a b c:
  Bool.eqb c (a || b) = true -> negb c || a || b = true.
Proof.
  intro H.
  destruct a; destruct b; destruct c; intuition.
Qed.

(** verit considers equality modulo its symmetry, so we have to recover the
    right direction in the instances of the theorems *)
(* TODO: currently incomplete *)

(* An auxiliary lemma to rewrite an eqb_of_compdec into its the symmetrical version *)
Lemma eqb_of_compdec_sym (A:Type) (HA:CompDec A) (a b:A) :
  eqb_of_compdec HA b a = eqb_of_compdec HA a b.
Proof.
  destruct (@eq_dec _ (@Decidable _ HA) a b) as [H|H].
  - now rewrite H.
  - case_eq (eqb_of_compdec HA a b).
    + now rewrite <- !(@compdec_eq_eqb _ HA).
    + intros _. case_eq (eqb_of_compdec HA b a); auto.
      intro H1. elim H. symmetry. now rewrite compdec_eq_eqb.
Qed.

(* First strategy: change the order of all equalities in the goal or the
   hypotheses
   Incomplete: all or none of the equalities are changed, whereas we may
   need to change some of them but not all of them *)
Definition hidden_eq_Z (a b : Z) := (a =? b)%Z.
Definition hidden_eq_U (A:Type) (HA:CompDec A) (a b : A) := eqb_of_compdec HA a b.
Ltac apply_sym_hyp T :=
  repeat match T with
         | context [ (?A =? ?B)%Z] =>
           change (A =? B)%Z with (hidden_eq_Z A B) in T
         end;
  repeat match T with
         | context [ @eqb_of_compdec ?A ?HA ?a ?b ] =>
           change (eqb_of_compdec HA a b) with (hidden_eq_U A HA a b) in T
         end;
  repeat match T with
         | context [ hidden_eq_Z ?A ?B] =>
           replace (hidden_eq_Z A B) with (B =? A)%Z in T;
           [ | now rewrite Z.eqb_sym]
         end;
  repeat match T with
         | context [ hidden_eq_U ?A ?HA ?a ?b] =>
           replace (hidden_eq_U A HA a b) with (eqb_of_compdec HA b a) in T;
           [ | now rewrite eqb_of_compdec_sym]
         end.
Ltac apply_sym_goal :=
  repeat match goal with
         | [ |- context [ (?A =? ?B)%Z] ] =>
           change (A =? B)%Z with (hidden_eq_Z A B)
         end;
  repeat match goal with
         | [ |- context [ @eqb_of_compdec ?A ?HA ?a ?b ] ] =>
           change (eqb_of_compdec HA a b) with (hidden_eq_U A HA a b)
         end;
  repeat match goal with
         | [ |- context [ hidden_eq_Z ?A ?B] ] =>
           replace (hidden_eq_Z A B) with (B =? A)%Z;
           [ | now rewrite Z.eqb_sym]
         end;
  repeat match goal with
         | [ |- context [ hidden_eq_U ?A ?HA ?a ?b] ] =>
           replace (hidden_eq_U A HA a b) with (eqb_of_compdec HA b a);
           [ | now rewrite eqb_of_compdec_sym]
         end.
Ltac strategy1 H :=
  first [ apply H
        | apply_sym_goal; apply H
        | apply_sym_hyp H; apply H
        | apply_sym_goal; apply_sym_hyp H; apply H
        ].

(* Second strategy: find the order of equalities
   Incomplete: does not work if the lemma is quantified *)
Ltac order_equalities g TH :=
  match g with
  | eqb_of_compdec ?HC ?a1 ?b1 =>
    match TH with
    | eqb_of_compdec _ ?a2 _ =>
      first [ constr_eq a1 a2 | replace (eqb_of_compdec HC a1 b1) with (eqb_of_compdec HC b1 a1) by now rewrite eqb_of_compdec_sym ]
    | _ => idtac
    end
  | Z.eqb ?a1 ?b1 =>
    match TH with
    | Z.eqb ?a2 _ =>
      first [ constr_eq a1 a2 | replace (Z.eqb a1 b1) with (Z.eqb b1 a1) by now rewrite Z.eqb_sym ]
    | _ => idtac
    end
  | ?f1 ?t1 =>
    match TH with
    | ?f2 ?t2 => order_equalities f1 f2; order_equalities t1 t2
    | _ => idtac
    end
  | _ => idtac
  end.
Ltac strategy2 H :=
  match goal with
  | [ |- ?g ] =>
    let TH := type of H in
    order_equalities g TH;
    apply H
  end.


(* An automatic tactic that takes into account all those transformations *)
Ltac vauto :=
  try (unfold is_true;
       let H := fresh "H" in
       intro H;
       first [ strategy1 H
             | strategy2 H
             | match goal with
               | [ |- (negb ?A || ?B) = true ] =>
                 first [ eapply impl_or_split_right;
                         first [ strategy1 H
                               | strategy2 H ]
                       | eapply impl_or_split_left;
                         first [ strategy1 H
                               | strategy2 H ]
                       | eapply eqb_sym_or_split_right;
                         first [ strategy1 H
                               | strategy2 H ]
                       | eapply eqb_sym_or_split_left;
                         first [ strategy1 H
                               | strategy2 H ]
                       | eapply eqb_or_split_right;
                         first [ strategy1 H
                               | strategy2 H ]
                       | eapply eqb_or_split_left;
                         first [ strategy1 H
                               | strategy2 H ]
                       ]
               | [ |- (negb ?A || ?B || ?C) = true ] =>
                 eapply eqb_or_split;
                 first [ strategy1 H
                       | strategy2 H ]
               end
             ]
      );
  auto with smtcoq_core.



(* 
   Local Variables:
   coq-load-path: ((rec "." "SMTCoq"))
   End: 
*)

Require Import DecidableType FMapWeakList FMapFacts.
(* Require Import List Bool NArith Psatz Int63. *)
Require Import Misc.

Section Array.

Class DecType T := {
  eq_dec : forall x y : T, { x = y } + { x <> y }
}.

SearchPattern (forall x y , { x = y } + { x <> y }).

Variables
  (key: Type)
  (elt_e: Type)
  (key_dec: DecType key) 
  (elt_e_dec: DecType elt_e).

Definition elt := option elt_e.

Lemma contra : forall A B: Prop, (A -> B) -> (~B -> ~A).
Proof. auto. Qed.

Lemma elt_dec : DecType elt.
Proof. split; intros x y; destruct elt_e_dec.
  case x; [ intro x'| ]; (case y; [ intro y'| ]).
  - destruct (eq_dec0 x' y') as [H|H].
    + left; rewrite H; reflexivity.
    + right; revert H; apply contra; intro H. now inversion H.
  - now right.
  - now right.
  - now left.
Qed.



Variable K: DecidableType.

(* Module Make (K: DecidableType) (V: DecidableType). *)
  
  Definition key := K.t. 
  Definition elt := option V.t.

  Module M := FMapWeakList.Make K.

  Module Import MFacts := WFacts M.
  
  Definition t := M.t elt.


  Definition select (a: t) (i: key) : elt :=
    match M.find i a with
    | Some v => v
    | None => None
    end.


  Definition store (a: t) (i: key) (v: elt) : t := M.add i v a.


  Lemma read_over_same_write : forall a i j v, K.eq i j -> select (store a i v) j = v.
  Proof.
    intros a i j v Heq.
    unfold select, store.
    rewrite add_eq_o; auto.
  Qed.  

  Lemma read_over_other_write : forall a i j v, ~ K.eq i j -> select (store a i v) j = select a j.
  Proof.
    intros a i j v Hneq.
    unfold select, store.
    rewrite add_neq_o; auto.
  Qed.  


  Lemma extensionnality : forall a b, (forall i, select a i = select b i) -> a = b.
  Admitted. (* TODO *)
  
(* End Make. *)

(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

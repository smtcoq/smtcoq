Require Import DecidableType FMapWeakList FMapFacts.
(* Require Import List Bool NArith Psatz Int63. *)
Require Import Misc.

(* Section Array. *)


Module Make (K: DecidableType).

  Class DecType T := {
    eq_dec : forall x y : T, { x = y } + { x <> y }
  }.


  Definition key := K.t.

  Module M := FMapWeakList.Make K.

  Module Import MFacts := WFacts M.

  Definition farray elt := M.t elt.


  Definition select elt (a: farray elt) (i: key) : option elt := M.find i a.


  Definition store elt (a: farray elt) (i: key) (v: elt) : farray elt := M.add i v a.


  Lemma read_over_same_write : forall elt a i j v,
      K.eq i j -> select elt (store elt a i v) j = Some v.
  Proof.
    intros elt a i j v Heq.
    unfold select, store.
    intros. rewrite add_eq_o; auto.
  Qed.  


  Lemma read_over_other_write : forall elt a i j v,
      ~ K.eq i j -> select elt (store elt a i v) j = select elt a j.
  Proof.
    intros elt a i j v Hneq.
    unfold select, store.
    rewrite add_neq_o; auto.
  Qed. 

  Lemma find_ext: forall elt cmp,
      (forall (x y: elt), cmp x y = true <-> x = y) ->
      (forall m1 m2, M.Equal m1 m2 -> (M.equal cmp m1 m2) = true).
  Proof. intros.
    specialize(Equal_Equivb H m1 m2).
    intros. apply H1 in H0.
    apply M.equal_1. exact H0.
  Qed.

  Lemma find_ext_dec:
    forall elt,
    forall eq_elt_dec : (forall (e e': elt), { e = e' } + { e <> e' }),
      let cmp := fun e e' => if eq_elt_dec e e' then true else false in
      (forall m1 m2, M.Equal m1 m2 -> (M.equal cmp m1 m2) = true).
  Proof. intros.
    specialize(Equal_Equivb_eqdec eq_elt_dec m1 m2).
    intros. apply H0 in H.
    apply M.equal_1. exact H.
  Qed.


  Definition eq_elt_dec :
    forall elt (elt_dec: DecType elt),
    forall x y : elt, { x = y } + { x <> y }.
    intros elt elt_dec. inversion elt_dec. auto.
  Defined.


  Definition eqb elt (elt_dec: DecType elt) a b :=
    let cmp := fun e e' => if eq_elt_dec elt elt_dec e e' then true else false in
    M.equal cmp a b.


  Lemma extensionnality : forall elt (elt_dec: DecType elt) a b,
      (forall i, select elt a i = select elt b i) -> eqb elt elt_dec a b = true.
  Proof.
    intros.
    unfold select in H.
    specialize (find_ext_dec elt (eq_elt_dec elt elt_dec)). intros Hext.
    unfold M.Equal in Hext.
    apply Hext in H. clear Hext.
    exact H.
  Qed.

End Make.


(* 
   Local Variables:
   coq-load-path: ((rec ".." "SMTCoq"))
   End: 
*)

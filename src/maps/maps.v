Require Import Arith Bool.
Require Import FunctionalExtensionality.

(* total maps in software foundations *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1, id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Definition total_map (A:Type) := id -> A.

Definition empty_map {A:Type} (v : A) : total_map A := (fun _ => v).

Definition update_map {A:Type} (m : total_map A) (x : id) (v : A) :=
                      fun x' => if beq_id x x' then v else m x'.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof. intros id. destruct id. simpl. now rewrite (beq_nat_refl n). Qed.

Theorem beq_id_diff : forall id1 id2, id1 <> id2 -> false = beq_id id1 id2.
Proof. intros id1 id2 H.
       destruct id1, id2 in *.
       simpl in *. symmetry. apply beq_nat_false_iff. unfold not in *.
       intro H1. apply H. now rewrite H1.    
 Qed.

Theorem beq_id_true_iff : forall id1 id2 : id, beq_id id1 id2 = true <-> id1 = id2.
Proof. intros id1 id2. split; intro H. 
       - destruct id1, id2. unfold beq_id in *.
         apply beq_nat_true in H. now rewrite H.
       - rewrite H. now rewrite (beq_id_refl id2).
Qed.

Theorem update_eq : forall A (m: total_map A) x v, (update_map m x v) x = v.
Proof. intros A m x v. unfold update_map.
       now rewrite <- beq_id_refl.
Qed.

Theorem update_neq : forall (A: Type) v x1 x2 (m : total_map A), x1 <> x2 -> (update_map m x1 v) x2 = m x2.
Proof. intros A v x1 x2 m H.
       unfold update_map.
       rewrite <- beq_id_diff; trivial.
Qed.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof. intros x y. apply iff_reflect. now rewrite beq_id_true_iff. Qed.

Lemma eta_expansion {A B} (f : A -> B) : f = fun x => f x.
Admitted.

Lemma map_ext: forall A (m1 m2: total_map A), (forall x, m1 x = m2 x -> m1 = m2).
Proof. intros A m1 m2.
       About functional_extensionality_dep.
       About functional_extensionality.
       intros x H.
       apply (@functional_extensionality id A m1 m2).
       destruct x. intro x. destruct x.
Admitted.


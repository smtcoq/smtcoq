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


(* Software implementation of arrays, based on finite maps using AVL
   trees *)


Declare Scope array_scope.

Require Import Int31.
Require Export Int63.
Require FMapAVL.

Local Open Scope int63_scope.


Module Map := FMapAVL.Make(IntOrderedType).

(* An array is represented as a tuple of a finite map, the default
   element, and the length *)
Definition array (A:Type) : Type :=
  (Map.t A * A * int)%type.

Definition make {A:Type} (l:int) (d:A) : array A := (Map.empty A, d, l).

Definition get {A:Type} (t:array A) (i:int) : A :=
  let (td,_) := t in
  let (t,d) := td in
  match Map.find i t with
    | Some x => x
    | None => d
  end.

Definition default {A:Type} (t:array A) : A :=
  let (td,_) := t in let (_,d) := td in d.

Definition set {A:Type} (t:array A) (i:int) (a:A) : array A :=
  let (td,l) := t in
  if l <= i then
    t
  else
    let (t,d) := td in
    (Map.add i a t, d, l).

Definition length {A:Type} (t:array A) : int :=
  let (_,l) := t in l.

Definition copy {A:Type} (t:array A) : array A := t.

Definition reroot : forall {A:Type}, array A -> array A := @copy.

Definition init {A:Type} (l:int) (f:int -> A) (d:A) : array A :=
  let r :=
      if l == 0 then
        Map.empty A
      else
        foldi (fun j m => Map.add j (f j) m) 0 (l-1) (Map.empty A) in
  (r, d, l).

Definition map {A B:Type} (f:A -> B) (t:array A) : array B :=
  let (td,l) := t in
  let (t,d) := td in
  (Map.map f t, f d, l).

Delimit Scope array_scope with array.
Notation "t '.[' i ']'" := (get t i) (at level 50) : array_scope.
Notation "t '.[' i '<-' a ']'" := (set t i a) (at level 50) : array_scope.

Local Open Scope array_scope.

Definition max_array_length := 4194302%int31.

(** Axioms *)
Axiom get_outofbound : forall A (t:array A) i, (i < length t) = false -> t.[i] = default t.

Axiom get_set_same : forall A t i (a:A), (i < length t) = true -> t.[i<-a].[i] = a.
Axiom get_set_other : forall A t i j (a:A), i <> j -> t.[i<-a].[j] = t.[j].
Axiom default_set : forall A t i (a:A), default (t.[i<-a]) = default t.


Axiom get_make : forall A (a:A) size i, (make size a).[i] = a.
Axiom default_make : forall A (a:A) size, (default (make size a)) = a.

Axiom ltb_length : forall A (t:array A), length t <= max_array_length = true.

Axiom length_make : forall A size (a:A),
  length (make size a) = if size <= max_array_length then size else max_array_length.
Axiom length_set : forall A t i (a:A),
  length (t.[i<-a]) = length t.

Axiom get_copy : forall A (t:array A) i, (copy t).[i] = t.[i].
Axiom length_copy : forall A (t:array A), length (copy t) = length t.

Axiom get_reroot : forall A (t:array A) i, (reroot t).[i] = t.[i].
Axiom length_reroot : forall A (t:array A), length (reroot t) = length t.


Axiom length_init : forall A f size (def:A),
  length (init size f def) = if size <= max_array_length then size else max_array_length.

Axiom get_init : forall A f size (def:A) i,
  (init size f def).[i] = if i < length (init size f def) then f i else def.

Axiom default_init : forall A f size (def:A), default (init size f def) = def.

(* Not true in this implementation (see #71, many thanks to Andres Erbsen) *)
(*
Axiom get_ext : forall A (t1 t2:array A),
  length t1 = length t2 ->
  (forall i, i < length t1 = true -> t1.[i] = t2.[i]) ->
  default t1 = default t2 ->
  t1 = t2.
*)

(* Definition *)
Definition to_list {A:Type} (t:array A) :=
  let len := length t in
  if 0 == len then nil
  else foldi_down (fun i l => t.[i] :: l)%list (len - 1) 0 nil.

Definition forallbi {A:Type} (f:int-> A->bool) (t:array A) :=
  let len := length t in
  if 0 == len then true
  else forallb (fun i => f i (t.[i])) 0 (len - 1).

Definition forallb {A:Type} (f: A->bool) (t:array A) :=
  let len := length t in
  if 0 == len then true
  else forallb (fun i => f (t.[i])) 0 (len - 1).

Definition existsbi {A:Type} (f:int->A->bool) (t:array A) :=
  let len := length t in
  if 0 == len then false
  else existsb (fun i => f i (t.[i])) 0 (len - 1).

Definition existsb {A:Type} (f:A->bool) (t:array A) :=
  let len := length t in
  if 0 == len then false
  else existsb (fun i => f (t.[i])) 0 (len - 1).

(* TODO : We should add init as native and add it *)
Definition mapi {A B:Type} (f:int->A->B) (t:array A) :=
  let size := length t in
  let def := f size (default t) in
  let tb := make size def in
  if size == 0 then tb
  else foldi (fun i tb => tb.[i<- f i (t.[i])]) 0 (size - 1) tb.

Definition foldi_left {A B:Type} (f:int -> A -> B -> A) a (t:array B) :=
  let len := length t in
  if 0 == len then a
  else foldi (fun i a => f i a (t.[i])) 0 (len - 1) a.

Definition fold_left {A B:Type} (f: A -> B -> A) a (t:array B) :=
  let len := length t in
  if 0 == len then a
  else foldi (fun i a => f a (t.[i])) 0 (length t - 1) a.

Definition foldi_right {A B:Type} (f:int -> A -> B -> B) (t:array A) b :=
  let len := length t in
  if 0 == len then b
  else foldi_down (fun i b => f i (t.[i]) b) (len - 1) 0 b.

Definition fold_right {A B:Type} (f: A -> B -> B) (t:array A) b :=
  let len := length t in
  if 0 == len then b
  else foldi_down (fun i b => f (t.[i]) b) (len - 1) 0 b.

(* Lemmas *)

Lemma default_copy : forall A (t:array A), default (copy t) = default t.
Proof.
 intros A t;assert (length t < length t = false).
  apply Bool.not_true_is_false; apply leb_not_gtb; apply leb_refl.
 rewrite <- (get_outofbound _ (copy t) (length t)), <- (get_outofbound _ t (length t)), get_copy;trivial.
Qed.

Lemma reroot_default : forall A (t:array A), default (reroot t) = default t.
Proof.
 intros A t;assert (length t < length t = false).
  apply Bool.not_true_is_false; apply leb_not_gtb; apply leb_refl.
 rewrite <- (get_outofbound _ (reroot t) (length t)), <- (get_outofbound _ t (length t)), get_reroot;trivial.
Qed.

Lemma get_set_same_default :
   forall (A : Type) (t : array A) (i : int) ,
       (t .[ i <- default t]) .[ i] = default t.
Proof.
 intros A t i;case_eq (i < (length t));intros.
 rewrite get_set_same;trivial.
 rewrite get_outofbound, default_set;trivial.
 rewrite length_set;trivial.
Qed.

Lemma get_not_default_lt : forall A (t:array A) x,
 t.[x] <> default t -> x < length t = true.
Proof.
 intros A t x Hd.
 case_eq (x < length t);intros Heq;[trivial | ].
 elim Hd;rewrite get_outofbound;trivial.
Qed.

Lemma foldi_left_Ind :
     forall A B (P : int -> A -> Prop) (f : int -> A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P i a -> P (i+1) (f i a (t.[i]))) ->
     forall a, P 0 a ->
     P (length t) (foldi_left f a t).
Proof.
 intros;unfold foldi_left.
 destruct (reflect_eqb 0 (length t)).
  rewrite <- e;trivial.
 assert ((length t - 1) + 1 = length t) by ring.
 rewrite <- H1 at 1;apply foldi_Ind;auto.
 assert (W:= leb_max_int (length t));rewrite leb_spec in W.
 rewrite ltb_spec, to_Z_sub_1_diff;auto with zarith.
 intros Hlt;elim (ltb_0 _ Hlt).
 intros;apply H;trivial. rewrite ltb_leb_sub1;auto.
Qed.

Lemma fold_left_Ind :
     forall A B (P : int -> A -> Prop) (f : A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P i a -> P (i+1) (f a (t.[i]))) ->
     forall a, P 0 a ->
     P (length t) (fold_left f a t).
Proof.
 intros.
 apply (foldi_left_Ind A B P (fun i => f));trivial.
Qed.

Lemma fold_left_ind :
     forall A B (P : A -> Prop) (f : A -> B -> A) (t:array B),
     (forall a i, i < length t = true -> P a -> P (f a (t.[i]))) ->
     forall a, P a ->
     P (fold_left f a t).
Proof.
 intros;apply (fold_left_Ind A B (fun _ => P));trivial.
Qed.

Lemma foldi_right_Ind :
     forall A B (P : int -> A -> Prop) (f : int -> B -> A -> A) (t:array B),
     (forall a i, i < length t = true -> P (i+1) a -> P i (f i (t.[i]) a)) ->
     forall a, P (length t) a ->
     P 0 (foldi_right f t a).
Proof.
 intros;unfold foldi_right.
 destruct (reflect_eqb 0 (length t)).
  rewrite e;trivial.
 set (P' z a := (*-1 <= z < [|length t|] ->*) P (of_Z (z + 1)) a).
 assert (P' ([|0|] - 1)%Z (foldi_down (fun (i : int) (b : A) => f i (t .[ i]) b) (length t - 1) 0 a)).
 apply foldi_down_ZInd;unfold P'.
 intros Hlt;elim (ltb_0 _ Hlt).
 rewrite to_Z_sub_1_diff;auto.
 ring_simplify ([|length t|] - 1 + 1)%Z;rewrite of_to_Z;trivial.
 intros;ring_simplify ([|i|] - 1 + 1)%Z;rewrite of_to_Z;auto.
 assert (i < length t = true).
   rewrite ltb_leb_sub1;auto.
 apply H;trivial.
 exact H1.
Qed.

Lemma fold_right_Ind :
     forall A B (P : int -> A -> Prop) (f : B -> A -> A) (t:array B),
     (forall a i, i < length t = true -> P (i+1) a -> P i (f (t.[i]) a)) ->
     forall a, P (length t) a ->
     P 0 (fold_right f t a).
Proof.
 intros;apply (foldi_right_Ind A B P (fun i => f));trivial.
Qed.

Lemma fold_right_ind :
     forall A B (P : A -> Prop) (f : B -> A -> A) (t:array B),
     (forall a i, i < length t = true -> P a -> P (f (t.[i]) a)) ->
     forall a, P a ->
     P (fold_right f t a).
Proof.
 intros;apply (fold_right_Ind A B (fun i => P));trivial.
Qed.

Lemma forallbi_spec : forall A (f : int -> A -> bool) t,
  forallbi f t = true <-> forall i, i < length t = true -> f i (t.[i]) = true.
Proof.
 unfold forallbi;intros A f t.
 destruct (reflect_eqb 0 (length t)).
 split;[intros | trivial].
 elim (ltb_0 i);rewrite e;trivial.
 rewrite forallb_spec;split;intros Hi i;intros;apply Hi.
 apply leb_0. rewrite <- ltb_leb_sub1;auto. rewrite ltb_leb_sub1;auto.
Qed.

Lemma forallb_spec : forall A (f : A -> bool) t,
  forallb f t = true <-> forall i, i < length t = true -> f (t.[i]) = true.
Proof.
 intros A f;apply (forallbi_spec A (fun i => f)).
Qed.

Lemma existsbi_spec : forall A (f : int -> A -> bool) t,
  existsbi f t = true <-> exists i, i < length t = true /\ f i (t.[i]) = true.
Proof.
 unfold existsbi;intros A f t.
 destruct (reflect_eqb 0 (length t)).
 split;[discriminate | intros [i [Hi _]];rewrite <- e in Hi;elim (ltb_0 _ Hi)].
 rewrite existsb_spec. repeat setoid_rewrite Bool.andb_true_iff.
 split;intros [i H];decompose [and] H;clear H;exists i;repeat split;trivial.
 rewrite ltb_leb_sub1;auto. apply leb_0. rewrite <- ltb_leb_sub1;auto.
Qed.

Lemma existsb_spec : forall A (f : A -> bool) t,
  existsb f t = true <-> exists i, i < length t = true /\ f (t.[i]) = true.
Proof.
 intros A f;apply (existsbi_spec A (fun i => f)).
Qed.

Local Open Scope list_scope.

Definition to_list_ntr A (t:array A) :=
  let len := length t in
  if 0 == len then nil
  else foldi_ntr _ (fun i l => t.[i] :: l) 0 (len - 1) nil.

Lemma to_list_to_list_ntr : forall A (t:array A),
   to_list t = to_list_ntr _ t.
Proof.
 unfold to_list, to_list_ntr; intros A t.
 destruct (reflect_eqb 0 (length t));trivial.
 rewrite foldi_ntr_foldi_down;trivial.
 apply leb_ltb_trans with max_array_length;[ | trivial].
 apply leb_trans with (length t);[ | apply ltb_length].
 rewrite leb_spec, sub_spec.
 rewrite to_Z_1, Zmod_small;try omega.
 generalize (to_Z_bounded (length t)).
 assert (0%Z <> [|length t|]);[ | omega].
   intros Heq;elim n;apply to_Z_inj;trivial.
Qed.

Lemma fold_left_to_list : forall (A B:Type) (t:array A) (f: B -> A -> B) b,
   fold_left f b t = List.fold_left f (to_list t) b.
Proof.
  intros A B t f;rewrite to_list_to_list_ntr.
  unfold fold_left, to_list_ntr; destruct (reflect_eqb 0 (length t));[trivial | ].
  set (P1 := fun i => forall b,
      foldi (fun (i : int) (a : B) => f a (t .[ i])) i (length t - 1) b =
      List.fold_left f
        (foldi_ntr (list A) (fun (i : int) (l : list A) => t .[ i] :: l) i
           (length t - 1) nil) b).
  assert (W: P1 0);[ | trivial].
  apply int_ind_bounded with (max := length t - 1);unfold P1.
  apply leb_0.
  intros b;unfold foldi_ntr;rewrite foldi_eq, foldi_cont_eq;trivial.
  intros i _ Hlt Hrec b.
  unfold foldi_ntr;rewrite foldi_lt, foldi_cont_lt;trivial;simpl.
  apply Hrec.
Qed.

Require Import Bool.
Local Open Scope bool_scope.

Definition eqb {A:Type} (Aeqb: A->A->bool) (t1 t2:array A) :=
  (length t1 == length t2) &&
  Aeqb (default t1) (default t2) &&
  forallbi (fun i a1 => Aeqb a1 (t2.[i])) t1.

(*
Lemma reflect_eqb : forall (A:Type) (Aeqb:A->A->bool),
  (forall a1 a2, reflect (a1 = a2) (Aeqb a1 a2)) ->
  forall t1 t2, reflect (t1 = t2) (eqb Aeqb t1 t2).
Proof.
 intros A Aeqb HA t1 t2.
 case_eq (eqb Aeqb t1 t2);unfold eqb;intros H;constructor.
 rewrite !andb_true_iff in H;destruct H as [[H1 H2] H3].
 apply get_ext.
 rewrite (reflect_iff _ _ (reflect_eqb _ _));trivial.
 rewrite forallbi_spec in H3.
 intros i Hlt;rewrite (reflect_iff _ _ (HA _ _));auto.
 rewrite (reflect_iff _ _ (HA _ _));trivial.
 intros Heq;rewrite Heq in H;clear Heq.
 revert H; rewrite Int63Axioms.eqb_refl;simpl.
 case_eq (Aeqb (default t2) (default t2));simpl;intros H0 H1.
 rewrite <- not_true_iff_false, forallbi_spec in H1;apply H1.
 intros i _; rewrite <- (reflect_iff _ _ (HA _ _));trivial.
 rewrite <- not_true_iff_false, <- (reflect_iff _ _ (HA _ _)) in H0;apply H0;trivial.
Qed.
*)


(* 
   Local Variables:
   coq-load-path: ((rec "../../.." "SMTCoq"))
   End: 
*)

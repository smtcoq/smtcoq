Require Import ZArith.

(********************************************************************)
(********************************************************************)
(* Ces composants sont communs à toutes les tactiques de conversion *)
(********************************************************************)
(********************************************************************)

(* SMTCoq utilise Zeq_bool *)
Lemma Zeq_bool_Zeqb a b : Z.eqb a b = Zeq_bool a b.
Proof.
  case_eq (a =? b)%Z.
  - rewrite Z.eqb_eq. intros ->. symmetry. now rewrite <- Zeq_is_eq_bool.
  - rewrite Z.eqb_neq. intro H. case_eq (Zeq_bool a b); auto. now rewrite <- Zeq_is_eq_bool.
Qed.

(* Généralise fun x => f (g x) *)
Ltac generalize_fun f g :=
  repeat
    match goal with
      | |- context [ f (g ?X) ] => change (f (g X)) with ((fun x => f (g x)) X)
    end;
  generalize (fun x => f (g x)).

(* SMTCoq travaille avec les booléens *)
Lemma implb_impl : forall a b : bool, (implb a b = true -> a = true -> b = true).
Proof.
intros a b H.
destruct a; destruct b; try reflexivity; discriminate.
Qed.

(****************************)
(****************************)
(* Conversion de pos vers Z *)
(****************************)
(****************************)

Definition Pos2Z := Zpos.

Definition Z2Pos (z : Z) :=
  match z with
    | 0%Z => 1%positive
    | Zpos p => p
    | Zneg _ => 1%positive
  end.

(* Remplace tous les sous-termes p de type positive par Z2Pos (Pos2Z p) *)
Ltac pos_converting :=
  (* On crée une variable fraîche de type positive *)
  let var := fresh "var" in
  pose proof xH as var;
  (* Coeur de la tactique *)
  repeat
    match goal with
    (* On capture chaque sous-terme p avec son contexte, i.e. le but est C[p] *)
    | |- context C[?p]  =>
      (* Si p est de type positive *)
      match type of p with
      | positive =>
        match p with
        (* Si p est de la forme Z2Pos (Pos2Z _) on abandonne le match car p est déjà réécrit *)
        | Z2Pos (Pos2Z _) => fail 1
        (* Il n'est pas nécessaire de réécrire au dessus des symboles connus *)
        | Pos.add _ _ => fail 1
        | Pos.mul _ _ => fail 1
        | _ =>
          (* Sinon, on analyse la formule obtenue en remplaçant p par notre variable fraîche dans le but *)
          match context C[var] with
          (* Si elle contient le terme Z2Pos (Pos2Z var), cela signifie que le contexte C[]
             est de la forme C'[Z2Pos (Pos2Z [])] et donc on abandonne le match car p est déjà réécrit *)
          | context [Z2Pos (Pos2Z var)] => fail 1
          (* Idem: si le contexte contient xO ou xI, c'est qu'on est à l'intérieur d'une constante *)
          | context [xO var] => fail 1
          | context [xI var] => fail 1
          (* Sinon on réécrit *)
          | _ => change p with (Z2Pos (Pos2Z p))
          end
        end
      end
    end;
  (* Finalement, on efface notre variable fraîche *)
  clear var.

(* Réécrit les opérations et relations de positive vers Z *)
Ltac pos_rewriting :=
  repeat
  match goal with
    | |-context [Pos.add (Z2Pos ?X) (Z2Pos ?Y) ] =>  change (Pos.add (Z2Pos X) (Z2Pos Y)) with (Z2Pos (X + Y))
    | |-context [Pos.mul (Z2Pos ?X) (Z2Pos ?Y) ] =>  change (Pos.mul (Z2Pos X) (Z2Pos Y)) with (Z2Pos (X * Y))
    | |-context [Pos.ltb (Z2Pos ?X) (Z2Pos ?Y) ] =>  change (Pos.ltb (Z2Pos X) (Z2Pos Y)) with (Z.ltb X Y)
    | |-context [Pos.leb (Z2Pos ?X) (Z2Pos ?Y) ] =>  change (Pos.leb (Z2Pos X) (Z2Pos Y)) with (Z.leb X Y)
    | |-context [Pos.eqb (Z2Pos ?X) (Z2Pos ?Y) ] =>  change (Pos.eqb (Z2Pos X) (Z2Pos Y)) with (Z.eqb X Y);rewrite Zeq_bool_Zeqb
  end.

(* Après avoir converti dans Z il faudra ajouter l'hypothèse de positivité *)
Lemma pos_is_ltb : forall p : positive, Z.ltb 0 (Pos2Z p) = true.
Proof. reflexivity. Qed.

(* Réussit si f est un symbole de fonction non interprété *)
Ltac pos_is_uninterp_fun f :=
  match f with
    | xI => fail 1
    | xO => fail 1
    | _ => idtac
  end.

(* Remplace les symbole de fonction et de variables par des versions dans Z
   et ajoute les hypothèses de positivité *)
Ltac pos_renaming :=
  repeat
  match goal with
    | |-context [Pos2Z ?X] => is_var X; generalize (pos_is_ltb X); apply implb_impl; generalize (Pos2Z X); clear X; intro X
    | |-context [?X (Z2Pos ?Y)] => pos_is_uninterp_fun X; generalize_fun X Z2Pos; clear X; intro X
    | |-context [Pos2Z (?X ?Y)] => pos_is_uninterp_fun X; generalize_fun Pos2Z X; clear X; intro X
  end;
  unfold Pos2Z.

(* La tactique complète *)
Ltac pos_convert := intros; pos_converting; pos_rewriting; pos_renaming.

(**************************)
(**************************)
(* Conversion de N vers Z *)
(**************************)
(**************************)

Definition N2Z := Z.of_N.
Definition Z2N := Z.to_N.

(* Remplace tous les sous-termes n de type N par Z2N (N2Z n) *)
Ltac N_converting :=
  (* On crée une variable fraîche de type N *)
  let var := fresh "var" in
  pose proof N0 as var;
  (* Coeur de la tactique *)
  repeat
    match goal with
    (* On capture chaque sous-terme n avec son contexte, i.e. le but est C[n] *)
    | |- context C[?n]  =>
      (* Si n est de type N *)
      match type of n with
      | N =>
        match n with
        (* Si n est de la forme Z2N (N2Z _) on abandonne le match car n est déjà réécrit *)
        | Z2N (N2Z _) => fail 1
        (* Il n'est pas nécessaire de réécrire au dessus des symboles connus *)
        | N.add _ _ => fail 1
        | N.mul _ _ => fail 1
        | _ =>
          (* Sinon, on analyse la formule obtenue en remplaçant n par notre variable fraîche dans le but *)
          match context C[var] with
          (* Si elle contient le terme Z2N (N2Z var), cela signifie que le contexte C[]
             est de la forme C'[Z2N (N2Z [])] et donc on abandonne le match car n est déjà réécrit *)
          | context [Z2N (N2Z var)] => fail 1
          (* Sinon on réécrit *)
          | _ => replace n with (Z2N (N2Z n)) by apply N2Z.id
          end
        end
      end
    end;
  (* Finalement, on efface notre variable fraîche *)
  clear var.

(* Résoud les hypothèses de positivité lors de la réécriture des opérations *)
Ltac N_solve_pos := repeat (try apply Z.add_nonneg_nonneg; try apply Z.mul_nonneg_nonneg; try apply N2Z.is_nonneg).

Lemma N_inj_leb : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.leb x y = N.leb (Z2N x) (Z2N y).
Proof. intros; apply Bool.eq_true_iff_eq; rewrite N.leb_le; rewrite Z.leb_le; apply Z2N.inj_le; assumption. Qed.

Lemma N_inj_ltb : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.ltb x y = N.ltb (Z2N x) (Z2N y).
Proof. intros; apply Bool.eq_true_iff_eq; rewrite N.ltb_lt; rewrite Z.ltb_lt; apply Z2N.inj_lt; assumption. Qed.

Lemma N_inj_eqb : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.eqb x y = N.eqb (Z2N x) (Z2N y).
Proof. intros; apply Bool.eq_true_iff_eq; rewrite N.eqb_eq; rewrite Z.eqb_eq; symmetry; apply Z2N.inj_iff; assumption. Qed.

(* Réécrit les opérations et relations de positive vers Z *)
Ltac N_rewriting :=
  repeat
  match goal with
    | |-context [N.add (Z2N ?X) (Z2N ?Y) ] =>  replace (N.add (Z2N X) (Z2N Y)) with (Z2N (X + Y)) by (apply Z2N.inj_add; N_solve_pos)
    | |-context [N.mul (Z2N ?X) (Z2N ?Y) ] =>  replace (N.mul (Z2N X) (Z2N Y)) with (Z2N (X * Y)) by (apply Z2N.inj_mul; N_solve_pos)
    | |-context [N.ltb (Z2N ?X) (Z2N ?Y) ] =>  replace (N.ltb (Z2N X) (Z2N Y)) with (Z.ltb X Y) by (apply N_inj_ltb; N_solve_pos)
    | |-context [N.leb (Z2N ?X) (Z2N ?Y) ] =>  replace (N.leb (Z2N X) (Z2N Y)) with (Z.leb X Y) by (apply N_inj_leb; N_solve_pos)
    | |-context [N.eqb (Z2N ?X) (Z2N ?Y) ] =>  replace (N.eqb (Z2N X) (Z2N Y)) with (Z.eqb X Y) by (apply N_inj_eqb; N_solve_pos);rewrite Zeq_bool_Zeqb
  end.

(* Après avoir converti dans Z il faudra ajouter l'hypothèse de positivité *)
Lemma N_is_leb : forall n : N, Z.leb 0 (N2Z n) = true.
Proof. intro; apply Zle_imp_le_bool; apply N2Z.is_nonneg. Qed.

(* Réussit si f est un symbole de fonction non interprété *)
Ltac N_is_uninterp_fun f :=
  match f with
    | Npos => fail 1
    | _ => idtac
  end.

(* Remplace les symbole de fonction et de variables par des versions dans Z
   et ajoute les hypothèses de positivité *)
Ltac N_renaming :=
  repeat
  match goal with
    | |-context [N2Z ?X] => is_var X; generalize (N_is_leb X); apply implb_impl; generalize (N2Z X); clear X; intro X
    | |-context [?X (Z2N ?Y)] => N_is_uninterp_fun X; generalize_fun X Z2N; clear X; intro X
    | |-context [N2Z (?X ?Y)] => N_is_uninterp_fun X; generalize_fun N2Z X; clear X; intro X
  end;
  unfold N2Z; simpl.

(* La tactique complète *)
Ltac N_convert := intros; N_converting; N_rewriting; N_renaming.

(****************************)
(****************************)
(* Conversion de nat vers Z *)
(****************************)
(****************************)

(* Nécessaire dans native-coq *)
Require Import NPeano.

Definition Nat2Z := Z.of_nat.
Definition Z2Nat := Z.to_nat.

(* Remplace tous les sous-termes n de type nat par Z2Nat (Nat2Z n) *)
Ltac nat_converting :=
  (* On crée une variable fraîche de type nat *)
  let var := fresh "var" in
  pose proof O as var;
  (* Coeur de la tactique *)
  repeat
    match goal with
    (* On capture chaque sous-terme n avec son contexte, i.e. le but est C[n] *)
    | |- context C[?n]  =>
      (* Si n est de type nat *)
      match type of n with
      | nat =>
        match n with
        (* Si n est de la forme Z2Nat (Nat2Z _) on abandonne le match car n est déjà réécrit *)
        | Z2Nat (Nat2Z _) => fail 1
        (* Il n'est pas nécessaire de réécrire au dessus des symboles connus *)
        | Nat.add _ _ => fail 1
        | Nat.mul _ _ => fail 1
        | _ =>
          (* Sinon, on analyse la formule obtenue en remplaçant n par notre variable fraîche dans le but *)
          match context C[var] with
          (* Si elle contient le terme Z2Nat (Nat2Z var), cela signifie que le contexte C[]
             est de la forme C'[Z2Nat (Nat2Z [])] et donc on abandonne le match car n est déjà réécrit *)
          | context [Z2Nat (Nat2Z var)] => fail 1
          (* Sinon on réécrit *)
          | _ => replace n with (Z2Nat (Nat2Z n)) by apply Nat2Z.id
          end
        end
      end
    end;
  (* Finalement, on efface notre variable fraîche *)
  clear var.

(* Résoud les hypothèses de positivité lors de la réécriture des opérations *)
Ltac nat_solve_pos := repeat (try apply Z.add_nonneg_nonneg; try apply Z.mul_nonneg_nonneg; try apply Nat2Z.is_nonneg).

Lemma nat_inj_leb : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.leb x y = Nat.leb (Z2Nat x) (Z2Nat y).
Proof. intros; apply Bool.eq_true_iff_eq; rewrite Nat.leb_le; rewrite Z.leb_le; apply Z2Nat.inj_le; assumption. Qed.

Lemma nat_inj_ltb : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.ltb x y = Nat.ltb (Z2Nat x) (Z2Nat y).
Proof. intros; apply Bool.eq_true_iff_eq; rewrite Nat.ltb_lt; rewrite Z.ltb_lt; apply Z2Nat.inj_lt; assumption. Qed.

Lemma nat_inj_eqb : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.eqb x y = Nat.eqb (Z2Nat x) (Z2Nat y).
Proof. intros; apply Bool.eq_true_iff_eq; rewrite Nat.eqb_eq; rewrite Z.eqb_eq; symmetry; apply Z2Nat.inj_iff; assumption. Qed.

(* Réécrit les opérations et relations de positive vers Z *)
Ltac nat_rewriting :=
  repeat
  match goal with
    | |-context [Nat.add (Z2Nat ?X) (Z2Nat ?Y) ] =>  replace (Nat.add (Z2Nat X) (Z2Nat Y)) with (Z2Nat (X + Y)) by (apply Z2Nat.inj_add; nat_solve_pos)
    | |-context [Nat.mul (Z2Nat ?X) (Z2Nat ?Y) ] =>  replace (Nat.mul (Z2Nat X) (Z2Nat Y)) with (Z2Nat (X * Y)) by (apply Z2Nat.inj_mul; nat_solve_pos)
    | |-context [Nat.ltb (Z2Nat ?X) (Z2Nat ?Y) ] =>  replace (Nat.ltb (Z2Nat X) (Z2Nat Y)) with (Z.ltb X Y) by (apply nat_inj_ltb; nat_solve_pos)
    | |-context [Nat.leb (Z2Nat ?X) (Z2Nat ?Y) ] =>  replace (Nat.leb (Z2Nat X) (Z2Nat Y)) with (Z.leb X Y) by (apply nat_inj_leb; nat_solve_pos)
    | |-context [Nat.eqb (Z2Nat ?X) (Z2Nat ?Y) ] =>  replace (Nat.eqb (Z2Nat X) (Z2Nat Y)) with (Z.eqb X Y) by (apply nat_inj_eqb; nat_solve_pos);rewrite Zeq_bool_Zeqb
  end.

(* Après avoir converti dans Z il faudra ajouter l'hypothèse de positivité *)
Lemma nat_is_leb : forall n : nat, Z.leb 0 (Nat2Z n) = true.
Proof. intro; apply Zle_imp_le_bool; apply Nat2Z.is_nonneg. Qed.

(* Réussit si f est un symbole de fonction non interprété *)
Ltac nat_is_uninterp_fun f :=
  match f with
    | O => fail 1
    | S => fail 1
    | _ => idtac
  end.

(* Remplace les symbole de fonction et de variables par des versions dans Z
   et ajoute les hypothèses de positivité *)
Ltac nat_renaming :=
  repeat
  match goal with
    | |-context [Nat2Z ?X] => is_var X; generalize (nat_is_leb X); apply implb_impl; generalize (Nat2Z X); clear X; intro X
    | |-context [?X (Z2Nat ?Y)] => nat_is_uninterp_fun X; generalize_fun X Z2Nat; clear X; intro X
    | |-context [Nat2Z (?X ?Y)] => nat_is_uninterp_fun X; generalize_fun Nat2Z X; clear X; intro X
  end;
  unfold Nat2Z; simpl.

(* La tactique complète *)
(* Les "fold" sont nécessaires car dans les anciennes versions de Coq
   les notations +, *, <? et <=? se réfèrent à plus, mult, ltb et leb
   et les Nat._ sont définis à partir de plus, mult, ltb et leb. *)
Ltac nat_convert := fold Nat.add; fold Nat.mul; fold Nat.ltb; fold Nat.leb; fold Nat.eqb; intros; nat_converting; nat_rewriting; nat_renaming.

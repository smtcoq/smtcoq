Require Import ZArith.

(* Ce module représente la structure que l'on souhaite convertir vers Z *)
Module Type convert_type.

(* Le type que l'on souhaite convertir *)
Parameter T : Type.

(* Les conversion dans les deux sens *)
Parameter Z2T : Z -> T.
Parameter T2Z : T -> Z.
(* T2Z est une injection *)
Axiom T2Z_id : forall x : T, Z2T (T2Z x) = x.

(* Une propriété décrivant les éléments de Z qui viennent d'éléments de T.
   Par exemple, pour nat il s'agit de (0 <=? z)%Z *)
Parameter inT : Z -> bool.
(* L'image de l'injection satisfait cette propriété *)
Axiom T2Z_pres : forall x, inT (T2Z x) = true.

(* Addition *)
Parameter add : T -> T -> T.
(* Pour des éléments venant de T, l'addition commute avec Z2T *)
Axiom add_morph : forall x y, inT x = true -> inT y = true -> add (Z2T x) (Z2T y) = Z2T (Z.add x y).
(* Pour des éléments venant de T, l'addition vient de T *)
Axiom add_pres : forall x y, inT x = true -> inT y = true -> inT (Z.add x y) = true.

(* Multiplication *)
Parameter mul : T -> T -> T.
(* Pour des éléments venant de T, la multiplication commute avec Z2T *)
Axiom mul_morph : forall x y, inT x = true -> inT y = true -> mul (Z2T x) (Z2T y) = Z2T (Z.mul x y).
(* Pour des éléments venant de T, la multiplication vient de T *)
Axiom mul_pres : forall x y, inT x = true -> inT y = true -> inT (Z.mul x y) = true.

(* <= *)
Parameter leb : T -> T -> bool.
(* Pour des éléments venant de T, <= commute avec Z2T *)
Axiom leb_morph : forall x y, inT x = true -> inT y = true -> Z.leb x y = leb (Z2T x) (Z2T y).

(* < *)
Parameter ltb : T -> T -> bool.
(* Pour des éléments venant de T, < commute avec Z2T *)
Axiom ltb_morph : forall x y, inT x = true -> inT y = true -> Z.ltb x y = ltb (Z2T x) (Z2T y).

(* = *)
Parameter eqb : T -> T -> bool.
(* Pour des éléments venant de T, = commute avec Z2T *)
Axiom eqb_morph : forall x y, inT x = true -> inT y = true -> Z.eqb x y = eqb (Z2T x) (Z2T y).

End convert_type.

(* Ce foncteur construit une tactique de conversion à partir d'un module du type ci-dessus *)
Module convert (M : convert_type).

Import M.

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

Ltac get_head x := lazymatch x with ?x _ => get_head x | _ => x end.

(* native-coq est basé sur coq 8.3 qui ne supporte pas la construction de termes
   par des tactiques (tactic-in-term). On utilise donc un "try" et un "fail 1".
   is_not_constructor T sym échoue si et seulement si sym est un symbole de constructeur de U *)
Ltac is_not_constructor T sym :=
assert (T -> True) by
       (let x := fresh in
        let y := fresh in
        intro x;
        pose x as y;
        destruct x;
        let C := eval unfold y in y in
        let c := get_head C in
        try (constr_eq sym c; fail 1); exact I).

(* inverse_tactic tactic réussit là où tactic échoue et inversement *)
Ltac inverse_tactic tactic := try (tactic; fail 1).

(* is_not_constructor U sym réussit si et seulement si sym est un symbole de constructeur de U *)
Ltac is_constructor U sym := inverse_tactic ltac:(is_not_constructor U sym).

(* Remplace tous les sous-termes x de type T par Z2T (T2Z p) *)
Ltac converting :=
  (* Coeur de la tactique *)
  repeat
    match goal with
    (* On capture chaque sous-terme x avec son contexte, i.e. le but est C[x] *)
    | |- appcontext C[?x]  =>
      (* Si x est de type T *)
      let U := type of x in
      lazymatch eval fold T in U with
      | T =>
        lazymatch x with
        (* Si x est de la forme Z2T (T2Z _) on abandonne le match car x est déjà réécrit *)
        | Z2T (T2Z _) => fail
        (* Il n'est pas nécessaire de réécrire au dessus des symboles connus *)
        | add _ _ => fail
        | mul _ _ => fail
        | _ =>
          (* On crée une variable fraîche de type T *)
          let var := fresh in
          pose proof x as var;
          (* Sinon, on analyse la formule obtenue en remplaçant x par notre variable fraîche dans le but *)
          lazymatch context C[var] with
          (* Si elle contient le terme Z2T (T2Z var), cela signifie que le contexte C[]
             est de la forme C'[Z2T (T2Z [])] et donc on abandonne le match car x est déjà réécrit *)
          | appcontext [Z2T (T2Z var)] => fail
          (* Idem: si le contexte contient un constructeur de Z, c'est qu'on est à l'intérieur d'une constante *)
          | appcontext [Zpos var] => fail
          | appcontext [Zneg var] => fail
          | appcontext [?h var] =>
            (* Idem: si le contexte contient un constructeur de T et que x commence par un
               constructeur de T, c'est qu'on est à l'intérieur d'une constante *)
            let h := get_head h in
            let hx := get_head x in
            try (is_constructor T h; is_constructor T hx; fail 1);
            (* Sinon, on réécrit *)
            let old_goal := context C[x] in
            let new_goal := context C[Z2T (T2Z x)] in
            replace old_goal with new_goal by (rewrite (T2Z_id x); reflexivity)
          end;
          (* On efface notre variable fraîche *)
          clear var
        end
      end
    end.

(* Résoud les hypothèses inT lors de la réécriture des opérations *)
Ltac solve_inT := repeat (try apply add_pres; try apply mul_pres; try apply T2Z_pres); reflexivity.

(* Réécrit les opérations et relations de T vers Z *)
Ltac rewriting :=
  repeat
  match goal with
    | |- context [add (Z2T ?X) (Z2T ?Y)] => replace (add (Z2T X) (Z2T Y)) with (Z2T (X + Y)) by (rewrite add_morph; solve_inT)
    | |- context [mul (Z2T ?X) (Z2T ?Y)] => replace (mul (Z2T X) (Z2T Y)) with (Z2T (X * Y)) by (rewrite mul_morph; solve_inT)
    | |- context [ltb (Z2T ?X) (Z2T ?Y)] => replace (ltb (Z2T X) (Z2T Y)) with (Z.ltb X Y) by (rewrite ltb_morph; solve_inT)
    | |- context [leb (Z2T ?X) (Z2T ?Y)] => replace (leb (Z2T X) (Z2T Y)) with (Z.leb X Y) by (rewrite leb_morph; solve_inT)
    | |- context [eqb (Z2T ?X) (Z2T ?Y)] => replace (eqb (Z2T X) (Z2T Y)) with (Z.eqb X Y) by (rewrite eqb_morph; solve_inT); rewrite Zeq_bool_Zeqb
  end.

(* Remplace les symbole de fonction et de variables par des versions dans Z
   et ajoute les hypothèses de positivité *)
Ltac renaming :=
  repeat
  match goal with
    | |-context [T2Z ?X] => is_var X; generalize (T2Z_pres X); apply implb_impl; generalize (T2Z X); clear X; intro X
    | |-context [?X (Z2T ?Y)] => try (is_constructor T X; fail 1); generalize_fun X Z2T; clear X; intro X
    | |-context [T2Z (?X ?Y)] => try (is_constructor T X; fail 1); generalize_fun T2Z X; clear X; intro X
  end.

(* La tactique complète *)
Ltac convert :=
fold T add mul ltb leb eqb;
intros;
converting;
rewriting;
renaming;
let T2Z_unfolded := eval red in T2Z in change T2Z with T2Z_unfolded;
let inT_unfolded := eval red in inT in change inT with inT_unfolded;
simpl.

End convert.

Module pos_convert_type <: convert_type.

Definition T : Type := positive.

Definition Z2T : Z -> T := fun z =>
  match z with
    | 0%Z => 1%positive
    | Zpos p => p
    | Zneg _ => 1%positive
  end.

Definition T2Z : T -> Z := Zpos.
Lemma T2Z_id : forall x : T, Z2T (T2Z x) = x. reflexivity. Qed.

Definition inT : Z -> bool := fun z => Z.ltb 0 z.
Lemma T2Z_pres : forall x, inT (T2Z x) = true. reflexivity. Qed.

Definition add : T -> T -> T := Pos.add.
Lemma add_morph : forall x y, inT x = true -> inT y = true -> add (Z2T x) (Z2T y) = Z2T (Z.add x y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.
Lemma add_pres : forall x y, inT x = true -> inT y = true -> inT (Z.add x y) = true.
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition mul : T -> T -> T := Pos.mul.
Lemma mul_morph : forall x y, inT x = true -> inT y = true -> mul (Z2T x) (Z2T y) = Z2T (Z.mul x y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.
Lemma mul_pres : forall x y, inT x = true -> inT y = true -> inT (Z.mul x y) = true.
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition leb : T -> T -> bool := Pos.leb.
Lemma leb_morph : forall x y, inT x = true -> inT y = true -> Z.leb x y = leb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition ltb : T -> T -> bool := Pos.ltb.
Lemma ltb_morph : forall x y, inT x = true -> inT y = true -> Z.ltb x y = ltb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition eqb : T -> T -> bool := Pos.eqb.
Lemma eqb_morph : forall x y, inT x = true -> inT y = true -> Z.eqb x y = eqb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

End pos_convert_type.

Module pos_convert_mod := convert pos_convert_type.

Ltac pos_convert := pos_convert_mod.convert.

Module N_convert_type <: convert_type.

Definition T : Type := N.

Definition Z2T : Z -> T := Z.to_N.

Definition T2Z : T -> Z := Z.of_N.
Lemma T2Z_id : forall x : T, Z2T (T2Z x) = x. exact N2Z.id. Qed.

Definition inT : Z -> bool := fun z => Z.leb 0 z.
Lemma T2Z_pres : forall x, inT (T2Z x) = true. intro; unfold inT; rewrite Z.leb_le; apply N2Z.is_nonneg. Qed.

Definition add : T -> T -> T := N.add.
Lemma add_morph : forall x y, inT x = true -> inT y = true -> add (Z2T x) (Z2T y) = Z2T (Z.add x y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.
Lemma add_pres : forall x y, inT x = true -> inT y = true -> inT (Z.add x y) = true.
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition mul : T -> T -> T := N.mul.
Lemma mul_morph : forall x y, inT x = true -> inT y = true -> mul (Z2T x) (Z2T y) = Z2T (Z.mul x y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.
Lemma mul_pres : forall x y, inT x = true -> inT y = true -> inT (Z.mul x y) = true.
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition leb : T -> T -> bool := N.leb.
Lemma leb_morph : forall x y, inT x = true -> inT y = true -> Z.leb x y = leb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition ltb : T -> T -> bool := N.ltb.
Lemma ltb_morph : forall x y, inT x = true -> inT y = true -> Z.ltb x y = ltb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition eqb : T -> T -> bool := N.eqb.
Lemma eqb_morph : forall x y, inT x = true -> inT y = true -> Z.eqb x y = eqb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

End N_convert_type.

Module N_convert_mod := convert N_convert_type.

Ltac N_convert := N_convert_mod.convert.

Require Import NPeano.
Module nat_convert_type <: convert_type.

Definition T : Type := nat.

Definition Z2T : Z -> T := Z.to_nat.

Definition T2Z : T -> Z := Z.of_nat.
Lemma T2Z_id : forall x : T, Z2T (T2Z x) = x. exact Nat2Z.id. Qed.

Definition inT : Z -> bool := fun z => Z.leb 0 z.
Lemma T2Z_pres : forall x, inT (T2Z x) = true. intro; unfold inT; rewrite Z.leb_le; apply Nat2Z.is_nonneg. Qed.

Definition add : T -> T -> T := Nat.add.
Lemma add_morph : forall x y, inT x = true -> inT y = true -> add (Z2T x) (Z2T y) = Z2T (Z.add x y).
intros x y; destruct x, y; try discriminate; try reflexivity.
intros; apply Nat.add_0_r.
unfold inT; rewrite 2 Z.leb_le.
symmetry; apply Z2Nat.inj_add; assumption.
Qed.
Lemma add_pres : forall x y, inT x = true -> inT y = true -> inT (Z.add x y) = true.
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition mul : T -> T -> T := Nat.mul.
Lemma mul_morph : forall x y, inT x = true -> inT y = true -> mul (Z2T x) (Z2T y) = Z2T (Z.mul x y).
intros x y; destruct x, y; try discriminate; try reflexivity.
intros; apply Nat.mul_0_r.
unfold inT; rewrite 2 Z.leb_le.
symmetry; apply Z2Nat.inj_mul; assumption.
Qed.
Lemma mul_pres : forall x y, inT x = true -> inT y = true -> inT (Z.mul x y) = true.
intros x y; destruct x, y; try discriminate; reflexivity. Qed.

Definition leb : T -> T -> bool := Nat.leb.
Lemma leb_morph : forall x y, inT x = true -> inT y = true -> Z.leb x y = leb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; try reflexivity.
intros H1 H2; clear H1 H2; change (Zpos p <=? 0)%Z with false; unfold Z2T, leb; symmetry.
apply Bool.not_true_is_false; rewrite Nat.leb_le.
apply lt_not_le; apply Pos2Nat.is_pos.
intros H1 H2; unfold Z2T, leb; apply Bool.eq_true_iff_eq.
rewrite Z.leb_le, Nat.leb_le, Z2Nat.inj_le; try reflexivity; apply Zle_0_pos.
Qed.

Definition ltb : T -> T -> bool := Nat.ltb.
Lemma ltb_morph : forall x y, inT x = true -> inT y = true -> Z.ltb x y = ltb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; try reflexivity.
intros H1 H2; clear H1 H2; change (0 <? Zpos p)%Z with true.
unfold Z2T, ltb; symmetry.
rewrite Nat.ltb_lt, <- Z2Nat.inj_lt; try rewrite <- Z.leb_le; reflexivity.
intros H1 H2; clear H1 H2; unfold Z2T, ltb.
apply Bool.eq_true_iff_eq.
rewrite Z.ltb_lt, Nat.ltb_lt.
rewrite Z2Nat.inj_lt; try reflexivity; apply Zle_0_pos.
Qed.

Definition eqb : T -> T -> bool := Nat.eqb.
Lemma eqb_morph : forall x y, inT x = true -> inT y = true -> Z.eqb x y = eqb (Z2T x) (Z2T y).
intros x y; destruct x, y; try discriminate; try reflexivity; unfold inT, Z2T, eqb.
intros H1 H2; clear H1 H2; change (0 =? Zpos p)%Z with false; symmetry.
rewrite Nat.eqb_neq, Z2Nat.inj_iff; discriminate.
intros H1 H2; clear H1 H2; change (Zpos p =? 0)%Z with false; symmetry.
rewrite Nat.eqb_neq, Z2Nat.inj_iff; discriminate.
intros H1 H2; clear H1 H2; apply Bool.eq_true_iff_eq.
rewrite Z.eqb_eq, Nat.eqb_eq, Z2Nat.inj_iff; try reflexivity; apply Zle_0_pos.
Qed.

End nat_convert_type.

Module nat_convert_mod := convert nat_convert_type.

Ltac nat_convert := fold Nat.add Nat.mul Nat.leb Nat.ltb Nat.eqb; nat_convert_mod.convert.
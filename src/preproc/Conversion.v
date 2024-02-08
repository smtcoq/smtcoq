(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


From Ltac2 Require Import Ltac2 Printf Control Fresh Bool Constr.
From Trakt Require Import Trakt.
Require Import Database_trakt.
Require Import ZArith.

Require SMT_classes BVList FArray.


(* Conversion tactic *)

Infix "--->" := implb (at level 60, right associativity) : bool_scope.
Infix "<--->" := Bool.eqb (at level 60, right associativity) : bool_scope.

(* fail with a message *)

Ltac2 fail s := Control.backtrack_tactic_failure s.

(* Get all hypotheses of type Prop *)

Ltac2 get_hyps_prop () := 
  let hs := hyps () in
  List.filter (fun (id, opt, ty) => neg (equal (type ty) 'Prop)) hs. 

(* Assert global and local hypotheses (local: to avoid problems with Section variables) *)

Ltac2 duplicate_hypotheses () : ident list :=
  let hs := Control.hyps () in
  let rec aux hs acc :=
    match hs with
      | (id, _, _) :: hs' =>
          let fresh_id := in_goal id in
          let t := hyp id in
          assert ($fresh_id := $t) ; aux hs' (fresh_id::acc)
      | _ => acc
    end 
  in aux hs [].

Ltac2 assert_list (hs : constr list) :=
  let rec aux hs acc :=
    match hs with
      | h :: hs' =>
          let fresh_id := in_goal @H in
          assert ($fresh_id := $h) ; aux hs' (fresh_id::acc)
      | _ => acc
    end 
  in aux hs [].

Ltac2 pose_hyps hs := 
  let hs1 := duplicate_hypotheses () in
  let hs2 := assert_list hs in
  List.append hs1 hs2.

(* Goal True -> False -> True -> nat -> Type.
intros.
let ids := pose_hyps ['(@List.nil_cons positive 5%positive nil); '(@List.nil_cons N 42%N nil); 'List.nil_cons] 
in List.iter (fun x => Message.print (Message.of_ident x)) ids. *)
(* Abort. *)

(* List of interpreted types *)

Ltac2 is_interpreted_type t :=
  match! t with
  | BVList.BITVECTOR_LIST.bitvector _ => true
  | FArray.farray _ _ => true
  | Z => true | nat => true | positive => true
  | bool => true
  | _ => false
  end.


(* Add CompDec for types over which an equality appears in the goal or
   in a local hypothesis *)

Ltac2 rec add_compdecs_term (u : constr) :=
  match! u with
    | context c [@Logic.eq ?t _ _] => 
      let u' := Pattern.instantiate c 'True in 
      match is_interpreted_type t with
        | true => add_compdecs_term u'
        | false =>
            let hs := hyps () in
            let rec aux hs :=
              match hs with
                | [] =>
                    let fresh_id := in_goal ident:(p) in
                    assert ($fresh_id: SMT_classes.CompDec $t) > [ try (exact _) | () ]
                | (_, _, ty) :: hs' =>
                    match! ty with
                      | SMT_classes.CompDec ?t' => 
                          if equal t t' then ()
                          else aux hs'
                      | _ => aux hs'
                    end
              end in aux hs ; Control.enter (fun () => add_compdecs_term u')
        end
    | _ => ()
   end. 

Ltac2 add_compdecs () :=
  let hs := hyps () in
  let hs' := List.map (fun (_, _, ty) => ty) hs in
  let g := goal () in 
  List.iter (fun x => Control.enter (fun () => add_compdecs_term x)) (List.append hs' [g]).

(*  Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C),
    3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 ->
     17%positive = 42%positive /\ (5,6) = (6,7). 
 Proof. 
  intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros.
   add_compdecs ().
   Show 3.
 Abort. *)


(* Collect CompDec in local hypotheses *)

Ltac2 collect_compdecs () :=
  let hs := hyps () in
  List.filter 
    ( fun (_, _, ty) => 
        match! ty with
          | SMT_classes.CompDec ?t  => neg (is_interpreted_type t)
          | _ => false
        end) hs.

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C),
     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 ->
     17%positive = 42%positive /\ (5,6) = (6,7).
 Proof.
   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros.
   add_compdecs_terms ().
   Focus 3.
   let cs := collect_compdecs () in List.iter (fun (_, _, x) => printf "%t" x) cs.
 Abort. *)


(* Generate CompDec rels for trakt *)

Ltac2 generate_rels compdecs :=
  List.fold_left
    (fun acc (id, _, ty) =>
      match! ty with
        | SMT_classes.CompDec ?a =>
         let ha := hyp id in
         let rel := 
            constr:((2%nat, @eq $a, @SMT_classes.eqb_of_compdec $a $ha, @SMT_classes.compdec_eq_eqb $a $ha)) in
            rel :: acc
        | _ => acc
      end) compdecs [].

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C),
     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 ->
     17%positive = 42%positive /\ (5,6) = (6,7).
 Proof.
   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros.
   add_compdecs ().
   Focus 3.
   let cs := collect_compdecs () in
   let rels := generate_rels cs in
   List.iter (fun x => printf "the relation is %t" x) rels.
 Abort. *)

(* Use trakt *)

Ltac2 rec list_to_tuple (l : constr list) : constr :=
  match l with
    | [] => fail "cannot have an empty tuple"
    | [x] => x
    | x :: xs => 
       let t := type x in
       let res := list_to_tuple xs in
       let t' := type res in
       constr:(@pair $t' $t $res $x)
  end.

Ltac2 rec trakt_rels rels :=
  match rels with
    | [] => ltac1:(trakt Z bool)
    | _ :: _ => 
      printf "tutu";
      let res := Ltac1.of_constr (list_to_tuple rels) in printf "titi" ;
      ltac1:(res |- idtac res ; trakt Z bool with rel res) res
  end.

 

Ltac2 rec revert_and_trakt hs rels :=
  match hs with
    | id :: xs => revert $id ; revert_and_trakt xs rels
    | [] => trakt_rels rels
  end.


Ltac2 rec post_trakt hs :=
  match hs with
    | [] => ()
    | h :: xs => 
        ltac1:(H |- try (revert H; trakt_reorder_quantifiers; trakt_boolify_arrows; intro H)) (Ltac1.of_ident h);
        post_trakt xs
  end. 

Ltac2 trakt1 rels hs :=
  match hs with
  | Some hs => revert_and_trakt hs rels
  | None => trakt_rels rels
  end.


(* Section Test.
   Variables (A:Type) (HA:SMT_classes.CompDec A).

   Goal forall (a1 a2:A), a1 = a2.
   Proof.
     intros a1 a2. 
     ltac1:(trakt Z bool with rel (2%nat, @eq A, @SMT_classes.eqb_of_compdec A HA, @SMT_classes.compdec_eq_eqb A HA)).
   Abort.
End Test. *)

(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C),
     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 ->
     17%positive = 42%positive /\ (5,6) = (6,7).
 Proof.
   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros H.
   add_compdecs ().
   Focus 12.
   (* Set Printing All. *) 
  let cs := collect_compdecs () in 
  let rels := generate_rels cs in
   trakt1 rels (Some [@H]).
Abort. *)


(* Remove quantifications on CompDecs in hypotheses *)

(* Ltac2 rec remove_compdec_hyp (h : (ident* constr option* constr)): unit :=
  let (id, _ , th) := h in 
  match! th with
  | forall p : SMT_classes.CompDec ?a, _ =>  
    match! goal with
    | [ p' : SMT_classes.CompDec ?a' |- _ ] =>
      if equal a a' then
      let h' := hyp id in
      let h1 := in_goal id in
      assert ($h1 := $h' $p'); clear h'; assert ($h1 := $h'); clear h1;
      remove_compdec_hyp h
      else
      let c := in_goal ident:(c) in
      assert (c : SMT_classes.CompDec ?a) >
      [ try (exact _) | 
          let h' := hyp id in
          let h1 := in_goal id in
          assert ($h1 := $h' $p'); clear h'; assert ($h1 := $h'); clear h1;
          remove_compdec_hyp h ]
    | [ |- _ ] =>
      let c := in_goal ident:(c) in
      assert (c : SMT_classes.CompDec ?a) >
      [ try (exact _)
      |       let h' := hyp id in
      let h1 := in_goal id in
      let c' := hyp c in
      assert ($h1 := $h' $c'); clear h'; assert ($h1 := $h'); clear h1;
      remove_compdec_hyp h ]
    end
  | _ => ()
  end. *)


(* Remove quantifications on CompDecs in hypotheses *)

Ltac remove_compdec_hyp H :=
  let TH := type of H in
  match TH with
  | forall p : SMT_classes.CompDec ?A, _ =>
    match goal with
    | [ p' : SMT_classes.CompDec A |- _ ] =>
      let H1 := fresh in
      assert (H1 := H p'); clear H; assert (H := H1); clear H1;
      remove_compdec_hyp H
    | _ =>
      let c := fresh "c" in
      assert (c : SMT_classes.CompDec A);
      [ try (exact _)
      | let H1 := fresh in
        assert (H1 := H c); clear H; assert (H := H1); clear H1;
        remove_compdec_hyp H ]
    end
  | _ => idtac
  end.

Ltac2 remove_compdec_hyps hs :=
  List.iter (fun (x, y, z) => ltac1:(h |- remove_compdec_hyp h) (Ltac1.of_ident x)) hs.

Ltac2 remove_compdec_hyps_option hs :=
  match hs with
  | Some hs => remove_compdec_hyps hs
  | None => ()
  end.


(* Perform all the preprocessing *)

Ltac2 preprocess1 hs := 
   add_compdecs () >
    [ .. |
    remove_compdec_hyps_option hs;
    let cpds := collect_compdecs () in
    let rels := generate_rels cpds in
    trakt1 rels (Option.map (List.map (fun (id, _, _) => id)) hs)].


(* Goal forall (A B C:Type) (HA:SMT_classes.CompDec A) (a1 a2:A) (b1 b2 b3 b4:B) (c1 c2:C), 
     3%Z = 4%Z /\ a1 = a2 /\ b1 = b2 /\ b3 = b4 /\ 5%nat = 6%nat /\ c1 = c2 ->
     17%positive = 42%positive /\ (5,6) = (6,7) (* /\ 0%N = 0%N *).
Proof. 
   intros A B C HA a1 a2 b1 b2 b3 b4 c1 c2. intros.
   assert (H1 := @List.nil_cons positive 5%positive nil). 
   preprocess1 None.
   Show 3.
 Abort. *)

Ltac2 preprocess2 hs' :=
  match hs' with
  | Some hs' => post_trakt hs'
  | None => ()
  end.




Definition sep := True.

Ltac get_hyps_upto_sep :=
  lazymatch goal with
  | H' : ?P |- _ =>
    lazymatch P with
    | sep => constr:(@None unit)
    | _ =>
      let T := type of P in
      lazymatch T with
      | Prop =>
        let _ := match goal with _ => revert H' end in
        let acc := get_hyps_upto_sep in
        let _ := match goal with _ => intro H' end in
        lazymatch acc with
        | Some ?acc' => constr:(Some (acc', H'))
        | None => constr:(Some H')
        end
      | _ =>
        let _ := match goal with _ => revert H' end in
        let acc := get_hyps_upto_sep in
        let _ := match goal with _ => intro H' end in
        acc
      end
    end
  end.

(* Goal False -> 1 = 1 -> unit -> false = true -> True. *)
(* Proof. *)
(*   intros H1 H2. *)
(*   assert (H : sep) by exact I. *)
(*   intros H3 H4. *)
(*   let Hs := get_hyps_upto_sep in idtac Hs. *)
(* Abort. *)


Ltac intros_names :=
  let H := fresh in
  let _ := match goal with _ => assert (H : sep) by exact I; intros end in
  let Hs := get_hyps_upto_sep in
  let _ := match goal with _ => clear H end in
  Hs.


(* Goal False -> 1 = 1 -> unit -> false = true -> True.
Proof.
   intros H1 H2.
   ltac1:(let Hs := intros_names in idtac Hs). 
Abort.  *)

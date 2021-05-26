(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2021                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

(** val implb : bool -> bool -> bool **)

let implb b1 b2 =
  if b1 then b2 else true

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

(** val fst : ('a1*'a2) -> 'a1 **)

let fst = function
| x,y -> x

(** val snd : ('a1*'a2) -> 'a2 **)

let snd = function
| x,y -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val compOpp : ExtrNative.comparison -> ExtrNative.comparison **)

let compOpp = function
| ExtrNative.Eq -> ExtrNative.Eq
| ExtrNative.Lt -> ExtrNative.Gt
| ExtrNative.Gt -> ExtrNative.Lt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : ExtrNative.comparison -> compareSpecT **)

let compareSpec2Type = function
| ExtrNative.Eq -> CompEqT
| ExtrNative.Lt -> CompLtT
| ExtrNative.Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type :
    'a1 -> 'a1 -> ExtrNative.comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val plus : nat -> nat -> nat **)

let rec plus n0 m =
  match n0 with
  | O -> m
  | S p -> S (plus p m)

(** val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec nat_iter n0 f x =
  match n0 with
  | O -> x
  | S n' -> f (nat_iter n' f x)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

module type TotalOrder' = 
 sig 
  type t 
 end

module MakeOrderTac = 
 functor (O:TotalOrder') ->
 struct 
  
 end

module MaxLogicalProperties = 
 functor (O:TotalOrder') ->
 functor (M:sig 
  val max : O.t -> O.t -> O.t
 end) ->
 struct 
  module Private_Tac = MakeOrderTac(O)
 end

module Pos = 
 struct 
  type t = positive
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p2 -> XI (XO (add (square p2) p2))
  | XO p2 -> XO (XO (square p2))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p2 -> p2
  | XO p2 -> p2
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p2 -> succ p2
  | XO p2 -> p2
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p2 -> S (size_nat p2)
  | XO p2 -> S (size_nat p2)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p2 -> succ (size p2)
  | XO p2 -> succ (size p2)
  | XH -> XH
  
  (** val compare_cont :
      positive -> positive -> ExtrNative.comparison -> ExtrNative.comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q ExtrNative.Gt
       | XH -> ExtrNative.Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q ExtrNative.Lt
       | XO q -> compare_cont p q r
       | XH -> ExtrNative.Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> ExtrNative.Lt)
  
  (** val compare : positive -> positive -> ExtrNative.comparison **)
  
  let compare x y =
    compare_cont x y ExtrNative.Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | ExtrNative.Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | ExtrNative.Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> eqb p2 q0
       | _ -> false)
    | XO p2 ->
      (match q with
       | XO q0 -> eqb p2 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | ExtrNative.Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | ExtrNative.Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
      positive*mask **)
  
  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then (XI s),(sub_mask r' s') else (XO s),(IsPos r')
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))
  
  (** val sqrtrem : positive -> positive*mask **)
  
  let rec sqrtrem = function
  | XI p2 ->
    (match p2 with
     | XI p3 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p3)
     | XO p3 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p3)
     | XH -> XH,(IsPos (XO XH)))
  | XO p2 ->
    (match p2 with
     | XI p3 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p3)
     | XO p3 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p3)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | ExtrNative.Eq -> a
             | ExtrNative.Lt -> gcdn n1 (sub b' a') a
             | ExtrNative.Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> positive -> positive -> positive*(positive*positive) **)
  
  let rec ggcdn n0 a b =
    match n0 with
    | O -> XH,(a,b)
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | ExtrNative.Eq -> a,(XH,XH)
             | ExtrNative.Lt ->
               let g,p = ggcdn n1 (sub b' a') a in
               let ba,aa = p in g,(aa,(add aa (XO ba)))
             | ExtrNative.Gt ->
               let g,p = ggcdn n1 (sub a' b') b in
               let ab,bb = p in g,((add bb (XO ab)),bb))
          | XO b0 ->
            let g,p = ggcdn n1 a b0 in let aa,bb = p in g,(aa,(XO bb))
          | XH -> XH,(a,XH))
       | XO a0 ->
         (match b with
          | XI p ->
            let g,p2 = ggcdn n1 a0 b in let aa,bb = p2 in g,((XO aa),bb)
          | XO b0 -> let g,p = ggcdn n1 a0 b0 in (XO g),p
          | XH -> XH,(a,XH))
       | XH -> XH,(XH,b))
  
  (** val ggcd : positive -> positive -> positive*(positive*positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> XI (coq_lor p2 q0)
       | XO q0 -> XI (coq_lor p2 q0)
       | XH -> p)
    | XO p2 ->
      (match q with
       | XI q0 -> XI (coq_lor p2 q0)
       | XO q0 -> XO (coq_lor p2 q0)
       | XH -> XI p2)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p2 q0)
       | XO q0 -> coq_Ndouble (coq_land p2 q0)
       | XH -> Npos XH)
    | XO p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p2 q0)
       | XO q0 -> coq_Ndouble (coq_land p2 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p2 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p2 q0)
       | XH -> Npos (XO p2))
    | XO p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p2 q0)
       | XO q0 -> coq_Ndouble (ldiff p2 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p2 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p2 q0)
       | XH -> Npos (XO p2))
    | XO p2 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p2 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p2 q0)
       | XH -> Npos (XI p2))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p2 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p2 n')
    | XO p2 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p2 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p2 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p2 (pred_N n1))
    | XO p2 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p2 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p2 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p2 -> op a (iter_op op p2 (op a a))
    | XO p2 -> iter_op op p2 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos = 
 struct 
  module Coq__1 = struct 
   type t = positive
  end
  type t = Coq__1.t
  
  (** val succ : positive -> positive **)
  
  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH
  
  (** val add : positive -> positive -> positive **)
  
  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH ->
      (match y with
       | XI q -> XO (succ q)
       | XO q -> XI q
       | XH -> XO XH)
  
  (** val add_carry : positive -> positive -> positive **)
  
  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)
  
  (** val pred_double : positive -> positive **)
  
  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH
  
  (** val pred : positive -> positive **)
  
  let pred = function
  | XI p -> XO p
  | XO p -> pred_double p
  | XH -> XH
  
  (** val pred_N : positive -> n **)
  
  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  (** val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rect f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1 **)
  
  let mask_rec f f0 f1 = function
  | IsNul -> f
  | IsPos x -> f0 x
  | IsNeg -> f1
  
  (** val succ_double_mask : mask -> mask **)
  
  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg
  
  (** val double_mask : mask -> mask **)
  
  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0
  
  (** val double_pred_mask : positive -> mask **)
  
  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul
  
  (** val pred_mask : mask -> mask **)
  
  let pred_mask = function
  | IsPos q ->
    (match q with
     | XH -> IsNul
     | _ -> IsPos (pred q))
  | _ -> IsNeg
  
  (** val sub_mask : positive -> positive -> mask **)
  
  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH ->
      (match y with
       | XH -> IsNul
       | _ -> IsNeg)
  
  (** val sub_mask_carry : positive -> positive -> mask **)
  
  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg
  
  (** val sub : positive -> positive -> positive **)
  
  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH
  
  (** val mul : positive -> positive -> positive **)
  
  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
  
  (** val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let rec iter n0 f x =
    match n0 with
    | XI n' -> f (iter n' f (iter n' f x))
    | XO n' -> iter n' f (iter n' f x)
    | XH -> f x
  
  (** val pow : positive -> positive -> positive **)
  
  let pow x y =
    iter y (mul x) XH
  
  (** val square : positive -> positive **)
  
  let rec square = function
  | XI p2 -> XI (XO (add (square p2) p2))
  | XO p2 -> XO (XO (square p2))
  | XH -> XH
  
  (** val div2 : positive -> positive **)
  
  let div2 = function
  | XI p2 -> p2
  | XO p2 -> p2
  | XH -> XH
  
  (** val div2_up : positive -> positive **)
  
  let div2_up = function
  | XI p2 -> succ p2
  | XO p2 -> p2
  | XH -> XH
  
  (** val size_nat : positive -> nat **)
  
  let rec size_nat = function
  | XI p2 -> S (size_nat p2)
  | XO p2 -> S (size_nat p2)
  | XH -> S O
  
  (** val size : positive -> positive **)
  
  let rec size = function
  | XI p2 -> succ (size p2)
  | XO p2 -> succ (size p2)
  | XH -> XH
  
  (** val compare_cont :
      positive -> positive -> ExtrNative.comparison -> ExtrNative.comparison **)
  
  let rec compare_cont x y r =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont p q r
       | XO q -> compare_cont p q ExtrNative.Gt
       | XH -> ExtrNative.Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont p q ExtrNative.Lt
       | XO q -> compare_cont p q r
       | XH -> ExtrNative.Gt)
    | XH ->
      (match y with
       | XH -> r
       | _ -> ExtrNative.Lt)
  
  (** val compare : positive -> positive -> ExtrNative.comparison **)
  
  let compare x y =
    compare_cont x y ExtrNative.Eq
  
  (** val min : positive -> positive -> positive **)
  
  let min p p' =
    match compare p p' with
    | ExtrNative.Gt -> p'
    | _ -> p
  
  (** val max : positive -> positive -> positive **)
  
  let max p p' =
    match compare p p' with
    | ExtrNative.Gt -> p
    | _ -> p'
  
  (** val eqb : positive -> positive -> bool **)
  
  let rec eqb p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> eqb p2 q0
       | _ -> false)
    | XO p2 ->
      (match q with
       | XO q0 -> eqb p2 q0
       | _ -> false)
    | XH ->
      (match q with
       | XH -> true
       | _ -> false)
  
  (** val leb : positive -> positive -> bool **)
  
  let leb x y =
    match compare x y with
    | ExtrNative.Gt -> false
    | _ -> true
  
  (** val ltb : positive -> positive -> bool **)
  
  let ltb x y =
    match compare x y with
    | ExtrNative.Lt -> true
    | _ -> false
  
  (** val sqrtrem_step :
      (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
      positive*mask **)
  
  let sqrtrem_step f g = function
  | s,y ->
    (match y with
     | IsPos r ->
       let s' = XI (XO s) in
       let r' = g (f r) in
       if leb s' r' then (XI s),(sub_mask r' s') else (XO s),(IsPos r')
     | _ -> (XO s),(sub_mask (g (f XH)) (XO (XO XH))))
  
  (** val sqrtrem : positive -> positive*mask **)
  
  let rec sqrtrem = function
  | XI p2 ->
    (match p2 with
     | XI p3 -> sqrtrem_step (fun x -> XI x) (fun x -> XI x) (sqrtrem p3)
     | XO p3 -> sqrtrem_step (fun x -> XO x) (fun x -> XI x) (sqrtrem p3)
     | XH -> XH,(IsPos (XO XH)))
  | XO p2 ->
    (match p2 with
     | XI p3 -> sqrtrem_step (fun x -> XI x) (fun x -> XO x) (sqrtrem p3)
     | XO p3 -> sqrtrem_step (fun x -> XO x) (fun x -> XO x) (sqrtrem p3)
     | XH -> XH,(IsPos XH))
  | XH -> XH,IsNul
  
  (** val sqrt : positive -> positive **)
  
  let sqrt p =
    fst (sqrtrem p)
  
  (** val gcdn : nat -> positive -> positive -> positive **)
  
  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | ExtrNative.Eq -> a
             | ExtrNative.Lt -> gcdn n1 (sub b' a') a
             | ExtrNative.Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI p -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)
  
  (** val gcd : positive -> positive -> positive **)
  
  let gcd a b =
    gcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val ggcdn :
      nat -> positive -> positive -> positive*(positive*positive) **)
  
  let rec ggcdn n0 a b =
    match n0 with
    | O -> XH,(a,b)
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | ExtrNative.Eq -> a,(XH,XH)
             | ExtrNative.Lt ->
               let g,p = ggcdn n1 (sub b' a') a in
               let ba,aa = p in g,(aa,(add aa (XO ba)))
             | ExtrNative.Gt ->
               let g,p = ggcdn n1 (sub a' b') b in
               let ab,bb = p in g,((add bb (XO ab)),bb))
          | XO b0 ->
            let g,p = ggcdn n1 a b0 in let aa,bb = p in g,(aa,(XO bb))
          | XH -> XH,(a,XH))
       | XO a0 ->
         (match b with
          | XI p ->
            let g,p2 = ggcdn n1 a0 b in let aa,bb = p2 in g,((XO aa),bb)
          | XO b0 -> let g,p = ggcdn n1 a0 b0 in (XO g),p
          | XH -> XH,(a,XH))
       | XH -> XH,(XH,b))
  
  (** val ggcd : positive -> positive -> positive*(positive*positive) **)
  
  let ggcd a b =
    ggcdn (plus (size_nat a) (size_nat b)) a b
  
  (** val coq_Nsucc_double : n -> n **)
  
  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val coq_Ndouble : n -> n **)
  
  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val coq_lor : positive -> positive -> positive **)
  
  let rec coq_lor p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> XI (coq_lor p2 q0)
       | XO q0 -> XI (coq_lor p2 q0)
       | XH -> p)
    | XO p2 ->
      (match q with
       | XI q0 -> XI (coq_lor p2 q0)
       | XO q0 -> XO (coq_lor p2 q0)
       | XH -> XI p2)
    | XH ->
      (match q with
       | XO q0 -> XI q0
       | _ -> q)
  
  (** val coq_land : positive -> positive -> n **)
  
  let rec coq_land p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p2 q0)
       | XO q0 -> coq_Ndouble (coq_land p2 q0)
       | XH -> Npos XH)
    | XO p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p2 q0)
       | XO q0 -> coq_Ndouble (coq_land p2 q0)
       | XH -> N0)
    | XH ->
      (match q with
       | XO q0 -> N0
       | _ -> Npos XH)
  
  (** val ldiff : positive -> positive -> n **)
  
  let rec ldiff p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p2 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p2 q0)
       | XH -> Npos (XO p2))
    | XO p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p2 q0)
       | XO q0 -> coq_Ndouble (ldiff p2 q0)
       | XH -> Npos p)
    | XH ->
      (match q with
       | XO q0 -> Npos XH
       | _ -> N0)
  
  (** val coq_lxor : positive -> positive -> n **)
  
  let rec coq_lxor p q =
    match p with
    | XI p2 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p2 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p2 q0)
       | XH -> Npos (XO p2))
    | XO p2 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p2 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p2 q0)
       | XH -> Npos (XI p2))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
  
  (** val shiftl_nat : positive -> nat -> positive **)
  
  let shiftl_nat p n0 =
    nat_iter n0 (fun x -> XO x) p
  
  (** val shiftr_nat : positive -> nat -> positive **)
  
  let shiftr_nat p n0 =
    nat_iter n0 div2 p
  
  (** val shiftl : positive -> n -> positive **)
  
  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter n1 (fun x -> XO x) p
  
  (** val shiftr : positive -> n -> positive **)
  
  let shiftr p = function
  | N0 -> p
  | Npos n1 -> iter n1 div2 p
  
  (** val testbit_nat : positive -> nat -> bool **)
  
  let rec testbit_nat p n0 =
    match p with
    | XI p2 ->
      (match n0 with
       | O -> true
       | S n' -> testbit_nat p2 n')
    | XO p2 ->
      (match n0 with
       | O -> false
       | S n' -> testbit_nat p2 n')
    | XH ->
      (match n0 with
       | O -> true
       | S n1 -> false)
  
  (** val testbit : positive -> n -> bool **)
  
  let rec testbit p n0 =
    match p with
    | XI p2 ->
      (match n0 with
       | N0 -> true
       | Npos n1 -> testbit p2 (pred_N n1))
    | XO p2 ->
      (match n0 with
       | N0 -> false
       | Npos n1 -> testbit p2 (pred_N n1))
    | XH ->
      (match n0 with
       | N0 -> true
       | Npos p2 -> false)
  
  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)
  
  let rec iter_op op p a =
    match p with
    | XI p2 -> op a (iter_op op p2 (op a a))
    | XO p2 -> iter_op op p2 (op a a)
    | XH -> a
  
  (** val to_nat : positive -> nat **)
  
  let to_nat x =
    iter_op plus x (S O)
  
  (** val of_nat : nat -> positive **)
  
  let rec of_nat = function
  | O -> XH
  | S x ->
    (match x with
     | O -> XH
     | S n1 -> succ (of_nat x))
  
  (** val of_succ_nat : nat -> positive **)
  
  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
  
  (** val eq_dec : positive -> positive -> sumbool **)
  
  let rec eq_dec p y0 =
    match p with
    | XI p2 ->
      (match y0 with
       | XI p3 -> eq_dec p2 p3
       | _ -> Right)
    | XO p2 ->
      (match y0 with
       | XO p3 -> eq_dec p2 p3
       | _ -> Right)
    | XH ->
      (match y0 with
       | XH -> Left
       | _ -> Right)
  
  (** val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let rec peano_rect a f p =
    let f2 = peano_rect (f XH a) (fun p2 x -> f (succ (XO p2)) (f (XO p2) x))
    in
    (match p with
     | XI q -> f (XO q) (f2 q)
     | XO q -> f2 q
     | XH -> a)
  
  (** val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  (** val coq_PeanoView_rect :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rect f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p3, p4) -> f0 p3 p4 (coq_PeanoView_rect f f0 p3 p4)
  
  (** val coq_PeanoView_rec :
      'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
      coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_rec f f0 p = function
  | PeanoOne -> f
  | PeanoSucc (p3, p4) -> f0 p3 p4 (coq_PeanoView_rec f f0 p3 p4)
  
  (** val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xO p = function
  | PeanoOne -> PeanoSucc (XH, PeanoOne)
  | PeanoSucc (p2, q0) ->
    PeanoSucc ((succ (XO p2)), (PeanoSucc ((XO p2), (peanoView_xO p2 q0))))
  
  (** val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView **)
  
  let rec peanoView_xI p = function
  | PeanoOne -> PeanoSucc ((succ XH), (PeanoSucc (XH, PeanoOne)))
  | PeanoSucc (p2, q0) ->
    PeanoSucc ((succ (XI p2)), (PeanoSucc ((XI p2), (peanoView_xI p2 q0))))
  
  (** val peanoView : positive -> coq_PeanoView **)
  
  let rec peanoView = function
  | XI p2 -> peanoView_xI p2 (peanoView p2)
  | XO p2 -> peanoView_xO p2 (peanoView p2)
  | XH -> PeanoOne
  
  (** val coq_PeanoView_iter :
      'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1 **)
  
  let rec coq_PeanoView_iter a f p = function
  | PeanoOne -> a
  | PeanoSucc (p2, q0) -> f p2 (coq_PeanoView_iter a f p2 q0)
  
  (** val eqb_spec : positive -> positive -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val switch_Eq :
      ExtrNative.comparison -> ExtrNative.comparison -> ExtrNative.comparison **)
  
  let switch_Eq c = function
  | ExtrNative.Eq -> c
  | x -> x
  
  (** val mask2cmp : mask -> ExtrNative.comparison **)
  
  let mask2cmp = function
  | IsNul -> ExtrNative.Eq
  | IsPos p2 -> ExtrNative.Gt
  | IsNeg -> ExtrNative.Lt
  
  (** val leb_spec0 : positive -> positive -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : positive -> positive -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = Coq__1.t
     end
    
    module MRev = 
     struct 
      (** val max : t -> t -> t **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : t -> t -> sumbool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) Left Right
    
    (** val min_case_strong :
        t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : t -> t -> sumbool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) Left Right
   end
  
  (** val max_case_strong : t -> t -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : t -> t -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : t -> t -> sumbool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : t -> t -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : t -> t -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : t -> t -> sumbool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module N = 
 struct 
  type t = n
  
  (** val zero : n **)
  
  let zero =
    N0
  
  (** val one : n **)
  
  let one =
    Npos XH
  
  (** val two : n **)
  
  let two =
    Npos (XO XH)
  
  (** val succ_double : n -> n **)
  
  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)
  
  (** val double : n -> n **)
  
  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)
  
  (** val succ : n -> n **)
  
  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Coq_Pos.succ p)
  
  (** val pred : n -> n **)
  
  let pred = function
  | N0 -> N0
  | Npos p -> Coq_Pos.pred_N p
  
  (** val succ_pos : n -> positive **)
  
  let succ_pos = function
  | N0 -> XH
  | Npos p -> Coq_Pos.succ p
  
  (** val add : n -> n -> n **)
  
  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.add p q))
  
  (** val sub : n -> n -> n **)
  
  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Coq_Pos.sub_mask n' m' with
          | Coq_Pos.IsPos p -> Npos p
          | _ -> N0))
  
  (** val mul : n -> n -> n **)
  
  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Npos (Coq_Pos.mul p q))
  
  (** val compare : n -> n -> ExtrNative.comparison **)
  
  let compare n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> ExtrNative.Eq
       | Npos m' -> ExtrNative.Lt)
    | Npos n' ->
      (match m with
       | N0 -> ExtrNative.Gt
       | Npos m' -> Coq_Pos.compare n' m')
  
  (** val eqb : n -> n -> bool **)
  
  let rec eqb n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> true
       | Npos p -> false)
    | Npos p ->
      (match m with
       | N0 -> false
       | Npos q -> Coq_Pos.eqb p q)
  
  (** val leb : n -> n -> bool **)
  
  let leb x y =
    match compare x y with
    | ExtrNative.Gt -> false
    | _ -> true
  
  (** val ltb : n -> n -> bool **)
  
  let ltb x y =
    match compare x y with
    | ExtrNative.Lt -> true
    | _ -> false
  
  (** val min : n -> n -> n **)
  
  let min n0 n' =
    match compare n0 n' with
    | ExtrNative.Gt -> n'
    | _ -> n0
  
  (** val max : n -> n -> n **)
  
  let max n0 n' =
    match compare n0 n' with
    | ExtrNative.Gt -> n0
    | _ -> n'
  
  (** val div2 : n -> n **)
  
  let div2 = function
  | N0 -> N0
  | Npos p2 ->
    (match p2 with
     | XI p -> Npos p
     | XO p -> Npos p
     | XH -> N0)
  
  (** val even : n -> bool **)
  
  let even = function
  | N0 -> true
  | Npos p ->
    (match p with
     | XO p2 -> true
     | _ -> false)
  
  (** val odd : n -> bool **)
  
  let odd n0 =
    negb (even n0)
  
  (** val pow : n -> n -> n **)
  
  let pow n0 = function
  | N0 -> Npos XH
  | Npos p2 ->
    (match n0 with
     | N0 -> N0
     | Npos q -> Npos (Coq_Pos.pow q p2))
  
  (** val square : n -> n **)
  
  let square = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.square p)
  
  (** val log2 : n -> n **)
  
  let log2 = function
  | N0 -> N0
  | Npos p2 ->
    (match p2 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
     | XH -> N0)
  
  (** val size : n -> n **)
  
  let size = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.size p)
  
  (** val size_nat : n -> nat **)
  
  let size_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.size_nat p
  
  (** val pos_div_eucl : positive -> n -> n*n **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then (succ_double q),(sub r' b) else (double q),r'
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then (succ_double q),(sub r' b) else (double q),r'
    | XH ->
      (match b with
       | N0 -> N0,(Npos XH)
       | Npos p ->
         (match p with
          | XH -> (Npos XH),N0
          | _ -> N0,(Npos XH)))
  
  (** val div_eucl : n -> n -> n*n **)
  
  let div_eucl a b =
    match a with
    | N0 -> N0,N0
    | Npos na ->
      (match b with
       | N0 -> N0,a
       | Npos p -> pos_div_eucl na b)
  
  (** val div : n -> n -> n **)
  
  let div a b =
    fst (div_eucl a b)
  
  (** val modulo : n -> n -> n **)
  
  let modulo a b =
    snd (div_eucl a b)
  
  (** val gcd : n -> n -> n **)
  
  let gcd a b =
    match a with
    | N0 -> b
    | Npos p ->
      (match b with
       | N0 -> a
       | Npos q -> Npos (Coq_Pos.gcd p q))
  
  (** val ggcd : n -> n -> n*(n*n) **)
  
  let ggcd a b =
    match a with
    | N0 -> b,(N0,(Npos XH))
    | Npos p ->
      (match b with
       | N0 -> a,((Npos XH),N0)
       | Npos q ->
         let g,p2 = Coq_Pos.ggcd p q in
         let aa,bb = p2 in (Npos g),((Npos aa),(Npos bb)))
  
  (** val sqrtrem : n -> n*n **)
  
  let sqrtrem = function
  | N0 -> N0,N0
  | Npos p ->
    let s,m = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> (Npos s),(Npos r)
     | _ -> (Npos s),N0)
  
  (** val sqrt : n -> n **)
  
  let sqrt = function
  | N0 -> N0
  | Npos p -> Npos (Coq_Pos.sqrt p)
  
  (** val coq_lor : n -> n -> n **)
  
  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Npos (Coq_Pos.coq_lor p q))
  
  (** val coq_land : n -> n -> n **)
  
  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> N0
       | Npos q -> Coq_Pos.coq_land p q)
  
  (** val ldiff : n -> n -> n **)
  
  let rec ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.ldiff p q)
  
  (** val coq_lxor : n -> n -> n **)
  
  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p ->
      (match m with
       | N0 -> n0
       | Npos q -> Coq_Pos.coq_lxor p q)
  
  (** val shiftl_nat : n -> nat -> n **)
  
  let shiftl_nat a n0 =
    nat_iter n0 double a
  
  (** val shiftr_nat : n -> nat -> n **)
  
  let shiftr_nat a n0 =
    nat_iter n0 div2 a
  
  (** val shiftl : n -> n -> n **)
  
  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)
  
  (** val shiftr : n -> n -> n **)
  
  let shiftr a = function
  | N0 -> a
  | Npos p -> Coq_Pos.iter p div2 a
  
  (** val testbit_nat : n -> nat -> bool **)
  
  let testbit_nat = function
  | N0 -> (fun x -> false)
  | Npos p -> Coq_Pos.testbit_nat p
  
  (** val testbit : n -> n -> bool **)
  
  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
  
  (** val to_nat : n -> nat **)
  
  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p
  
  (** val of_nat : nat -> n **)
  
  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')
  
  (** val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | N0 -> x
    | Npos p -> Coq_Pos.iter p f x
  
  (** val eq_dec : n -> n -> sumbool **)
  
  let eq_dec n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Left
       | Npos p -> Right)
    | Npos x ->
      (match m with
       | N0 -> Right
       | Npos p2 -> Coq_Pos.eq_dec x p2)
  
  (** val discr : n -> positive sumor **)
  
  let discr = function
  | N0 -> Inright
  | Npos p -> Inleft p
  
  (** val binary_rect :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rect f0 f2 fS2 n0 =
    let f2' = fun p -> f2 (Npos p) in
    let fS2' = fun p -> fS2 (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p ->
       let rec f = function
       | XI p3 -> fS2' p3 (f p3)
       | XO p3 -> f2' p3 (f p3)
       | XH -> fS2 N0 f0
       in f p)
  
  (** val binary_rec :
      'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let binary_rec =
    binary_rect
  
  (** val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rect f0 f n0 =
    let f' = fun p -> f (Npos p) in
    (match n0 with
     | N0 -> f0
     | Npos p -> Coq_Pos.peano_rect (f N0 f0) f' p)
  
  (** val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let peano_rec =
    peano_rect
  
  (** val leb_spec0 : n -> n -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : n -> n -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1 **)
  
  let recursion x =
    peano_rect x
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = n
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  module Private_NZPow = 
   struct 
    
   end
  
  module Private_NZSqrt = 
   struct 
    
   end
  
  (** val sqrt_up : n -> n **)
  
  let sqrt_up a =
    match compare N0 a with
    | ExtrNative.Lt -> succ (sqrt (pred a))
    | _ -> N0
  
  (** val log2_up : n -> n **)
  
  let log2_up a =
    match compare (Npos XH) a with
    | ExtrNative.Lt -> succ (log2 (pred a))
    | _ -> N0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  (** val lcm : n -> n -> n **)
  
  let lcm a b =
    mul a (div b (gcd a b))
  
  (** val eqb_spec : n -> n -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2n : bool -> n **)
  
  let b2n = function
  | true -> Npos XH
  | false -> N0
  
  (** val setbit : n -> n -> n **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Npos XH) n0)
  
  (** val clearbit : n -> n -> n **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Npos XH) n0)
  
  (** val ones : n -> n **)
  
  let ones n0 =
    pred (shiftl (Npos XH) n0)
  
  (** val lnot : n -> n -> n **)
  
  let lnot a n0 =
    coq_lxor a (ones n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = n
     end
    
    module MRev = 
     struct 
      (** val max : n -> n -> n **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : n -> n -> sumbool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) Left Right
    
    (** val min_case_strong :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : n -> n -> sumbool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) Left Right
   end
  
  (** val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : n -> n -> sumbool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : n -> n -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : n -> n -> sumbool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

module Z = 
 struct 
  type t = z
  
  (** val zero : z **)
  
  let zero =
    Z0
  
  (** val one : z **)
  
  let one =
    Zpos XH
  
  (** val two : z **)
  
  let two =
    Zpos (XO XH)
  
  (** val double : z -> z **)
  
  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)
  
  (** val succ_double : z -> z **)
  
  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)
  
  (** val pred_double : z -> z **)
  
  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)
  
  (** val pos_sub : positive -> positive -> z **)
  
  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Coq_Pos.pred_double q)
       | XH -> Z0)
  
  (** val add : z -> z -> z **)
  
  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))
  
  (** val opp : z -> z **)
  
  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0
  
  (** val succ : z -> z **)
  
  let succ x =
    add x (Zpos XH)
  
  (** val pred : z -> z **)
  
  let pred x =
    add x (Zneg XH)
  
  (** val sub : z -> z -> z **)
  
  let sub m n0 =
    add m (opp n0)
  
  (** val mul : z -> z -> z **)
  
  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))
  
  (** val pow_pos : z -> positive -> z **)
  
  let pow_pos z0 n0 =
    Coq_Pos.iter n0 (mul z0) (Zpos XH)
  
  (** val pow : z -> z -> z **)
  
  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg p -> Z0
  
  (** val square : z -> z **)
  
  let square = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_Pos.square p)
  | Zneg p -> Zpos (Coq_Pos.square p)
  
  (** val compare : z -> z -> ExtrNative.comparison **)
  
  let compare x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> ExtrNative.Eq
       | Zpos y' -> ExtrNative.Lt
       | Zneg y' -> ExtrNative.Gt)
    | Zpos x' ->
      (match y with
       | Zpos y' -> Coq_Pos.compare x' y'
       | _ -> ExtrNative.Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> ExtrNative.Lt)
  
  (** val sgn : z -> z **)
  
  let sgn = function
  | Z0 -> Z0
  | Zpos p -> Zpos XH
  | Zneg p -> Zneg XH
  
  (** val leb : z -> z -> bool **)
  
  let leb x y =
    match compare x y with
    | ExtrNative.Gt -> false
    | _ -> true
  
  (** val ltb : z -> z -> bool **)
  
  let ltb x y =
    match compare x y with
    | ExtrNative.Lt -> true
    | _ -> false
  
  (** val geb : z -> z -> bool **)
  
  let geb x y =
    match compare x y with
    | ExtrNative.Lt -> false
    | _ -> true
  
  (** val gtb : z -> z -> bool **)
  
  let gtb x y =
    match compare x y with
    | ExtrNative.Gt -> true
    | _ -> false
  
  (** val eqb : z -> z -> bool **)
  
  let rec eqb x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> true
       | _ -> false)
    | Zpos p ->
      (match y with
       | Zpos q -> Coq_Pos.eqb p q
       | _ -> false)
    | Zneg p ->
      (match y with
       | Zneg q -> Coq_Pos.eqb p q
       | _ -> false)
  
  (** val max : z -> z -> z **)
  
  let max n0 m =
    match compare n0 m with
    | ExtrNative.Lt -> m
    | _ -> n0
  
  (** val min : z -> z -> z **)
  
  let min n0 m =
    match compare n0 m with
    | ExtrNative.Gt -> m
    | _ -> n0
  
  (** val abs : z -> z **)
  
  let abs = function
  | Zneg p -> Zpos p
  | x -> x
  
  (** val abs_nat : z -> nat **)
  
  let abs_nat = function
  | Z0 -> O
  | Zpos p -> Coq_Pos.to_nat p
  | Zneg p -> Coq_Pos.to_nat p
  
  (** val abs_N : z -> n **)
  
  let abs_N = function
  | Z0 -> N0
  | Zpos p -> Npos p
  | Zneg p -> Npos p
  
  (** val to_nat : z -> nat **)
  
  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> O
  
  (** val to_N : z -> n **)
  
  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0
  
  (** val of_nat : nat -> z **)
  
  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)
  
  (** val of_N : n -> z **)
  
  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p
  
  (** val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)
  
  let iter n0 f x =
    match n0 with
    | Zpos p -> Coq_Pos.iter p f x
    | _ -> x
  
  (** val pos_div_eucl : positive -> z -> z*z **)
  
  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then (mul (Zpos (XO XH)) q),r'
      else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then (mul (Zpos (XO XH)) q),r'
      else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XH -> if leb (Zpos (XO XH)) b then Z0,(Zpos XH) else (Zpos XH),Z0
  
  (** val div_eucl : z -> z -> z*z **)
  
  let div_eucl a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos p -> pos_div_eucl a' b
       | Zneg b' ->
         let q,r = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(add b r)))
    | Zneg a' ->
      (match b with
       | Z0 -> Z0,Z0
       | Zpos p ->
         let q,r = pos_div_eucl a' b in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(sub b r))
       | Zneg b' -> let q,r = pos_div_eucl a' (Zpos b') in q,(opp r))
  
  (** val div : z -> z -> z **)
  
  let div a b =
    let q,x = div_eucl a b in q
  
  (** val modulo : z -> z -> z **)
  
  let modulo a b =
    let x,r = div_eucl a b in r
  
  (** val quotrem : z -> z -> z*z **)
  
  let quotrem a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0,a
       | Zpos b0 ->
         let q,r = N.pos_div_eucl a0 (Npos b0) in (of_N q),(of_N r)
       | Zneg b0 ->
         let q,r = N.pos_div_eucl a0 (Npos b0) in (opp (of_N q)),(of_N r))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0,a
       | Zpos b0 ->
         let q,r = N.pos_div_eucl a0 (Npos b0) in
         (opp (of_N q)),(opp (of_N r))
       | Zneg b0 ->
         let q,r = N.pos_div_eucl a0 (Npos b0) in (of_N q),(opp (of_N r)))
  
  (** val quot : z -> z -> z **)
  
  let quot a b =
    fst (quotrem a b)
  
  (** val rem : z -> z -> z **)
  
  let rem a b =
    snd (quotrem a b)
  
  (** val even : z -> bool **)
  
  let even = function
  | Z0 -> true
  | Zpos p ->
    (match p with
     | XO p2 -> true
     | _ -> false)
  | Zneg p ->
    (match p with
     | XO p2 -> true
     | _ -> false)
  
  (** val odd : z -> bool **)
  
  let odd = function
  | Z0 -> false
  | Zpos p ->
    (match p with
     | XO p2 -> false
     | _ -> true)
  | Zneg p ->
    (match p with
     | XO p2 -> false
     | _ -> true)
  
  (** val div2 : z -> z **)
  
  let div2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p -> Zneg (Coq_Pos.div2_up p)
  
  (** val quot2 : z -> z **)
  
  let quot2 = function
  | Z0 -> Z0
  | Zpos p ->
    (match p with
     | XH -> Z0
     | _ -> Zpos (Coq_Pos.div2 p))
  | Zneg p ->
    (match p with
     | XH -> Z0
     | _ -> Zneg (Coq_Pos.div2 p))
  
  (** val log2 : z -> z **)
  
  let log2 = function
  | Zpos p2 ->
    (match p2 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0
  
  (** val sqrtrem : z -> z*z **)
  
  let sqrtrem = function
  | Zpos p ->
    let s,m = Coq_Pos.sqrtrem p in
    (match m with
     | Coq_Pos.IsPos r -> (Zpos s),(Zpos r)
     | _ -> (Zpos s),Z0)
  | _ -> Z0,Z0
  
  (** val sqrt : z -> z **)
  
  let sqrt = function
  | Zpos p -> Zpos (Coq_Pos.sqrt p)
  | _ -> Z0
  
  (** val gcd : z -> z -> z **)
  
  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Coq_Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Coq_Pos.gcd a0 b0))
  
  (** val ggcd : z -> z -> z*(z*z) **)
  
  let ggcd a b =
    match a with
    | Z0 -> (abs b),(Z0,(sgn b))
    | Zpos a0 ->
      (match b with
       | Z0 -> (abs a),((sgn a),Z0)
       | Zpos b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zpos aa),(Zpos bb))
       | Zneg b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zpos aa),(Zneg bb)))
    | Zneg a0 ->
      (match b with
       | Z0 -> (abs a),((sgn a),Z0)
       | Zpos b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zneg aa),(Zpos bb))
       | Zneg b0 ->
         let g,p = Coq_Pos.ggcd a0 b0 in
         let aa,bb = p in (Zpos g),((Zneg aa),(Zneg bb)))
  
  (** val testbit : z -> z -> bool **)
  
  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg p -> false
  
  (** val shiftl : z -> z -> z **)
  
  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Coq_Pos.iter p (mul (Zpos (XO XH))) a
  | Zneg p -> Coq_Pos.iter p div2 a
  
  (** val shiftr : z -> z -> z **)
  
  let shiftr a n0 =
    shiftl a (opp n0)
  
  (** val coq_lor : z -> z -> z **)
  
  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Coq_Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_land (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val coq_land : z -> z -> z **)
  
  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Coq_Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Coq_Pos.pred_N a0))
       | Zneg b0 ->
         Zneg
           (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0))))
  
  (** val ldiff : z -> z -> z **)
  
  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Coq_Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Coq_Pos.pred_N b0) (Coq_Pos.pred_N a0)))
  
  (** val coq_lxor : z -> z -> z **)
  
  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Coq_Pos.coq_lxor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Coq_Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.coq_lxor (Coq_Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Coq_Pos.pred_N a0) (Coq_Pos.pred_N b0)))
  
  (** val eq_dec : z -> z -> sumbool **)
  
  let eq_dec x y =
    match x with
    | Z0 ->
      (match y with
       | Z0 -> Left
       | _ -> Right)
    | Zpos x0 ->
      (match y with
       | Zpos p2 -> Coq_Pos.eq_dec x0 p2
       | _ -> Right)
    | Zneg x0 ->
      (match y with
       | Zneg p2 -> Coq_Pos.eq_dec x0 p2
       | _ -> Right)
  
  module Private_BootStrap = 
   struct 
    
   end
  
  (** val leb_spec0 : z -> z -> reflect **)
  
  let leb_spec0 x y =
    iff_reflect (leb x y)
  
  (** val ltb_spec0 : z -> z -> reflect **)
  
  let ltb_spec0 x y =
    iff_reflect (ltb x y)
  
  module Private_OrderTac = 
   struct 
    module Elts = 
     struct 
      type t = z
     end
    
    module Tac = MakeOrderTac(Elts)
   end
  
  (** val sqrt_up : z -> z **)
  
  let sqrt_up a =
    match compare Z0 a with
    | ExtrNative.Lt -> succ (sqrt (pred a))
    | _ -> Z0
  
  (** val log2_up : z -> z **)
  
  let log2_up a =
    match compare (Zpos XH) a with
    | ExtrNative.Lt -> succ (log2 (pred a))
    | _ -> Z0
  
  module Private_NZDiv = 
   struct 
    
   end
  
  module Private_Div = 
   struct 
    module Quot2Div = 
     struct 
      (** val div : z -> z -> z **)
      
      let div =
        quot
      
      (** val modulo : z -> z -> z **)
      
      let modulo =
        rem
     end
    
    module NZQuot = 
     struct 
      
     end
   end
  
  (** val lcm : z -> z -> z **)
  
  let lcm a b =
    abs (mul a (div b (gcd a b)))
  
  (** val eqb_spec : z -> z -> reflect **)
  
  let eqb_spec x y =
    iff_reflect (eqb x y)
  
  (** val b2z : bool -> z **)
  
  let b2z = function
  | true -> Zpos XH
  | false -> Z0
  
  (** val setbit : z -> z -> z **)
  
  let setbit a n0 =
    coq_lor a (shiftl (Zpos XH) n0)
  
  (** val clearbit : z -> z -> z **)
  
  let clearbit a n0 =
    ldiff a (shiftl (Zpos XH) n0)
  
  (** val lnot : z -> z **)
  
  let lnot a =
    pred (opp a)
  
  (** val ones : z -> z **)
  
  let ones n0 =
    pred (shiftl (Zpos XH) n0)
  
  module Private_Tac = 
   struct 
    
   end
  
  module Private_Rev = 
   struct 
    module ORev = 
     struct 
      type t = z
     end
    
    module MRev = 
     struct 
      (** val max : z -> z -> z **)
      
      let max x y =
        min y x
     end
    
    module MPRev = MaxLogicalProperties(ORev)(MRev)
   end
  
  module Private_Dec = 
   struct 
    (** val max_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let max_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat n0 (max n0 m) __ (hl __)
       | _ -> compat m (max n0 m) __ (hr __))
    
    (** val max_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let max_case n0 m x x0 x1 =
      max_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val max_dec : z -> z -> sumbool **)
    
    let max_dec n0 m =
      max_case n0 m (fun x y _ h0 -> h0) Left Right
    
    (** val min_case_strong :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1)
        -> 'a1 **)
    
    let min_case_strong n0 m compat hl hr =
      let c = compSpec2Type n0 m (compare n0 m) in
      (match c with
       | CompGtT -> compat m (min n0 m) __ (hr __)
       | _ -> compat n0 (min n0 m) __ (hl __))
    
    (** val min_case :
        z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)
    
    let min_case n0 m x x0 x1 =
      min_case_strong n0 m x (fun _ -> x0) (fun _ -> x1)
    
    (** val min_dec : z -> z -> sumbool **)
    
    let min_dec n0 m =
      min_case n0 m (fun x y _ h0 -> h0) Left Right
   end
  
  (** val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let max_case_strong n0 m x x0 =
    Private_Dec.max_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val max_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let max_case n0 m x x0 =
    max_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val max_dec : z -> z -> sumbool **)
  
  let max_dec =
    Private_Dec.max_dec
  
  (** val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)
  
  let min_case_strong n0 m x x0 =
    Private_Dec.min_case_strong n0 m (fun x1 y _ x2 -> x2) x x0
  
  (** val min_case : z -> z -> 'a1 -> 'a1 -> 'a1 **)
  
  let min_case n0 m x x0 =
    min_case_strong n0 m (fun _ -> x) (fun _ -> x0)
  
  (** val min_dec : z -> z -> sumbool **)
  
  let min_dec =
    Private_Dec.min_dec
 end

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | ExtrNative.Eq -> true
  | _ -> false

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default0 =
  match n0 with
  | O ->
    (match l with
     | Nil -> default0
     | Cons (x, l') -> x)
  | S m ->
    (match l with
     | Nil -> default0
     | Cons (x, t0) -> nth m t0 default0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> false
| Cons (a, l0) -> if f a then true else existsb f l0

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> true
| Cons (a, l0) -> if f a then forallb f l0 else false

type int = ExtrNative.uint

(** val lsl0 : int -> int -> int **)

let lsl0 = ExtrNative.l_sl

(** val lsr0 : int -> int -> int **)

let lsr0 = ExtrNative.l_sr

(** val land0 : int -> int -> int **)

let land0 = ExtrNative.l_and

(** val lxor0 : int -> int -> int **)

let lxor0 = ExtrNative.l_xor

(** val sub0 : int -> int -> int **)

let sub0 = ExtrNative.sub

(** val eqb0 : int -> int -> bool **)

let eqb0 = fun i j -> ExtrNative.compare i j = ExtrNative.Eq

(** val ltb0 : int -> int -> bool **)

let ltb0 = ExtrNative.lt

(** val leb0 : int -> int -> bool **)

let leb0 = ExtrNative.le

(** val foldi_cont :
    (int -> ('a1 -> 'a2) -> 'a1 -> 'a2) -> int -> int -> ('a1 -> 'a2) -> 'a1
    -> 'a2 **)

let foldi_cont = ExtrNative.foldi_cont

(** val foldi_down_cont :
    (int -> ('a1 -> 'a2) -> 'a1 -> 'a2) -> int -> int -> ('a1 -> 'a2) -> 'a1
    -> 'a2 **)

let foldi_down_cont = ExtrNative.foldi_down_cont

(** val is_zero : int -> bool **)

let is_zero i =
  eqb0 i (ExtrNative.of_uint(0))

(** val is_even : int -> bool **)

let is_even i =
  is_zero (land0 i (ExtrNative.of_uint(1)))

(** val compare0 : int -> int -> ExtrNative.comparison **)

let compare0 = ExtrNative.compare

(** val foldi : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 **)

let foldi f from to0 =
  foldi_cont (fun i cont a -> cont (f i a)) from to0 (fun a -> a)

(** val fold : ('a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 **)

let fold f from to0 =
  foldi_cont (fun i cont a -> cont (f a)) from to0 (fun a -> a)

(** val foldi_down : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 **)

let foldi_down f from downto0 =
  foldi_down_cont (fun i cont a -> cont (f i a)) from downto0 (fun a -> a)

(** val forallb0 : (int -> bool) -> int -> int -> bool **)

let forallb0 f from to0 =
  foldi_cont (fun i cont x -> if f i then cont Tt else false) from to0
    (fun x -> true) Tt

(** val existsb0 : (int -> bool) -> int -> int -> bool **)

let existsb0 f from to0 =
  foldi_cont (fun i cont x -> if f i then true else cont Tt) from to0
    (fun x -> false) Tt

(** val cast : int -> int -> (__ -> __ -> __) option **)

let cast i j =
  if eqb0 i j then Some (fun _ hi -> hi) else None

(** val reflect_eqb : int -> int -> reflect **)

let reflect_eqb i j =
  iff_reflect (eqb0 i j)

type 'a array = 'a ExtrNative.parray

(** val make : int -> 'a1 -> 'a1 array **)

let make = ExtrNative.parray_make

module Coq__2 = struct 
 (** val get : 'a1 array -> int -> 'a1 **)
 
 let get = ExtrNative.parray_get
end
let get = Coq__2.get

(** val default : 'a1 array -> 'a1 **)

let default = ExtrNative.parray_default

(** val set : 'a1 array -> int -> 'a1 -> 'a1 array **)

let set = ExtrNative.parray_set

(** val length : 'a1 array -> int **)

let length = ExtrNative.parray_length

(** val to_list : 'a1 array -> 'a1 list **)

let to_list t0 =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then Nil
  else foldi_down (fun i l -> Cons ((get t0 i), l))
         (sub0 len (ExtrNative.of_uint(1))) (ExtrNative.of_uint(0)) Nil

(** val forallbi : (int -> 'a1 -> bool) -> 'a1 array -> bool **)

let forallbi f t0 =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then true
  else forallb0 (fun i -> f i (get t0 i)) (ExtrNative.of_uint(0))
         (sub0 len (ExtrNative.of_uint(1)))

(** val forallb1 : ('a1 -> bool) -> 'a1 array -> bool **)

let forallb1 f t0 =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then true
  else forallb0 (fun i -> f (get t0 i)) (ExtrNative.of_uint(0))
         (sub0 len (ExtrNative.of_uint(1)))

(** val existsb1 : ('a1 -> bool) -> 'a1 array -> bool **)

let existsb1 f t0 =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then false
  else existsb0 (fun i -> f (get t0 i)) (ExtrNative.of_uint(0))
         (sub0 len (ExtrNative.of_uint(1)))

(** val mapi : (int -> 'a1 -> 'a2) -> 'a1 array -> 'a2 array **)

let mapi f t0 =
  let size0 = length t0 in
  let def = f size0 (default t0) in
  let tb = make size0 def in
  if eqb0 size0 (ExtrNative.of_uint(0))
  then tb
  else foldi (fun i tb0 -> set tb0 i (f i (get t0 i)))
         (ExtrNative.of_uint(0)) (sub0 size0 (ExtrNative.of_uint(1))) tb

(** val foldi_left :
    (int -> 'a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1 **)

let foldi_left f a t0 =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then a
  else foldi (fun i a0 -> f i a0 (get t0 i)) (ExtrNative.of_uint(0))
         (sub0 len (ExtrNative.of_uint(1))) a

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1 **)

let fold_left f a t0 =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then a
  else foldi (fun i a0 -> f a0 (get t0 i)) (ExtrNative.of_uint(0))
         (sub0 (length t0) (ExtrNative.of_uint(1))) a

(** val foldi_right :
    (int -> 'a1 -> 'a2 -> 'a2) -> 'a1 array -> 'a2 -> 'a2 **)

let foldi_right f t0 b =
  let len = length t0 in
  if eqb0 (ExtrNative.of_uint(0)) len
  then b
  else foldi_down (fun i b0 -> f i (get t0 i) b0)
         (sub0 len (ExtrNative.of_uint(1))) (ExtrNative.of_uint(0)) b

module Valuation = 
 struct 
  type t = int -> bool
 end

module Var = 
 struct 
  (** val _true : int **)
  
  let _true =
    (ExtrNative.of_uint(0))
  
  (** val _false : int **)
  
  let _false =
    (ExtrNative.of_uint(1))
  
  (** val interp : Valuation.t -> int -> bool **)
  
  let interp rho x =
    rho x
 end

module Lit = 
 struct 
  (** val is_pos : int -> bool **)
  
  let is_pos l =
    is_even l
  
  (** val blit : int -> int **)
  
  let blit l =
    lsr0 l (ExtrNative.of_uint(1))
  
  (** val lit : int -> int **)
  
  let lit x =
    lsl0 x (ExtrNative.of_uint(1))
  
  (** val neg : int -> int **)
  
  let neg l =
    lxor0 l (ExtrNative.of_uint(1))
  
  (** val nlit : int -> int **)
  
  let nlit x =
    neg (lit x)
  
  (** val _true : int **)
  
  let _true =
    (ExtrNative.of_uint(0))
  
  (** val _false : int **)
  
  let _false =
    (ExtrNative.of_uint(2))
  
  (** val eqb : int -> int -> bool **)
  
  let eqb l l' =
    eqb0 l l'
  
  (** val interp : Valuation.t -> int -> bool **)
  
  let interp rho l =
    if is_pos l
    then Var.interp rho (blit l)
    else negb (Var.interp rho (blit l))
 end

module C = 
 struct 
  type t = int list
  
  (** val interp : Valuation.t -> t -> bool **)
  
  let interp rho l =
    existsb (Lit.interp rho) l
  
  (** val _true : t **)
  
  let _true =
    Cons (Lit._true, Nil)
  
  (** val is_false : t -> bool **)
  
  let is_false = function
  | Nil -> true
  | Cons (i, l) -> false
  
  (** val or_aux : (t -> t -> t) -> int -> t -> t -> int list **)
  
  let rec or_aux or0 l1 c1 c2 = match c2 with
  | Nil -> Cons (l1, c1)
  | Cons (l2, c2') ->
    (match compare0 l1 l2 with
     | ExtrNative.Eq -> Cons (l1, (or0 c1 c2'))
     | ExtrNative.Lt -> Cons (l1, (or0 c1 c2))
     | ExtrNative.Gt -> Cons (l2, (or_aux or0 l1 c1 c2')))
  
  (** val coq_or : t -> t -> t **)
  
  let rec coq_or c1 c2 =
    match c1 with
    | Nil -> c2
    | Cons (l1, c3) ->
      (match c2 with
       | Nil -> c1
       | Cons (l2, c2') ->
         (match compare0 l1 l2 with
          | ExtrNative.Eq -> Cons (l1, (coq_or c3 c2'))
          | ExtrNative.Lt -> Cons (l1, (coq_or c3 c2))
          | ExtrNative.Gt -> Cons (l2, (or_aux coq_or l1 c3 c2'))))
  
  (** val resolve_aux : (t -> t -> t) -> int -> t -> t -> t **)
  
  let rec resolve_aux resolve0 l1 c1 c2 = match c2 with
  | Nil -> _true
  | Cons (l2, c2') ->
    (match compare0 l1 l2 with
     | ExtrNative.Eq -> Cons (l1, (resolve0 c1 c2'))
     | ExtrNative.Lt ->
       if eqb0 (lxor0 l1 l2) (ExtrNative.of_uint(1))
       then coq_or c1 c2'
       else Cons (l1, (resolve0 c1 c2))
     | ExtrNative.Gt ->
       if eqb0 (lxor0 l1 l2) (ExtrNative.of_uint(1))
       then coq_or c1 c2'
       else Cons (l2, (resolve_aux resolve0 l1 c1 c2')))
  
  (** val resolve : t -> t -> t **)
  
  let rec resolve c1 c2 =
    match c1 with
    | Nil -> _true
    | Cons (l1, c3) ->
      (match c2 with
       | Nil -> _true
       | Cons (l2, c2') ->
         (match compare0 l1 l2 with
          | ExtrNative.Eq -> Cons (l1, (resolve c3 c2'))
          | ExtrNative.Lt ->
            if eqb0 (lxor0 l1 l2) (ExtrNative.of_uint(1))
            then coq_or c3 c2'
            else Cons (l1, (resolve c3 c2))
          | ExtrNative.Gt ->
            if eqb0 (lxor0 l1 l2) (ExtrNative.of_uint(1))
            then coq_or c3 c2'
            else Cons (l2, (resolve_aux resolve l1 c3 c2'))))
 end

module S = 
 struct 
  type t = C.t array
  
  (** val get : t -> int -> C.t **)
  
  let get s cid =
    get s cid
  
  (** val internal_set : t -> int -> C.t -> t **)
  
  let internal_set s cid c =
    set s cid c
  
  (** val make : int -> t **)
  
  let make nclauses =
    make nclauses C._true
  
  (** val insert : int -> int list -> int list **)
  
  let rec insert l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare0 l1 l2 with
     | ExtrNative.Eq -> c
     | ExtrNative.Lt ->
       if eqb0 (lxor0 l1 l2) (ExtrNative.of_uint(1))
       then C._true
       else Cons (l1, c)
     | ExtrNative.Gt ->
       if eqb0 (lxor0 l1 l2) (ExtrNative.of_uint(1))
       then C._true
       else Cons (l2, (insert l1 c')))
  
  (** val sort_uniq : int list -> int list **)
  
  let rec sort_uniq = function
  | Nil -> Nil
  | Cons (l1, c0) -> insert l1 (sort_uniq c0)
  
  (** val set_clause : t -> int -> C.t -> t **)
  
  let set_clause s pos c =
    set s pos (sort_uniq c)
  
  (** val set_resolve : t -> int -> int array -> t **)
  
  let set_resolve s pos r =
    let len = length r in
    if eqb0 len (ExtrNative.of_uint(0))
    then s
    else let c =
           foldi (fun i c -> C.resolve (get s (Coq__2.get r i)) c)
             (ExtrNative.of_uint(1)) (sub0 len (ExtrNative.of_uint(1)))
             (get s (Coq__2.get r (ExtrNative.of_uint(0))))
         in
         internal_set s pos c
 end

(** val afold_left :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1 **)

let afold_left default0 oP f v =
  let n0 = length v in
  if eqb0 n0 (ExtrNative.of_uint(0))
  then default0
  else foldi (fun i a -> oP a (f (get v i))) (ExtrNative.of_uint(1))
         (sub0 n0 (ExtrNative.of_uint(1)))
         (f (get v (ExtrNative.of_uint(0))))

(** val afold_right :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1 **)

let afold_right default0 oP f v =
  let n0 = length v in
  if eqb0 n0 (ExtrNative.of_uint(0))
  then default0
  else if leb0 n0 (ExtrNative.of_uint(1))
       then f (get v (ExtrNative.of_uint(0)))
       else foldi_down (fun i b -> oP (f (get v i)) b)
              (sub0 n0 (ExtrNative.of_uint(2))) (ExtrNative.of_uint(0))
              (f (get v (sub0 n0 (ExtrNative.of_uint(1)))))

(** val rev_aux : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_aux acc = function
| Nil -> acc
| Cons (t0, q) -> rev_aux (Cons (t0, acc)) q

(** val rev : 'a1 list -> 'a1 list **)

let rev l =
  rev_aux Nil l

(** val distinct_aux2 :
    ('a1 -> 'a1 -> bool) -> bool -> 'a1 -> 'a1 list -> bool **)

let rec distinct_aux2 eq acc ref = function
| Nil -> acc
| Cons (t0, q) ->
  distinct_aux2 eq (if acc then negb (eq ref t0) else false) ref q

(** val distinct_aux : ('a1 -> 'a1 -> bool) -> bool -> 'a1 list -> bool **)

let rec distinct_aux eq acc = function
| Nil -> acc
| Cons (t0, q) ->
  let acc' = distinct_aux2 eq acc t0 q in distinct_aux eq acc' q

(** val distinct : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool **)

let distinct eq =
  distinct_aux eq true

(** val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb2 f l1 l2 =
  match l1 with
  | Nil ->
    (match l2 with
     | Nil -> true
     | Cons (y, l) -> false)
  | Cons (a, l3) ->
    (match l2 with
     | Nil -> false
     | Cons (b, l4) -> if f a b then forallb2 f l3 l4 else false)

module Form = 
 struct 
  type form =
  | Fatom of int
  | Ftrue
  | Ffalse
  | Fnot2 of int * int
  | Fand of int array
  | For of int array
  | Fimp of int array
  | Fxor of int * int
  | Fiff of int * int
  | Fite of int * int * int
  
  (** val form_rect :
      (int -> 'a1) -> 'a1 -> 'a1 -> (int -> int -> 'a1) -> (int array -> 'a1)
      -> (int array -> 'a1) -> (int array -> 'a1) -> (int -> int -> 'a1) ->
      (int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> form -> 'a1 **)
  
  let form_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
  | Fatom x -> f x
  | Ftrue -> f0
  | Ffalse -> f1
  | Fnot2 (x, x0) -> f2 x x0
  | Fand x -> f3 x
  | For x -> f4 x
  | Fimp x -> f5 x
  | Fxor (x, x0) -> f6 x x0
  | Fiff (x, x0) -> f7 x x0
  | Fite (x, x0, x1) -> f8 x x0 x1
  
  (** val form_rec :
      (int -> 'a1) -> 'a1 -> 'a1 -> (int -> int -> 'a1) -> (int array -> 'a1)
      -> (int array -> 'a1) -> (int array -> 'a1) -> (int -> int -> 'a1) ->
      (int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> form -> 'a1 **)
  
  let form_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 = function
  | Fatom x -> f x
  | Ftrue -> f0
  | Ffalse -> f1
  | Fnot2 (x, x0) -> f2 x x0
  | Fand x -> f3 x
  | For x -> f4 x
  | Fimp x -> f5 x
  | Fxor (x, x0) -> f6 x x0
  | Fiff (x, x0) -> f7 x x0
  | Fite (x, x0, x1) -> f8 x x0 x1
  
  (** val is_Ftrue : form -> bool **)
  
  let is_Ftrue = function
  | Ftrue -> true
  | _ -> false
  
  (** val is_Ffalse : form -> bool **)
  
  let is_Ffalse = function
  | Ffalse -> true
  | _ -> false
  
  (** val interp_aux : (int -> bool) -> (int -> bool) -> form -> bool **)
  
  let interp_aux interp_atom interp_var = function
  | Fatom a -> interp_atom a
  | Ftrue -> true
  | Ffalse -> false
  | Fnot2 (i, l) ->
    fold (fun b -> negb (negb b)) (ExtrNative.of_uint(1)) i
      (Lit.interp interp_var l)
  | Fand args ->
    afold_left true (fun b1 b2 -> if b1 then b2 else false)
      (Lit.interp interp_var) args
  | For args ->
    afold_left false (fun b1 b2 -> if b1 then true else b2)
      (Lit.interp interp_var) args
  | Fimp args -> afold_right true implb (Lit.interp interp_var) args
  | Fxor (a, b) -> xorb (Lit.interp interp_var a) (Lit.interp interp_var b)
  | Fiff (a, b) -> eqb (Lit.interp interp_var a) (Lit.interp interp_var b)
  | Fite (a, b, c) ->
    if Lit.interp interp_var a
    then Lit.interp interp_var b
    else Lit.interp interp_var c
  
  (** val t_interp : (int -> bool) -> form array -> bool array **)
  
  let t_interp interp_atom t_form =
    foldi_left (fun i t_b hf ->
      set t_b i (interp_aux interp_atom (get t_b) hf))
      (make (length t_form) true) t_form
  
  (** val lt_form : int -> form -> bool **)
  
  let rec lt_form i = function
  | Fnot2 (i0, l) -> ltb0 (Lit.blit l) i
  | Fand args -> forallb1 (fun l -> ltb0 (Lit.blit l) i) args
  | For args -> forallb1 (fun l -> ltb0 (Lit.blit l) i) args
  | Fimp args -> forallb1 (fun l -> ltb0 (Lit.blit l) i) args
  | Fxor (a, b) -> if ltb0 (Lit.blit a) i then ltb0 (Lit.blit b) i else false
  | Fiff (a, b) -> if ltb0 (Lit.blit a) i then ltb0 (Lit.blit b) i else false
  | Fite (a, b, c) ->
    if if ltb0 (Lit.blit a) i then ltb0 (Lit.blit b) i else false
    then ltb0 (Lit.blit c) i
    else false
  | _ -> true
  
  (** val wf : form array -> bool **)
  
  let wf t_form =
    forallbi lt_form t_form
  
  (** val interp_state_var : (int -> bool) -> form array -> int -> bool **)
  
  let interp_state_var interp_atom t_form =
    let t_interp0 = t_interp interp_atom t_form in get t_interp0
  
  (** val interp : (int -> bool) -> form array -> form -> bool **)
  
  let interp interp_atom t_form =
    interp_aux interp_atom (interp_state_var interp_atom t_form)
  
  (** val check_form : form array -> bool **)
  
  let check_form t_form =
    if if if is_Ftrue (default t_form)
          then is_Ftrue (get t_form (ExtrNative.of_uint(0)))
          else false
       then is_Ffalse (get t_form (ExtrNative.of_uint(1)))
       else false
    then wf t_form
    else false
 end

type typ_eqb = { te_eqb : (__ -> __ -> bool);
                 te_reflect : (__ -> __ -> reflect) }

type te_carrier = __

(** val te_eqb : typ_eqb -> te_carrier -> te_carrier -> bool **)

let te_eqb x = x.te_eqb

module Typ = 
 struct 
  type coq_type =
  | Tindex of int
  | TZ
  | Tbool
  | Tpositive
  
  (** val type_rect :
      (int -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_type -> 'a1 **)
  
  let type_rect f f0 f1 f2 = function
  | Tindex x -> f x
  | TZ -> f0
  | Tbool -> f1
  | Tpositive -> f2
  
  (** val type_rec : (int -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_type -> 'a1 **)
  
  let type_rec f f0 f1 f2 = function
  | Tindex x -> f x
  | TZ -> f0
  | Tbool -> f1
  | Tpositive -> f2
  
  type ftype = coq_type list*coq_type
  
  type interp = __
  
  type interp_ftype = __
  
  (** val i_eqb : typ_eqb array -> coq_type -> interp -> interp -> bool **)
  
  let i_eqb t_i = function
  | Tindex i -> (get t_i i).te_eqb
  | TZ -> Obj.magic zeq_bool
  | Tbool -> Obj.magic eqb
  | Tpositive -> Obj.magic Coq_Pos.eqb
  
  (** val reflect_i_eqb :
      typ_eqb array -> coq_type -> interp -> interp -> reflect **)
  
  let reflect_i_eqb t_i t0 x y =
    iff_reflect (i_eqb t_i t0 x y)
  
  type cast_result =
  | Cast of (__ -> __ -> __)
  | NoCast
  
  (** val cast_result_rect :
      coq_type -> coq_type -> ((__ -> __ -> __) -> 'a1) -> 'a1 -> cast_result
      -> 'a1 **)
  
  let cast_result_rect a b f f0 = function
  | Cast x -> f x
  | NoCast -> f0
  
  (** val cast_result_rec :
      coq_type -> coq_type -> ((__ -> __ -> __) -> 'a1) -> 'a1 -> cast_result
      -> 'a1 **)
  
  let cast_result_rec a b f f0 = function
  | Cast x -> f x
  | NoCast -> f0
  
  (** val cast : coq_type -> coq_type -> cast_result **)
  
  let cast a b =
    match a with
    | Tindex i ->
      (match b with
       | Tindex j ->
         (match cast i j with
          | Some k -> Cast (fun _ -> k __)
          | None -> NoCast)
       | _ -> NoCast)
    | TZ ->
      (match b with
       | TZ -> Cast (fun _ x -> x)
       | _ -> NoCast)
    | Tbool ->
      (match b with
       | Tbool -> Cast (fun _ x -> x)
       | _ -> NoCast)
    | Tpositive ->
      (match b with
       | Tpositive -> Cast (fun _ x -> x)
       | _ -> NoCast)
  
  (** val eqb : coq_type -> coq_type -> bool **)
  
  let eqb a b =
    match a with
    | Tindex i ->
      (match b with
       | Tindex j -> eqb0 i j
       | _ -> false)
    | TZ ->
      (match b with
       | TZ -> true
       | _ -> false)
    | Tbool ->
      (match b with
       | Tbool -> true
       | _ -> false)
    | Tpositive ->
      (match b with
       | Tpositive -> true
       | _ -> false)
  
  (** val reflect_eqb : coq_type -> coq_type -> reflect **)
  
  let reflect_eqb x y =
    match x with
    | Tindex i ->
      (match y with
       | Tindex i0 -> iff_reflect (eqb0 i i0)
       | _ -> ReflectF)
    | TZ ->
      (match y with
       | TZ -> ReflectT
       | _ -> ReflectF)
    | Tbool ->
      (match y with
       | Tbool -> ReflectT
       | _ -> ReflectF)
    | Tpositive ->
      (match y with
       | Tpositive -> ReflectT
       | _ -> ReflectF)
 end

(** val list_beq : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_beq eq_A x y =
  match x with
  | Nil ->
    (match y with
     | Nil -> true
     | Cons (a, l) -> false)
  | Cons (x0, x1) ->
    (match y with
     | Nil -> false
     | Cons (x2, x3) -> if eq_A x0 x2 then list_beq eq_A x1 x3 else false)

(** val reflect_list_beq :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> reflect) -> 'a1 list -> 'a1 list
    -> reflect **)

let rec reflect_list_beq beq hbeq x y =
  match x with
  | Nil ->
    (match y with
     | Nil -> ReflectT
     | Cons (a, y0) -> ReflectF)
  | Cons (y0, l) ->
    (match y with
     | Nil -> ReflectF
     | Cons (a0, y1) ->
       let r = hbeq y0 a0 in
       (match r with
        | ReflectT -> reflect_list_beq beq hbeq l y1
        | ReflectF -> ReflectF))

module Atom = 
 struct 
  type cop =
  | CO_xH
  | CO_Z0
  
  (** val cop_rect : 'a1 -> 'a1 -> cop -> 'a1 **)
  
  let cop_rect f f0 = function
  | CO_xH -> f
  | CO_Z0 -> f0
  
  (** val cop_rec : 'a1 -> 'a1 -> cop -> 'a1 **)
  
  let cop_rec f f0 = function
  | CO_xH -> f
  | CO_Z0 -> f0
  
  type unop =
  | UO_xO
  | UO_xI
  | UO_Zpos
  | UO_Zneg
  | UO_Zopp
  
  (** val unop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> unop -> 'a1 **)
  
  let unop_rect f f0 f1 f2 f3 = function
  | UO_xO -> f
  | UO_xI -> f0
  | UO_Zpos -> f1
  | UO_Zneg -> f2
  | UO_Zopp -> f3
  
  (** val unop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> unop -> 'a1 **)
  
  let unop_rec f f0 f1 f2 f3 = function
  | UO_xO -> f
  | UO_xI -> f0
  | UO_Zpos -> f1
  | UO_Zneg -> f2
  | UO_Zopp -> f3
  
  type binop =
  | BO_Zplus
  | BO_Zminus
  | BO_Zmult
  | BO_Zlt
  | BO_Zle
  | BO_Zge
  | BO_Zgt
  | BO_eq of Typ.coq_type
  
  (** val binop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (Typ.coq_type -> 'a1)
      -> binop -> 'a1 **)
  
  let binop_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | BO_Zplus -> f
  | BO_Zminus -> f0
  | BO_Zmult -> f1
  | BO_Zlt -> f2
  | BO_Zle -> f3
  | BO_Zge -> f4
  | BO_Zgt -> f5
  | BO_eq x -> f6 x
  
  (** val binop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (Typ.coq_type -> 'a1)
      -> binop -> 'a1 **)
  
  let binop_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | BO_Zplus -> f
  | BO_Zminus -> f0
  | BO_Zmult -> f1
  | BO_Zlt -> f2
  | BO_Zle -> f3
  | BO_Zge -> f4
  | BO_Zgt -> f5
  | BO_eq x -> f6 x
  
  type nop =
    Typ.coq_type
    (* singleton inductive, whose constructor was NO_distinct *)
  
  (** val nop_rect : (Typ.coq_type -> 'a1) -> nop -> 'a1 **)
  
  let nop_rect f n0 =
    f n0
  
  (** val nop_rec : (Typ.coq_type -> 'a1) -> nop -> 'a1 **)
  
  let nop_rec f n0 =
    f n0
  
  type atom =
  | Acop of cop
  | Auop of unop * int
  | Abop of binop * int * int
  | Anop of nop * int list
  | Aapp of int * int list
  
  (** val atom_rect :
      (cop -> 'a1) -> (unop -> int -> 'a1) -> (binop -> int -> int -> 'a1) ->
      (nop -> int list -> 'a1) -> (int -> int list -> 'a1) -> atom -> 'a1 **)
  
  let atom_rect f f0 f1 f2 f3 = function
  | Acop x -> f x
  | Auop (x, x0) -> f0 x x0
  | Abop (x, x0, x1) -> f1 x x0 x1
  | Anop (x, x0) -> f2 x x0
  | Aapp (x, x0) -> f3 x x0
  
  (** val atom_rec :
      (cop -> 'a1) -> (unop -> int -> 'a1) -> (binop -> int -> int -> 'a1) ->
      (nop -> int list -> 'a1) -> (int -> int list -> 'a1) -> atom -> 'a1 **)
  
  let atom_rec f f0 f1 f2 f3 = function
  | Acop x -> f x
  | Auop (x, x0) -> f0 x x0
  | Abop (x, x0, x1) -> f1 x x0 x1
  | Anop (x, x0) -> f2 x x0
  | Aapp (x, x0) -> f3 x x0
  
  (** val cop_eqb : cop -> cop -> bool **)
  
  let cop_eqb o o' =
    match o with
    | CO_xH ->
      (match o' with
       | CO_xH -> true
       | CO_Z0 -> false)
    | CO_Z0 ->
      (match o' with
       | CO_xH -> false
       | CO_Z0 -> true)
  
  (** val uop_eqb : unop -> unop -> bool **)
  
  let uop_eqb o o' =
    match o with
    | UO_xO ->
      (match o' with
       | UO_xO -> true
       | _ -> false)
    | UO_xI ->
      (match o' with
       | UO_xI -> true
       | _ -> false)
    | UO_Zpos ->
      (match o' with
       | UO_Zpos -> true
       | _ -> false)
    | UO_Zneg ->
      (match o' with
       | UO_Zneg -> true
       | _ -> false)
    | UO_Zopp ->
      (match o' with
       | UO_Zopp -> true
       | _ -> false)
  
  (** val bop_eqb : binop -> binop -> bool **)
  
  let bop_eqb o o' =
    match o with
    | BO_Zplus ->
      (match o' with
       | BO_Zplus -> true
       | _ -> false)
    | BO_Zminus ->
      (match o' with
       | BO_Zminus -> true
       | _ -> false)
    | BO_Zmult ->
      (match o' with
       | BO_Zmult -> true
       | _ -> false)
    | BO_Zlt ->
      (match o' with
       | BO_Zlt -> true
       | _ -> false)
    | BO_Zle ->
      (match o' with
       | BO_Zle -> true
       | _ -> false)
    | BO_Zge ->
      (match o' with
       | BO_Zge -> true
       | _ -> false)
    | BO_Zgt ->
      (match o' with
       | BO_Zgt -> true
       | _ -> false)
    | BO_eq t0 ->
      (match o' with
       | BO_eq t' -> Typ.eqb t0 t'
       | _ -> false)
  
  (** val nop_eqb : nop -> nop -> bool **)
  
  let nop_eqb o o' =
    Typ.eqb o o'
  
  (** val eqb : atom -> atom -> bool **)
  
  let eqb t0 t' =
    match t0 with
    | Acop o ->
      (match t' with
       | Acop o' -> cop_eqb o o'
       | _ -> false)
    | Auop (o, t1) ->
      (match t' with
       | Auop (o', t'0) -> if uop_eqb o o' then eqb0 t1 t'0 else false
       | _ -> false)
    | Abop (o, t1, t2) ->
      (match t' with
       | Abop (o', t1', t2') ->
         if if bop_eqb o o' then eqb0 t1 t1' else false
         then eqb0 t2 t2'
         else false
       | _ -> false)
    | Anop (o, t1) ->
      (match t' with
       | Anop (o', t'0) ->
         if nop_eqb o o' then list_beq eqb0 t1 t'0 else false
       | _ -> false)
    | Aapp (a, la) ->
      (match t' with
       | Aapp (b, lb) -> if eqb0 a b then list_beq eqb0 la lb else false
       | _ -> false)
  
  (** val reflect_cop_eqb : cop -> cop -> reflect **)
  
  let reflect_cop_eqb o1 o2 =
    match o1 with
    | CO_xH ->
      (match o2 with
       | CO_xH -> ReflectT
       | CO_Z0 -> ReflectF)
    | CO_Z0 ->
      (match o2 with
       | CO_xH -> ReflectF
       | CO_Z0 -> ReflectT)
  
  (** val reflect_uop_eqb : unop -> unop -> reflect **)
  
  let reflect_uop_eqb o1 o2 =
    match o1 with
    | UO_xO ->
      (match o2 with
       | UO_xO -> ReflectT
       | _ -> ReflectF)
    | UO_xI ->
      (match o2 with
       | UO_xI -> ReflectT
       | _ -> ReflectF)
    | UO_Zpos ->
      (match o2 with
       | UO_Zpos -> ReflectT
       | _ -> ReflectF)
    | UO_Zneg ->
      (match o2 with
       | UO_Zneg -> ReflectT
       | _ -> ReflectF)
    | UO_Zopp ->
      (match o2 with
       | UO_Zopp -> ReflectT
       | _ -> ReflectF)
  
  (** val reflect_bop_eqb : binop -> binop -> reflect **)
  
  let reflect_bop_eqb o1 o2 =
    match o1 with
    | BO_Zplus ->
      (match o2 with
       | BO_Zplus -> ReflectT
       | _ -> ReflectF)
    | BO_Zminus ->
      (match o2 with
       | BO_Zminus -> ReflectT
       | _ -> ReflectF)
    | BO_Zmult ->
      (match o2 with
       | BO_Zmult -> ReflectT
       | _ -> ReflectF)
    | BO_Zlt ->
      (match o2 with
       | BO_Zlt -> ReflectT
       | _ -> ReflectF)
    | BO_Zle ->
      (match o2 with
       | BO_Zle -> ReflectT
       | _ -> ReflectF)
    | BO_Zge ->
      (match o2 with
       | BO_Zge -> ReflectT
       | _ -> ReflectF)
    | BO_Zgt ->
      (match o2 with
       | BO_Zgt -> ReflectT
       | _ -> ReflectF)
    | BO_eq t0 ->
      (match o2 with
       | BO_eq t1 -> Typ.reflect_eqb t0 t1
       | _ -> ReflectF)
  
  (** val reflect_nop_eqb : nop -> nop -> reflect **)
  
  let reflect_nop_eqb o1 o2 =
    Typ.reflect_eqb o1 o2
  
  (** val reflect_eqb : atom -> atom -> reflect **)
  
  let reflect_eqb t1 t2 =
    match t1 with
    | Acop c ->
      (match t2 with
       | Acop c0 -> reflect_cop_eqb c c0
       | _ -> ReflectF)
    | Auop (u, i) ->
      (match t2 with
       | Auop (u0, i0) ->
         let r = reflect_uop_eqb u u0 in
         (match r with
          | ReflectT -> reflect_eqb i i0
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
    | Abop (b, i, i0) ->
      (match t2 with
       | Abop (b0, i1, i2) ->
         let r = reflect_bop_eqb b b0 in
         (match r with
          | ReflectT ->
            let r0 = reflect_eqb i i1 in
            (match r0 with
             | ReflectT -> reflect_eqb i0 i2
             | ReflectF -> ReflectF)
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
    | Anop (n0, l) ->
      (match t2 with
       | Anop (n1, l0) ->
         let r = reflect_nop_eqb n0 n1 in
         (match r with
          | ReflectT -> reflect_list_beq eqb0 reflect_eqb l l0
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
    | Aapp (i, l) ->
      (match t2 with
       | Aapp (i0, l0) ->
         let r = reflect_eqb i i0 in
         (match r with
          | ReflectT -> reflect_list_beq eqb0 reflect_eqb l l0
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
  
  type ('t, 'i) coq_val = { v_type : 't; v_val : 'i }
  
  (** val val_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_val -> 'a3 **)
  
  let val_rect f v =
    let { v_type = x; v_val = x0 } = v in f x x0
  
  (** val val_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_val -> 'a3 **)
  
  let val_rec f v =
    let { v_type = x; v_val = x0 } = v in f x x0
  
  (** val v_type : ('a1, 'a2) coq_val -> 'a1 **)
  
  let v_type x = x.v_type
  
  (** val v_val : ('a1, 'a2) coq_val -> 'a2 **)
  
  let v_val x = x.v_val
  
  type bval = (Typ.coq_type, Typ.interp) coq_val
  
  (** val coq_Bval :
      typ_eqb array -> Typ.coq_type -> Typ.interp -> (Typ.coq_type,
      Typ.interp) coq_val **)
  
  let coq_Bval t_i x x0 =
    { v_type = x; v_val = x0 }
  
  type tval = (Typ.ftype, Typ.interp_ftype) coq_val
  
  (** val coq_Tval :
      typ_eqb array -> Typ.ftype -> Typ.interp_ftype -> (Typ.ftype,
      Typ.interp_ftype) coq_val **)
  
  let coq_Tval t_i x x0 =
    { v_type = x; v_val = x0 }
  
  (** val bvtrue : typ_eqb array -> bval **)
  
  let bvtrue t_i =
    coq_Bval t_i Typ.Tbool (Obj.magic true)
  
  (** val bvfalse : typ_eqb array -> bval **)
  
  let bvfalse t_i =
    coq_Bval t_i Typ.Tbool (Obj.magic false)
  
  (** val typ_cop : cop -> Typ.coq_type **)
  
  let typ_cop = function
  | CO_xH -> Typ.Tpositive
  | CO_Z0 -> Typ.TZ
  
  (** val typ_uop : unop -> Typ.coq_type*Typ.coq_type **)
  
  let typ_uop = function
  | UO_xO -> Typ.Tpositive,Typ.Tpositive
  | UO_xI -> Typ.Tpositive,Typ.Tpositive
  | UO_Zopp -> Typ.TZ,Typ.TZ
  | _ -> Typ.Tpositive,Typ.TZ
  
  (** val typ_bop : binop -> (Typ.coq_type*Typ.coq_type)*Typ.coq_type **)
  
  let typ_bop = function
  | BO_Zplus -> (Typ.TZ,Typ.TZ),Typ.TZ
  | BO_Zminus -> (Typ.TZ,Typ.TZ),Typ.TZ
  | BO_Zmult -> (Typ.TZ,Typ.TZ),Typ.TZ
  | BO_eq t0 -> (t0,t0),Typ.Tbool
  | _ -> (Typ.TZ,Typ.TZ),Typ.Tbool
  
  (** val typ_nop : nop -> Typ.coq_type*Typ.coq_type **)
  
  let typ_nop o =
    o,Typ.Tbool
  
  (** val check_args :
      (int -> Typ.coq_type) -> int list -> Typ.coq_type list -> bool **)
  
  let rec check_args get_type0 args targs =
    match args with
    | Nil ->
      (match targs with
       | Nil -> true
       | Cons (t0, l) -> false)
    | Cons (a, args0) ->
      (match targs with
       | Nil -> false
       | Cons (t0, targs0) ->
         if Typ.eqb (get_type0 a) t0
         then check_args get_type0 args0 targs0
         else false)
  
  (** val check_aux :
      typ_eqb array -> tval array -> (int -> Typ.coq_type) -> atom ->
      Typ.coq_type -> bool **)
  
  let check_aux t_i t_func get_type0 a t0 =
    match a with
    | Acop o -> Typ.eqb (typ_cop o) t0
    | Auop (o, a0) ->
      let ta,t' = typ_uop o in
      if Typ.eqb t' t0 then Typ.eqb (get_type0 a0) ta else false
    | Abop (o, a1, a2) ->
      let ta,t' = typ_bop o in
      let ta1,ta2 = ta in
      if if Typ.eqb t' t0 then Typ.eqb (get_type0 a1) ta1 else false
      then Typ.eqb (get_type0 a2) ta2
      else false
    | Anop (o, a0) ->
      let ta,t' = typ_nop o in
      if Typ.eqb t' t0
      then forallb (fun t1 -> Typ.eqb (get_type0 t1) ta) a0
      else false
    | Aapp (f, args) ->
      let targs,tr = (get t_func f).v_type in
      if check_args get_type0 args targs then Typ.eqb tr t0 else false
  
  (** val check_args_dec :
      (int -> Typ.coq_type) -> Typ.coq_type -> int list -> Typ.coq_type list
      -> sumbool **)
  
  let rec check_args_dec get_type0 a args targs =
    match args with
    | Nil ->
      (match targs with
       | Nil -> Left
       | Cons (t0, l) -> Right)
    | Cons (y, l) ->
      (match targs with
       | Nil -> Right
       | Cons (b, targs0) ->
         if Typ.eqb (get_type0 y) b
         then check_args_dec get_type0 a l targs0
         else Right)
  
  (** val check_aux_dec :
      typ_eqb array -> tval array -> (int -> Typ.coq_type) -> atom -> sumbool **)
  
  let check_aux_dec t_i t_func get_type0 = function
  | Acop op -> Left
  | Auop (op, h) ->
    (match op with
     | UO_Zopp -> if Typ.eqb (get_type0 h) Typ.TZ then Left else Right
     | _ -> if Typ.eqb (get_type0 h) Typ.Tpositive then Left else Right)
  | Abop (op, h1, h2) ->
    (match op with
     | BO_eq t0 ->
       if Typ.eqb (get_type0 h1) t0
       then if Typ.eqb (get_type0 h2) t0 then Left else Right
       else Right
     | _ ->
       if Typ.eqb (get_type0 h1) Typ.TZ
       then if Typ.eqb (get_type0 h2) Typ.TZ then Left else Right
       else Right)
  | Anop (op, ha) ->
    if forallb (fun t1 -> Typ.eqb (get_type0 t1) op) ha then Left else Right
  | Aapp (f, args) ->
    let l,t0 = (get t_func f).v_type in check_args_dec get_type0 t0 args l
  
  (** val apply_unop :
      typ_eqb array -> Typ.coq_type -> Typ.coq_type -> (Typ.interp ->
      Typ.interp) -> bval -> (Typ.coq_type, Typ.interp) coq_val **)
  
  let apply_unop t_i t0 r op tv =
    let { v_type = t'; v_val = v } = tv in
    (match Typ.cast t' t0 with
     | Typ.Cast k -> coq_Bval t_i r (op (k __ v))
     | Typ.NoCast -> bvtrue t_i)
  
  (** val apply_binop :
      typ_eqb array -> Typ.coq_type -> Typ.coq_type -> Typ.coq_type ->
      (Typ.interp -> Typ.interp -> Typ.interp) -> bval -> bval ->
      (Typ.coq_type, Typ.interp) coq_val **)
  
  let apply_binop t_i t1 t2 r op tv1 tv2 =
    let { v_type = t1'; v_val = v1 } = tv1 in
    let { v_type = t2'; v_val = v2 } = tv2 in
    (match Typ.cast t1' t1 with
     | Typ.Cast k1 ->
       (match Typ.cast t2' t2 with
        | Typ.Cast k2 -> coq_Bval t_i r (op (k1 __ v1) (k2 __ v2))
        | Typ.NoCast -> bvtrue t_i)
     | Typ.NoCast -> bvtrue t_i)
  
  (** val apply_func :
      typ_eqb array -> Typ.coq_type list -> Typ.coq_type -> Typ.interp_ftype
      -> bval list -> bval **)
  
  let rec apply_func t_i targs tr f lv =
    match targs with
    | Nil ->
      (match lv with
       | Nil -> coq_Bval t_i tr f
       | Cons (b, l) -> bvtrue t_i)
    | Cons (t0, targs0) ->
      (match lv with
       | Nil -> bvtrue t_i
       | Cons (v, lv0) ->
         let { v_type = tv; v_val = v0 } = v in
         (match Typ.cast tv t0 with
          | Typ.Cast k ->
            let f0 = Obj.magic f (k __ v0) in apply_func t_i targs0 tr f0 lv0
          | Typ.NoCast -> bvtrue t_i))
  
  (** val interp_cop :
      typ_eqb array -> cop -> (Typ.coq_type, Typ.interp) coq_val **)
  
  let interp_cop t_i = function
  | CO_xH -> coq_Bval t_i Typ.Tpositive (Obj.magic XH)
  | CO_Z0 -> coq_Bval t_i Typ.TZ (Obj.magic Z0)
  
  (** val interp_uop :
      typ_eqb array -> unop -> bval -> (Typ.coq_type, Typ.interp) coq_val **)
  
  let interp_uop t_i = function
  | UO_xO ->
    apply_unop t_i Typ.Tpositive Typ.Tpositive (Obj.magic (fun x -> XO x))
  | UO_xI ->
    apply_unop t_i Typ.Tpositive Typ.Tpositive (Obj.magic (fun x -> XI x))
  | UO_Zpos ->
    apply_unop t_i Typ.Tpositive Typ.TZ (Obj.magic (fun x -> Zpos x))
  | UO_Zneg ->
    apply_unop t_i Typ.Tpositive Typ.TZ (Obj.magic (fun x -> Zneg x))
  | UO_Zopp -> apply_unop t_i Typ.TZ Typ.TZ (Obj.magic Z.opp)
  
  (** val interp_bop :
      typ_eqb array -> binop -> bval -> bval -> (Typ.coq_type, Typ.interp)
      coq_val **)
  
  let interp_bop t_i = function
  | BO_Zplus -> apply_binop t_i Typ.TZ Typ.TZ Typ.TZ (Obj.magic Z.add)
  | BO_Zminus -> apply_binop t_i Typ.TZ Typ.TZ Typ.TZ (Obj.magic Z.sub)
  | BO_Zmult -> apply_binop t_i Typ.TZ Typ.TZ Typ.TZ (Obj.magic Z.mul)
  | BO_Zlt -> apply_binop t_i Typ.TZ Typ.TZ Typ.Tbool (Obj.magic Z.ltb)
  | BO_Zle -> apply_binop t_i Typ.TZ Typ.TZ Typ.Tbool (Obj.magic Z.leb)
  | BO_Zge -> apply_binop t_i Typ.TZ Typ.TZ Typ.Tbool (Obj.magic Z.geb)
  | BO_Zgt -> apply_binop t_i Typ.TZ Typ.TZ Typ.Tbool (Obj.magic Z.gtb)
  | BO_eq t0 ->
    apply_binop t_i t0 t0 Typ.Tbool (Obj.magic (Typ.i_eqb t_i t0))
  
  (** val compute_interp :
      typ_eqb array -> (int -> bval) -> Typ.coq_type -> Typ.interp list ->
      int list -> Typ.interp list option **)
  
  let rec compute_interp t_i interp_hatom0 ty acc = function
  | Nil -> Some acc
  | Cons (a, q) ->
    let { v_type = ta; v_val = va } = interp_hatom0 a in
    (match Typ.cast ta ty with
     | Typ.Cast ka ->
       compute_interp t_i interp_hatom0 ty (Cons ((ka __ va), acc)) q
     | Typ.NoCast -> None)
  
  (** val interp_aux :
      typ_eqb array -> tval array -> (int -> bval) -> atom -> bval **)
  
  let interp_aux t_i t_func interp_hatom0 = function
  | Acop o -> interp_cop t_i o
  | Auop (o, a0) -> interp_uop t_i o (interp_hatom0 a0)
  | Abop (o, a1, a2) ->
    interp_bop t_i o (interp_hatom0 a1) (interp_hatom0 a2)
  | Anop (n0, a0) ->
    (match compute_interp t_i interp_hatom0 n0 Nil a0 with
     | Some l ->
       coq_Bval t_i Typ.Tbool
         (Obj.magic (distinct (Typ.i_eqb t_i n0) (rev l)))
     | None -> bvtrue t_i)
  | Aapp (f, args) ->
    let { v_type = tf; v_val = f0 } = get t_func f in
    let lv = map interp_hatom0 args in apply_func t_i (fst tf) (snd tf) f0 lv
  
  (** val interp_bool : typ_eqb array -> bval -> bool **)
  
  let interp_bool t_i v =
    let { v_type = t0; v_val = v0 } = v in
    (match Typ.cast t0 Typ.Tbool with
     | Typ.Cast k -> Obj.magic k __ v0
     | Typ.NoCast -> true)
  
  (** val t_interp :
      typ_eqb array -> tval array -> atom array -> bval array **)
  
  let t_interp t_i t_func t_atom =
    foldi_left (fun i t_a a -> set t_a i (interp_aux t_i t_func (get t_a) a))
      (make (length t_atom) (interp_cop t_i CO_xH)) t_atom
  
  (** val lt_atom : int -> atom -> bool **)
  
  let lt_atom i = function
  | Acop c -> true
  | Auop (u, h) -> ltb0 h i
  | Abop (b, h1, h2) -> if ltb0 h1 i then ltb0 h2 i else false
  | Anop (n0, ha) -> forallb (fun h -> ltb0 h i) ha
  | Aapp (f, args) -> forallb (fun h -> ltb0 h i) args
  
  (** val wf : atom array -> bool **)
  
  let wf t_atom =
    forallbi lt_atom t_atom
  
  (** val get_type' : typ_eqb array -> bval array -> int -> Typ.coq_type **)
  
  let get_type' t_i t_interp' i =
    (get t_interp' i).v_type
  
  (** val get_type :
      typ_eqb array -> tval array -> atom array -> int -> Typ.coq_type **)
  
  let get_type t_i t_func t_atom =
    get_type' t_i (t_interp t_i t_func t_atom)
  
  (** val wt : typ_eqb array -> tval array -> atom array -> bool **)
  
  let wt t_i t_func t_atom =
    let t_interp0 = t_interp t_i t_func t_atom in
    let get_type0 = get_type' t_i t_interp0 in
    forallbi (fun i h -> check_aux t_i t_func get_type0 h (get_type0 i))
      t_atom
  
  (** val interp_hatom :
      typ_eqb array -> tval array -> atom array -> int -> bval **)
  
  let interp_hatom t_i t_func t_atom =
    let t_a = t_interp t_i t_func t_atom in get t_a
  
  (** val interp :
      typ_eqb array -> tval array -> atom array -> atom -> bval **)
  
  let interp t_i t_func t_atom =
    interp_aux t_i t_func (interp_hatom t_i t_func t_atom)
  
  (** val interp_form_hatom :
      typ_eqb array -> tval array -> atom array -> int -> bool **)
  
  let interp_form_hatom t_i t_func t_atom =
    let interp0 = interp_hatom t_i t_func t_atom in
    (fun a -> interp_bool t_i (interp0 a))
  
  (** val check_atom : atom array -> bool **)
  
  let check_atom t_atom =
    match default t_atom with
    | Acop c ->
      (match c with
       | CO_xH -> wf t_atom
       | CO_Z0 -> false)
    | _ -> false
 end

(** val or_of_imp : int array -> int array **)

let or_of_imp args =
  let last = sub0 (length args) (ExtrNative.of_uint(1)) in
  mapi (fun i l -> if eqb0 i last then l else Lit.neg l) args

(** val check_True : C.t **)

let check_True =
  C._true

(** val check_False : int list **)

let check_False =
  Cons ((Lit.neg Lit._false), Nil)

(** val check_BuildDef : Form.form array -> int -> C.t **)

let check_BuildDef t_form l =
  match get t_form (Lit.blit l) with
  | Form.Fand args ->
    if Lit.is_pos l then Cons (l, (map Lit.neg (to_list args))) else C._true
  | Form.For args ->
    if Lit.is_pos l then C._true else Cons (l, (to_list args))
  | Form.Fimp args ->
    if Lit.is_pos l
    then C._true
    else let args0 = or_of_imp args in Cons (l, (to_list args0))
  | Form.Fxor (a, b) ->
    if Lit.is_pos l
    then Cons (l, (Cons (a, (Cons ((Lit.neg b), Nil)))))
    else Cons (l, (Cons (a, (Cons (b, Nil)))))
  | Form.Fiff (a, b) ->
    if Lit.is_pos l
    then Cons (l, (Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))))
    else Cons (l, (Cons (a, (Cons ((Lit.neg b), Nil)))))
  | Form.Fite (a, b, c) ->
    if Lit.is_pos l
    then Cons (l, (Cons (a, (Cons ((Lit.neg c), Nil)))))
    else Cons (l, (Cons (a, (Cons (c, Nil)))))
  | _ -> C._true

(** val check_ImmBuildDef : Form.form array -> S.t -> int -> C.t **)

let check_ImmBuildDef t_form s pos =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       (match get t_form (Lit.blit l) with
        | Form.Fand args ->
          if Lit.is_pos l then C._true else map Lit.neg (to_list args)
        | Form.For args -> if Lit.is_pos l then to_list args else C._true
        | Form.Fimp args ->
          if Lit.is_pos l
          then let args0 = or_of_imp args in to_list args0
          else C._true
        | Form.Fxor (a, b) ->
          if Lit.is_pos l
          then Cons (a, (Cons (b, Nil)))
          else Cons (a, (Cons ((Lit.neg b), Nil)))
        | Form.Fiff (a, b) ->
          if Lit.is_pos l
          then Cons (a, (Cons ((Lit.neg b), Nil)))
          else Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))
        | Form.Fite (a, b, c) ->
          if Lit.is_pos l
          then Cons (a, (Cons (c, Nil)))
          else Cons (a, (Cons ((Lit.neg c), Nil)))
        | _ -> C._true)
     | Cons (i, l1) -> C._true)

(** val check_BuildDef2 : Form.form array -> int -> C.t **)

let check_BuildDef2 t_form l =
  match get t_form (Lit.blit l) with
  | Form.Fxor (a, b) ->
    if Lit.is_pos l
    then Cons (l, (Cons ((Lit.neg a), (Cons (b, Nil)))))
    else Cons (l, (Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))))
  | Form.Fiff (a, b) ->
    if Lit.is_pos l
    then Cons (l, (Cons (a, (Cons (b, Nil)))))
    else Cons (l, (Cons ((Lit.neg a), (Cons (b, Nil)))))
  | Form.Fite (a, b, c) ->
    if Lit.is_pos l
    then Cons (l, (Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))))
    else Cons (l, (Cons ((Lit.neg a), (Cons (b, Nil)))))
  | _ -> C._true

(** val check_ImmBuildDef2 : Form.form array -> S.t -> int -> C.t **)

let check_ImmBuildDef2 t_form s pos =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       (match get t_form (Lit.blit l) with
        | Form.Fxor (a, b) ->
          if Lit.is_pos l
          then Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))
          else Cons ((Lit.neg a), (Cons (b, Nil)))
        | Form.Fiff (a, b) ->
          if Lit.is_pos l
          then Cons ((Lit.neg a), (Cons (b, Nil)))
          else Cons (a, (Cons (b, Nil)))
        | Form.Fite (a, b, c) ->
          if Lit.is_pos l
          then Cons ((Lit.neg a), (Cons (b, Nil)))
          else Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))
        | _ -> C._true)
     | Cons (i, l1) -> C._true)

(** val check_BuildProj : Form.form array -> int -> int -> C.t **)

let check_BuildProj t_form l i =
  let x = Lit.blit l in
  (match get t_form x with
   | Form.Fand args ->
     if ltb0 i (length args)
     then Cons ((Lit.nlit x), (Cons ((get args i), Nil)))
     else C._true
   | Form.For args ->
     if ltb0 i (length args)
     then Cons ((Lit.lit x), (Cons ((Lit.neg (get args i)), Nil)))
     else C._true
   | Form.Fimp args ->
     let len = length args in
     if ltb0 i len
     then if eqb0 i (sub0 len (ExtrNative.of_uint(1)))
          then Cons ((Lit.lit x), (Cons ((Lit.neg (get args i)), Nil)))
          else Cons ((Lit.lit x), (Cons ((get args i), Nil)))
     else C._true
   | _ -> C._true)

(** val check_ImmBuildProj : Form.form array -> S.t -> int -> int -> C.t **)

let check_ImmBuildProj t_form s pos i =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       let x = Lit.blit l in
       (match get t_form x with
        | Form.Fand args ->
          if if ltb0 i (length args) then Lit.is_pos l else false
          then Cons ((get args i), Nil)
          else C._true
        | Form.For args ->
          if if ltb0 i (length args) then negb (Lit.is_pos l) else false
          then Cons ((Lit.neg (get args i)), Nil)
          else C._true
        | Form.Fimp args ->
          let len = length args in
          if if ltb0 i len then negb (Lit.is_pos l) else false
          then if eqb0 i (sub0 len (ExtrNative.of_uint(1)))
               then Cons ((Lit.neg (get args i)), Nil)
               else Cons ((get args i), Nil)
          else C._true
        | _ -> C._true)
     | Cons (i0, l1) -> C._true)

(** val get_eq :
    Form.form array -> Atom.atom array -> int -> (int -> int -> C.t) -> C.t **)

let get_eq t_form t_atom x f =
  match get t_form x with
  | Form.Fatom xa ->
    (match get t_atom xa with
     | Atom.Abop (b0, a, b) ->
       (match b0 with
        | Atom.BO_eq t0 -> f a b
        | _ -> C._true)
     | _ -> C._true)
  | _ -> C._true

(** val check_trans_aux :
    Form.form array -> Atom.atom array -> int -> int -> int list -> int ->
    C.t -> C.t **)

let rec check_trans_aux t_form t_atom t1 t2 eqs res clause0 =
  match eqs with
  | Nil ->
    let xres = Lit.blit res in
    get_eq t_form t_atom xres (fun t1' t2' ->
      if if if eqb0 t1 t1' then eqb0 t2 t2' else false
         then true
         else if eqb0 t1 t2' then eqb0 t2 t1' else false
      then Cons ((Lit.lit xres), clause0)
      else C._true)
  | Cons (leq, eqs0) ->
    let xeq = Lit.blit leq in
    get_eq t_form t_atom xeq (fun t0 t' ->
      if eqb0 t2 t'
      then check_trans_aux t_form t_atom t1 t0 eqs0 res (Cons
             ((Lit.nlit xeq), clause0))
      else if eqb0 t2 t0
           then check_trans_aux t_form t_atom t1 t' eqs0 res (Cons
                  ((Lit.nlit xeq), clause0))
           else if eqb0 t1 t'
                then check_trans_aux t_form t_atom t0 t2 eqs0 res (Cons
                       ((Lit.nlit xeq), clause0))
                else if eqb0 t1 t0
                     then check_trans_aux t_form t_atom t' t2 eqs0 res (Cons
                            ((Lit.nlit xeq), clause0))
                     else C._true)

(** val check_trans :
    Form.form array -> Atom.atom array -> int -> int list -> C.t **)

let check_trans t_form t_atom res = function
| Nil ->
  let xres = Lit.blit res in
  get_eq t_form t_atom xres (fun t1 t2 ->
    if eqb0 t1 t2 then Cons ((Lit.lit xres), Nil) else C._true)
| Cons (leq, eqs0) ->
  let xeq = Lit.blit leq in
  get_eq t_form t_atom xeq (fun t1 t2 ->
    check_trans_aux t_form t_atom t1 t2 eqs0 res (Cons ((Lit.nlit xeq), Nil)))

(** val build_congr :
    Form.form array -> Atom.atom array -> int option list -> int list -> int
    list -> C.t -> C.t **)

let rec build_congr t_form t_atom eqs l r c =
  match eqs with
  | Nil ->
    (match l with
     | Nil ->
       (match r with
        | Nil -> c
        | Cons (i, l0) -> C._true)
     | Cons (i, l0) -> C._true)
  | Cons (eq, eqs0) ->
    (match l with
     | Nil -> C._true
     | Cons (t1, l0) ->
       (match r with
        | Nil -> C._true
        | Cons (t2, r0) ->
          (match eq with
           | Some leq ->
             let xeq = Lit.blit leq in
             get_eq t_form t_atom xeq (fun t1' t2' ->
               if if if eqb0 t1 t1' then eqb0 t2 t2' else false
                  then true
                  else if eqb0 t1 t2' then eqb0 t2 t1' else false
               then build_congr t_form t_atom eqs0 l0 r0 (Cons
                      ((Lit.nlit xeq), c))
               else C._true)
           | None ->
             if eqb0 t1 t2
             then build_congr t_form t_atom eqs0 l0 r0 c
             else C._true)))

(** val check_congr :
    Form.form array -> Atom.atom array -> int -> int option list -> C.t **)

let check_congr t_form t_atom leq eqs =
  let xeq = Lit.blit leq in
  get_eq t_form t_atom xeq (fun t1 t2 ->
    match get t_atom t1 with
    | Atom.Auop (o1, a) ->
      (match get t_atom t2 with
       | Atom.Auop (o2, b) ->
         if Atom.uop_eqb o1 o2
         then build_congr t_form t_atom eqs (Cons (a, Nil)) (Cons (b, Nil))
                (Cons ((Lit.lit xeq), Nil))
         else C._true
       | _ -> C._true)
    | Atom.Abop (o1, a1, a2) ->
      (match get t_atom t2 with
       | Atom.Abop (o2, b1, b2) ->
         if Atom.bop_eqb o1 o2
         then build_congr t_form t_atom eqs (Cons (a1, (Cons (a2, Nil))))
                (Cons (b1, (Cons (b2, Nil)))) (Cons ((Lit.lit xeq), Nil))
         else C._true
       | _ -> C._true)
    | Atom.Aapp (f1, args1) ->
      (match get t_atom t2 with
       | Atom.Aapp (f2, args2) ->
         if eqb0 f1 f2
         then build_congr t_form t_atom eqs args1 args2 (Cons ((Lit.lit xeq),
                Nil))
         else C._true
       | _ -> C._true)
    | _ -> C._true)

(** val check_congr_pred :
    Form.form array -> Atom.atom array -> int -> int -> int option list ->
    C.t **)

let check_congr_pred t_form t_atom pA pB eqs =
  let xPA = Lit.blit pA in
  let xPB = Lit.blit pB in
  (match get t_form xPA with
   | Form.Fatom pa ->
     (match get t_form xPB with
      | Form.Fatom pb ->
        (match get t_atom pa with
         | Atom.Auop (o1, a) ->
           (match get t_atom pb with
            | Atom.Auop (o2, b) ->
              if Atom.uop_eqb o1 o2
              then build_congr t_form t_atom eqs (Cons (a, Nil)) (Cons (b,
                     Nil)) (Cons ((Lit.nlit xPA), (Cons ((Lit.lit xPB),
                     Nil))))
              else C._true
            | _ -> C._true)
         | Atom.Abop (o1, a1, a2) ->
           (match get t_atom pb with
            | Atom.Abop (o2, b1, b2) ->
              if Atom.bop_eqb o1 o2
              then build_congr t_form t_atom eqs (Cons (a1, (Cons (a2,
                     Nil)))) (Cons (b1, (Cons (b2, Nil)))) (Cons
                     ((Lit.nlit xPA), (Cons ((Lit.lit xPB), Nil))))
              else C._true
            | _ -> C._true)
         | Atom.Aapp (p, a) ->
           (match get t_atom pb with
            | Atom.Aapp (p', b) ->
              if eqb0 p p'
              then build_congr t_form t_atom eqs a b (Cons ((Lit.nlit xPA),
                     (Cons ((Lit.lit xPB), Nil))))
              else C._true
            | _ -> C._true)
         | _ -> C._true)
      | _ -> C._true)
   | _ -> C._true)

type 'c pol =
| Pc of 'c
| Pinj of positive * 'c pol
| PX of 'c pol * positive * 'c pol

(** val p0 : 'a1 -> 'a1 pol **)

let p0 cO =
  Pc cO

(** val p1 : 'a1 -> 'a1 pol **)

let p1 cI =
  Pc cI

(** val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool **)

let rec peq ceqb p p' =
  match p with
  | Pc c ->
    (match p' with
     | Pc c' -> ceqb c c'
     | _ -> false)
  | Pinj (j, q) ->
    (match p' with
     | Pinj (j', q') ->
       (match Coq_Pos.compare j j' with
        | ExtrNative.Eq -> peq ceqb q q'
        | _ -> false)
     | _ -> false)
  | PX (p2, i, q) ->
    (match p' with
     | PX (p'0, i', q') ->
       (match Coq_Pos.compare i i' with
        | ExtrNative.Eq -> if peq ceqb p2 p'0 then peq ceqb q q' else false
        | _ -> false)
     | _ -> false)

(** val mkPinj : positive -> 'a1 pol -> 'a1 pol **)

let mkPinj j p = match p with
| Pc c -> p
| Pinj (j', q) -> Pinj ((Coq_Pos.add j j'), q)
| PX (p2, p3, p4) -> Pinj (j, p)

(** val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol **)

let mkPinj_pred j p =
  match j with
  | XI j0 -> Pinj ((XO j0), p)
  | XO j0 -> Pinj ((Coq_Pos.pred_double j0), p)
  | XH -> p

(** val mkPX :
    'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let mkPX cO ceqb p i q =
  match p with
  | Pc c -> if ceqb c cO then mkPinj XH q else PX (p, i, q)
  | Pinj (p2, p3) -> PX (p, i, q)
  | PX (p', i', q') ->
    if peq ceqb q' (p0 cO)
    then PX (p', (Coq_Pos.add i' i), q)
    else PX (p, i, q)

(** val mkXi : 'a1 -> 'a1 -> positive -> 'a1 pol **)

let mkXi cO cI i =
  PX ((p1 cI), i, (p0 cO))

(** val mkX : 'a1 -> 'a1 -> 'a1 pol **)

let mkX cO cI =
  mkXi cO cI XH

(** val popp : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol **)

let rec popp copp = function
| Pc c -> Pc (copp c)
| Pinj (j, q) -> Pinj (j, (popp copp q))
| PX (p2, i, q) -> PX ((popp copp p2), i, (popp copp q))

(** val paddC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol **)

let rec paddC cadd p c =
  match p with
  | Pc c1 -> Pc (cadd c1 c)
  | Pinj (j, q) -> Pinj (j, (paddC cadd q c))
  | PX (p2, i, q) -> PX (p2, i, (paddC cadd q c))

(** val psubC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol **)

let rec psubC csub p c =
  match p with
  | Pc c1 -> Pc (csub c1 c)
  | Pinj (j, q) -> Pinj (j, (psubC csub q c))
  | PX (p2, i, q) -> PX (p2, i, (psubC csub q c))

(** val paddI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol ->
    positive -> 'a1 pol -> 'a1 pol **)

let rec paddI cadd pop q j = function
| Pc c -> mkPinj j (paddC cadd q c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pop q' q)
   | Zpos k -> mkPinj j (pop (Pinj (k, q')) q)
   | Zneg k -> mkPinj j' (paddI cadd pop q k q'))
| PX (p2, i, q') ->
  (match j with
   | XI j0 -> PX (p2, i, (paddI cadd pop q (XO j0) q'))
   | XO j0 -> PX (p2, i, (paddI cadd pop q (Coq_Pos.pred_double j0) q'))
   | XH -> PX (p2, i, (pop q' q)))

(** val psubI :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) ->
    'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec psubI cadd copp pop q j = function
| Pc c -> mkPinj j (paddC cadd (popp copp q) c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pop q' q)
   | Zpos k -> mkPinj j (pop (Pinj (k, q')) q)
   | Zneg k -> mkPinj j' (psubI cadd copp pop q k q'))
| PX (p2, i, q') ->
  (match j with
   | XI j0 -> PX (p2, i, (psubI cadd copp pop q (XO j0) q'))
   | XO j0 -> PX (p2, i, (psubI cadd copp pop q (Coq_Pos.pred_double j0) q'))
   | XH -> PX (p2, i, (pop q' q)))

(** val paddX :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol
    -> positive -> 'a1 pol -> 'a1 pol **)

let rec paddX cO ceqb pop p' i' p = match p with
| Pc c -> PX (p', i', p)
| Pinj (j, q') ->
  (match j with
   | XI j0 -> PX (p', i', (Pinj ((XO j0), q')))
   | XO j0 -> PX (p', i', (Pinj ((Coq_Pos.pred_double j0), q')))
   | XH -> PX (p', i', q'))
| PX (p2, i, q') ->
  (match Z.pos_sub i i' with
   | Z0 -> mkPX cO ceqb (pop p2 p') i q'
   | Zpos k -> mkPX cO ceqb (pop (PX (p2, k, (p0 cO))) p') i' q'
   | Zneg k -> mkPX cO ceqb (paddX cO ceqb pop p' k p2) i q')

(** val psubX :
    'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
    pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec psubX cO copp ceqb pop p' i' p = match p with
| Pc c -> PX ((popp copp p'), i', p)
| Pinj (j, q') ->
  (match j with
   | XI j0 -> PX ((popp copp p'), i', (Pinj ((XO j0), q')))
   | XO j0 -> PX ((popp copp p'), i', (Pinj ((Coq_Pos.pred_double j0), q')))
   | XH -> PX ((popp copp p'), i', q'))
| PX (p2, i, q') ->
  (match Z.pos_sub i i' with
   | Z0 -> mkPX cO ceqb (pop p2 p') i q'
   | Zpos k -> mkPX cO ceqb (pop (PX (p2, k, (p0 cO))) p') i' q'
   | Zneg k -> mkPX cO ceqb (psubX cO copp ceqb pop p' k p2) i q')

(** val padd :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let rec padd cO cadd ceqb p = function
| Pc c' -> paddC cadd p c'
| Pinj (j', q') -> paddI cadd (padd cO cadd ceqb) q' j' p
| PX (p'0, i', q') ->
  (match p with
   | Pc c -> PX (p'0, i', (paddC cadd q' c))
   | Pinj (j, q) ->
     (match j with
      | XI j0 -> PX (p'0, i', (padd cO cadd ceqb (Pinj ((XO j0), q)) q'))
      | XO j0 ->
        PX (p'0, i',
          (padd cO cadd ceqb (Pinj ((Coq_Pos.pred_double j0), q)) q'))
      | XH -> PX (p'0, i', (padd cO cadd ceqb q q')))
   | PX (p2, i, q) ->
     (match Z.pos_sub i i' with
      | Z0 ->
        mkPX cO ceqb (padd cO cadd ceqb p2 p'0) i (padd cO cadd ceqb q q')
      | Zpos k ->
        mkPX cO ceqb (padd cO cadd ceqb (PX (p2, k, (p0 cO))) p'0) i'
          (padd cO cadd ceqb q q')
      | Zneg k ->
        mkPX cO ceqb (paddX cO ceqb (padd cO cadd ceqb) p'0 k p2) i
          (padd cO cadd ceqb q q')))

(** val psub :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let rec psub cO cadd csub copp ceqb p = function
| Pc c' -> psubC csub p c'
| Pinj (j', q') -> psubI cadd copp (psub cO cadd csub copp ceqb) q' j' p
| PX (p'0, i', q') ->
  (match p with
   | Pc c -> PX ((popp copp p'0), i', (paddC cadd (popp copp q') c))
   | Pinj (j, q) ->
     (match j with
      | XI j0 ->
        PX ((popp copp p'0), i',
          (psub cO cadd csub copp ceqb (Pinj ((XO j0), q)) q'))
      | XO j0 ->
        PX ((popp copp p'0), i',
          (psub cO cadd csub copp ceqb (Pinj ((Coq_Pos.pred_double j0), q))
            q'))
      | XH -> PX ((popp copp p'0), i', (psub cO cadd csub copp ceqb q q')))
   | PX (p2, i, q) ->
     (match Z.pos_sub i i' with
      | Z0 ->
        mkPX cO ceqb (psub cO cadd csub copp ceqb p2 p'0) i
          (psub cO cadd csub copp ceqb q q')
      | Zpos k ->
        mkPX cO ceqb (psub cO cadd csub copp ceqb (PX (p2, k, (p0 cO))) p'0)
          i' (psub cO cadd csub copp ceqb q q')
      | Zneg k ->
        mkPX cO ceqb
          (psubX cO copp ceqb (psub cO cadd csub copp ceqb) p'0 k p2) i
          (psub cO cadd csub copp ceqb q q')))

(** val pmulC_aux :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 ->
    'a1 pol **)

let rec pmulC_aux cO cmul ceqb p c =
  match p with
  | Pc c' -> Pc (cmul c' c)
  | Pinj (j, q) -> mkPinj j (pmulC_aux cO cmul ceqb q c)
  | PX (p2, i, q) ->
    mkPX cO ceqb (pmulC_aux cO cmul ceqb p2 c) i (pmulC_aux cO cmul ceqb q c)

(** val pmulC :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol ->
    'a1 -> 'a1 pol **)

let pmulC cO cI cmul ceqb p c =
  if ceqb c cO
  then p0 cO
  else if ceqb c cI then p else pmulC_aux cO cmul ceqb p c

(** val pmulI :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol ->
    'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol **)

let rec pmulI cO cI cmul ceqb pmul0 q j = function
| Pc c -> mkPinj j (pmulC cO cI cmul ceqb q c)
| Pinj (j', q') ->
  (match Z.pos_sub j' j with
   | Z0 -> mkPinj j (pmul0 q' q)
   | Zpos k -> mkPinj j (pmul0 (Pinj (k, q')) q)
   | Zneg k -> mkPinj j' (pmulI cO cI cmul ceqb pmul0 q k q'))
| PX (p', i', q') ->
  (match j with
   | XI j' ->
     mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q j p') i'
       (pmulI cO cI cmul ceqb pmul0 q (XO j') q')
   | XO j' ->
     mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q j p') i'
       (pmulI cO cI cmul ceqb pmul0 q (Coq_Pos.pred_double j') q')
   | XH -> mkPX cO ceqb (pmulI cO cI cmul ceqb pmul0 q XH p') i' (pmul0 q' q))

(** val pmul :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let rec pmul cO cI cadd cmul ceqb p p'' = match p'' with
| Pc c -> pmulC cO cI cmul ceqb p c
| Pinj (j', q') -> pmulI cO cI cmul ceqb (pmul cO cI cadd cmul ceqb) q' j' p
| PX (p', i', q') ->
  (match p with
   | Pc c -> pmulC cO cI cmul ceqb p'' c
   | Pinj (j, q) ->
     let qQ' =
       match j with
       | XI j0 -> pmul cO cI cadd cmul ceqb (Pinj ((XO j0), q)) q'
       | XO j0 ->
         pmul cO cI cadd cmul ceqb (Pinj ((Coq_Pos.pred_double j0), q)) q'
       | XH -> pmul cO cI cadd cmul ceqb q q'
     in
     mkPX cO ceqb (pmul cO cI cadd cmul ceqb p p') i' qQ'
   | PX (p2, i, q) ->
     let qQ' = pmul cO cI cadd cmul ceqb q q' in
     let pQ' = pmulI cO cI cmul ceqb (pmul cO cI cadd cmul ceqb) q' XH p2 in
     let qP' = pmul cO cI cadd cmul ceqb (mkPinj XH q) p' in
     let pP' = pmul cO cI cadd cmul ceqb p2 p' in
     padd cO cadd ceqb
       (mkPX cO ceqb (padd cO cadd ceqb (mkPX cO ceqb pP' i (p0 cO)) qP') i'
         (p0 cO)) (mkPX cO ceqb pQ' i qQ'))

(** val psquare :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 pol -> 'a1 pol **)

let rec psquare cO cI cadd cmul ceqb = function
| Pc c -> Pc (cmul c c)
| Pinj (j, q) -> Pinj (j, (psquare cO cI cadd cmul ceqb q))
| PX (p2, i, q) ->
  let twoPQ =
    pmul cO cI cadd cmul ceqb p2
      (mkPinj XH (pmulC cO cI cmul ceqb q (cadd cI cI)))
  in
  let q2 = psquare cO cI cadd cmul ceqb q in
  let p3 = psquare cO cI cadd cmul ceqb p2 in
  mkPX cO ceqb (padd cO cadd ceqb (mkPX cO ceqb p3 i (p0 cO)) twoPQ) i q2

type 'c pExpr =
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

(** val mk_X : 'a1 -> 'a1 -> positive -> 'a1 pol **)

let mk_X cO cI j =
  mkPinj_pred j (mkX cO cI)

(** val ppow_pos :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol -> positive -> 'a1
    pol **)

let rec ppow_pos cO cI cadd cmul ceqb subst_l res p = function
| XI p3 ->
  subst_l
    (pmul cO cI cadd cmul ceqb
      (ppow_pos cO cI cadd cmul ceqb subst_l
        (ppow_pos cO cI cadd cmul ceqb subst_l res p p3) p p3) p)
| XO p3 ->
  ppow_pos cO cI cadd cmul ceqb subst_l
    (ppow_pos cO cI cadd cmul ceqb subst_l res p p3) p p3
| XH -> subst_l (pmul cO cI cadd cmul ceqb res p)

(** val ppow_N :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1 pol **)

let ppow_N cO cI cadd cmul ceqb subst_l p = function
| N0 -> p1 cI
| Npos p2 -> ppow_pos cO cI cadd cmul ceqb subst_l (p1 cI) p p2

(** val norm_aux :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol **)

let rec norm_aux cO cI cadd cmul csub copp ceqb = function
| PEc c -> Pc c
| PEX j -> mk_X cO cI j
| PEadd (pe1, pe2) ->
  (match pe1 with
   | PEopp pe3 ->
     psub cO cadd csub copp ceqb
       (norm_aux cO cI cadd cmul csub copp ceqb pe2)
       (norm_aux cO cI cadd cmul csub copp ceqb pe3)
   | _ ->
     (match pe2 with
      | PEopp pe3 ->
        psub cO cadd csub copp ceqb
          (norm_aux cO cI cadd cmul csub copp ceqb pe1)
          (norm_aux cO cI cadd cmul csub copp ceqb pe3)
      | _ ->
        padd cO cadd ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
          (norm_aux cO cI cadd cmul csub copp ceqb pe2)))
| PEsub (pe1, pe2) ->
  psub cO cadd csub copp ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
    (norm_aux cO cI cadd cmul csub copp ceqb pe2)
| PEmul (pe1, pe2) ->
  pmul cO cI cadd cmul ceqb (norm_aux cO cI cadd cmul csub copp ceqb pe1)
    (norm_aux cO cI cadd cmul csub copp ceqb pe2)
| PEopp pe1 -> popp copp (norm_aux cO cI cadd cmul csub copp ceqb pe1)
| PEpow (pe1, n0) ->
  ppow_N cO cI cadd cmul ceqb (fun p -> p)
    (norm_aux cO cI cadd cmul csub copp ceqb pe1) n0

type 'a bFormula =
| TT
| FF
| X
| A of 'a
| Cj of 'a bFormula * 'a bFormula
| D of 'a bFormula * 'a bFormula
| N of 'a bFormula
| I of 'a bFormula * 'a bFormula

type 'term' clause = 'term' list

type 'term' cnf = 'term' clause list

(** val tt : 'a1 cnf **)

let tt =
  Nil

(** val ff : 'a1 cnf **)

let ff =
  Cons (Nil, Nil)

(** val add_term :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 -> 'a1 clause -> 'a1
    clause option **)

let rec add_term unsat deduce t0 = function
| Nil ->
  (match deduce t0 t0 with
   | Some u -> if unsat u then None else Some (Cons (t0, Nil))
   | None -> Some (Cons (t0, Nil)))
| Cons (t', cl0) ->
  (match deduce t0 t' with
   | Some u ->
     if unsat u
     then None
     else (match add_term unsat deduce t0 cl0 with
           | Some cl' -> Some (Cons (t', cl'))
           | None -> None)
   | None ->
     (match add_term unsat deduce t0 cl0 with
      | Some cl' -> Some (Cons (t', cl'))
      | None -> None))

(** val or_clause :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 clause
    -> 'a1 clause option **)

let rec or_clause unsat deduce cl1 cl2 =
  match cl1 with
  | Nil -> Some cl2
  | Cons (t0, cl) ->
    (match add_term unsat deduce t0 cl2 with
     | Some cl' -> or_clause unsat deduce cl cl'
     | None -> None)

(** val or_clause_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 cnf ->
    'a1 cnf **)

let or_clause_cnf unsat deduce t0 f =
  fold_right (fun e acc ->
    match or_clause unsat deduce t0 e with
    | Some cl -> Cons (cl, acc)
    | None -> acc) Nil f

(** val or_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 cnf -> 'a1 cnf -> 'a1
    cnf **)

let rec or_cnf unsat deduce f f' =
  match f with
  | Nil -> tt
  | Cons (e, rst) ->
    app (or_cnf unsat deduce rst f') (or_clause_cnf unsat deduce e f')

(** val and_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf **)

let and_cnf f1 f2 =
  app f1 f2

(** val xcnf :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1
    -> 'a2 cnf) -> bool -> 'a1 bFormula -> 'a2 cnf **)

let rec xcnf unsat deduce normalise0 negate0 pol0 = function
| TT -> if pol0 then tt else ff
| FF -> if pol0 then ff else tt
| X -> ff
| A x -> if pol0 then normalise0 x else negate0 x
| Cj (e1, e2) ->
  if pol0
  then and_cnf (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
  else or_cnf unsat deduce (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
| D (e1, e2) ->
  if pol0
  then or_cnf unsat deduce (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
  else and_cnf (xcnf unsat deduce normalise0 negate0 pol0 e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
| N e -> xcnf unsat deduce normalise0 negate0 (negb pol0) e
| I (e1, e2) ->
  if pol0
  then or_cnf unsat deduce
         (xcnf unsat deduce normalise0 negate0 (negb pol0) e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)
  else and_cnf (xcnf unsat deduce normalise0 negate0 (negb pol0) e1)
         (xcnf unsat deduce normalise0 negate0 pol0 e2)

(** val cnf_checker :
    ('a1 list -> 'a2 -> bool) -> 'a1 cnf -> 'a2 list -> bool **)

let rec cnf_checker checker0 f l =
  match f with
  | Nil -> true
  | Cons (e, f0) ->
    (match l with
     | Nil -> false
     | Cons (c, l0) ->
       if checker0 e c then cnf_checker checker0 f0 l0 else false)

(** val tauto_checker :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1
    -> 'a2 cnf) -> ('a2 list -> 'a3 -> bool) -> 'a1 bFormula -> 'a3 list ->
    bool **)

let tauto_checker unsat deduce normalise0 negate0 checker0 f w =
  cnf_checker checker0 (xcnf unsat deduce normalise0 negate0 true f) w

(** val cneqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let cneqb ceqb x y =
  negb (ceqb x y)

(** val cltb :
    ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool **)

let cltb ceqb cleb x y =
  if cleb x y then cneqb ceqb x y else false

type 'c polC = 'c pol

type op1 =
| Equal
| NonEqual
| Strict
| NonStrict

type 'c nFormula = 'c polC*op1

(** val opMult : op1 -> op1 -> op1 option **)

let opMult o o' =
  match o with
  | Equal -> Some Equal
  | NonEqual ->
    (match o' with
     | Strict -> None
     | NonStrict -> None
     | x -> Some x)
  | Strict ->
    (match o' with
     | NonEqual -> None
     | _ -> Some o')
  | NonStrict ->
    (match o' with
     | NonEqual -> None
     | Strict -> Some NonStrict
     | x -> Some x)

(** val opAdd : op1 -> op1 -> op1 option **)

let opAdd o o' =
  match o with
  | Equal -> Some o'
  | NonEqual ->
    (match o' with
     | Equal -> Some NonEqual
     | _ -> None)
  | Strict ->
    (match o' with
     | NonEqual -> None
     | _ -> Some Strict)
  | NonStrict ->
    (match o' with
     | Equal -> Some NonStrict
     | NonEqual -> None
     | x -> Some x)

type 'c psatz =
| PsatzIn of nat
| PsatzSquare of 'c polC
| PsatzMulC of 'c polC * 'c psatz
| PsatzMulE of 'c psatz * 'c psatz
| PsatzAdd of 'c psatz * 'c psatz
| PsatzC of 'c
| PsatzZ

(** val map_option : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option **)

let map_option f = function
| Some x -> f x
| None -> None

(** val map_option2 :
    ('a1 -> 'a2 -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option **)

let map_option2 f o o' =
  match o with
  | Some x ->
    (match o' with
     | Some x' -> f x x'
     | None -> None)
  | None -> None

(** val pexpr_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula option **)

let pexpr_times_nformula cO cI cplus ctimes ceqb e = function
| ef,o ->
  (match o with
   | Equal -> Some ((pmul cO cI cplus ctimes ceqb e ef),Equal)
   | _ -> None)

(** val nformula_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option **)

let nformula_times_nformula cO cI cplus ctimes ceqb f1 f2 =
  let e1,o1 = f1 in
  let e2,o2 = f2 in
  map_option (fun x -> Some ((pmul cO cI cplus ctimes ceqb e1 e2),x))
    (opMult o1 o2)

(** val nformula_plus_nformula :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1
    nFormula -> 'a1 nFormula option **)

let nformula_plus_nformula cO cplus ceqb f1 f2 =
  let e1,o1 = f1 in
  let e2,o2 = f2 in
  map_option (fun x -> Some ((padd cO cplus ceqb e1 e2),x)) (opAdd o1 o2)

(** val eval_Psatz :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1
    nFormula option **)

let rec eval_Psatz cO cI cplus ctimes ceqb cleb l = function
| PsatzIn n0 -> Some (nth n0 l ((Pc cO),Equal))
| PsatzSquare e0 -> Some ((psquare cO cI cplus ctimes ceqb e0),NonStrict)
| PsatzMulC (re, e0) ->
  map_option (pexpr_times_nformula cO cI cplus ctimes ceqb re)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l e0)
| PsatzMulE (f1, f2) ->
  map_option2 (nformula_times_nformula cO cI cplus ctimes ceqb)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f1)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f2)
| PsatzAdd (f1, f2) ->
  map_option2 (nformula_plus_nformula cO cplus ceqb)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f1)
    (eval_Psatz cO cI cplus ctimes ceqb cleb l f2)
| PsatzC c -> if cltb ceqb cleb cO c then Some ((Pc c),Strict) else None
| PsatzZ -> Some ((Pc cO),Equal)

(** val check_inconsistent :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula ->
    bool **)

let check_inconsistent cO ceqb cleb = function
| e,op ->
  (match e with
   | Pc c ->
     (match op with
      | Equal -> cneqb ceqb c cO
      | NonEqual -> ceqb c cO
      | Strict -> cleb c cO
      | NonStrict -> cltb ceqb cleb c cO)
   | _ -> false)

type op2 =
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt

type 't formula = { flhs : 't pExpr; fop : op2; frhs : 't pExpr }

(** val norm :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol **)

let norm cO cI cplus ctimes cminus copp ceqb =
  norm_aux cO cI cplus ctimes cminus copp ceqb

(** val psub0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let psub0 cO cplus cminus copp ceqb =
  psub cO cplus cminus copp ceqb

(** val padd0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let padd0 cO cplus ceqb =
  padd cO cplus ceqb

type zWitness = z psatz

(** val psub1 : z pol -> z pol -> z pol **)

let psub1 =
  psub0 Z0 Z.add Z.sub Z.opp zeq_bool

(** val padd1 : z pol -> z pol -> z pol **)

let padd1 =
  padd0 Z0 Z.add zeq_bool

(** val norm0 : z pExpr -> z pol **)

let norm0 =
  norm Z0 (Zpos XH) Z.add Z.mul Z.sub Z.opp zeq_bool

(** val xnormalise : z formula -> z nFormula list **)

let xnormalise t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm0 lhs in
  let rhs0 = norm0 rhs in
  (match o with
   | OpEq ->
     Cons (((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict), (Cons
       (((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))),NonStrict), Nil)))
   | OpNEq -> Cons (((psub1 lhs0 rhs0),Equal), Nil)
   | OpLe -> Cons (((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict), Nil)
   | OpGe -> Cons (((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))),NonStrict), Nil)
   | OpLt -> Cons (((psub1 lhs0 rhs0),NonStrict), Nil)
   | OpGt -> Cons (((psub1 rhs0 lhs0),NonStrict), Nil))

(** val normalise : z formula -> z nFormula cnf **)

let normalise t0 =
  map (fun x -> Cons (x, Nil)) (xnormalise t0)

(** val xnegate : z formula -> z nFormula list **)

let xnegate t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = norm0 lhs in
  let rhs0 = norm0 rhs in
  (match o with
   | OpEq -> Cons (((psub1 lhs0 rhs0),Equal), Nil)
   | OpNEq ->
     Cons (((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict), (Cons
       (((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))),NonStrict), Nil)))
   | OpLe -> Cons (((psub1 rhs0 lhs0),NonStrict), Nil)
   | OpGe -> Cons (((psub1 lhs0 rhs0),NonStrict), Nil)
   | OpLt -> Cons (((psub1 rhs0 (padd1 lhs0 (Pc (Zpos XH)))),NonStrict), Nil)
   | OpGt -> Cons (((psub1 lhs0 (padd1 rhs0 (Pc (Zpos XH)))),NonStrict), Nil))

(** val negate : z formula -> z nFormula cnf **)

let negate t0 =
  map (fun x -> Cons (x, Nil)) (xnegate t0)

(** val zunsat : z nFormula -> bool **)

let zunsat =
  check_inconsistent Z0 zeq_bool Z.leb

(** val zdeduce : z nFormula -> z nFormula -> z nFormula option **)

let zdeduce =
  nformula_plus_nformula Z0 Z.add zeq_bool

(** val ceiling : z -> z -> z **)

let ceiling a b =
  let q,r = Z.div_eucl a b in
  (match r with
   | Z0 -> q
   | _ -> Z.add q (Zpos XH))

type zArithProof =
| DoneProof
| RatProof of zWitness * zArithProof
| CutProof of zWitness * zArithProof
| EnumProof of zWitness * zWitness * zArithProof list

(** val zgcdM : z -> z -> z **)

let zgcdM x y =
  Z.max (Z.gcd x y) (Zpos XH)

(** val zgcd_pol : z polC -> z*z **)

let rec zgcd_pol = function
| Pc c -> Z0,c
| Pinj (p2, p3) -> zgcd_pol p3
| PX (p2, p3, q) ->
  let g1,c1 = zgcd_pol p2 in
  let g2,c2 = zgcd_pol q in (zgcdM (zgcdM g1 c1) g2),c2

(** val zdiv_pol : z polC -> z -> z polC **)

let rec zdiv_pol p x =
  match p with
  | Pc c -> Pc (Z.div c x)
  | Pinj (j, p2) -> Pinj (j, (zdiv_pol p2 x))
  | PX (p2, j, q) -> PX ((zdiv_pol p2 x), j, (zdiv_pol q x))

(** val makeCuttingPlane : z polC -> z polC*z **)

let makeCuttingPlane p =
  let g,c = zgcd_pol p in
  if Z.gtb g Z0
  then (zdiv_pol (psubC Z.sub p c) g),(Z.opp (ceiling (Z.opp c) g))
  else p,Z0

(** val genCuttingPlane : z nFormula -> ((z polC*z)*op1) option **)

let genCuttingPlane = function
| e,op ->
  (match op with
   | Equal ->
     let g,c = zgcd_pol e in
     if if Z.gtb g Z0
        then if negb (zeq_bool c Z0)
             then negb (zeq_bool (Z.gcd g c) g)
             else false
        else false
     then None
     else Some ((makeCuttingPlane e),Equal)
   | NonEqual -> Some ((e,Z0),op)
   | Strict -> Some ((makeCuttingPlane (psubC Z.sub e (Zpos XH))),NonStrict)
   | NonStrict -> Some ((makeCuttingPlane e),NonStrict))

(** val nformula_of_cutting_plane : ((z polC*z)*op1) -> z nFormula **)

let nformula_of_cutting_plane = function
| e_z,o -> let e,z0 = e_z in (padd1 e (Pc z0)),o

(** val is_pol_Z0 : z polC -> bool **)

let is_pol_Z0 = function
| Pc z0 ->
  (match z0 with
   | Z0 -> true
   | _ -> false)
| _ -> false

(** val eval_Psatz0 : z nFormula list -> zWitness -> z nFormula option **)

let eval_Psatz0 =
  eval_Psatz Z0 (Zpos XH) Z.add Z.mul zeq_bool Z.leb

(** val valid_cut_sign : op1 -> bool **)

let valid_cut_sign = function
| Equal -> true
| NonStrict -> true
| _ -> false

(** val zChecker : z nFormula list -> zArithProof -> bool **)

let rec zChecker l = function
| DoneProof -> false
| RatProof (w, pf0) ->
  (match eval_Psatz0 l w with
   | Some f -> if zunsat f then true else zChecker (Cons (f, l)) pf0
   | None -> false)
| CutProof (w, pf0) ->
  (match eval_Psatz0 l w with
   | Some f ->
     (match genCuttingPlane f with
      | Some cp -> zChecker (Cons ((nformula_of_cutting_plane cp), l)) pf0
      | None -> true)
   | None -> false)
| EnumProof (w1, w2, pf0) ->
  (match eval_Psatz0 l w1 with
   | Some f1 ->
     (match eval_Psatz0 l w2 with
      | Some f2 ->
        (match genCuttingPlane f1 with
         | Some p ->
           let p2,op3 = p in
           let e1,z1 = p2 in
           (match genCuttingPlane f2 with
            | Some p3 ->
              let p4,op4 = p3 in
              let e2,z2 = p4 in
              if if if valid_cut_sign op3 then valid_cut_sign op4 else false
                 then is_pol_Z0 (padd1 e1 e2)
                 else false
              then let rec label pfs lb ub =
                     match pfs with
                     | Nil -> Z.gtb lb ub
                     | Cons (pf1, rsr) ->
                       if zChecker (Cons (((psub1 e1 (Pc lb)),Equal), l)) pf1
                       then label rsr (Z.add lb (Zpos XH)) ub
                       else false
                   in label pf0 (Z.opp z1) z2
              else false
            | None -> true)
         | None -> true)
      | None -> false)
   | None -> false)

(** val zTautoChecker : z formula bFormula -> zArithProof list -> bool **)

let zTautoChecker f w =
  tauto_checker zunsat zdeduce normalise negate zChecker f w

(** val build_positive_atom_aux :
    (int -> positive option) -> Atom.atom -> positive option **)

let build_positive_atom_aux build_positive0 = function
| Atom.Acop c ->
  (match c with
   | Atom.CO_xH -> Some XH
   | Atom.CO_Z0 -> None)
| Atom.Auop (u, a0) ->
  (match u with
   | Atom.UO_xO -> option_map (fun x -> XO x) (build_positive0 a0)
   | Atom.UO_xI -> option_map (fun x -> XI x) (build_positive0 a0)
   | _ -> None)
| _ -> None

(** val build_positive : Atom.atom array -> int -> positive option **)

let build_positive t_atom =
  foldi_down_cont (fun i cont h ->
    build_positive_atom_aux cont (get t_atom h)) (length t_atom)
    (ExtrNative.of_uint(0)) (fun x -> None)

(** val build_z_atom_aux : Atom.atom array -> Atom.atom -> z option **)

let build_z_atom_aux t_atom = function
| Atom.Acop c ->
  (match c with
   | Atom.CO_xH -> None
   | Atom.CO_Z0 -> Some Z0)
| Atom.Auop (u, a0) ->
  (match u with
   | Atom.UO_Zpos -> option_map (fun x -> Zpos x) (build_positive t_atom a0)
   | Atom.UO_Zneg -> option_map (fun x -> Zneg x) (build_positive t_atom a0)
   | _ -> None)
| _ -> None

(** val build_z_atom : Atom.atom array -> Atom.atom -> z option **)

let build_z_atom t_atom =
  build_z_atom_aux t_atom

type vmap = positive*Atom.atom list

(** val find_var_aux :
    Atom.atom -> positive -> Atom.atom list -> positive option **)

let rec find_var_aux h p = function
| Nil -> None
| Cons (h', l0) ->
  let p2 = Coq_Pos.pred p in
  if Atom.eqb h h' then Some p2 else find_var_aux h p2 l0

(** val find_var : vmap -> Atom.atom -> vmap*positive **)

let find_var vm h =
  let count,map0 = vm in
  (match find_var_aux h count map0 with
   | Some p -> vm,p
   | None -> ((Coq_Pos.succ count),(Cons (h, map0))),count)

(** val empty_vmap : vmap **)

let empty_vmap =
  XH,Nil

(** val build_pexpr_atom_aux :
    Atom.atom array -> (vmap -> int -> vmap*z pExpr) -> vmap -> Atom.atom ->
    vmap*z pExpr **)

let build_pexpr_atom_aux t_atom build_pexpr0 vm h = match h with
| Atom.Auop (u, a) ->
  (match u with
   | Atom.UO_Zopp -> let vm0,pe = build_pexpr0 vm a in vm0,(PEopp pe)
   | _ ->
     (match build_z_atom t_atom h with
      | Some z0 -> vm,(PEc z0)
      | None -> let vm0,p = find_var vm h in vm0,(PEX p)))
| Atom.Abop (b, a1, a2) ->
  (match b with
   | Atom.BO_Zplus ->
     let vm0,pe1 = build_pexpr0 vm a1 in
     let vm1,pe2 = build_pexpr0 vm0 a2 in vm1,(PEadd (pe1, pe2))
   | Atom.BO_Zminus ->
     let vm0,pe1 = build_pexpr0 vm a1 in
     let vm1,pe2 = build_pexpr0 vm0 a2 in vm1,(PEsub (pe1, pe2))
   | Atom.BO_Zmult ->
     let vm0,pe1 = build_pexpr0 vm a1 in
     let vm1,pe2 = build_pexpr0 vm0 a2 in vm1,(PEmul (pe1, pe2))
   | _ ->
     (match build_z_atom t_atom h with
      | Some z0 -> vm,(PEc z0)
      | None -> let vm0,p = find_var vm h in vm0,(PEX p)))
| _ ->
  (match build_z_atom t_atom h with
   | Some z0 -> vm,(PEc z0)
   | None -> let vm0,p = find_var vm h in vm0,(PEX p))

(** val build_pexpr : Atom.atom array -> vmap -> int -> vmap*z pExpr **)

let build_pexpr t_atom =
  foldi_down_cont (fun i cont vm h ->
    build_pexpr_atom_aux t_atom cont vm (get t_atom h)) (length t_atom)
    (ExtrNative.of_uint(0)) (fun vm x -> vm,(PEc Z0))

(** val build_op2 : Atom.binop -> op2 option **)

let build_op2 = function
| Atom.BO_Zlt -> Some OpLt
| Atom.BO_Zle -> Some OpLe
| Atom.BO_Zge -> Some OpGe
| Atom.BO_Zgt -> Some OpGt
| Atom.BO_eq t0 ->
  (match t0 with
   | Typ.TZ -> Some OpEq
   | _ -> None)
| _ -> None

(** val build_formula_atom :
    Atom.atom array -> vmap -> Atom.atom -> (vmap*z formula) option **)

let build_formula_atom t_atom vm = function
| Atom.Abop (op, a1, a2) ->
  (match build_op2 op with
   | Some o ->
     let vm0,pe1 = build_pexpr t_atom vm a1 in
     let vm1,pe2 = build_pexpr t_atom vm0 a2 in
     Some (vm1,{ flhs = pe1; fop = o; frhs = pe2 })
   | None -> None)
| _ -> None

(** val build_formula :
    Atom.atom array -> vmap -> int -> (vmap*z formula) option **)

let build_formula t_atom vm h =
  build_formula_atom t_atom vm (get t_atom h)

(** val build_not2 : int -> z formula bFormula -> z formula bFormula **)

let build_not2 i f =
  fold (fun f' -> N (N f')) (ExtrNative.of_uint(1)) i f

(** val build_hform :
    Atom.atom array -> (vmap -> int -> (vmap*z formula bFormula) option) ->
    vmap -> Form.form -> (vmap*z formula bFormula) option **)

let build_hform t_atom build_var0 vm = function
| Form.Fatom h ->
  (match build_formula t_atom vm h with
   | Some p -> let vm0,f0 = p in Some (vm0,(A f0))
   | None -> None)
| Form.Ftrue -> Some (vm,TT)
| Form.Ffalse -> Some (vm,FF)
| Form.Fnot2 (i, l) ->
  (match build_var0 vm (Lit.blit l) with
   | Some p ->
     let vm0,f0 = p in
     let f' = build_not2 i f0 in
     let f'' = if Lit.is_pos l then f' else N f' in Some (vm0,f'')
   | None -> None)
| Form.Fand args ->
  let n0 = length args in
  if eqb0 n0 (ExtrNative.of_uint(0))
  then Some (vm,TT)
  else foldi (fun i f1 ->
         match f1 with
         | Some y ->
           let vm',f1' = y in
           let l = get args i in
           (match build_var0 vm' (Lit.blit l) with
            | Some p ->
              let vm2,f2 = p in
              let f2' = if Lit.is_pos l then f2 else N f2 in
              Some (vm2,(Cj (f1', f2')))
            | None -> None)
         | None -> None) (ExtrNative.of_uint(1))
         (sub0 n0 (ExtrNative.of_uint(1)))
         (let l = get args (ExtrNative.of_uint(0)) in
          match build_var0 vm (Lit.blit l) with
          | Some p ->
            let vm',f0 = p in
            if Lit.is_pos l then Some (vm',f0) else Some (vm',(N f0))
          | None -> None)
| Form.For args ->
  let n0 = length args in
  if eqb0 n0 (ExtrNative.of_uint(0))
  then Some (vm,FF)
  else foldi (fun i f1 ->
         match f1 with
         | Some y ->
           let vm',f1' = y in
           let l = get args i in
           (match build_var0 vm' (Lit.blit l) with
            | Some p ->
              let vm2,f2 = p in
              let f2' = if Lit.is_pos l then f2 else N f2 in
              Some (vm2,(D (f1', f2')))
            | None -> None)
         | None -> None) (ExtrNative.of_uint(1))
         (sub0 n0 (ExtrNative.of_uint(1)))
         (let l = get args (ExtrNative.of_uint(0)) in
          match build_var0 vm (Lit.blit l) with
          | Some p ->
            let vm',f0 = p in
            if Lit.is_pos l then Some (vm',f0) else Some (vm',(N f0))
          | None -> None)
| Form.Fimp args ->
  let n0 = length args in
  if eqb0 n0 (ExtrNative.of_uint(0))
  then Some (vm,TT)
  else if leb0 n0 (ExtrNative.of_uint(1))
       then let l = get args (ExtrNative.of_uint(0)) in
            (match build_var0 vm (Lit.blit l) with
             | Some p ->
               let vm',f0 = p in
               if Lit.is_pos l then Some (vm',f0) else Some (vm',(N f0))
             | None -> None)
       else foldi_down (fun i f1 ->
              match f1 with
              | Some y ->
                let vm',f1' = y in
                let l = get args i in
                (match build_var0 vm' (Lit.blit l) with
                 | Some p ->
                   let vm2,f2 = p in
                   let f2' = if Lit.is_pos l then f2 else N f2 in
                   Some (vm2,(I (f2', f1')))
                 | None -> None)
              | None -> None) (sub0 n0 (ExtrNative.of_uint(2)))
              (ExtrNative.of_uint(0))
              (let l = get args (sub0 n0 (ExtrNative.of_uint(1))) in
               match build_var0 vm (Lit.blit l) with
               | Some p ->
                 let vm',f0 = p in
                 if Lit.is_pos l then Some (vm',f0) else Some (vm',(N f0))
               | None -> None)
| Form.Fxor (a, b) ->
  (match build_var0 vm (Lit.blit a) with
   | Some p ->
     let vm1,f1 = p in
     (match build_var0 vm1 (Lit.blit b) with
      | Some p2 ->
        let vm2,f2 = p2 in
        let f1' = if Lit.is_pos a then f1 else N f1 in
        let f2' = if Lit.is_pos b then f2 else N f2 in
        Some (vm2,(Cj ((D (f1', f2')), (D ((N f1'), (N f2'))))))
      | None -> None)
   | None -> None)
| Form.Fiff (a, b) ->
  (match build_var0 vm (Lit.blit a) with
   | Some p ->
     let vm1,f1 = p in
     (match build_var0 vm1 (Lit.blit b) with
      | Some p2 ->
        let vm2,f2 = p2 in
        let f1' = if Lit.is_pos a then f1 else N f1 in
        let f2' = if Lit.is_pos b then f2 else N f2 in
        Some (vm2,(Cj ((D (f1', (N f2'))), (D ((N f1'), f2')))))
      | None -> None)
   | None -> None)
| Form.Fite (a, b, c) ->
  (match build_var0 vm (Lit.blit a) with
   | Some p ->
     let vm1,f1 = p in
     (match build_var0 vm1 (Lit.blit b) with
      | Some p2 ->
        let vm2,f2 = p2 in
        (match build_var0 vm2 (Lit.blit c) with
         | Some p3 ->
           let vm3,f3 = p3 in
           let f1' = if Lit.is_pos a then f1 else N f1 in
           let f2' = if Lit.is_pos b then f2 else N f2 in
           let f3' = if Lit.is_pos c then f3 else N f3 in
           Some (vm3,(D ((Cj (f1', f2')), (Cj ((N f1'), f3')))))
         | None -> None)
      | None -> None)
   | None -> None)

(** val build_var :
    Form.form array -> Atom.atom array -> vmap -> int -> (vmap*z formula
    bFormula) option **)

let build_var t_form t_atom =
  foldi_down_cont (fun i cont vm h ->
    build_hform t_atom cont vm (get t_form h)) (length t_form)
    (ExtrNative.of_uint(0)) (fun x x0 -> None)

(** val build_form :
    Form.form array -> Atom.atom array -> vmap -> Form.form -> (vmap*z
    formula bFormula) option **)

let build_form t_form t_atom =
  build_hform t_atom (build_var t_form t_atom)

(** val build_nlit :
    Form.form array -> Atom.atom array -> vmap -> int -> (vmap*z formula
    bFormula) option **)

let build_nlit t_form t_atom vm l =
  let l0 = Lit.neg l in
  (match build_form t_form t_atom vm (get t_form (Lit.blit l0)) with
   | Some p ->
     let vm0,f = p in
     let f0 = if Lit.is_pos l0 then f else N f in Some (vm0,f0)
   | None -> None)

(** val build_clause_aux :
    Form.form array -> Atom.atom array -> vmap -> int list -> (vmap*z formula
    bFormula) option **)

let rec build_clause_aux t_form t_atom vm = function
| Nil -> None
| Cons (l, cl0) ->
  (match cl0 with
   | Nil -> build_nlit t_form t_atom vm l
   | Cons (i, l0) ->
     (match build_nlit t_form t_atom vm l with
      | Some p ->
        let vm0,bf1 = p in
        (match build_clause_aux t_form t_atom vm0 cl0 with
         | Some p2 -> let vm1,bf2 = p2 in Some (vm1,(Cj (bf1, bf2)))
         | None -> None)
      | None -> None))

(** val build_clause :
    Form.form array -> Atom.atom array -> vmap -> int list -> (vmap*z formula
    bFormula) option **)

let build_clause t_form t_atom vm cl =
  match build_clause_aux t_form t_atom vm cl with
  | Some p -> let vm0,bf = p in Some (vm0,(I (bf, FF)))
  | None -> None

(** val get_eq0 :
    Form.form array -> Atom.atom array -> int -> (int -> int -> C.t) -> C.t **)

let get_eq0 t_form t_atom l f =
  if Lit.is_pos l
  then (match get t_form (Lit.blit l) with
        | Form.Fatom xa ->
          (match get t_atom xa with
           | Atom.Abop (b0, a, b) ->
             (match b0 with
              | Atom.BO_eq t0 -> f a b
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val get_not_le :
    Form.form array -> Atom.atom array -> int -> (int -> int -> C.t) -> C.t **)

let get_not_le t_form t_atom l f =
  if negb (Lit.is_pos l)
  then (match get t_form (Lit.blit l) with
        | Form.Fatom xa ->
          (match get t_atom xa with
           | Atom.Abop (b0, a, b) ->
             (match b0 with
              | Atom.BO_Zle -> f a b
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val check_micromega :
    Form.form array -> Atom.atom array -> int list -> zArithProof list -> C.t **)

let check_micromega t_form t_atom cl c =
  match build_clause t_form t_atom empty_vmap cl with
  | Some p -> let v,bf = p in if zTautoChecker bf c then cl else C._true
  | None -> C._true

(** val check_diseq : Form.form array -> Atom.atom array -> int -> C.t **)

let check_diseq t_form t_atom l =
  match get t_form (Lit.blit l) with
  | Form.For a ->
    if eqb0 (length a) (ExtrNative.of_uint(3))
    then let a_eq_b = get a (ExtrNative.of_uint(0)) in
         let not_a_le_b = get a (ExtrNative.of_uint(1)) in
         let not_b_le_a = get a (ExtrNative.of_uint(2)) in
         get_eq0 t_form t_atom a_eq_b (fun a0 b ->
           get_not_le t_form t_atom not_a_le_b (fun a' b' ->
             get_not_le t_form t_atom not_b_le_a (fun b'' a'' ->
               if if if if eqb0 a0 a' then eqb0 a0 a'' else false
                     then eqb0 b b'
                     else false
                  then eqb0 b b''
                  else false
               then Cons ((Lit.lit (Lit.blit l)), Nil)
               else if if if if eqb0 a0 b' then eqb0 a0 b'' else false
                          then eqb0 b a'
                          else false
                       then eqb0 b a''
                       else false
                    then Cons ((Lit.lit (Lit.blit l)), Nil)
                    else C._true)))
    else C._true
  | _ -> C._true

(** val check_atom_aux :
    Atom.atom array -> (int -> int -> bool) -> Atom.atom -> Atom.atom -> bool **)

let check_atom_aux t_atom check_hatom0 a b =
  match a with
  | Atom.Acop o1 ->
    (match b with
     | Atom.Acop o2 -> Atom.cop_eqb o1 o2
     | _ -> false)
  | Atom.Auop (o1, a0) ->
    (match o1 with
     | Atom.UO_Zneg ->
       (match b with
        | Atom.Auop (o2, b0) ->
          (match o2 with
           | Atom.UO_Zopp ->
             (match get t_atom b0 with
              | Atom.Auop (u, q) ->
                (match u with
                 | Atom.UO_Zpos -> check_hatom0 a0 q
                 | _ -> false)
              | _ -> false)
           | _ -> if Atom.uop_eqb o1 o2 then check_hatom0 a0 b0 else false)
        | _ -> false)
     | Atom.UO_Zopp ->
       (match b with
        | Atom.Auop (o2, b0) ->
          (match o2 with
           | Atom.UO_Zneg ->
             (match get t_atom a0 with
              | Atom.Auop (u, p) ->
                (match u with
                 | Atom.UO_Zpos -> check_hatom0 p b0
                 | _ -> false)
              | _ -> false)
           | _ -> if Atom.uop_eqb o1 o2 then check_hatom0 a0 b0 else false)
        | _ -> false)
     | _ ->
       (match b with
        | Atom.Auop (o2, b0) ->
          if Atom.uop_eqb o1 o2 then check_hatom0 a0 b0 else false
        | _ -> false))
  | Atom.Abop (o1, a1, a2) ->
    (match b with
     | Atom.Abop (o2, b1, b2) ->
       (match o1 with
        | Atom.BO_Zplus ->
          (match o2 with
           | Atom.BO_Zplus ->
             if if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
             then true
             else if check_hatom0 a1 b2 then check_hatom0 a2 b1 else false
           | _ -> false)
        | Atom.BO_Zminus ->
          (match o2 with
           | Atom.BO_Zminus ->
             if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
           | _ -> false)
        | Atom.BO_Zmult ->
          (match o2 with
           | Atom.BO_Zmult ->
             if if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
             then true
             else if check_hatom0 a1 b2 then check_hatom0 a2 b1 else false
           | _ -> false)
        | Atom.BO_Zlt ->
          (match o2 with
           | Atom.BO_Zlt ->
             if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
           | Atom.BO_Zgt ->
             if check_hatom0 a1 b2 then check_hatom0 a2 b1 else false
           | _ -> false)
        | Atom.BO_Zle ->
          (match o2 with
           | Atom.BO_Zle ->
             if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
           | Atom.BO_Zge ->
             if check_hatom0 a1 b2 then check_hatom0 a2 b1 else false
           | _ -> false)
        | Atom.BO_Zge ->
          (match o2 with
           | Atom.BO_Zle ->
             if check_hatom0 a1 b2 then check_hatom0 a2 b1 else false
           | Atom.BO_Zge ->
             if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
           | _ -> false)
        | Atom.BO_Zgt ->
          (match o2 with
           | Atom.BO_Zlt ->
             if check_hatom0 a1 b2 then check_hatom0 a2 b1 else false
           | Atom.BO_Zgt ->
             if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
           | _ -> false)
        | Atom.BO_eq t1 ->
          (match o2 with
           | Atom.BO_eq t2 ->
             if Typ.eqb t1 t2
             then if if check_hatom0 a1 b1 then check_hatom0 a2 b2 else false
                  then true
                  else if check_hatom0 a1 b2
                       then check_hatom0 a2 b1
                       else false
             else false
           | _ -> false))
     | _ -> false)
  | Atom.Anop (o1, l1) ->
    (match b with
     | Atom.Anop (o2, l2) ->
       if Typ.eqb o1 o2 then list_beq check_hatom0 l1 l2 else false
     | _ -> false)
  | Atom.Aapp (f1, aargs) ->
    (match b with
     | Atom.Aapp (f2, bargs) ->
       if eqb0 f1 f2 then list_beq check_hatom0 aargs bargs else false
     | _ -> false)

(** val check_hatom : Atom.atom array -> int -> int -> bool **)

let check_hatom t_atom h1 h2 =
  foldi_down_cont (fun x cont h3 h4 ->
    if eqb0 h3 h4
    then true
    else check_atom_aux t_atom cont (get t_atom h3) (get t_atom h4))
    (length t_atom) (ExtrNative.of_uint(0)) (fun h3 h4 -> false) h1 h2

(** val check_neg_hatom : Atom.atom array -> int -> int -> bool **)

let check_neg_hatom t_atom h1 h2 =
  match get t_atom h1 with
  | Atom.Abop (op3, a1, a2) ->
    (match get t_atom h2 with
     | Atom.Abop (op4, b1, b2) ->
       (match op3 with
        | Atom.BO_Zlt ->
          (match op4 with
           | Atom.BO_Zle ->
             if check_hatom t_atom a1 b2
             then check_hatom t_atom a2 b1
             else false
           | Atom.BO_Zge ->
             if check_hatom t_atom a1 b1
             then check_hatom t_atom a2 b2
             else false
           | _ -> false)
        | Atom.BO_Zle ->
          (match op4 with
           | Atom.BO_Zlt ->
             if check_hatom t_atom a1 b2
             then check_hatom t_atom a2 b1
             else false
           | Atom.BO_Zgt ->
             if check_hatom t_atom a1 b1
             then check_hatom t_atom a2 b2
             else false
           | _ -> false)
        | Atom.BO_Zge ->
          (match op4 with
           | Atom.BO_Zlt ->
             if check_hatom t_atom a1 b1
             then check_hatom t_atom a2 b2
             else false
           | Atom.BO_Zgt ->
             if check_hatom t_atom a1 b2
             then check_hatom t_atom a2 b1
             else false
           | _ -> false)
        | Atom.BO_Zgt ->
          (match op4 with
           | Atom.BO_Zle ->
             if check_hatom t_atom a1 b1
             then check_hatom t_atom a2 b2
             else false
           | Atom.BO_Zge ->
             if check_hatom t_atom a1 b2
             then check_hatom t_atom a2 b1
             else false
           | _ -> false)
        | _ -> false)
     | _ -> false)
  | _ -> false

(** val remove_not : Form.form array -> int -> int **)

let remove_not t_form l =
  match get t_form (Lit.blit l) with
  | Form.Fnot2 (i, l') -> if Lit.is_pos l then l' else Lit.neg l'
  | _ -> l

(** val get_and : Form.form array -> int -> int array option **)

let get_and t_form l =
  let l0 = remove_not t_form l in
  if Lit.is_pos l0
  then (match get t_form (Lit.blit l0) with
        | Form.Fand args -> Some args
        | _ -> None)
  else None

(** val get_or : Form.form array -> int -> int array option **)

let get_or t_form l =
  let l0 = remove_not t_form l in
  if Lit.is_pos l0
  then (match get t_form (Lit.blit l0) with
        | Form.For args -> Some args
        | _ -> None)
  else None

(** val flatten_op_body :
    (int -> int array option) -> (int list -> int -> int list) -> int list ->
    int -> int list **)

let flatten_op_body get_op frec largs l =
  match get_op l with
  | Some a -> fold_left frec largs a
  | None -> Cons (l, largs)

(** val flatten_op_lit :
    (int -> int array option) -> int -> int list -> int -> int list **)

let flatten_op_lit get_op max0 =
  foldi_cont (fun x -> flatten_op_body get_op) (ExtrNative.of_uint(0)) max0
    (fun largs l -> Cons (l, largs))

(** val flatten_and : Form.form array -> int array -> int list **)

let flatten_and t_form t0 =
  fold_left (flatten_op_lit (get_and t_form) (length t_form)) Nil t0

(** val flatten_or : Form.form array -> int array -> int list **)

let flatten_or t_form t0 =
  fold_left (flatten_op_lit (get_or t_form) (length t_form)) Nil t0

(** val check_flatten_body :
    Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> (int
    -> int -> bool) -> int -> int -> bool **)

let check_flatten_body t_form check_atom0 check_neg_atom frec l lf =
  let l0 = remove_not t_form l in
  let lf0 = remove_not t_form lf in
  if eqb0 l0 lf0
  then true
  else if eqb0 (land0 (ExtrNative.of_uint(1)) (lxor0 l0 lf0))
            (ExtrNative.of_uint(0))
       then (match get t_form (Lit.blit l0) with
             | Form.Fatom a1 ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fatom a2 -> check_atom0 a1 a2
                | _ -> false)
             | Form.Ftrue ->
               (match get t_form (Lit.blit lf0) with
                | Form.Ftrue -> true
                | _ -> false)
             | Form.Ffalse ->
               (match get t_form (Lit.blit lf0) with
                | Form.Ffalse -> true
                | _ -> false)
             | Form.Fnot2 (i, i0) -> false
             | Form.Fand args1 ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fand args2 ->
                  let args3 = flatten_and t_form args1 in
                  let args4 = flatten_and t_form args2 in
                  forallb2 frec args3 args4
                | _ -> false)
             | Form.For args1 ->
               (match get t_form (Lit.blit lf0) with
                | Form.For args2 ->
                  let args3 = flatten_or t_form args1 in
                  let args4 = flatten_or t_form args2 in
                  forallb2 frec args3 args4
                | _ -> false)
             | Form.Fimp args1 ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fimp args2 ->
                  if eqb0 (length args1) (length args2)
                  then forallbi (fun i l1 -> frec l1 (get args2 i)) args1
                  else false
                | _ -> false)
             | Form.Fxor (l1, l2) ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fxor (lf1, lf2) ->
                  if frec l1 lf1 then frec l2 lf2 else false
                | _ -> false)
             | Form.Fiff (l1, l2) ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fiff (lf1, lf2) ->
                  if frec l1 lf1 then frec l2 lf2 else false
                | _ -> false)
             | Form.Fite (l1, l2, l3) ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fite (lf1, lf2, lf3) ->
                  if if frec l1 lf1 then frec l2 lf2 else false
                  then frec l3 lf3
                  else false
                | _ -> false))
       else (match get t_form (Lit.blit l0) with
             | Form.Fatom a1 ->
               (match get t_form (Lit.blit lf0) with
                | Form.Fatom a2 -> check_neg_atom a1 a2
                | _ -> false)
             | _ -> false)

(** val check_flatten_aux :
    Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> int ->
    int -> bool **)

let check_flatten_aux t_form check_atom0 check_neg_atom l lf =
  foldi_cont (fun x -> check_flatten_body t_form check_atom0 check_neg_atom)
    (ExtrNative.of_uint(0)) (length t_form) (fun x x0 -> false) l lf

(** val check_flatten :
    Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> S.t ->
    int -> int -> C.t **)

let check_flatten t_form check_atom0 check_neg_atom s cid lf =
  match S.get s cid with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       if check_flatten_aux t_form check_atom0 check_neg_atom l lf
       then Cons (lf, Nil)
       else C._true
     | Cons (i, l1) -> C._true)

(** val check_spl_arith :
    Form.form array -> Atom.atom array -> int list -> int -> zArithProof list
    -> C.t **)

let check_spl_arith t_form t_atom orig res l =
  match orig with
  | Nil -> C._true
  | Cons (li, l0) ->
    (match l0 with
     | Nil ->
       let cl = Cons ((Lit.neg li), (Cons (res, Nil))) in
       (match build_clause t_form t_atom empty_vmap cl with
        | Some p ->
          let v,bf = p in
          if zTautoChecker bf l then Cons (res, Nil) else C._true
        | None -> C._true)
     | Cons (y, l1) -> C._true)

(** val check_in : int -> int list -> bool **)

let rec check_in x = function
| Nil -> false
| Cons (t0, q) -> if eqb0 x t0 then true else check_in x q

(** val check_diseqs_complete_aux :
    int -> int list -> (int*int) option array -> bool **)

let rec check_diseqs_complete_aux a dist t0 =
  match dist with
  | Nil -> true
  | Cons (b, q) ->
    if existsb1 (fun x ->
         match x with
         | Some p ->
           let a',b' = p in
           if if eqb0 a a' then eqb0 b b' else false
           then true
           else if eqb0 a b' then eqb0 b a' else false
         | None -> false) t0
    then check_diseqs_complete_aux a q t0
    else false

(** val check_diseqs_complete :
    int list -> (int*int) option array -> bool **)

let rec check_diseqs_complete dist t0 =
  match dist with
  | Nil -> true
  | Cons (a, q) ->
    if check_diseqs_complete_aux a q t0
    then check_diseqs_complete q t0
    else false

(** val check_diseqs :
    Form.form array -> Atom.atom array -> Typ.coq_type -> int list -> int
    array -> bool **)

let check_diseqs t_form t_atom ty dist diseq =
  let t0 =
    mapi (fun x t0 ->
      if Lit.is_pos t0
      then None
      else (match get t_form (Lit.blit t0) with
            | Form.Fatom a ->
              (match get t_atom a with
               | Atom.Acop c -> None
               | Atom.Auop (u, i) -> None
               | Atom.Abop (b, h1, h2) ->
                 (match b with
                  | Atom.BO_Zplus -> None
                  | Atom.BO_Zminus -> None
                  | Atom.BO_Zmult -> None
                  | Atom.BO_Zlt -> None
                  | Atom.BO_Zle -> None
                  | Atom.BO_Zge -> None
                  | Atom.BO_Zgt -> None
                  | Atom.BO_eq a0 ->
                    if if if if Typ.eqb ty a0
                             then negb (eqb0 h1 h2)
                             else false
                          then check_in h1 dist
                          else false
                       then check_in h2 dist
                       else false
                    then Some (h1,h2)
                    else None)
               | _ -> None)
            | _ -> None)) diseq
  in
  if forallb1 (fun x ->
       match x with
       | Some y -> true
       | None -> false) t0
  then check_diseqs_complete dist t0
  else false

(** val check_distinct :
    Form.form array -> Atom.atom array -> int -> int array -> bool **)

let check_distinct t_form t_atom ha diseq =
  match get t_atom ha with
  | Atom.Anop (n0, dist) -> check_diseqs t_form t_atom n0 dist diseq
  | _ -> false

(** val check_distinct_two_args :
    Form.form array -> Atom.atom array -> int -> int -> bool **)

let check_distinct_two_args t_form t_atom f1 f2 =
  match get t_form f1 with
  | Form.Fatom ha ->
    (match get t_form f2 with
     | Form.Fatom hb ->
       (match get t_atom ha with
        | Atom.Anop (n0, l) ->
          (match l with
           | Nil -> false
           | Cons (x, l0) ->
             (match l0 with
              | Nil -> false
              | Cons (y, l1) ->
                (match l1 with
                 | Nil ->
                   (match get t_atom hb with
                    | Atom.Abop (b, x', y') ->
                      (match b with
                       | Atom.BO_eq ty' ->
                         if Typ.eqb n0 ty'
                         then if if eqb0 x x' then eqb0 y y' else false
                              then true
                              else if eqb0 x y' then eqb0 y x' else false
                         else false
                       | _ -> false)
                    | _ -> false)
                 | Cons (i, l2) -> false)))
        | _ -> false)
     | _ -> false)
  | _ -> false

(** val check_lit :
    Form.form array -> Atom.atom array -> (int -> int -> bool) -> int -> int
    -> bool **)

let check_lit t_form t_atom check_var l1 l2 =
  if if eqb0 l1 l2
     then true
     else if eqb (Lit.is_pos l1) (Lit.is_pos l2)
          then check_var (Lit.blit l1) (Lit.blit l2)
          else false
  then true
  else if eqb (Lit.is_pos l1) (negb (Lit.is_pos l2))
       then check_distinct_two_args t_form t_atom (Lit.blit l1) (Lit.blit l2)
       else false

(** val check_form_aux :
    Form.form array -> Atom.atom array -> (int -> int -> bool) -> Form.form
    -> Form.form -> bool **)

let check_form_aux t_form t_atom check_var a b =
  match a with
  | Form.Fatom a0 ->
    (match b with
     | Form.Fatom b0 -> eqb0 a0 b0
     | Form.Fand diseq -> check_distinct t_form t_atom a0 diseq
     | _ -> false)
  | Form.Ftrue ->
    (match b with
     | Form.Ftrue -> true
     | _ -> false)
  | Form.Ffalse ->
    (match b with
     | Form.Ffalse -> true
     | _ -> false)
  | Form.Fnot2 (i1, l1) ->
    (match b with
     | Form.Fnot2 (i2, l2) ->
       if eqb0 i1 i2 then check_lit t_form t_atom check_var l1 l2 else false
     | _ -> false)
  | Form.Fand a1 ->
    (match b with
     | Form.Fand a2 ->
       if eqb0 (length a1) (length a2)
       then forallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.For a1 ->
    (match b with
     | Form.For a2 ->
       if eqb0 (length a1) (length a2)
       then forallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.Fimp a1 ->
    (match b with
     | Form.Fimp a2 ->
       if eqb0 (length a1) (length a2)
       then forallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.Fxor (l1, l2) ->
    (match b with
     | Form.Fxor (j1, j2) ->
       if check_lit t_form t_atom check_var l1 j1
       then check_lit t_form t_atom check_var l2 j2
       else false
     | _ -> false)
  | Form.Fiff (l1, l2) ->
    (match b with
     | Form.Fiff (j1, j2) ->
       if check_lit t_form t_atom check_var l1 j1
       then check_lit t_form t_atom check_var l2 j2
       else false
     | _ -> false)
  | Form.Fite (l1, l2, l3) ->
    (match b with
     | Form.Fite (j1, j2, j3) ->
       if if check_lit t_form t_atom check_var l1 j1
          then check_lit t_form t_atom check_var l2 j2
          else false
       then check_lit t_form t_atom check_var l3 j3
       else false
     | _ -> false)

(** val check_hform :
    Form.form array -> Atom.atom array -> int -> int -> bool **)

let check_hform t_form t_atom h1 h2 =
  foldi_down_cont (fun x cont h3 h4 ->
    if eqb0 h3 h4
    then true
    else check_form_aux t_form t_atom cont (get t_form h3) (get t_form h4))
    (length t_form) (ExtrNative.of_uint(0)) (fun h3 h4 -> false) h1 h2

(** val check_lit' :
    Form.form array -> Atom.atom array -> int -> int -> bool **)

let check_lit' t_form t_atom =
  check_lit t_form t_atom (check_hform t_form t_atom)

(** val check_distinct_elim :
    Form.form array -> Atom.atom array -> int list -> int -> int list **)

let rec check_distinct_elim t_form t_atom input res =
  match input with
  | Nil -> Nil
  | Cons (l, q) ->
    if check_lit' t_form t_atom l res
    then Cons (res, q)
    else Cons (l, (check_distinct_elim t_form t_atom q res))

type 'step _trace_ = 'step array array

(** val _checker_ :
    (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> int -> bool **)

let _checker_ check_step is_false0 s t0 confl =
  let s' = fold_left (fun s0 a -> fold_left check_step s0 a) s t0 in
  is_false0 (S.get s' confl)

module Euf_Checker = 
 struct 
  type step =
  | Res of int * int array
  | ImmFlatten of int * int * int
  | CTrue of int
  | CFalse of int
  | BuildDef of int * int
  | BuildDef2 of int * int
  | BuildProj of int * int * int
  | ImmBuildDef of int * int
  | ImmBuildDef2 of int * int
  | ImmBuildProj of int * int * int
  | EqTr of int * int * int list
  | EqCgr of int * int * int option list
  | EqCgrP of int * int * int * int option list
  | LiaMicromega of int * int list * zArithProof list
  | LiaDiseq of int * int
  | SplArith of int * int * int * zArithProof list
  | SplDistinctElim of int * int * int
  
  (** val step_rect :
      (int -> int array -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> 'a1)
      -> (int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int
      -> int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) ->
      (int -> int -> int -> 'a1) -> (int -> int -> int list -> 'a1) -> (int
      -> int -> int option list -> 'a1) -> (int -> int -> int -> int option
      list -> 'a1) -> (int -> int list -> zArithProof list -> 'a1) -> (int ->
      int -> 'a1) -> (int -> int -> int -> zArithProof list -> 'a1) -> (int
      -> int -> int -> 'a1) -> step -> 'a1 **)
  
  let step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
  | Res (x, x0) -> f x x0
  | ImmFlatten (x, x0, x1) -> f0 x x0 x1
  | CTrue x -> f1 x
  | CFalse x -> f2 x
  | BuildDef (x, x0) -> f3 x x0
  | BuildDef2 (x, x0) -> f4 x x0
  | BuildProj (x, x0, x1) -> f5 x x0 x1
  | ImmBuildDef (x, x0) -> f6 x x0
  | ImmBuildDef2 (x, x0) -> f7 x x0
  | ImmBuildProj (x, x0, x1) -> f8 x x0 x1
  | EqTr (x, x0, x1) -> f9 x x0 x1
  | EqCgr (x, x0, x1) -> f10 x x0 x1
  | EqCgrP (x, x0, x1, x2) -> f11 x x0 x1 x2
  | LiaMicromega (x, x0, x1) -> f12 x x0 x1
  | LiaDiseq (x, x0) -> f13 x x0
  | SplArith (x, x0, x1, x2) -> f14 x x0 x1 x2
  | SplDistinctElim (x, x0, x1) -> f15 x x0 x1
  
  (** val step_rec :
      (int -> int array -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> 'a1)
      -> (int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int
      -> int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) ->
      (int -> int -> int -> 'a1) -> (int -> int -> int list -> 'a1) -> (int
      -> int -> int option list -> 'a1) -> (int -> int -> int -> int option
      list -> 'a1) -> (int -> int list -> zArithProof list -> 'a1) -> (int ->
      int -> 'a1) -> (int -> int -> int -> zArithProof list -> 'a1) -> (int
      -> int -> int -> 'a1) -> step -> 'a1 **)
  
  let step_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
  | Res (x, x0) -> f x x0
  | ImmFlatten (x, x0, x1) -> f0 x x0 x1
  | CTrue x -> f1 x
  | CFalse x -> f2 x
  | BuildDef (x, x0) -> f3 x x0
  | BuildDef2 (x, x0) -> f4 x x0
  | BuildProj (x, x0, x1) -> f5 x x0 x1
  | ImmBuildDef (x, x0) -> f6 x x0
  | ImmBuildDef2 (x, x0) -> f7 x x0
  | ImmBuildProj (x, x0, x1) -> f8 x x0 x1
  | EqTr (x, x0, x1) -> f9 x x0 x1
  | EqCgr (x, x0, x1) -> f10 x x0 x1
  | EqCgrP (x, x0, x1, x2) -> f11 x x0 x1 x2
  | LiaMicromega (x, x0, x1) -> f12 x x0 x1
  | LiaDiseq (x, x0) -> f13 x x0
  | SplArith (x, x0, x1, x2) -> f14 x x0 x1 x2
  | SplDistinctElim (x, x0, x1) -> f15 x x0 x1
  
  (** val step_checker :
      Atom.atom array -> Form.form array -> S.t -> step -> S.t **)
  
  let step_checker t_atom t_form s = function
  | Res (pos, res) -> S.set_resolve s pos res
  | ImmFlatten (pos, cid, lf) ->
    S.set_clause s pos
      (check_flatten t_form (check_hatom t_atom) (check_neg_hatom t_atom) s
        cid lf)
  | CTrue pos -> S.set_clause s pos check_True
  | CFalse pos -> S.set_clause s pos check_False
  | BuildDef (pos, l) -> S.set_clause s pos (check_BuildDef t_form l)
  | BuildDef2 (pos, l) -> S.set_clause s pos (check_BuildDef2 t_form l)
  | BuildProj (pos, l, i) -> S.set_clause s pos (check_BuildProj t_form l i)
  | ImmBuildDef (pos, cid) ->
    S.set_clause s pos (check_ImmBuildDef t_form s cid)
  | ImmBuildDef2 (pos, cid) ->
    S.set_clause s pos (check_ImmBuildDef2 t_form s cid)
  | ImmBuildProj (pos, cid, i) ->
    S.set_clause s pos (check_ImmBuildProj t_form s cid i)
  | EqTr (pos, l, fl) -> S.set_clause s pos (check_trans t_form t_atom l fl)
  | EqCgr (pos, l, fl) -> S.set_clause s pos (check_congr t_form t_atom l fl)
  | EqCgrP (pos, l1, l2, fl) ->
    S.set_clause s pos (check_congr_pred t_form t_atom l1 l2 fl)
  | LiaMicromega (pos, cl, c) ->
    S.set_clause s pos (check_micromega t_form t_atom cl c)
  | LiaDiseq (pos, l) -> S.set_clause s pos (check_diseq t_form t_atom l)
  | SplArith (pos, orig, res, l) ->
    S.set_clause s pos (check_spl_arith t_form t_atom (S.get s orig) res l)
  | SplDistinctElim (pos, orig, res) ->
    S.set_clause s pos (check_distinct_elim t_form t_atom (S.get s orig) res)
  
  (** val euf_checker :
      Atom.atom array -> Form.form array -> (C.t -> bool) -> S.t -> step
      _trace_ -> int -> bool **)
  
  let euf_checker t_atom t_form s t0 =
    _checker_ (step_checker t_atom t_form) s t0
  
  type certif =
  | Certif of int * step _trace_ * int
  
  (** val certif_rect :
      (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1 **)
  
  let certif_rect f = function
  | Certif (x, x0, x1) -> f x x0 x1
  
  (** val certif_rec :
      (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1 **)
  
  let certif_rec f = function
  | Certif (x, x0, x1) -> f x x0 x1
  
  (** val add_roots : S.t -> int array -> int array option -> S.t **)
  
  let add_roots s d = function
  | Some ur ->
    foldi_right (fun i c_index s0 ->
      let c =
        if ltb0 c_index (length d)
        then Cons ((get d c_index), Nil)
        else C._true
      in
      S.set_clause s0 i c) ur s
  | None -> foldi_right (fun i c s0 -> S.set_clause s0 i (Cons (c, Nil))) d s
  
  (** val valid :
      typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array
      -> int array -> bool **)
  
  let valid t_i t_func t_atom t_form d =
    let rho =
      Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom) t_form
    in
    afold_left true (fun b1 b2 -> if b1 then b2 else false) (Lit.interp rho)
      d
  
  (** val checker :
      typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array
      -> int array -> int array option -> certif -> bool **)
  
  let checker t_i t_func t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    if if if Form.check_form t_form then Atom.check_atom t_atom else false
       then Atom.wt t_i t_func t_atom
       else false
    then euf_checker t_atom t_form C.is_false
           (add_roots (S.make nclauses) d used_roots) t0 confl
    else false
  
  (** val checker_b :
      typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array
      -> int -> bool -> certif -> bool **)
  
  let checker_b t_i t_func t_atom t_form l b c =
    let l0 = if b then Lit.neg l else l in
    let Certif (nclauses, x, x0) = c in
    checker t_i t_func t_atom t_form (make nclauses l0) None c
  
  (** val checker_eq :
      typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array
      -> int -> int -> int -> certif -> bool **)
  
  let checker_eq t_i t_func t_atom t_form l1 l2 l c =
    if if negb (Lit.is_pos l)
       then (match get t_form (Lit.blit l) with
             | Form.Fiff (l1', l2') ->
               if eqb0 l1 l1' then eqb0 l2 l2' else false
             | _ -> false)
       else false
    then let Certif (nclauses, x, x0) = c in
         checker t_i t_func t_atom t_form (make nclauses l) None c
    else false
  
  (** val checker_ext :
      Atom.atom array -> Form.form array -> int array -> int array option ->
      certif -> bool **)
  
  let checker_ext t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    if if Form.check_form t_form then Atom.check_atom t_atom else false
    then euf_checker t_atom t_form C.is_false
           (add_roots (S.make nclauses) d used_roots) t0 confl
    else false
 end


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

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (a, l') -> S (length l')

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

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (x0, h) -> h

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

(** val mult : nat -> nat -> nat **)

let rec mult n0 m =
  match n0 with
  | O -> O
  | S p -> plus m (mult p m)

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

(** val beq_nat : nat -> nat -> bool **)

let rec beq_nat n0 m =
  match n0 with
  | O ->
    (match m with
     | O -> true
     | S n1 -> false)
  | S n1 ->
    (match m with
     | O -> false
     | S m1 -> beq_nat n1 m1)

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

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| Nil -> Nil
| Cons (a, l0) ->
  (match l0 with
   | Nil -> Nil
   | Cons (a0, l1) -> Cons (a, (removelast l0)))

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

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

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  match n0 with
  | O -> Nil
  | S n1 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> Cons (a, (firstn n1 l0)))

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
  eqb0 i (Uint63.of_int (0))

(** val is_even : int -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

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

module Coq__3 = struct 
 (** val cast : int -> int -> (__ -> __ -> __) option **)
 
 let cast i j =
   if eqb0 i j then Some (fun _ hi -> hi) else None
end
let cast = Coq__3.cast

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

(** val length0 : 'a1 array -> int **)

let length0 = ExtrNative.parray_length

(** val to_list : 'a1 array -> 'a1 list **)

let to_list t0 =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then Nil
  else foldi_down (fun i l -> Cons ((get t0 i), l))
         (sub0 len (Uint63.of_int (1))) (Uint63.of_int (0)) Nil

(** val forallbi : (int -> 'a1 -> bool) -> 'a1 array -> bool **)

let forallbi f t0 =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then true
  else forallb0 (fun i -> f i (get t0 i)) (Uint63.of_int (0))
         (sub0 len (Uint63.of_int (1)))

(** val forallb1 : ('a1 -> bool) -> 'a1 array -> bool **)

let forallb1 f t0 =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then true
  else forallb0 (fun i -> f (get t0 i)) (Uint63.of_int (0))
         (sub0 len (Uint63.of_int (1)))

(** val existsb1 : ('a1 -> bool) -> 'a1 array -> bool **)

let existsb1 f t0 =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then false
  else existsb0 (fun i -> f (get t0 i)) (Uint63.of_int (0))
         (sub0 len (Uint63.of_int (1)))

(** val mapi : (int -> 'a1 -> 'a2) -> 'a1 array -> 'a2 array **)

let mapi f t0 =
  let size0 = length0 t0 in
  let def = f size0 (default t0) in
  let tb = make size0 def in
  if eqb0 size0 (Uint63.of_int (0))
  then tb
  else foldi (fun i tb0 -> set tb0 i (f i (get t0 i))) (Uint63.of_int (0))
         (sub0 size0 (Uint63.of_int (1))) tb

(** val foldi_left :
    (int -> 'a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1 **)

let foldi_left f a t0 =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then a
  else foldi (fun i a0 -> f i a0 (get t0 i)) (Uint63.of_int (0))
         (sub0 len (Uint63.of_int (1))) a

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1 **)

let fold_left f a t0 =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then a
  else foldi (fun i a0 -> f a0 (get t0 i)) (Uint63.of_int (0))
         (sub0 (length0 t0) (Uint63.of_int (1))) a

(** val foldi_right :
    (int -> 'a1 -> 'a2 -> 'a2) -> 'a1 array -> 'a2 -> 'a2 **)

let foldi_right f t0 b =
  let len = length0 t0 in
  if eqb0 (Uint63.of_int (0)) len
  then b
  else foldi_down (fun i b0 -> f i (get t0 i) b0)
         (sub0 len (Uint63.of_int (1))) (Uint63.of_int (0)) b

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

(** val afold_left :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1 **)

let afold_left default0 oP f v =
  let n0 = length0 v in
  if eqb0 n0 (Uint63.of_int (0))
  then default0
  else foldi (fun i a -> oP a (f (get v i))) (Uint63.of_int (1))
         (sub0 n0 (Uint63.of_int (1))) (f (get v (Uint63.of_int (0))))

(** val afold_right :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1 **)

let afold_right default0 oP f v =
  let n0 = length0 v in
  if eqb0 n0 (Uint63.of_int (0))
  then default0
  else if leb0 n0 (Uint63.of_int (1))
       then f (get v (Uint63.of_int (0)))
       else foldi_down (fun i b -> oP (f (get v i)) b)
              (sub0 n0 (Uint63.of_int (2))) (Uint63.of_int (0))
              (f (get v (sub0 n0 (Uint63.of_int (1)))))

(** val rev_aux : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_aux acc = function
| Nil -> acc
| Cons (t0, q) -> rev_aux (Cons (t0, acc)) q

(** val rev0 : 'a1 list -> 'a1 list **)

let rev0 l =
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

(** val nat_eqb : nat -> nat -> bool **)

let rec nat_eqb n0 m =
  match n0 with
  | O ->
    (match m with
     | O -> true
     | S n1 -> false)
  | S n' ->
    (match m with
     | O -> false
     | S m' -> nat_eqb n' m')

module RAWBITVECTOR_LIST = 
 struct 
  type bitvector = bool list
  
  (** val bits : bitvector -> bool list **)
  
  let bits a =
    a
  
  (** val size : bitvector -> n **)
  
  let size a =
    N.of_nat (length a)
  
  (** val of_bits : bool list -> bitvector **)
  
  let of_bits a =
    a
  
  (** val beq_list : bool list -> bool list -> bool **)
  
  let rec beq_list l m =
    match l with
    | Nil ->
      (match m with
       | Nil -> true
       | Cons (b, l0) -> false)
    | Cons (x, l') ->
      (match m with
       | Nil -> false
       | Cons (y, m') -> if eqb x y then beq_list l' m' else false)
  
  (** val bv_eq : bitvector -> bitvector -> bool **)
  
  let bv_eq a b =
    if N.eqb (size a) (size b) then beq_list (bits a) (bits b) else false
  
  (** val bv_concat : bitvector -> bitvector -> bitvector **)
  
  let bv_concat a b =
    app b a
  
  (** val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list **)
  
  let rec map2 f l1 l2 =
    match l1 with
    | Nil -> Nil
    | Cons (b1, tl1) ->
      (match l2 with
       | Nil -> Nil
       | Cons (b2, tl2) -> Cons ((f b1 b2), (map2 f tl1 tl2)))
  
  (** val fold_left2 :
      ('a1 -> 'a2 -> 'a2 -> 'a1) -> 'a2 list -> 'a2 list -> 'a1 -> 'a1 **)
  
  let rec fold_left2 f xs ys acc =
    match xs with
    | Nil -> acc
    | Cons (x, xs0) ->
      (match ys with
       | Nil -> acc
       | Cons (y, ys0) -> fold_left2 f xs0 ys0 (f acc x y))
  
  (** val mk_list_true_acc : nat -> bool list -> bool list **)
  
  let rec mk_list_true_acc t0 acc =
    match t0 with
    | O -> acc
    | S t' -> mk_list_true_acc t' (Cons (true, acc))
  
  (** val mk_list_true : nat -> bool list **)
  
  let rec mk_list_true = function
  | O -> Nil
  | S t' -> Cons (true, (mk_list_true t'))
  
  (** val mk_list_false_acc : nat -> bool list -> bool list **)
  
  let rec mk_list_false_acc t0 acc =
    match t0 with
    | O -> acc
    | S t' -> mk_list_false_acc t' (Cons (false, acc))
  
  (** val mk_list_false : nat -> bool list **)
  
  let rec mk_list_false = function
  | O -> Nil
  | S t' -> Cons (false, (mk_list_false t'))
  
  (** val zeros : n -> bitvector **)
  
  let zeros n0 =
    mk_list_false (N.to_nat n0)
  
  (** val bitOf : nat -> bitvector -> bool **)
  
  let bitOf n0 a =
    nth n0 a false
  
  (** val bv_and : bitvector -> bitvector -> bitvector **)
  
  let bv_and a b =
    if N.eqb (size a) (size b)
    then map2 (fun b1 b2 -> if b1 then b2 else false) (bits a) (bits b)
    else Nil
  
  (** val bv_or : bitvector -> bitvector -> bitvector **)
  
  let bv_or a b =
    if N.eqb (size a) (size b)
    then map2 (fun b1 b2 -> if b1 then true else b2) (bits a) (bits b)
    else Nil
  
  (** val bv_xor : bitvector -> bitvector -> bitvector **)
  
  let bv_xor a b =
    if N.eqb (size a) (size b) then map2 xorb (bits a) (bits b) else Nil
  
  (** val bv_not : bitvector -> bitvector **)
  
  let bv_not a =
    map negb (bits a)
  
  (** val add_carry : bool -> bool -> bool -> bool*bool **)
  
  let add_carry b1 b2 c =
    if b1
    then if b2
         then if c then true,true else false,true
         else if c then false,true else true,false
    else if b2
         then if c then false,true else true,false
         else if c then true,false else false,false
  
  (** val add_list_ingr : bool list -> bool list -> bool -> bool list **)
  
  let rec add_list_ingr bs1 bs2 c =
    match bs1 with
    | Nil -> Nil
    | Cons (b1, bs3) ->
      (match bs2 with
       | Nil -> Nil
       | Cons (b2, bs4) ->
         let r,c0 = add_carry b1 b2 c in Cons (r, (add_list_ingr bs3 bs4 c0)))
  
  (** val add_list : bool list -> bool list -> bool list **)
  
  let add_list a b =
    add_list_ingr a b false
  
  (** val bv_add : bitvector -> bitvector -> bitvector **)
  
  let bv_add a b =
    if N.eqb (size a) (size b) then add_list a b else Nil
  
  (** val twos_complement : bool list -> bool list **)
  
  let twos_complement b =
    add_list_ingr (map negb b) (mk_list_false (length b)) true
  
  (** val bv_neg : bitvector -> bitvector **)
  
  let bv_neg a =
    twos_complement a
  
  (** val subst_list' : bool list -> bool list -> bool list **)
  
  let subst_list' a b =
    add_list a (twos_complement b)
  
  (** val bv_subt' : bitvector -> bitvector -> bitvector **)
  
  let bv_subt' a b =
    if N.eqb (size a) (size b) then subst_list' (bits a) (bits b) else Nil
  
  (** val subst_borrow : bool -> bool -> bool -> bool*bool **)
  
  let subst_borrow b1 b2 b =
    if b1
    then if b2 then b,b else if b then false,false else true,false
    else if b2 then if b then false,true else true,true else b,b
  
  (** val subst_list_borrow : bool list -> bool list -> bool -> bool list **)
  
  let rec subst_list_borrow bs1 bs2 b =
    match bs1 with
    | Nil -> Nil
    | Cons (b1, bs3) ->
      (match bs2 with
       | Nil -> Nil
       | Cons (b2, bs4) ->
         let r,b0 = subst_borrow b1 b2 b in
         Cons (r, (subst_list_borrow bs3 bs4 b0)))
  
  (** val subst_list : bool list -> bool list -> bool list **)
  
  let subst_list a b =
    subst_list_borrow a b false
  
  (** val bv_subt : bitvector -> bitvector -> bitvector **)
  
  let bv_subt a b =
    if N.eqb (size a) (size b) then subst_list (bits a) (bits b) else Nil
  
  (** val ult_list_big_endian : bool list -> bool list -> bool **)
  
  let rec ult_list_big_endian x y =
    match x with
    | Nil -> false
    | Cons (xi, x') ->
      (match x' with
       | Nil ->
         (match y with
          | Nil -> false
          | Cons (yi, y') ->
            (match y' with
             | Nil -> if negb xi then yi else false
             | Cons (b, l) ->
               if if eqb xi yi then ult_list_big_endian x' y' else false
               then true
               else if negb xi then yi else false))
       | Cons (b, l) ->
         (match y with
          | Nil -> false
          | Cons (yi, y') ->
            if if eqb xi yi then ult_list_big_endian x' y' else false
            then true
            else if negb xi then yi else false))
  
  (** val ult_list : bool list -> bool list -> bool **)
  
  let ult_list x y =
    ult_list_big_endian (rev x) (rev y)
  
  (** val slt_list_big_endian : bool list -> bool list -> bool **)
  
  let rec slt_list_big_endian x y =
    match x with
    | Nil -> false
    | Cons (xi, x') ->
      (match x' with
       | Nil ->
         (match y with
          | Nil -> false
          | Cons (yi, y') ->
            (match y' with
             | Nil -> if xi then negb yi else false
             | Cons (b, l) ->
               if if eqb xi yi then ult_list_big_endian x' y' else false
               then true
               else if xi then negb yi else false))
       | Cons (b, l) ->
         (match y with
          | Nil -> false
          | Cons (yi, y') ->
            if if eqb xi yi then ult_list_big_endian x' y' else false
            then true
            else if xi then negb yi else false))
  
  (** val slt_list : bool list -> bool list -> bool **)
  
  let slt_list x y =
    slt_list_big_endian (rev x) (rev y)
  
  (** val bv_ult : bitvector -> bitvector -> bool **)
  
  let bv_ult a b =
    if N.eqb (size a) (size b) then ult_list a b else false
  
  (** val bv_slt : bitvector -> bitvector -> bool **)
  
  let bv_slt a b =
    if N.eqb (size a) (size b) then slt_list a b else false
  
  (** val mult_list_carry : bool list -> bool list -> nat -> bool list **)
  
  let rec mult_list_carry a b n0 =
    match a with
    | Nil -> mk_list_false n0
    | Cons (a', xs) ->
      if a'
      then add_list b (mult_list_carry xs (Cons (false, b)) n0)
      else mult_list_carry xs (Cons (false, b)) n0
  
  (** val mult_list_carry2 : bool list -> bool list -> nat -> bool list **)
  
  let rec mult_list_carry2 a b n0 =
    match a with
    | Nil -> mk_list_false n0
    | Cons (a', xs) ->
      if a'
      then add_list b (mult_list_carry2 xs (Cons (false, (removelast b))) n0)
      else mult_list_carry2 xs (Cons (false, (removelast b))) n0
  
  (** val and_with_bool : bool list -> bool -> bool list **)
  
  let rec and_with_bool a bt =
    match a with
    | Nil -> Nil
    | Cons (ai, a') ->
      Cons ((if bt then ai else false), (and_with_bool a' bt))
  
  (** val mult_bool_step_k_h :
      bool list -> bool list -> bool -> z -> bool list **)
  
  let rec mult_bool_step_k_h a b c k =
    match a with
    | Nil -> Nil
    | Cons (ai, a') ->
      (match b with
       | Nil -> Cons (ai, (mult_bool_step_k_h a' b c k))
       | Cons (bi, b') ->
         if Z.ltb (Z.sub k (Zpos XH)) Z0
         then let carry_out =
                if if ai then bi else false
                then true
                else if xorb ai bi then c else false
              in
              let curr = xorb (xorb ai bi) c in
              Cons (curr,
              (mult_bool_step_k_h a' b' carry_out (Z.sub k (Zpos XH))))
         else Cons (ai, (mult_bool_step_k_h a' b c (Z.sub k (Zpos XH)))))
  
  (** val top_k_bools : bool list -> int -> bool list **)
  
  let rec top_k_bools a k =
    if eqb0 k (Uint63.of_int (0))
    then Nil
    else (match a with
          | Nil -> Nil
          | Cons (ai, a') ->
            Cons (ai, (top_k_bools a' (sub0 k (Uint63.of_int (1))))))
  
  (** val mult_bool_step :
      bool list -> bool list -> bool list -> nat -> nat -> bool list **)
  
  let rec mult_bool_step a b res k k' =
    let ak = firstn (S k') a in
    let b' = and_with_bool ak (nth k b false) in
    let res' = mult_bool_step_k_h res b' false (Z.of_nat k) in
    (match k' with
     | O -> res'
     | S pk' -> mult_bool_step a b res' (S k) pk')
  
  (** val bvmult_bool : bool list -> bool list -> nat -> bool list **)
  
  let bvmult_bool a b n0 =
    let res = and_with_bool a (nth O b false) in
    (match n0 with
     | O -> res
     | S n1 ->
       (match n1 with
        | O -> res
        | S k -> mult_bool_step a b res (S O) k))
  
  (** val mult_list : bool list -> bool list -> bool list **)
  
  let mult_list a b =
    bvmult_bool a b (length a)
  
  (** val bv_mult : bitvector -> bitvector -> bitvector **)
  
  let bv_mult a b =
    if N.eqb (size a) (size b) then mult_list a b else zeros (size a)
  
  (** val _of_bits : bool list -> n -> bool list **)
  
  let _of_bits a s =
    if N.eqb (N.of_nat (length a)) s then a else zeros s
  
  (** val bv_empty : bitvector **)
  
  let bv_empty =
    Nil
  
  (** val extract : bool list -> nat -> nat -> bool list **)
  
  let rec extract x i j =
    match x with
    | Nil -> Nil
    | Cons (bx, x') ->
      (match i with
       | O ->
         (match j with
          | O -> Nil
          | S j' -> Cons (bx, (extract x' i j')))
       | S i' ->
         (match j with
          | O -> Nil
          | S j' -> extract x' i' j'))
  
  (** val bv_extr : n -> n -> n -> bool list -> bitvector **)
  
  let bv_extr i n0 n1 a =
    if N.ltb n1 (N.add n0 i)
    then mk_list_false (N.to_nat n0)
    else extract a (N.to_nat i) (N.to_nat (N.add n0 i))
  
  (** val extend : bool list -> nat -> bool -> bool list **)
  
  let rec extend x i b =
    match i with
    | O -> x
    | S i' -> Cons (b, (extend x i' b))
  
  (** val zextend : bool list -> nat -> bool list **)
  
  let zextend x i =
    extend x i false
  
  (** val sextend : bool list -> nat -> bool list **)
  
  let sextend x i =
    match x with
    | Nil -> mk_list_false i
    | Cons (xb, x') -> extend x i xb
  
  (** val bv_zextn : n -> n -> bitvector -> bitvector **)
  
  let bv_zextn n0 i a =
    zextend a (N.to_nat i)
  
  (** val bv_sextn : n -> n -> bitvector -> bitvector **)
  
  let bv_sextn n0 i a =
    sextend a (N.to_nat i)
  
  (** val pow2 : nat -> nat **)
  
  let rec pow2 = function
  | O -> S O
  | S n' -> mult (S (S O)) (pow2 n')
  
  (** val _list2nat_be : bool list -> nat -> nat -> nat **)
  
  let rec _list2nat_be a n0 i =
    match a with
    | Nil -> n0
    | Cons (xa, xsa) ->
      if xa
      then _list2nat_be xsa (plus n0 (pow2 i)) (plus i (S O))
      else _list2nat_be xsa n0 (plus i (S O))
  
  (** val list2nat_be : bool list -> nat **)
  
  let list2nat_be a =
    _list2nat_be a O O
  
  (** val _shl_be : bool list -> bool list **)
  
  let _shl_be a = match a with
  | Nil -> Nil
  | Cons (b, l) -> Cons (false, (removelast a))
  
  (** val nshl_be : bool list -> nat -> bool list **)
  
  let rec nshl_be a = function
  | O -> a
  | S n' -> nshl_be (_shl_be a) n'
  
  (** val shl_be : bool list -> bool list -> bool list **)
  
  let shl_be a b =
    nshl_be a (list2nat_be b)
  
  (** val bv_shl : bitvector -> bitvector -> bitvector **)
  
  let bv_shl a b =
    if N.eqb (size a) (size b) then shl_be a b else zeros (size a)
  
  (** val _shr_be : bool list -> bool list **)
  
  let _shr_be = function
  | Nil -> Nil
  | Cons (xa, xsa) -> app xsa (Cons (false, Nil))
  
  (** val nshr_be : bool list -> nat -> bool list **)
  
  let rec nshr_be a = function
  | O -> a
  | S n' -> nshr_be (_shr_be a) n'
  
  (** val shr_be : bool list -> bool list -> bool list **)
  
  let shr_be a b =
    nshr_be a (list2nat_be b)
  
  (** val bv_shr : bitvector -> bitvector -> bitvector **)
  
  let bv_shr a b =
    if N.eqb (size a) (size b) then shr_be a b else zeros (size a)
 end

module BITVECTOR_LIST = 
 struct 
  type bitvector_ =
    RAWBITVECTOR_LIST.bitvector
    (* singleton inductive, whose constructor was MkBitvector *)
  
  (** val bitvector__rect :
      n -> (RAWBITVECTOR_LIST.bitvector -> __ -> 'a1) -> bitvector_ -> 'a1 **)
  
  let bitvector__rect n0 f b =
    f b __
  
  (** val bitvector__rec :
      n -> (RAWBITVECTOR_LIST.bitvector -> __ -> 'a1) -> bitvector_ -> 'a1 **)
  
  let bitvector__rec n0 f b =
    f b __
  
  (** val bv : n -> bitvector_ -> RAWBITVECTOR_LIST.bitvector **)
  
  let bv n0 b =
    b
  
  type bitvector = bitvector_
  
  (** val bits : n -> bitvector -> bool list **)
  
  let bits n0 bv0 =
    RAWBITVECTOR_LIST.bits (bv n0 bv0)
  
  (** val of_bits : bool list -> bitvector **)
  
  let of_bits l =
    RAWBITVECTOR_LIST.of_bits l
  
  (** val _of_bits : bool list -> n -> bitvector **)
  
  let _of_bits l s =
    RAWBITVECTOR_LIST._of_bits l s
  
  (** val bitOf : n -> nat -> bitvector -> bool **)
  
  let bitOf n0 p bv0 =
    RAWBITVECTOR_LIST.bitOf p (bv n0 bv0)
  
  (** val zeros : n -> bitvector **)
  
  let zeros n0 =
    RAWBITVECTOR_LIST.zeros n0
  
  (** val bv_eq : n -> bitvector -> bitvector -> bool **)
  
  let bv_eq n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_eq (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_and : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_and n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_and (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_or : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_or n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_or (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_add : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_add n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_add (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_subt : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_subt n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_subt (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_mult : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_mult n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_mult (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_xor : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_xor n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_xor (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_ult : n -> bitvector -> bitvector -> bool **)
  
  let bv_ult n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_ult (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_slt : n -> bitvector -> bitvector -> bool **)
  
  let bv_slt n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_slt (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_not : n -> bitvector -> bitvector **)
  
  let bv_not n0 bv1 =
    RAWBITVECTOR_LIST.bv_not (bv n0 bv1)
  
  (** val bv_neg : n -> bitvector -> bitvector **)
  
  let bv_neg n0 bv1 =
    RAWBITVECTOR_LIST.bv_neg (bv n0 bv1)
  
  (** val bv_concat : n -> n -> bitvector -> bitvector -> bitvector **)
  
  let bv_concat n0 m bv1 bv2 =
    RAWBITVECTOR_LIST.bv_concat (bv n0 bv1) (bv m bv2)
  
  (** val bv_extr : n -> n -> n -> bitvector -> bitvector **)
  
  let bv_extr i n0 n1 bv1 =
    RAWBITVECTOR_LIST.bv_extr i n0 n1 (bv n1 bv1)
  
  (** val bv_zextn : n -> n -> bitvector -> bitvector **)
  
  let bv_zextn n0 i bv1 =
    RAWBITVECTOR_LIST.bv_zextn n0 i (bv n0 bv1)
  
  (** val bv_sextn : n -> n -> bitvector -> bitvector **)
  
  let bv_sextn n0 i bv1 =
    RAWBITVECTOR_LIST.bv_sextn n0 i (bv n0 bv1)
  
  (** val bv_shl : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_shl n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_shl (bv n0 bv1) (bv n0 bv2)
  
  (** val bv_shr : n -> bitvector -> bitvector -> bitvector **)
  
  let bv_shr n0 bv1 bv2 =
    RAWBITVECTOR_LIST.bv_shr (bv n0 bv1) (bv n0 bv2)
 end

type 'x compare1 =
| LT
| EQ
| GT

(** val eqb_to_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> sumbool **)

let eqb_to_eq_dec eqb2 x y =
  if eqb2 x y then Left else Right

type 't eqbType =
  't -> 't -> bool
  (* singleton inductive, whose constructor was Build_EqbType *)

type 't decType =
  't -> 't -> sumbool
  (* singleton inductive, whose constructor was Build_DecType *)

(** val eq_dec0 : 'a1 decType -> 'a1 -> 'a1 -> sumbool **)

let eq_dec0 decType0 =
  decType0

(** val eqbToDecType : 'a1 eqbType -> 'a1 decType **)

let eqbToDecType h =
  eqb_to_eq_dec h

type 't ordType =
| Build_OrdType

type 't comparable =
  't -> 't -> 't compare1
  (* singleton inductive, whose constructor was Build_Comparable *)

(** val compare2 :
    'a1 ordType -> 'a1 comparable -> 'a1 -> 'a1 -> 'a1 compare1 **)

let compare2 ot comparable0 =
  comparable0

type 't inhabited =
  't
  (* singleton inductive, whose constructor was Build_Inhabited *)

(** val default_value : 'a1 inhabited -> 'a1 **)

let default_value inhabited0 =
  inhabited0

type 't compDec = { eqb1 : 't eqbType; ordered : 't ordType;
                    comp : 't comparable; inh : 't inhabited }

type 't ty = 't

(** val eqb1 : 'a1 compDec -> 'a1 ty eqbType **)

let eqb1 x = x.eqb1

(** val ordered : 'a1 compDec -> 'a1 ty ordType **)

let ordered x = x.ordered

(** val inh : 'a1 compDec -> 'a1 ty inhabited **)

let inh x = x.inh

(** val ord_of_compdec : 'a1 compDec -> 'a1 ordType **)

let ord_of_compdec c =
  c.ordered

(** val inh_of_compdec : 'a1 compDec -> 'a1 inhabited **)

let inh_of_compdec c =
  c.inh

(** val comp_of_compdec : 'a1 compDec -> 'a1 comparable **)

let comp_of_compdec c =
  c.comp

(** val eqbtype_of_compdec : 'a1 compDec -> 'a1 eqbType **)

let eqbtype_of_compdec c =
  c.eqb1

(** val dec_of_compdec : 'a1 compDec -> 'a1 decType **)

let dec_of_compdec c =
  let { eqb1 = x; ordered = x0; comp = x1; inh = x2 } = c in eqbToDecType x

type 'ty type_compdec = 'ty

(** val eqb_of_compdec : 'a1 compDec -> 'a1 -> 'a1 -> bool **)

let eqb_of_compdec c =
  c.eqb1

type typ_compdec =
  __ compDec
  (* singleton inductive, whose constructor was Typ_compdec *)

type te_carrier = __

(** val te_compdec : typ_compdec -> te_carrier compDec **)

let te_compdec t0 =
  t0

(** val constructive_indefinite_description : __ -> 'a1 **)

let constructive_indefinite_description =
  failwith "AXIOM TO BE REALIZED"

module Raw = 
 struct 
  (** val eqb_key : 'a1 decType -> 'a1 -> 'a1 -> bool **)
  
  let eqb_key key_dec x y =
    match eq_dec0 key_dec x y with
    | Left -> true
    | Right -> false
  
  (** val eqb_elt : 'a1 decType -> 'a1 -> 'a1 -> bool **)
  
  let eqb_elt elt_dec x y =
    match eq_dec0 elt_dec x y with
    | Left -> true
    | Right -> false
  
  type ('key, 'elt) farray = ('key*'elt) list
  
  (** val ke_dec : 'a1 decType -> 'a2 decType -> ('a1*'a2) decType **)
  
  let ke_dec key_dec elt_dec x y =
    let k,e = x in
    let k0,e0 = y in
    let s = eq_dec0 key_dec k k0 in
    (match s with
     | Left -> eq_dec0 elt_dec e e0
     | Right -> Right)
  
  (** val ke_ord : 'a1 ordType -> ('a1*'a2) ordType **)
  
  let ke_ord key_ord =
    Build_OrdType
  
  (** val empty : ('a1, 'a2) farray **)
  
  let empty =
    Nil
  
  (** val is_empty : ('a1, 'a2) farray -> bool **)
  
  let is_empty = function
  | Nil -> true
  | Cons (x, x0) -> false
  
  (** val mem :
      'a1 ordType -> 'a1 comparable -> 'a1 -> ('a1, 'a2) farray -> bool **)
  
  let rec mem key_ord key_comp k = function
  | Nil -> false
  | Cons (p, l) ->
    let k',e = p in
    (match compare2 key_ord key_comp k k' with
     | LT -> false
     | EQ -> true
     | GT -> mem key_ord key_comp k l)
  
  (** val find :
      'a1 ordType -> 'a1 comparable -> 'a1 -> ('a1, 'a2) farray -> 'a2 option **)
  
  let rec find key_ord key_comp k = function
  | Nil -> None
  | Cons (p, s') ->
    let k',x = p in
    (match compare2 key_ord key_comp k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find key_ord key_comp k s')
  
  (** val add :
      'a1 ordType -> 'a1 comparable -> 'a1 -> 'a2 -> ('a1, 'a2) farray ->
      ('a1, 'a2) farray **)
  
  let rec add key_ord key_comp k x s = match s with
  | Nil -> Cons ((k,x), Nil)
  | Cons (p, l) ->
    let k',y = p in
    (match compare2 key_ord key_comp k k' with
     | LT -> Cons ((k,x), s)
     | EQ -> Cons ((k,x), l)
     | GT -> Cons ((k',y), (add key_ord key_comp k x l)))
  
  (** val remove :
      'a1 ordType -> 'a1 comparable -> 'a1 -> ('a1, 'a2) farray -> ('a1, 'a2)
      farray **)
  
  let rec remove key_ord key_comp k s = match s with
  | Nil -> Nil
  | Cons (p, l) ->
    let k',x = p in
    (match compare2 key_ord key_comp k k' with
     | LT -> s
     | EQ -> l
     | GT -> Cons ((k',x), (remove key_ord key_comp k l)))
  
  (** val elements : ('a1, 'a2) farray -> ('a1, 'a2) farray **)
  
  let elements m =
    m
  
  (** val fold :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) farray -> 'a3 -> 'a3 **)
  
  let rec fold f m acc =
    match m with
    | Nil -> acc
    | Cons (p, m') -> let k,e = p in fold f m' (f k e acc)
  
  (** val equal :
      'a1 ordType -> 'a1 comparable -> ('a2 -> 'a2 -> bool) -> ('a1, 'a2)
      farray -> ('a1, 'a2) farray -> bool **)
  
  let rec equal key_ord key_comp cmp0 m m' =
    match m with
    | Nil ->
      (match m' with
       | Nil -> true
       | Cons (p, l) -> false)
    | Cons (p, l) ->
      let x,e = p in
      (match m' with
       | Nil -> false
       | Cons (p2, l') ->
         let x',e' = p2 in
         (match compare2 key_ord key_comp x x' with
          | EQ ->
            if cmp0 e e' then equal key_ord key_comp cmp0 l l' else false
          | _ -> false))
 end

type ('key, 'elt) farray0 =
  ('key, 'elt) Raw.farray
  (* singleton inductive, whose constructor was Build_farray *)

(** val this :
    'a1 ordType -> 'a2 inhabited -> ('a1, 'a2) farray0 -> ('a1, 'a2)
    Raw.farray **)

let this key_ord elt_inh f =
  f

(** val cmp : 'a1 ordType -> 'a1 comparable -> 'a1 -> 'a1 -> bool **)

let cmp elt_ord elt_comp e e' =
  match compare2 elt_ord elt_comp e e' with
  | EQ -> true
  | _ -> false

(** val raw_add_nodefault :
    'a1 ordType -> 'a1 comparable -> 'a2 ordType -> 'a2 comparable -> 'a2
    inhabited -> 'a1 -> 'a2 -> ('a1, 'a2) Raw.farray -> ('a1, 'a2) Raw.farray **)

let raw_add_nodefault key_ord key_comp elt_ord elt_comp elt_inh k x l =
  if cmp elt_ord elt_comp x (default_value elt_inh)
  then if Raw.mem key_ord key_comp k l
       then Raw.remove key_ord key_comp k l
       else l
  else Raw.add key_ord key_comp k x l

(** val empty0 : 'a1 ordType -> 'a2 inhabited -> ('a1, 'a2) farray0 **)

let empty0 key_ord elt_inh =
  Raw.empty

(** val add0 :
    'a1 decType -> 'a1 ordType -> 'a1 comparable -> 'a2 ordType -> 'a2
    comparable -> 'a2 inhabited -> 'a1 -> 'a2 -> ('a1, 'a2) farray0 -> ('a1,
    'a2) farray0 **)

let add0 key_dec key_ord key_comp elt_ord elt_comp elt_inh x e m =
  raw_add_nodefault key_ord key_comp elt_ord elt_comp elt_inh x e
    (this key_ord elt_inh m)

(** val find0 :
    'a1 ordType -> 'a1 comparable -> 'a2 inhabited -> 'a1 -> ('a1, 'a2)
    farray0 -> 'a2 option **)

let find0 key_ord key_comp elt_inh x m =
  Raw.find key_ord key_comp x (this key_ord elt_inh m)

(** val equal0 :
    'a1 ordType -> 'a1 comparable -> 'a2 ordType -> 'a2 comparable -> 'a2
    inhabited -> ('a1, 'a2) farray0 -> ('a1, 'a2) farray0 -> bool **)

let equal0 key_ord key_comp elt_ord elt_comp elt_inh m m' =
  Raw.equal key_ord key_comp (cmp elt_ord elt_comp) (this key_ord elt_inh m)
    (this key_ord elt_inh m')

(** val compare_farray :
    'a1 ordType -> 'a1 comparable -> 'a2 decType -> 'a2 ordType -> 'a2
    comparable -> 'a2 inhabited -> ('a1, 'a2) farray0 -> ('a1, 'a2) farray0
    -> ('a1, 'a2) farray0 compare1 **)

let rec compare_farray key_ord key_comp elt_dec elt_ord elt_comp elt_inh m1 m2 =
  match m1 with
  | Nil ->
    (match m2 with
     | Nil -> EQ
     | Cons (p, m3) -> LT)
  | Cons (y, l) ->
    (match m2 with
     | Nil -> GT
     | Cons (p, m3) ->
       let x,e = y in
       let x',e' = p in
       let c = compare2 key_ord key_comp x x' in
       (match c with
        | LT -> LT
        | EQ ->
          let c0 = compare2 elt_ord elt_comp e e' in
          (match c0 with
           | LT -> LT
           | EQ ->
             compare_farray key_ord key_comp elt_dec elt_ord elt_comp elt_inh
               l m3
           | GT -> GT)
        | GT -> GT))

(** val select :
    'a1 ordType -> 'a1 comparable -> 'a2 inhabited -> ('a1, 'a2) farray0 ->
    'a1 -> 'a2 **)

let select key_ord key_comp elt_inh a i =
  match find0 key_ord key_comp elt_inh i a with
  | Some v -> v
  | None -> default_value elt_inh

(** val store :
    'a1 decType -> 'a1 ordType -> 'a1 comparable -> 'a2 ordType -> 'a2
    comparable -> 'a2 inhabited -> ('a1, 'a2) farray0 -> 'a1 -> 'a2 -> ('a1,
    'a2) farray0 **)

let store key_dec key_ord key_comp elt_ord elt_comp elt_inh a i v =
  add0 key_dec key_ord key_comp elt_ord elt_comp elt_inh i v a

(** val diff_index_p :
    'a1 decType -> 'a1 ordType -> 'a1 comparable -> 'a2 decType -> 'a2
    ordType -> 'a2 comparable -> 'a2 inhabited -> ('a1, 'a2) farray0 -> ('a1,
    'a2) farray0 -> 'a1 **)

let diff_index_p key_dec key_ord key_comp elt_dec elt_ord elt_comp elt_inh a b =
  constructive_indefinite_description __

(** val diff_index :
    'a1 decType -> 'a1 ordType -> 'a1 comparable -> 'a2 decType -> 'a2
    ordType -> 'a2 comparable -> 'a2 inhabited -> ('a1, 'a2) farray0 -> ('a1,
    'a2) farray0 -> 'a1 **)

let diff_index key_dec key_ord key_comp elt_dec elt_ord elt_comp elt_inh a b =
  diff_index_p key_dec key_ord key_comp elt_dec elt_ord elt_comp elt_inh a b

(** val diff :
    'a1 decType -> 'a1 ordType -> 'a1 comparable -> 'a2 decType -> 'a2
    ordType -> 'a2 comparable -> 'a1 inhabited -> 'a2 inhabited -> ('a1, 'a2)
    farray0 -> ('a1, 'a2) farray0 -> 'a1 **)

let diff key_dec key_ord key_comp elt_dec elt_ord elt_comp key_inh elt_inh a b =
  if equal0 key_ord key_comp elt_ord elt_comp elt_inh a b
  then default_value key_inh
  else diff_index key_dec key_ord key_comp elt_dec elt_ord elt_comp elt_inh a
         b

module Z_as_OT = 
 struct 
  type t = z
  
  (** val compare : z -> z -> z compare1 **)
  
  let compare x y =
    let c = Z.compare x y in
    (match c with
     | ExtrNative.Eq -> EQ
     | ExtrNative.Lt -> LT
     | ExtrNative.Gt -> GT)
  
  (** val eq_dec : z -> z -> sumbool **)
  
  let eq_dec =
    Z.eq_dec
 end

module Positive_as_OT = 
 struct 
  type t = positive
  
  (** val compare : t -> t -> positive compare1 **)
  
  let compare x y =
    let c = Coq_Pos.compare x y in
    (match c with
     | ExtrNative.Eq -> EQ
     | ExtrNative.Lt -> LT
     | ExtrNative.Gt -> GT)
  
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
 end

module Valuation = 
 struct 
  type t = int -> bool
 end

module Var = 
 struct 
  (** val _true : int **)
  
  let _true =
    (Uint63.of_int (0))
  
  (** val _false : int **)
  
  let _false =
    (Uint63.of_int (1))
  
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
    lsr0 l (Uint63.of_int (1))
  
  (** val lit : int -> int **)
  
  let lit x =
    lsl0 x (Uint63.of_int (1))
  
  (** val neg : int -> int **)
  
  let neg l =
    lxor0 l (Uint63.of_int (1))
  
  (** val nlit : int -> int **)
  
  let nlit x =
    neg (lit x)
  
  (** val _true : int **)
  
  let _true =
    (Uint63.of_int (0))
  
  (** val _false : int **)
  
  let _false =
    (Uint63.of_int (2))
  
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
  
  (** val has_true : t -> bool **)
  
  let rec has_true = function
  | Nil -> false
  | Cons (l, c0) -> if eqb0 l Lit._true then true else has_true c0
  
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
       if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
       then coq_or c1 c2'
       else Cons (l1, (resolve0 c1 c2))
     | ExtrNative.Gt ->
       if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
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
            if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
            then coq_or c3 c2'
            else Cons (l1, (resolve c3 c2))
          | ExtrNative.Gt ->
            if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
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
       if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
       then C._true
       else Cons (l1, c)
     | ExtrNative.Gt ->
       if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
       then C._true
       else Cons (l2, (insert l1 c')))
  
  (** val insert_no_simpl : int -> int list -> int list **)
  
  let rec insert_no_simpl l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare0 l1 l2 with
     | ExtrNative.Eq -> c
     | ExtrNative.Lt -> Cons (l1, c)
     | ExtrNative.Gt -> Cons (l2, (insert_no_simpl l1 c')))
  
  (** val insert_keep : int -> int list -> int list **)
  
  let rec insert_keep l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare0 l1 l2 with
     | ExtrNative.Gt -> Cons (l2, (insert_keep l1 c'))
     | _ -> Cons (l1, c))
  
  (** val sort : int list -> int list **)
  
  let rec sort = function
  | Nil -> Nil
  | Cons (l1, c0) -> insert_no_simpl l1 (sort c0)
  
  (** val sort_uniq : int list -> int list **)
  
  let rec sort_uniq = function
  | Nil -> Nil
  | Cons (l1, c0) -> insert l1 (sort_uniq c0)
  
  (** val sort_keep : int list -> int list **)
  
  let rec sort_keep = function
  | Nil -> Nil
  | Cons (l1, c0) -> insert_keep l1 (sort_keep c0)
  
  (** val set_clause : t -> int -> C.t -> t **)
  
  let set_clause s pos c =
    set s pos (sort c)
  
  (** val set_clause_keep : t -> int -> C.t -> t **)
  
  let set_clause_keep s pos c =
    set s pos (sort_keep c)
  
  (** val set_resolve : t -> int -> int array -> t **)
  
  let set_resolve s pos r =
    let len = length0 r in
    if eqb0 len (Uint63.of_int (0))
    then s
    else let c =
           foldi (fun i c' -> C.resolve (get s (Coq__2.get r i)) c')
             (Uint63.of_int (1)) (sub0 len (Uint63.of_int (1)))
             (get s (Coq__2.get r (Uint63.of_int (0))))
         in
         internal_set s pos c
  
  (** val subclause : int list -> int list -> bool **)
  
  let subclause cl1 cl2 =
    forallb (fun l1 ->
      if if eqb0 l1 Lit._false then true else eqb0 l1 (Lit.neg Lit._true)
      then true
      else existsb (fun l2 -> eqb0 l1 l2) cl2) cl1
  
  (** val check_weaken : t -> int -> int list -> C.t **)
  
  let check_weaken s cid cl =
    if subclause (get s cid) cl then cl else C._true
  
  (** val set_weaken : t -> int -> int -> int list -> t **)
  
  let set_weaken s pos cid cl =
    set_clause_keep s pos (check_weaken s cid cl)
 end

type 'step trace = 'step array array

(** val trace_to_list : 'a1 trace -> 'a1 list **)

let trace_to_list t0 =
  fold_left (fun res a -> app res (to_list a)) Nil t0

(** val trace_fold : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 trace -> 'a1 **)

let trace_fold transition s0 t0 =
  fold_left (fold_left transition) s0 t0

(** val nat_eqb0 : nat -> nat -> bool **)

let nat_eqb0 =
  beq_nat

(** val ltb_bool : bool -> bool -> bool **)

let ltb_bool x y =
  if negb x then y else false

(** val bool_ord : bool ordType **)

let bool_ord =
  Build_OrdType

(** val bool_eqbtype : bool eqbType **)

let bool_eqbtype =
  eqb

(** val bool_comp : bool comparable **)

let bool_comp x y =
  if ltb_bool x y then LT else if eqb x y then EQ else GT

(** val bool_inh : bool inhabited **)

let bool_inh =
  false

(** val bool_compdec : bool compDec **)

let bool_compdec =
  { eqb1 = bool_eqbtype; ordered = bool_ord; comp = bool_comp; inh =
    bool_inh }

(** val z_ord : z ordType **)

let z_ord =
  Build_OrdType

(** val z_eqbtype : z eqbType **)

let z_eqbtype =
  Z.eqb

(** val z_comp : z comparable **)

let z_comp =
  Z_as_OT.compare

(** val z_inh : z inhabited **)

let z_inh =
  Z0

(** val z_compdec : z compDec **)

let z_compdec =
  { eqb1 = z_eqbtype; ordered = z_ord; comp = z_comp; inh = z_inh }

(** val positive_ord : positive ordType **)

let positive_ord =
  Build_OrdType

(** val positive_eqbtype : positive eqbType **)

let positive_eqbtype =
  Coq_Pos.eqb

(** val positive_comp : positive comparable **)

let positive_comp =
  Positive_as_OT.compare

(** val positive_inh : positive inhabited **)

let positive_inh =
  XH

(** val positive_compdec : positive compDec **)

let positive_compdec =
  { eqb1 = positive_eqbtype; ordered = positive_ord; comp = positive_comp;
    inh = positive_inh }

(** val bV_ord : n -> BITVECTOR_LIST.bitvector ordType **)

let bV_ord n0 =
  Build_OrdType

(** val bV_eqbtype : n -> BITVECTOR_LIST.bitvector eqbType **)

let bV_eqbtype n0 =
  BITVECTOR_LIST.bv_eq n0

(** val bV_comp : n -> BITVECTOR_LIST.bitvector comparable **)

let bV_comp n0 x y =
  if BITVECTOR_LIST.bv_ult n0 x y
  then LT
  else if BITVECTOR_LIST.bv_eq n0 x y then EQ else GT

(** val bV_inh : n -> BITVECTOR_LIST.bitvector inhabited **)

let bV_inh n0 =
  BITVECTOR_LIST.zeros n0

(** val bV_compdec : n -> BITVECTOR_LIST.bitvector compDec **)

let bV_compdec n0 =
  { eqb1 = (bV_eqbtype n0); ordered = (bV_ord n0); comp = (bV_comp n0); inh =
    (bV_inh n0) }

(** val fArray_ord :
    'a1 ordType -> 'a2 ordType -> 'a2 decType -> 'a2 inhabited -> 'a1
    comparable -> ('a1, 'a2) farray0 ordType **)

let fArray_ord key_ord elt_ord elt_dec elt_inh key_comp =
  Build_OrdType

(** val fArray_eqbtype :
    'a1 ordType -> 'a2 ordType -> 'a2 eqbType -> 'a1 comparable -> 'a2
    comparable -> 'a2 inhabited -> ('a1, 'a2) farray0 eqbType **)

let fArray_eqbtype key_ord elt_ord elt_eqbtype key_comp elt_comp elt_inh =
  equal0 key_ord key_comp elt_ord elt_comp elt_inh

(** val fArray_comp :
    'a1 ordType -> 'a2 ordType -> 'a2 eqbType -> 'a1 comparable -> 'a2
    inhabited -> 'a2 comparable -> ('a1, 'a2) farray0 comparable **)

let fArray_comp key_ord elt_ord elt_eqbtype key_comp elt_inh elt_comp x y =
  compare_farray key_ord key_comp (eqbToDecType elt_eqbtype) elt_ord elt_comp
    elt_inh x y

(** val fArray_inh :
    'a1 ordType -> 'a2 inhabited -> ('a1, 'a2) farray0 inhabited **)

let fArray_inh key_ord elt_inh =
  empty0 key_ord elt_inh

(** val fArray_compdec_obligation_1 :
    'a1 compDec -> 'a2 compDec -> ('a1, 'a2) farray0 comparable **)

let fArray_compdec_obligation_1 key_compdec elt_compdec =
  let { eqb1 = eqb2; ordered = x; comp = x0; inh = x1 } = key_compdec in
  let { eqb1 = eqb3; ordered = x2; comp = x3; inh = x4 } = elt_compdec in
  let decidable0 = eqbToDecType eqb3 in
  (fun x5 y ->
  compare2 (fArray_ord x x2 decidable0 x4 x0)
    (fArray_comp x x2 eqb3 x0 x4 x3) x5 y)

(** val fArray_compdec :
    'a1 compDec -> 'a2 compDec -> ('a1, 'a2) farray0 compDec **)

let fArray_compdec key_compdec elt_compdec =
  { eqb1 =
    (fArray_eqbtype (ord_of_compdec key_compdec) (ord_of_compdec elt_compdec)
      (eqbtype_of_compdec elt_compdec) (comp_of_compdec key_compdec)
      (comp_of_compdec elt_compdec) (inh_of_compdec elt_compdec)); ordered =
    (fArray_ord (ord_of_compdec key_compdec) (ord_of_compdec elt_compdec)
      (dec_of_compdec elt_compdec) (inh_of_compdec elt_compdec)
      (comp_of_compdec key_compdec)); comp =
    (fArray_compdec_obligation_1 key_compdec elt_compdec); inh =
    (fArray_inh (ord_of_compdec key_compdec) (inh_of_compdec elt_compdec)) }

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
  | FbbT of int * int list
  
  (** val form_rect :
      (int -> 'a1) -> 'a1 -> 'a1 -> (int -> int -> 'a1) -> (int array -> 'a1)
      -> (int array -> 'a1) -> (int array -> 'a1) -> (int -> int -> 'a1) ->
      (int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> int list
      -> 'a1) -> form -> 'a1 **)
  
  let form_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
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
  | FbbT (x, x0) -> f9 x x0
  
  (** val form_rec :
      (int -> 'a1) -> 'a1 -> 'a1 -> (int -> int -> 'a1) -> (int array -> 'a1)
      -> (int array -> 'a1) -> (int array -> 'a1) -> (int -> int -> 'a1) ->
      (int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> int list
      -> 'a1) -> form -> 'a1 **)
  
  let form_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
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
  | FbbT (x, x0) -> f9 x x0
  
  (** val is_Ftrue : form -> bool **)
  
  let is_Ftrue = function
  | Ftrue -> true
  | _ -> false
  
  (** val is_Ffalse : form -> bool **)
  
  let is_Ffalse = function
  | Ffalse -> true
  | _ -> false
  
  (** val interp_aux :
      (int -> bool) -> (int -> n -> BITVECTOR_LIST.bitvector) -> (int ->
      bool) -> form -> bool **)
  
  let interp_aux interp_atom interp_bvatom interp_var = function
  | Fatom a -> interp_atom a
  | Ftrue -> true
  | Ffalse -> false
  | Fnot2 (i, l) ->
    fold (fun b -> negb (negb b)) (Uint63.of_int (1)) i
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
  | FbbT (a, ls) ->
    let ils = map (Lit.interp interp_var) ls in
    let n0 = N.of_nat (length ils) in
    BITVECTOR_LIST.bv_eq n0 (interp_bvatom a n0) (BITVECTOR_LIST.of_bits ils)
  
  (** val t_interp :
      (int -> bool) -> (int -> n -> BITVECTOR_LIST.bitvector) -> form array
      -> bool array **)
  
  let t_interp interp_atom interp_bvatom t_form =
    foldi_left (fun i t_b hf ->
      set t_b i (interp_aux interp_atom interp_bvatom (get t_b) hf))
      (make (length0 t_form) true) t_form
  
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
  | FbbT (i0, ls) -> forallb (fun l -> ltb0 (Lit.blit l) i) ls
  | _ -> true
  
  (** val wf : form array -> bool **)
  
  let wf t_form =
    forallbi lt_form t_form
  
  (** val interp_state_var :
      (int -> bool) -> (int -> n -> BITVECTOR_LIST.bitvector) -> form array
      -> int -> bool **)
  
  let interp_state_var interp_atom interp_bvatom t_form =
    let t_interp0 = t_interp interp_atom interp_bvatom t_form in
    get t_interp0
  
  (** val interp :
      (int -> bool) -> (int -> n -> BITVECTOR_LIST.bitvector) -> form array
      -> form -> bool **)
  
  let interp interp_atom interp_bvatom t_form =
    interp_aux interp_atom interp_bvatom
      (interp_state_var interp_atom interp_bvatom t_form)
  
  (** val check_form : form array -> bool **)
  
  let check_form t_form =
    if if if is_Ftrue (default t_form)
          then is_Ftrue (get t_form (Uint63.of_int (0)))
          else false
       then is_Ffalse (get t_form (Uint63.of_int (1)))
       else false
    then wf t_form
    else false
 end

module Typ = 
 struct 
  type coq_type =
  | TFArray of coq_type * coq_type
  | Tindex of int
  | TZ
  | Tbool
  | Tpositive
  | TBV of n
  
  (** val type_rect :
      (coq_type -> 'a1 -> coq_type -> 'a1 -> 'a1) -> (int -> 'a1) -> 'a1 ->
      'a1 -> 'a1 -> (n -> 'a1) -> coq_type -> 'a1 **)
  
  let rec type_rect f f0 f1 f2 f3 f4 = function
  | TFArray (t1, t2) ->
    f t1 (type_rect f f0 f1 f2 f3 f4 t1) t2 (type_rect f f0 f1 f2 f3 f4 t2)
  | Tindex i -> f0 i
  | TZ -> f1
  | Tbool -> f2
  | Tpositive -> f3
  | TBV n0 -> f4 n0
  
  (** val type_rec :
      (coq_type -> 'a1 -> coq_type -> 'a1 -> 'a1) -> (int -> 'a1) -> 'a1 ->
      'a1 -> 'a1 -> (n -> 'a1) -> coq_type -> 'a1 **)
  
  let rec type_rec f f0 f1 f2 f3 f4 = function
  | TFArray (t1, t2) ->
    f t1 (type_rec f f0 f1 f2 f3 f4 t1) t2 (type_rec f f0 f1 f2 f3 f4 t2)
  | Tindex i -> f0 i
  | TZ -> f1
  | Tbool -> f2
  | Tpositive -> f3
  | TBV n0 -> f4 n0
  
  type ftype = coq_type list*coq_type
  
  (** val interp_compdec_aux :
      typ_compdec array -> coq_type -> (__, __ compDec) sigT **)
  
  let rec interp_compdec_aux t_i = function
  | TFArray (ti, te) ->
    ExistT (__,
      (Obj.magic
        (fArray_compdec (projT2 (interp_compdec_aux t_i ti))
          (projT2 (interp_compdec_aux t_i te)))))
  | Tindex i -> ExistT (__, (te_compdec (get t_i i)))
  | TZ -> ExistT (__, (Obj.magic z_compdec))
  | Tbool -> ExistT (__, (Obj.magic bool_compdec))
  | Tpositive -> ExistT (__, (Obj.magic positive_compdec))
  | TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
  
  (** val interp_compdec : typ_compdec array -> coq_type -> __ compDec **)
  
  let interp_compdec t_i t0 =
    projT2 (interp_compdec_aux t_i t0)
  
  type interp = __ type_compdec
  
  type interp_ftype = __
  
  (** val dec_interp : typ_compdec array -> coq_type -> interp decType **)
  
  let dec_interp t_i t0 =
    let c = interp_compdec t_i t0 in
    let { eqb1 = eqb2; ordered = x; comp = x0; inh = x1 } = c in
    eqbToDecType eqb2
  
  (** val comp_interp :
      typ_compdec array -> coq_type -> interp comparable **)
  
  let comp_interp t_i t0 =
    let c = interp_compdec t_i t0 in c.comp
  
  (** val ord_interp : typ_compdec array -> coq_type -> interp ordType **)
  
  let ord_interp t_i t0 =
    let c = interp_compdec t_i t0 in c.ordered
  
  (** val inh_interp : typ_compdec array -> coq_type -> interp inhabited **)
  
  let inh_interp t_i t0 =
    let c = interp_compdec t_i t0 in c.inh
  
  (** val inhabitant_interp : typ_compdec array -> coq_type -> interp **)
  
  let inhabitant_interp t_i t0 =
    default_value (interp_compdec t_i t0).inh
  
  (** val i_eqb :
      typ_compdec array -> coq_type -> interp -> interp -> bool **)
  
  let i_eqb t_i t0 =
    eqb_of_compdec (interp_compdec t_i t0)
  
  (** val reflect_eqb_compdec : 'a1 compDec -> 'a1 -> 'a1 -> reflect **)
  
  let reflect_eqb_compdec c x y =
    let { eqb1 = eqb2; ordered = x0; comp = x1; inh = x2 } = c in
    iff_reflect (eqb2 x y)
  
  (** val reflect_i_eqb :
      typ_compdec array -> coq_type -> interp -> interp -> reflect **)
  
  let reflect_i_eqb t_i t0 x y =
    reflect_eqb_compdec (interp_compdec t_i t0) x y
  
  (** val i_eqb_eqb :
      typ_compdec array -> coq_type -> interp -> interp -> bool **)
  
  let i_eqb_eqb t_i = function
  | TFArray (ti, te) -> i_eqb t_i (TFArray (ti, te))
  | Tindex i -> eqb_of_compdec (te_compdec (get t_i i))
  | TZ -> Obj.magic Z.eqb
  | Tbool -> Obj.magic eqb
  | Tpositive -> Obj.magic Coq_Pos.eqb
  | TBV n0 -> Obj.magic (BITVECTOR_LIST.bv_eq n0)
  
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
  
  (** val positive_cast : positive -> positive -> (__ -> __ -> __) option **)
  
  let rec positive_cast n0 m =
    match n0 with
    | XI p ->
      (match m with
       | XI q ->
         (match positive_cast p q with
          | Some k -> Some (fun _ -> k __)
          | None -> None)
       | _ -> None)
    | XO p ->
      (match m with
       | XO q ->
         (match positive_cast p q with
          | Some k -> Some (fun _ -> k __)
          | None -> None)
       | _ -> None)
    | XH ->
      (match m with
       | XH -> Some (fun _ x -> x)
       | _ -> None)
  
  (** val coq_N_cast : n -> n -> (__ -> __ -> __) option **)
  
  let coq_N_cast n0 m =
    match n0 with
    | N0 ->
      (match m with
       | N0 -> Some (fun _ x -> x)
       | Npos p -> None)
    | Npos p ->
      (match m with
       | N0 -> None
       | Npos q ->
         (match positive_cast p q with
          | Some k -> Some (fun _ -> k __)
          | None -> None))
  
  (** val cast : coq_type -> coq_type -> cast_result **)
  
  let rec cast a b =
    match a with
    | TFArray (k1, e1) ->
      (match b with
       | TFArray (k2, e2) ->
         (match cast k1 k2 with
          | Cast kk ->
            (match cast e1 e2 with
             | Cast ke ->
               let ka = fun x -> ke __ (kk __ x) in Cast (fun _ x -> ka x)
             | NoCast -> NoCast)
          | NoCast -> NoCast)
       | _ -> NoCast)
    | Tindex i ->
      (match b with
       | Tindex j ->
         (match Coq__3.cast i j with
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
    | TBV n0 ->
      (match b with
       | TBV m ->
         (match coq_N_cast n0 m with
          | Some k -> Cast (fun _ -> k __)
          | None -> NoCast)
       | _ -> NoCast)
  
  (** val eqb : coq_type -> coq_type -> bool **)
  
  let rec eqb a b =
    match a with
    | TFArray (k1, e1) ->
      (match b with
       | TFArray (k2, e2) -> if eqb k1 k2 then eqb e1 e2 else false
       | _ -> false)
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
    | TBV n0 ->
      (match b with
       | TBV m -> N.eqb n0 m
       | _ -> false)
  
  (** val reflect_eqb : coq_type -> coq_type -> reflect **)
  
  let reflect_eqb x y =
    match x with
    | TFArray (x1, x2) ->
      (match y with
       | TFArray (y1, y2) ->
         iff_reflect (if eqb x1 y1 then eqb x2 y2 else false)
       | _ -> ReflectF)
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
    | TBV n0 ->
      (match y with
       | TBV n1 -> iff_reflect (N.eqb n0 n1)
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
  | CO_BV of bool list * n
  
  (** val cop_rect : 'a1 -> 'a1 -> (bool list -> n -> 'a1) -> cop -> 'a1 **)
  
  let cop_rect f f0 f1 = function
  | CO_xH -> f
  | CO_Z0 -> f0
  | CO_BV (x, x0) -> f1 x x0
  
  (** val cop_rec : 'a1 -> 'a1 -> (bool list -> n -> 'a1) -> cop -> 'a1 **)
  
  let cop_rec f f0 f1 = function
  | CO_xH -> f
  | CO_Z0 -> f0
  | CO_BV (x, x0) -> f1 x x0
  
  type unop =
  | UO_xO
  | UO_xI
  | UO_Zpos
  | UO_Zneg
  | UO_Zopp
  | UO_BVbitOf of n * nat
  | UO_BVnot of n
  | UO_BVneg of n
  | UO_BVextr of n * n * n
  | UO_BVzextn of n * n
  | UO_BVsextn of n * n
  
  (** val unop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (n -> nat -> 'a1) -> (n -> 'a1) ->
      (n -> 'a1) -> (n -> n -> n -> 'a1) -> (n -> n -> 'a1) -> (n -> n ->
      'a1) -> unop -> 'a1 **)
  
  let unop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | UO_xO -> f
  | UO_xI -> f0
  | UO_Zpos -> f1
  | UO_Zneg -> f2
  | UO_Zopp -> f3
  | UO_BVbitOf (x, x0) -> f4 x x0
  | UO_BVnot x -> f5 x
  | UO_BVneg x -> f6 x
  | UO_BVextr (x, x0, x1) -> f7 x x0 x1
  | UO_BVzextn (x, x0) -> f8 x x0
  | UO_BVsextn (x, x0) -> f9 x x0
  
  (** val unop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (n -> nat -> 'a1) -> (n -> 'a1) ->
      (n -> 'a1) -> (n -> n -> n -> 'a1) -> (n -> n -> 'a1) -> (n -> n ->
      'a1) -> unop -> 'a1 **)
  
  let unop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | UO_xO -> f
  | UO_xI -> f0
  | UO_Zpos -> f1
  | UO_Zneg -> f2
  | UO_Zopp -> f3
  | UO_BVbitOf (x, x0) -> f4 x x0
  | UO_BVnot x -> f5 x
  | UO_BVneg x -> f6 x
  | UO_BVextr (x, x0, x1) -> f7 x x0 x1
  | UO_BVzextn (x, x0) -> f8 x x0
  | UO_BVsextn (x, x0) -> f9 x x0
  
  type binop =
  | BO_Zplus
  | BO_Zminus
  | BO_Zmult
  | BO_Zlt
  | BO_Zle
  | BO_Zge
  | BO_Zgt
  | BO_eq of Typ.coq_type
  | BO_BVand of n
  | BO_BVor of n
  | BO_BVxor of n
  | BO_BVadd of n
  | BO_BVsubst of n
  | BO_BVmult of n
  | BO_BVult of n
  | BO_BVslt of n
  | BO_BVconcat of n * n
  | BO_BVshl of n
  | BO_BVshr of n
  | BO_select of Typ.coq_type * Typ.coq_type
  | BO_diffarray of Typ.coq_type * Typ.coq_type
  
  (** val binop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (Typ.coq_type -> 'a1)
      -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1)
      -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1) -> (n -> n -> 'a1) -> (n ->
      'a1) -> (n -> 'a1) -> (Typ.coq_type -> Typ.coq_type -> 'a1) ->
      (Typ.coq_type -> Typ.coq_type -> 'a1) -> binop -> 'a1 **)
  
  let binop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 = function
  | BO_Zplus -> f
  | BO_Zminus -> f0
  | BO_Zmult -> f1
  | BO_Zlt -> f2
  | BO_Zle -> f3
  | BO_Zge -> f4
  | BO_Zgt -> f5
  | BO_eq x -> f6 x
  | BO_BVand x -> f7 x
  | BO_BVor x -> f8 x
  | BO_BVxor x -> f9 x
  | BO_BVadd x -> f10 x
  | BO_BVsubst x -> f11 x
  | BO_BVmult x -> f12 x
  | BO_BVult x -> f13 x
  | BO_BVslt x -> f14 x
  | BO_BVconcat (x, x0) -> f15 x x0
  | BO_BVshl x -> f16 x
  | BO_BVshr x -> f17 x
  | BO_select (x, x0) -> f18 x x0
  | BO_diffarray (x, x0) -> f19 x x0
  
  (** val binop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (Typ.coq_type -> 'a1)
      -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1)
      -> (n -> 'a1) -> (n -> 'a1) -> (n -> 'a1) -> (n -> n -> 'a1) -> (n ->
      'a1) -> (n -> 'a1) -> (Typ.coq_type -> Typ.coq_type -> 'a1) ->
      (Typ.coq_type -> Typ.coq_type -> 'a1) -> binop -> 'a1 **)
  
  let binop_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 = function
  | BO_Zplus -> f
  | BO_Zminus -> f0
  | BO_Zmult -> f1
  | BO_Zlt -> f2
  | BO_Zle -> f3
  | BO_Zge -> f4
  | BO_Zgt -> f5
  | BO_eq x -> f6 x
  | BO_BVand x -> f7 x
  | BO_BVor x -> f8 x
  | BO_BVxor x -> f9 x
  | BO_BVadd x -> f10 x
  | BO_BVsubst x -> f11 x
  | BO_BVmult x -> f12 x
  | BO_BVult x -> f13 x
  | BO_BVslt x -> f14 x
  | BO_BVconcat (x, x0) -> f15 x x0
  | BO_BVshl x -> f16 x
  | BO_BVshr x -> f17 x
  | BO_select (x, x0) -> f18 x x0
  | BO_diffarray (x, x0) -> f19 x x0
  
  type nop =
    Typ.coq_type
    (* singleton inductive, whose constructor was NO_distinct *)
  
  (** val nop_rect : (Typ.coq_type -> 'a1) -> nop -> 'a1 **)
  
  let nop_rect f n0 =
    f n0
  
  (** val nop_rec : (Typ.coq_type -> 'a1) -> nop -> 'a1 **)
  
  let nop_rec f n0 =
    f n0
  
  type terop =
  | TO_store of Typ.coq_type * Typ.coq_type
  
  (** val terop_rect :
      (Typ.coq_type -> Typ.coq_type -> 'a1) -> terop -> 'a1 **)
  
  let terop_rect f = function
  | TO_store (x, x0) -> f x x0
  
  (** val terop_rec :
      (Typ.coq_type -> Typ.coq_type -> 'a1) -> terop -> 'a1 **)
  
  let terop_rec f = function
  | TO_store (x, x0) -> f x x0
  
  type atom =
  | Acop of cop
  | Auop of unop * int
  | Abop of binop * int * int
  | Atop of terop * int * int * int
  | Anop of nop * int list
  | Aapp of int * int list
  
  (** val atom_rect :
      (cop -> 'a1) -> (unop -> int -> 'a1) -> (binop -> int -> int -> 'a1) ->
      (terop -> int -> int -> int -> 'a1) -> (nop -> int list -> 'a1) -> (int
      -> int list -> 'a1) -> atom -> 'a1 **)
  
  let atom_rect f f0 f1 f2 f3 f4 = function
  | Acop x -> f x
  | Auop (x, x0) -> f0 x x0
  | Abop (x, x0, x1) -> f1 x x0 x1
  | Atop (x, x0, x1, x2) -> f2 x x0 x1 x2
  | Anop (x, x0) -> f3 x x0
  | Aapp (x, x0) -> f4 x x0
  
  (** val atom_rec :
      (cop -> 'a1) -> (unop -> int -> 'a1) -> (binop -> int -> int -> 'a1) ->
      (terop -> int -> int -> int -> 'a1) -> (nop -> int list -> 'a1) -> (int
      -> int list -> 'a1) -> atom -> 'a1 **)
  
  let atom_rec f f0 f1 f2 f3 f4 = function
  | Acop x -> f x
  | Auop (x, x0) -> f0 x x0
  | Abop (x, x0, x1) -> f1 x x0 x1
  | Atop (x, x0, x1, x2) -> f2 x x0 x1 x2
  | Anop (x, x0) -> f3 x x0
  | Aapp (x, x0) -> f4 x x0
  
  (** val cop_eqb : cop -> cop -> bool **)
  
  let cop_eqb o o' =
    match o with
    | CO_xH ->
      (match o' with
       | CO_xH -> true
       | _ -> false)
    | CO_Z0 ->
      (match o' with
       | CO_Z0 -> true
       | _ -> false)
    | CO_BV (bv0, s) ->
      (match o' with
       | CO_BV (bv', s') ->
         if N.eqb s s' then RAWBITVECTOR_LIST.beq_list bv0 bv' else false
       | _ -> false)
  
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
    | UO_BVbitOf (s1, n0) ->
      (match o' with
       | UO_BVbitOf (s2, m) -> if nat_eqb n0 m then N.eqb s1 s2 else false
       | _ -> false)
    | UO_BVnot s1 ->
      (match o' with
       | UO_BVnot s2 -> N.eqb s1 s2
       | _ -> false)
    | UO_BVneg s1 ->
      (match o' with
       | UO_BVneg s2 -> N.eqb s1 s2
       | _ -> false)
    | UO_BVextr (i0, n00, n01) ->
      (match o' with
       | UO_BVextr (i1, n10, n11) ->
         if if N.eqb i0 i1 then N.eqb n00 n10 else false
         then N.eqb n01 n11
         else false
       | _ -> false)
    | UO_BVzextn (s1, i1) ->
      (match o' with
       | UO_BVzextn (s2, i2) -> if N.eqb s1 s2 then N.eqb i1 i2 else false
       | _ -> false)
    | UO_BVsextn (s1, i1) ->
      (match o' with
       | UO_BVsextn (s2, i2) -> if N.eqb s1 s2 then N.eqb i1 i2 else false
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
    | BO_BVand s1 ->
      (match o' with
       | BO_BVand s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVor s1 ->
      (match o' with
       | BO_BVor s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVxor s1 ->
      (match o' with
       | BO_BVxor s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVadd s1 ->
      (match o' with
       | BO_BVadd s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVsubst s1 ->
      (match o' with
       | BO_BVsubst s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVmult s1 ->
      (match o' with
       | BO_BVmult s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVult s1 ->
      (match o' with
       | BO_BVult s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVslt s1 ->
      (match o' with
       | BO_BVslt s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVconcat (s1, s2) ->
      (match o' with
       | BO_BVconcat (s3, s4) -> if N.eqb s1 s3 then N.eqb s2 s4 else false
       | _ -> false)
    | BO_BVshl s1 ->
      (match o' with
       | BO_BVshl s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_BVshr s1 ->
      (match o' with
       | BO_BVshr s2 -> N.eqb s1 s2
       | _ -> false)
    | BO_select (ti, te) ->
      (match o' with
       | BO_select (ti', te') ->
         if Typ.eqb ti ti' then Typ.eqb te te' else false
       | _ -> false)
    | BO_diffarray (ti, te) ->
      (match o' with
       | BO_diffarray (ti', te') ->
         if Typ.eqb ti ti' then Typ.eqb te te' else false
       | _ -> false)
  
  (** val top_eqb : terop -> terop -> bool **)
  
  let top_eqb o o' =
    let TO_store (ti, te) = o in
    let TO_store (ti', te') = o' in
    if Typ.eqb ti ti' then Typ.eqb te te' else false
  
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
    | Atop (o, t1, t2, t3) ->
      (match t' with
       | Atop (o', t1', t2', t3') ->
         if if if top_eqb o o' then eqb0 t1 t1' else false
            then eqb0 t2 t2'
            else false
         then eqb0 t3 t3'
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
       | _ -> ReflectF)
    | CO_Z0 ->
      (match o2 with
       | CO_Z0 -> ReflectT
       | _ -> ReflectF)
    | CO_BV (l, n0) ->
      (match o2 with
       | CO_BV (l0, n1) ->
         iff_reflect
           (if N.eqb n0 n1 then RAWBITVECTOR_LIST.beq_list l l0 else false)
       | _ -> ReflectF)
  
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
    | UO_BVbitOf (s1, n1) ->
      (match o2 with
       | UO_BVbitOf (s2, n2) ->
         iff_reflect (if nat_eqb n1 n2 then N.eqb s1 s2 else false)
       | _ -> ReflectF)
    | UO_BVnot s1 ->
      (match o2 with
       | UO_BVnot s2 -> iff_reflect (N.eqb s1 s2)
       | _ -> ReflectF)
    | UO_BVneg s1 ->
      (match o2 with
       | UO_BVneg s2 -> iff_reflect (N.eqb s1 s2)
       | _ -> ReflectF)
    | UO_BVextr (s1, n0, n1) ->
      (match o2 with
       | UO_BVextr (s2, n2, n3) ->
         iff_reflect
           (if if N.eqb s1 s2 then N.eqb n0 n2 else false
            then N.eqb n1 n3
            else false)
       | _ -> ReflectF)
    | UO_BVzextn (s1, i) ->
      (match o2 with
       | UO_BVzextn (s2, i0) ->
         iff_reflect (if N.eqb s1 s2 then N.eqb i i0 else false)
       | _ -> ReflectF)
    | UO_BVsextn (s1, i) ->
      (match o2 with
       | UO_BVsextn (s2, i0) ->
         iff_reflect (if N.eqb s1 s2 then N.eqb i i0 else false)
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
    | BO_eq a1 ->
      (match o2 with
       | BO_eq a2 -> Typ.reflect_eqb a1 a2
       | _ -> ReflectF)
    | BO_BVand s1 ->
      (match o2 with
       | BO_BVand s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVor s1 ->
      (match o2 with
       | BO_BVor s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVxor s1 ->
      (match o2 with
       | BO_BVxor s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVadd s1 ->
      (match o2 with
       | BO_BVadd s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVsubst s1 ->
      (match o2 with
       | BO_BVsubst s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVmult s1 ->
      (match o2 with
       | BO_BVmult s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVult s1 ->
      (match o2 with
       | BO_BVult s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVslt s1 ->
      (match o2 with
       | BO_BVslt s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVconcat (s1, n0) ->
      (match o2 with
       | BO_BVconcat (s2, n1) ->
         let r = N.eqb_spec s1 s2 in
         (match r with
          | ReflectT -> N.eqb_spec n0 n1
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
    | BO_BVshl s1 ->
      (match o2 with
       | BO_BVshl s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_BVshr s1 ->
      (match o2 with
       | BO_BVshr s2 -> N.eqb_spec s1 s2
       | _ -> ReflectF)
    | BO_select (i1, e1) ->
      (match o2 with
       | BO_select (i2, e2) ->
         let r = Typ.reflect_eqb i1 i2 in
         (match r with
          | ReflectT -> Typ.reflect_eqb e1 e2
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
    | BO_diffarray (i1, e1) ->
      (match o2 with
       | BO_diffarray (i2, e2) ->
         let r = Typ.reflect_eqb i1 i2 in
         (match r with
          | ReflectT -> Typ.reflect_eqb e1 e2
          | ReflectF -> ReflectF)
       | _ -> ReflectF)
  
  (** val reflect_top_eqb : terop -> terop -> reflect **)
  
  let reflect_top_eqb o1 o2 =
    let TO_store (i1, e1) = o1 in
    let TO_store (i2, e2) = o2 in
    let r = Typ.reflect_eqb i1 i2 in
    (match r with
     | ReflectT -> Typ.reflect_eqb e1 e2
     | ReflectF -> ReflectF)
  
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
    | Atop (t0, i, i0, i1) ->
      (match t2 with
       | Atop (t3, i2, i3, i4) ->
         let r = reflect_top_eqb t0 t3 in
         (match r with
          | ReflectT ->
            let r0 = reflect_eqb i i2 in
            (match r0 with
             | ReflectT ->
               let r1 = reflect_eqb i0 i3 in
               (match r1 with
                | ReflectT -> reflect_eqb i1 i4
                | ReflectF -> ReflectF)
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
      typ_compdec array -> Typ.coq_type -> Typ.interp -> (Typ.coq_type,
      Typ.interp) coq_val **)
  
  let coq_Bval t_i x x0 =
    { v_type = x; v_val = x0 }
  
  type tval = (Typ.ftype, Typ.interp_ftype) coq_val
  
  (** val coq_Tval :
      typ_compdec array -> Typ.ftype -> Typ.interp_ftype -> (Typ.ftype,
      Typ.interp_ftype) coq_val **)
  
  let coq_Tval t_i x x0 =
    { v_type = x; v_val = x0 }
  
  (** val bvtrue : typ_compdec array -> bval **)
  
  let bvtrue t_i =
    coq_Bval t_i Typ.Tbool (Obj.magic true)
  
  (** val bvfalse : typ_compdec array -> bval **)
  
  let bvfalse t_i =
    coq_Bval t_i Typ.Tbool (Obj.magic false)
  
  (** val typ_cop : cop -> Typ.coq_type **)
  
  let typ_cop = function
  | CO_xH -> Typ.Tpositive
  | CO_Z0 -> Typ.TZ
  | CO_BV (l, s) -> Typ.TBV s
  
  (** val typ_uop : unop -> Typ.coq_type*Typ.coq_type **)
  
  let typ_uop = function
  | UO_xO -> Typ.Tpositive,Typ.Tpositive
  | UO_xI -> Typ.Tpositive,Typ.Tpositive
  | UO_Zopp -> Typ.TZ,Typ.TZ
  | UO_BVbitOf (s, n0) -> (Typ.TBV s),Typ.Tbool
  | UO_BVnot s -> (Typ.TBV s),(Typ.TBV s)
  | UO_BVneg s -> (Typ.TBV s),(Typ.TBV s)
  | UO_BVextr (i, n0, n1) -> (Typ.TBV n1),(Typ.TBV n0)
  | UO_BVzextn (s, i) -> (Typ.TBV s),(Typ.TBV (N.add i s))
  | UO_BVsextn (s, i) -> (Typ.TBV s),(Typ.TBV (N.add i s))
  | _ -> Typ.Tpositive,Typ.TZ
  
  (** val typ_bop : binop -> (Typ.coq_type*Typ.coq_type)*Typ.coq_type **)
  
  let typ_bop = function
  | BO_Zplus -> (Typ.TZ,Typ.TZ),Typ.TZ
  | BO_Zminus -> (Typ.TZ,Typ.TZ),Typ.TZ
  | BO_Zmult -> (Typ.TZ,Typ.TZ),Typ.TZ
  | BO_eq t0 -> (t0,t0),Typ.Tbool
  | BO_BVand s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVor s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVxor s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVadd s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVsubst s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVmult s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVult s -> ((Typ.TBV s),(Typ.TBV s)),Typ.Tbool
  | BO_BVslt s -> ((Typ.TBV s),(Typ.TBV s)),Typ.Tbool
  | BO_BVconcat (s1, s2) ->
    ((Typ.TBV s1),(Typ.TBV s2)),(Typ.TBV (N.add s1 s2))
  | BO_BVshl s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_BVshr s -> ((Typ.TBV s),(Typ.TBV s)),(Typ.TBV s)
  | BO_select (ti, te) -> ((Typ.TFArray (ti, te)),ti),te
  | BO_diffarray (ti, te) ->
    ((Typ.TFArray (ti, te)),(Typ.TFArray (ti, te))),ti
  | _ -> (Typ.TZ,Typ.TZ),Typ.Tbool
  
  (** val typ_top :
      terop -> ((Typ.coq_type*Typ.coq_type)*Typ.coq_type)*Typ.coq_type **)
  
  let typ_top = function
  | TO_store (ti, te) ->
    (((Typ.TFArray (ti, te)),ti),te),(Typ.TFArray (ti, te))
  
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
      typ_compdec array -> tval array -> (int -> Typ.coq_type) -> atom ->
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
    | Atop (o, a1, a2, a3) ->
      let ta,t' = typ_top o in
      let p,ta3 = ta in
      let ta1,ta2 = p in
      if if if Typ.eqb t' t0 then Typ.eqb (get_type0 a1) ta1 else false
         then Typ.eqb (get_type0 a2) ta2
         else false
      then Typ.eqb (get_type0 a3) ta3
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
      typ_compdec array -> tval array -> (int -> Typ.coq_type) -> atom ->
      sumbool **)
  
  let check_aux_dec t_i t_func get_type0 = function
  | Acop op -> Left
  | Auop (op, h) ->
    (match op with
     | UO_Zopp -> if Typ.eqb (get_type0 h) Typ.TZ then Left else Right
     | UO_BVbitOf (n0, n1) ->
       if Typ.eqb (get_type0 h) (Typ.TBV n0) then Left else Right
     | UO_BVnot n0 ->
       if Typ.eqb (get_type0 h) (Typ.TBV n0) then Left else Right
     | UO_BVneg n0 ->
       if Typ.eqb (get_type0 h) (Typ.TBV n0) then Left else Right
     | UO_BVextr (i, n0, n1) ->
       if Typ.eqb (get_type0 h) (Typ.TBV n1) then Left else Right
     | UO_BVzextn (n0, i) ->
       if Typ.eqb (get_type0 h) (Typ.TBV n0) then Left else Right
     | UO_BVsextn (n0, i) ->
       if Typ.eqb (get_type0 h) (Typ.TBV n0) then Left else Right
     | _ -> if Typ.eqb (get_type0 h) Typ.Tpositive then Left else Right)
  | Abop (op, h1, h2) ->
    (match op with
     | BO_eq t0 ->
       if Typ.eqb (get_type0 h1) t0
       then if Typ.eqb (get_type0 h2) t0 then Left else Right
       else Right
     | BO_BVand n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVor n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVxor n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVadd n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVsubst n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVmult n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVult n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVslt n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVconcat (n0, n1) ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n1) then Left else Right
       else Right
     | BO_BVshl n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_BVshr n0 ->
       if Typ.eqb (get_type0 h1) (Typ.TBV n0)
       then if Typ.eqb (get_type0 h2) (Typ.TBV n0) then Left else Right
       else Right
     | BO_select (t0, t1) ->
       if Typ.eqb (get_type0 h1) (Typ.TFArray (t0, t1))
       then if Typ.eqb (get_type0 h2) t0 then Left else Right
       else Right
     | BO_diffarray (t0, t1) ->
       if Typ.eqb (get_type0 h1) (Typ.TFArray (t0, t1))
       then if Typ.eqb (get_type0 h2) (Typ.TFArray (t0, t1))
            then Left
            else Right
       else Right
     | _ ->
       if Typ.eqb (get_type0 h1) Typ.TZ
       then if Typ.eqb (get_type0 h2) Typ.TZ then Left else Right
       else Right)
  | Atop (op, ha, i, i0) ->
    let TO_store (t0, t1) = op in
    if Typ.eqb (get_type0 i) t0
    then if Typ.eqb (get_type0 i0) t1
         then if Typ.eqb (get_type0 ha) (Typ.TFArray (t0, t1))
              then Left
              else Right
         else Right
    else Right
  | Anop (f, args) ->
    if forallb (fun t1 -> Typ.eqb (get_type0 t1) f) args then Left else Right
  | Aapp (i, e) ->
    let l,t0 = (get t_func i).v_type in check_args_dec get_type0 t0 e l
  
  (** val apply_unop :
      typ_compdec array -> Typ.coq_type -> Typ.coq_type -> (Typ.interp ->
      Typ.interp) -> bval -> (Typ.coq_type, Typ.interp) coq_val **)
  
  let apply_unop t_i t0 r op tv =
    let { v_type = t'; v_val = v } = tv in
    (match Typ.cast t' t0 with
     | Typ.Cast k -> coq_Bval t_i r (op (k __ v))
     | Typ.NoCast -> bvtrue t_i)
  
  (** val apply_binop :
      typ_compdec array -> Typ.coq_type -> Typ.coq_type -> Typ.coq_type ->
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
  
  (** val apply_terop :
      typ_compdec array -> Typ.coq_type -> Typ.coq_type -> Typ.coq_type ->
      Typ.coq_type -> (Typ.interp -> Typ.interp -> Typ.interp -> Typ.interp)
      -> bval -> bval -> bval -> (Typ.coq_type, Typ.interp) coq_val **)
  
  let apply_terop t_i t1 t2 t3 r op tv1 tv2 tv3 =
    let { v_type = t1'; v_val = v1 } = tv1 in
    let { v_type = t2'; v_val = v2 } = tv2 in
    let { v_type = t3'; v_val = v3 } = tv3 in
    (match Typ.cast t1' t1 with
     | Typ.Cast k1 ->
       (match Typ.cast t2' t2 with
        | Typ.Cast k2 ->
          (match Typ.cast t3' t3 with
           | Typ.Cast k3 ->
             coq_Bval t_i r (op (k1 __ v1) (k2 __ v2) (k3 __ v3))
           | Typ.NoCast -> bvtrue t_i)
        | Typ.NoCast -> bvtrue t_i)
     | Typ.NoCast -> bvtrue t_i)
  
  (** val apply_func :
      typ_compdec array -> Typ.coq_type list -> Typ.coq_type ->
      Typ.interp_ftype -> bval list -> bval **)
  
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
      typ_compdec array -> cop -> (Typ.coq_type, Typ.interp) coq_val **)
  
  let interp_cop t_i = function
  | CO_xH -> coq_Bval t_i Typ.Tpositive (Obj.magic XH)
  | CO_Z0 -> coq_Bval t_i Typ.TZ (Obj.magic Z0)
  | CO_BV (bv0, s) ->
    coq_Bval t_i (Typ.TBV s) (Obj.magic (BITVECTOR_LIST._of_bits bv0 s))
  
  (** val interp_uop :
      typ_compdec array -> unop -> bval -> (Typ.coq_type, Typ.interp) coq_val **)
  
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
  | UO_BVbitOf (s, n0) ->
    apply_unop t_i (Typ.TBV s) Typ.Tbool
      (Obj.magic (BITVECTOR_LIST.bitOf s n0))
  | UO_BVnot s ->
    apply_unop t_i (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_not s))
  | UO_BVneg s ->
    apply_unop t_i (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_neg s))
  | UO_BVextr (i, n0, n1) ->
    apply_unop t_i (Typ.TBV n1) (Typ.TBV n0)
      (Obj.magic (BITVECTOR_LIST.bv_extr i n0 n1))
  | UO_BVzextn (s, i) ->
    apply_unop t_i (Typ.TBV s) (Typ.TBV (N.add i s))
      (Obj.magic (BITVECTOR_LIST.bv_zextn s i))
  | UO_BVsextn (s, i) ->
    apply_unop t_i (Typ.TBV s) (Typ.TBV (N.add i s))
      (Obj.magic (BITVECTOR_LIST.bv_sextn s i))
  
  (** val interp_bop :
      typ_compdec array -> binop -> bval -> bval -> (Typ.coq_type,
      Typ.interp) coq_val **)
  
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
  | BO_BVand s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_and s))
  | BO_BVor s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_or s))
  | BO_BVxor s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_xor s))
  | BO_BVadd s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_add s))
  | BO_BVsubst s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_subt s))
  | BO_BVmult s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_mult s))
  | BO_BVult s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) Typ.Tbool
      (Obj.magic (BITVECTOR_LIST.bv_ult s))
  | BO_BVslt s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) Typ.Tbool
      (Obj.magic (BITVECTOR_LIST.bv_slt s))
  | BO_BVconcat (s1, s2) ->
    apply_binop t_i (Typ.TBV s1) (Typ.TBV s2) (Typ.TBV (N.add s1 s2))
      (Obj.magic (BITVECTOR_LIST.bv_concat s1 s2))
  | BO_BVshl s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_shl s))
  | BO_BVshr s ->
    apply_binop t_i (Typ.TBV s) (Typ.TBV s) (Typ.TBV s)
      (Obj.magic (BITVECTOR_LIST.bv_shr s))
  | BO_select (ti, te) ->
    apply_binop t_i (Typ.TFArray (ti, te)) ti te
      (Obj.magic
        (select
          (ord_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)))
          (comp_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)))
          (inh_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 te)))))
  | BO_diffarray (ti, te) ->
    apply_binop t_i (Typ.TFArray (ti, te)) (Typ.TFArray (ti, te)) ti
      (Obj.magic
        (diff
          (eqbToDecType
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)).eqb1)
          (ord_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)))
          (comp_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)))
          (eqbToDecType
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 te)).eqb1)
          (projT2
            (let rec interp_compdec_aux0 = function
             | Typ.TFArray (ti0, te0) ->
               ExistT (__,
                 (fArray_compdec (projT2 (Obj.magic interp_compdec_aux0 ti0))
                   (projT2 (Obj.magic interp_compdec_aux0 te0))))
             | Typ.Tindex i ->
               ExistT (__, (Obj.magic (te_compdec (get t_i i))))
             | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
             | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
             | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
             | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
             in interp_compdec_aux0 te)).ordered
          (comp_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 te)))
          (projT2
            (let rec interp_compdec_aux0 = function
             | Typ.TFArray (ti0, te0) ->
               ExistT (__,
                 (fArray_compdec (projT2 (Obj.magic interp_compdec_aux0 ti0))
                   (projT2 (Obj.magic interp_compdec_aux0 te0))))
             | Typ.Tindex i ->
               ExistT (__, (Obj.magic (te_compdec (get t_i i))))
             | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
             | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
             | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
             | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
             in interp_compdec_aux0 ti)).inh
          (inh_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 te)))))
  
  (** val interp_top :
      typ_compdec array -> terop -> bval -> bval -> bval -> (Typ.coq_type,
      Typ.interp) coq_val **)
  
  let interp_top t_i = function
  | TO_store (ti, te) ->
    apply_terop t_i (Typ.TFArray (ti, te)) ti te (Typ.TFArray (ti, te))
      (Obj.magic
        (store
          (eqbToDecType
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)).eqb1)
          (ord_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)))
          (comp_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 ti)))
          (projT2
            (let rec interp_compdec_aux0 = function
             | Typ.TFArray (ti0, te0) ->
               ExistT (__,
                 (fArray_compdec (projT2 (Obj.magic interp_compdec_aux0 ti0))
                   (projT2 (Obj.magic interp_compdec_aux0 te0))))
             | Typ.Tindex i ->
               ExistT (__, (Obj.magic (te_compdec (get t_i i))))
             | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
             | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
             | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
             | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
             in interp_compdec_aux0 te)).ordered
          (comp_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 te)))
          (inh_of_compdec
            (projT2
              (let rec interp_compdec_aux0 = function
               | Typ.TFArray (ti0, te0) ->
                 ExistT (__,
                   (fArray_compdec
                     (projT2 (Obj.magic interp_compdec_aux0 ti0))
                     (projT2 (Obj.magic interp_compdec_aux0 te0))))
               | Typ.Tindex i ->
                 ExistT (__, (Obj.magic (te_compdec (get t_i i))))
               | Typ.TZ -> ExistT (__, (Obj.magic z_compdec))
               | Typ.Tbool -> ExistT (__, (Obj.magic bool_compdec))
               | Typ.Tpositive -> ExistT (__, (Obj.magic positive_compdec))
               | Typ.TBV n0 -> ExistT (__, (Obj.magic (bV_compdec n0)))
               in interp_compdec_aux0 te)))))
  
  (** val compute_interp :
      typ_compdec array -> (int -> bval) -> Typ.coq_type -> Typ.interp list
      -> int list -> Typ.interp list option **)
  
  let rec compute_interp t_i interp_hatom0 ty0 acc = function
  | Nil -> Some acc
  | Cons (a, q) ->
    let { v_type = ta; v_val = va } = interp_hatom0 a in
    (match Typ.cast ta ty0 with
     | Typ.Cast ka ->
       compute_interp t_i interp_hatom0 ty0 (Cons ((ka __ va), acc)) q
     | Typ.NoCast -> None)
  
  (** val interp_aux :
      typ_compdec array -> tval array -> (int -> bval) -> atom -> bval **)
  
  let interp_aux t_i t_func interp_hatom0 = function
  | Acop o -> interp_cop t_i o
  | Auop (o, a0) -> interp_uop t_i o (interp_hatom0 a0)
  | Abop (o, a1, a2) ->
    interp_bop t_i o (interp_hatom0 a1) (interp_hatom0 a2)
  | Atop (o, a1, a2, a3) ->
    interp_top t_i o (interp_hatom0 a1) (interp_hatom0 a2) (interp_hatom0 a3)
  | Anop (n0, a0) ->
    (match compute_interp t_i interp_hatom0 n0 Nil a0 with
     | Some l ->
       coq_Bval t_i Typ.Tbool
         (Obj.magic (distinct (Typ.i_eqb t_i n0) (rev0 l)))
     | None -> bvtrue t_i)
  | Aapp (f, args) ->
    let { v_type = tf; v_val = f0 } = get t_func f in
    let lv = map interp_hatom0 args in apply_func t_i (fst tf) (snd tf) f0 lv
  
  (** val interp_bool : typ_compdec array -> bval -> bool **)
  
  let interp_bool t_i v =
    let { v_type = t0; v_val = v0 } = v in
    (match Typ.cast t0 Typ.Tbool with
     | Typ.Cast k -> Obj.magic k __ v0
     | Typ.NoCast -> true)
  
  (** val interp_bv :
      typ_compdec array -> bval -> n -> BITVECTOR_LIST.bitvector **)
  
  let interp_bv t_i v s =
    let { v_type = t0; v_val = v0 } = v in
    (match Typ.cast t0 (Typ.TBV s) with
     | Typ.Cast k -> Obj.magic k __ v0
     | Typ.NoCast -> BITVECTOR_LIST.zeros s)
  
  (** val t_interp :
      typ_compdec array -> tval array -> atom array -> bval array **)
  
  let t_interp t_i t_func t_atom =
    foldi_left (fun i t_a a -> set t_a i (interp_aux t_i t_func (get t_a) a))
      (make (length0 t_atom) (interp_cop t_i CO_xH)) t_atom
  
  (** val lt_atom : int -> atom -> bool **)
  
  let lt_atom i = function
  | Acop c -> true
  | Auop (u, h) -> ltb0 h i
  | Abop (b, h1, h2) -> if ltb0 h1 i then ltb0 h2 i else false
  | Atop (t0, h1, h2, h3) ->
    if if ltb0 h1 i then ltb0 h2 i else false then ltb0 h3 i else false
  | Anop (n0, ha) -> forallb (fun h -> ltb0 h i) ha
  | Aapp (f, args) -> forallb (fun h -> ltb0 h i) args
  
  (** val wf : atom array -> bool **)
  
  let wf t_atom =
    forallbi lt_atom t_atom
  
  (** val get_type' :
      typ_compdec array -> bval array -> int -> Typ.coq_type **)
  
  let get_type' t_i t_interp' i =
    (get t_interp' i).v_type
  
  (** val get_type :
      typ_compdec array -> tval array -> atom array -> int -> Typ.coq_type **)
  
  let get_type t_i t_func t_atom =
    get_type' t_i (t_interp t_i t_func t_atom)
  
  (** val wt : typ_compdec array -> tval array -> atom array -> bool **)
  
  let wt t_i t_func t_atom =
    let t_interp0 = t_interp t_i t_func t_atom in
    let get_type0 = get_type' t_i t_interp0 in
    forallbi (fun i h -> check_aux t_i t_func get_type0 h (get_type0 i))
      t_atom
  
  (** val interp_hatom :
      typ_compdec array -> tval array -> atom array -> int -> bval **)
  
  let interp_hatom t_i t_func t_atom =
    let t_a = t_interp t_i t_func t_atom in get t_a
  
  (** val interp :
      typ_compdec array -> tval array -> atom array -> atom -> bval **)
  
  let interp t_i t_func t_atom =
    interp_aux t_i t_func (interp_hatom t_i t_func t_atom)
  
  (** val interp_form_hatom :
      typ_compdec array -> tval array -> atom array -> int -> bool **)
  
  let interp_form_hatom t_i t_func t_atom =
    let interp0 = interp_hatom t_i t_func t_atom in
    (fun a -> interp_bool t_i (interp0 a))
  
  (** val interp_form_hatom_bv :
      typ_compdec array -> tval array -> atom array -> int -> n ->
      BITVECTOR_LIST.bitvector **)
  
  let interp_form_hatom_bv t_i t_func t_atom =
    let interp0 = interp_hatom t_i t_func t_atom in
    (fun a s -> interp_bv t_i (interp0 a) s)
  
  (** val check_atom : atom array -> bool **)
  
  let check_atom t_atom =
    match default t_atom with
    | Acop c ->
      (match c with
       | CO_xH -> wf t_atom
       | _ -> false)
    | _ -> false
 end

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

(** val build_positive_atom_aux :
    (int -> positive option) -> Atom.atom -> positive option **)

let build_positive_atom_aux build_positive0 = function
| Atom.Acop c ->
  (match c with
   | Atom.CO_xH -> Some XH
   | _ -> None)
| Atom.Auop (u, a0) ->
  (match u with
   | Atom.UO_xO -> option_map (fun x -> XO x) (build_positive0 a0)
   | Atom.UO_xI -> option_map (fun x -> XI x) (build_positive0 a0)
   | _ -> None)
| _ -> None

(** val build_positive : Atom.atom array -> int -> positive option **)

let build_positive t_atom =
  foldi_down_cont (fun i cont h ->
    build_positive_atom_aux cont (get t_atom h)) (length0 t_atom)
    (Uint63.of_int (0)) (fun x -> None)

(** val build_z_atom_aux : Atom.atom array -> Atom.atom -> z option **)

let build_z_atom_aux t_atom = function
| Atom.Acop c ->
  (match c with
   | Atom.CO_Z0 -> Some Z0
   | _ -> None)
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
    build_pexpr_atom_aux t_atom cont vm (get t_atom h)) (length0 t_atom)
    (Uint63.of_int (0)) (fun vm x -> vm,(PEc Z0))

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
  fold (fun f' -> N (N f')) (Uint63.of_int (1)) i f

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
  let n0 = length0 args in
  if eqb0 n0 (Uint63.of_int (0))
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
         | None -> None) (Uint63.of_int (1)) (sub0 n0 (Uint63.of_int (1)))
         (let l = get args (Uint63.of_int (0)) in
          match build_var0 vm (Lit.blit l) with
          | Some p ->
            let vm',f0 = p in
            if Lit.is_pos l then Some (vm',f0) else Some (vm',(N f0))
          | None -> None)
| Form.For args ->
  let n0 = length0 args in
  if eqb0 n0 (Uint63.of_int (0))
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
         | None -> None) (Uint63.of_int (1)) (sub0 n0 (Uint63.of_int (1)))
         (let l = get args (Uint63.of_int (0)) in
          match build_var0 vm (Lit.blit l) with
          | Some p ->
            let vm',f0 = p in
            if Lit.is_pos l then Some (vm',f0) else Some (vm',(N f0))
          | None -> None)
| Form.Fimp args ->
  let n0 = length0 args in
  if eqb0 n0 (Uint63.of_int (0))
  then Some (vm,TT)
  else if leb0 n0 (Uint63.of_int (1))
       then let l = get args (Uint63.of_int (0)) in
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
              | None -> None) (sub0 n0 (Uint63.of_int (2)))
              (Uint63.of_int (0))
              (let l = get args (sub0 n0 (Uint63.of_int (1))) in
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
| Form.FbbT (i, l) -> None

(** val build_var :
    Form.form array -> Atom.atom array -> vmap -> int -> (vmap*z formula
    bFormula) option **)

let build_var t_form t_atom =
  foldi_down_cont (fun i cont vm h ->
    build_hform t_atom cont vm (get t_form h)) (length0 t_form)
    (Uint63.of_int (0)) (fun x x0 -> None)

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
    if eqb0 (length0 a) (Uint63.of_int (3))
    then let a_eq_b = get a (Uint63.of_int (0)) in
         let not_a_le_b = get a (Uint63.of_int (1)) in
         let not_b_le_a = get a (Uint63.of_int (2)) in
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
           | _ -> false)
        | Atom.BO_BVand s1 ->
          (match o2 with
           | Atom.BO_BVand s2 ->
             if if N.eqb s1 s2 then check_hatom0 a1 b1 else false
             then check_hatom0 a2 b2
             else false
           | _ -> false)
        | Atom.BO_BVor s1 ->
          (match o2 with
           | Atom.BO_BVor s2 ->
             if if N.eqb s1 s2 then check_hatom0 a1 b1 else false
             then check_hatom0 a2 b2
             else false
           | _ -> false)
        | _ -> false)
     | _ -> false)
  | Atom.Atop (t0, i, i0, i1) -> false
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
    (length0 t_atom) (Uint63.of_int (0)) (fun h3 h4 -> false) h1 h2

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
  foldi_cont (fun x -> flatten_op_body get_op) (Uint63.of_int (0)) max0
    (fun largs l -> Cons (l, largs))

(** val flatten_and : Form.form array -> int array -> int list **)

let flatten_and t_form t0 =
  fold_left (flatten_op_lit (get_and t_form) (length0 t_form)) Nil t0

(** val flatten_or : Form.form array -> int array -> int list **)

let flatten_or t_form t0 =
  fold_left (flatten_op_lit (get_or t_form) (length0 t_form)) Nil t0

(** val check_flatten_body :
    Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> (int
    -> int -> bool) -> int -> int -> bool **)

let check_flatten_body t_form check_atom0 check_neg_atom frec l lf =
  let l0 = remove_not t_form l in
  let lf0 = remove_not t_form lf in
  if eqb0 l0 lf0
  then true
  else if eqb0 (land0 (Uint63.of_int (1)) (lxor0 l0 lf0)) (Uint63.of_int (0))
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
                  if eqb0 (length0 args1) (length0 args2)
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
                | _ -> false)
             | _ -> false)
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
    (Uint63.of_int (0)) (length0 t_form) (fun x x0 -> false) l lf

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

let check_diseqs t_form t_atom ty0 dist diseq =
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
                    if if if if Typ.eqb ty0 a0
                             then negb (eqb0 h1 h2)
                             else false
                          then check_in h1 dist
                          else false
                       then check_in h2 dist
                       else false
                    then Some (h1,h2)
                    else None
                  | _ -> None)
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
       if eqb0 (length0 a1) (length0 a2)
       then forallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.For a1 ->
    (match b with
     | Form.For a2 ->
       if eqb0 (length0 a1) (length0 a2)
       then forallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.Fimp a1 ->
    (match b with
     | Form.Fimp a2 ->
       if eqb0 (length0 a1) (length0 a2)
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
  | Form.FbbT (i, l) -> false

(** val check_hform :
    Form.form array -> Atom.atom array -> int -> int -> bool **)

let check_hform t_form t_atom h1 h2 =
  foldi_down_cont (fun x cont h3 h4 ->
    if eqb0 h3 h4
    then true
    else check_form_aux t_form t_atom cont (get t_form h3) (get t_form h4))
    (length0 t_form) (Uint63.of_int (0)) (fun h3 h4 -> false) h1 h2

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

(** val forallb3 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb3 p xs ys =
  match xs with
  | Nil ->
    (match ys with
     | Nil -> true
     | Cons (b, l) -> false)
  | Cons (x, xs0) ->
    (match ys with
     | Nil -> false
     | Cons (y, ys0) -> if p x y then forallb3 p xs0 ys0 else false)

(** val check_hole : S.t -> int list -> C.t list -> C.t -> C.t **)

let check_hole s prem_id prem concl =
  if forallb3 (fun id c ->
       forallb3 (fun i j -> eqb0 i j) (S.get s id) (S.sort_uniq c)) prem_id
       prem
  then concl
  else C._true

(** val or_of_imp : int array -> int array **)

let or_of_imp args =
  let last = sub0 (length0 args) (Uint63.of_int (1)) in
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
     if ltb0 i (length0 args)
     then Cons ((Lit.nlit x), (Cons ((get args i), Nil)))
     else C._true
   | Form.For args ->
     if ltb0 i (length0 args)
     then Cons ((Lit.lit x), (Cons ((Lit.neg (get args i)), Nil)))
     else C._true
   | Form.Fimp args ->
     let len = length0 args in
     if ltb0 i len
     then if eqb0 i (sub0 len (Uint63.of_int (1)))
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
          if if ltb0 i (length0 args) then Lit.is_pos l else false
          then Cons ((get args i), Nil)
          else C._true
        | Form.For args ->
          if if ltb0 i (length0 args) then negb (Lit.is_pos l) else false
          then Cons ((Lit.neg (get args i)), Nil)
          else C._true
        | Form.Fimp args ->
          let len = length0 args in
          if if ltb0 i len then negb (Lit.is_pos l) else false
          then if eqb0 i (sub0 len (Uint63.of_int (1)))
               then Cons ((Lit.neg (get args i)), Nil)
               else Cons ((get args i), Nil)
          else C._true
        | _ -> C._true)
     | Cons (i0, l1) -> C._true)

(** val check_bbc : Form.form array -> bool list -> int list -> bool **)

let rec check_bbc t_form a_bv bs =
  match a_bv with
  | Nil ->
    (match bs with
     | Nil -> true
     | Cons (i, l) -> false)
  | Cons (v, a_bv0) ->
    (match bs with
     | Nil -> false
     | Cons (b, bs0) ->
       if Lit.is_pos b
       then (match get t_form (Lit.blit b) with
             | Form.Ftrue -> if v then check_bbc t_form a_bv0 bs0 else false
             | Form.Ffalse -> if v then false else check_bbc t_form a_bv0 bs0
             | _ -> false)
       else false)

(** val check_bbConst : Atom.atom array -> Form.form array -> int -> C.t **)

let check_bbConst t_atom t_form lres =
  if Lit.is_pos lres
  then (match get t_form (Lit.blit lres) with
        | Form.FbbT (a, bs) ->
          (match get t_atom a with
           | Atom.Acop c ->
             (match c with
              | Atom.CO_BV (bv0, n0) ->
                if if check_bbc t_form bv0 bs
                   then N.eqb (N.of_nat (length bv0)) n0
                   else false
                then Cons (lres, Nil)
                else C._true
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val check_bb :
    Atom.atom array -> Form.form array -> int -> int list -> nat -> nat ->
    bool **)

let rec check_bb t_atom t_form a bs i n0 =
  match bs with
  | Nil -> nat_eqb i n0
  | Cons (b, bs0) ->
    if Lit.is_pos b
    then (match get t_form (Lit.blit b) with
          | Form.Fatom a' ->
            (match get t_atom a' with
             | Atom.Auop (u, a'0) ->
               (match u with
                | Atom.UO_BVbitOf (n1, p) ->
                  if if if eqb0 a a'0 then nat_eqb i p else false
                     then nat_eqb n0 (N.to_nat n1)
                     else false
                  then check_bb t_atom t_form a bs0 (S i) n0
                  else false
                | _ -> false)
             | _ -> false)
          | _ -> false)
    else false

(** val check_bbVar : Atom.atom array -> Form.form array -> int -> C.t **)

let check_bbVar t_atom t_form lres =
  if Lit.is_pos lres
  then (match get t_form (Lit.blit lres) with
        | Form.FbbT (a, bs) ->
          if check_bb t_atom t_form a bs O (length bs)
          then Cons (lres, Nil)
          else C._true
        | _ -> C._true)
  else C._true

(** val check_not : int list -> int list -> bool **)

let rec check_not bs br =
  match bs with
  | Nil ->
    (match br with
     | Nil -> true
     | Cons (i, l) -> false)
  | Cons (b, bs0) ->
    (match br with
     | Nil -> false
     | Cons (r, br0) ->
       if eqb0 r (Lit.neg b) then check_not bs0 br0 else false)

(** val check_bbNot :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> C.t **)

let check_bbNot t_atom t_form s pos lres =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       if if Lit.is_pos l then Lit.is_pos lres else false
       then (match get t_form (Lit.blit l) with
             | Form.FbbT (a, bs) ->
               (match get t_form (Lit.blit lres) with
                | Form.FbbT (r, br) ->
                  (match get t_atom r with
                   | Atom.Auop (u, a') ->
                     (match u with
                      | Atom.UO_BVnot n0 ->
                        if if if eqb0 a a' then check_not bs br else false
                           then N.eqb (N.of_nat (length bs)) n0
                           else false
                        then Cons (lres, Nil)
                        else C._true
                      | _ -> C._true)
                   | _ -> C._true)
                | _ -> C._true)
             | _ -> C._true)
       else C._true
     | Cons (i, l1) -> C._true)

(** val check_symopp :
    Form.form array -> int list -> int list -> int list -> Atom.binop -> bool **)

let rec check_symopp t_form bs1 bs2 bsres bvop =
  match bs1 with
  | Nil ->
    (match bs2 with
     | Nil ->
       (match bsres with
        | Nil -> true
        | Cons (i, l) -> false)
     | Cons (i, l) -> false)
  | Cons (b1, bs3) ->
    (match bs2 with
     | Nil -> false
     | Cons (b2, bs4) ->
       (match bsres with
        | Nil -> false
        | Cons (bres, bsres0) ->
          if Lit.is_pos bres
          then (match get t_form (Lit.blit bres) with
                | Form.Fand args ->
                  (match bvop with
                   | Atom.BO_BVand n0 ->
                     let ires =
                       if eqb0 (length0 args) (Uint63.of_int (2))
                       then let a1 = get args (Uint63.of_int (0)) in
                            let a2 = get args (Uint63.of_int (1)) in
                            if if eqb0 a1 b1 then eqb0 a2 b2 else false
                            then true
                            else if eqb0 a1 b2 then eqb0 a2 b1 else false
                       else false
                     in
                     let bvop0 = Atom.BO_BVand (N.sub n0 (Npos XH)) in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop0
                     else false
                   | _ ->
                     let ires = false in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop
                     else false)
                | Form.For args ->
                  (match bvop with
                   | Atom.BO_BVor n0 ->
                     let ires =
                       if eqb0 (length0 args) (Uint63.of_int (2))
                       then let a1 = get args (Uint63.of_int (0)) in
                            let a2 = get args (Uint63.of_int (1)) in
                            if if eqb0 a1 b1 then eqb0 a2 b2 else false
                            then true
                            else if eqb0 a1 b2 then eqb0 a2 b1 else false
                       else false
                     in
                     let bvop0 = Atom.BO_BVor (N.sub n0 (Npos XH)) in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop0
                     else false
                   | _ ->
                     let ires = false in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop
                     else false)
                | Form.Fxor (a1, a2) ->
                  (match bvop with
                   | Atom.BO_BVxor n0 ->
                     let ires =
                       if if eqb0 a1 b1 then eqb0 a2 b2 else false
                       then true
                       else if eqb0 a1 b2 then eqb0 a2 b1 else false
                     in
                     let bvop0 = Atom.BO_BVxor (N.sub n0 (Npos XH)) in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop0
                     else false
                   | _ ->
                     let ires = false in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop
                     else false)
                | Form.Fiff (a1, a2) ->
                  (match bvop with
                   | Atom.BO_eq t0 ->
                     (match t0 with
                      | Typ.TBV n0 ->
                        let ires =
                          if if eqb0 a1 b1 then eqb0 a2 b2 else false
                          then true
                          else if eqb0 a1 b2 then eqb0 a2 b1 else false
                        in
                        let bvop0 = Atom.BO_eq (Typ.TBV n0) in
                        if ires
                        then check_symopp t_form bs3 bs4 bsres0 bvop0
                        else false
                      | _ ->
                        let ires = false in
                        if ires
                        then check_symopp t_form bs3 bs4 bsres0 bvop
                        else false)
                   | _ ->
                     let ires = false in
                     if ires
                     then check_symopp t_form bs3 bs4 bsres0 bvop
                     else false)
                | _ ->
                  let ires = false in
                  if ires
                  then check_symopp t_form bs3 bs4 bsres0 bvop
                  else false)
          else false))

(** val check_bbOp :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbOp t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.FbbT (a, bsres) ->
                           (match get t_atom a with
                            | Atom.Abop (b, a1', a2') ->
                              (match b with
                               | Atom.BO_BVand n0 ->
                                 if if if if if eqb0 a1 a1'
                                             then eqb0 a2 a2'
                                             else false
                                          then true
                                          else if eqb0 a1 a2'
                                               then eqb0 a2 a1'
                                               else false
                                       then check_symopp t_form bs1 bs2 bsres
                                              (Atom.BO_BVand n0)
                                       else false
                                    then N.eqb (N.of_nat (length bs1)) n0
                                    else false
                                 then Cons (lres, Nil)
                                 else C._true
                               | Atom.BO_BVor n0 ->
                                 if if if if if eqb0 a1 a1'
                                             then eqb0 a2 a2'
                                             else false
                                          then true
                                          else if eqb0 a1 a2'
                                               then eqb0 a2 a1'
                                               else false
                                       then check_symopp t_form bs1 bs2 bsres
                                              (Atom.BO_BVor n0)
                                       else false
                                    then N.eqb (N.of_nat (length bs1)) n0
                                    else false
                                 then Cons (lres, Nil)
                                 else C._true
                               | Atom.BO_BVxor n0 ->
                                 if if if if if eqb0 a1 a1'
                                             then eqb0 a2 a2'
                                             else false
                                          then true
                                          else if eqb0 a1 a2'
                                               then eqb0 a2 a1'
                                               else false
                                       then check_symopp t_form bs1 bs2 bsres
                                              (Atom.BO_BVxor n0)
                                       else false
                                    then N.eqb (N.of_nat (length bs1)) n0
                                    else false
                                 then Cons (lres, Nil)
                                 else C._true
                               | _ -> C._true)
                            | _ -> C._true)
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val check_eq :
    Form.form array -> int list -> int list -> int list -> bool **)

let rec check_eq t_form bs1 bs2 bsres =
  match bs1 with
  | Nil ->
    (match bs2 with
     | Nil ->
       (match bsres with
        | Nil -> true
        | Cons (i, l) -> false)
     | Cons (i, l) -> false)
  | Cons (b1, bs3) ->
    (match bs2 with
     | Nil -> false
     | Cons (b2, bs4) ->
       (match bsres with
        | Nil -> false
        | Cons (bres, bsres0) ->
          (match bs3 with
           | Nil ->
             if Lit.is_pos bres
             then let ires =
                    match get t_form (Lit.blit bres) with
                    | Form.Fiff (a1, a2) ->
                      if if eqb0 a1 b1 then eqb0 a2 b2 else false
                      then true
                      else if eqb0 a1 b2 then eqb0 a2 b1 else false
                    | _ -> false
                  in
                  if ires then check_eq t_form bs3 bs4 bsres0 else false
             else false
           | Cons (i, l) ->
             (match bs4 with
              | Nil ->
                if Lit.is_pos bres
                then let ires =
                       match get t_form (Lit.blit bres) with
                       | Form.Fiff (a1, a2) ->
                         if if eqb0 a1 b1 then eqb0 a2 b2 else false
                         then true
                         else if eqb0 a1 b2 then eqb0 a2 b1 else false
                       | _ -> false
                     in
                     if ires then check_eq t_form bs3 bs4 bsres0 else false
                else false
              | Cons (i0, l0) ->
                (match bsres0 with
                 | Nil ->
                   if Lit.is_pos bres
                   then (match get t_form (Lit.blit bres) with
                         | Form.Fand args ->
                           (match to_list args with
                            | Nil -> false
                            | Cons (bres0, bsres1) ->
                              if Lit.is_pos bres0
                              then let ires =
                                     match get t_form (Lit.blit bres0) with
                                     | Form.Fiff (a1, a2) ->
                                       if if eqb0 a1 b1
                                          then eqb0 a2 b2
                                          else false
                                       then true
                                       else if eqb0 a1 b2
                                            then eqb0 a2 b1
                                            else false
                                     | _ -> false
                                   in
                                   if ires
                                   then check_eq t_form bs3 bs4 bsres1
                                   else false
                              else false)
                         | _ -> false)
                   else false
                 | Cons (i1, l1) ->
                   if Lit.is_pos bres
                   then let ires =
                          match get t_form (Lit.blit bres) with
                          | Form.Fiff (a1, a2) ->
                            if if eqb0 a1 b1 then eqb0 a2 b2 else false
                            then true
                            else if eqb0 a1 b2 then eqb0 a2 b1 else false
                          | _ -> false
                        in
                        if ires
                        then check_eq t_form bs3 bs4 bsres0
                        else false
                   else false)))))

(** val check_bbEq :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbEq t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.Fiff (leq, lbb) ->
                           if eqb (Lit.is_pos leq) (Lit.is_pos lbb)
                           then (match get t_form (Lit.blit leq) with
                                 | Form.Fatom a ->
                                   (match get t_atom a with
                                    | Atom.Abop (b, a1', a2') ->
                                      (match b with
                                       | Atom.BO_eq t0 ->
                                         (match t0 with
                                          | Typ.TBV n0 ->
                                            if if if if if eqb0 a1 a1'
                                                        then eqb0 a2 a2'
                                                        else false
                                                     then true
                                                     else if eqb0 a1 a2'
                                                          then eqb0 a2 a1'
                                                          else false
                                                  then check_eq t_form bs1
                                                         bs2 (Cons (lbb,
                                                         Nil))
                                                  else false
                                               then N.eqb
                                                      (N.of_nat (length bs1))
                                                      n0
                                               else false
                                            then Cons (lres, Nil)
                                            else C._true
                                          | _ -> C._true)
                                       | _ -> C._true)
                                    | _ -> C._true)
                                 | _ -> C._true)
                           else C._true
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

type carry =
| Clit of int
| Cand of carry * carry
| Cxor of carry * carry
| Cor of carry * carry
| Ciff of carry * carry

(** val eq_carry_lit : Form.form array -> carry -> int -> bool **)

let rec eq_carry_lit t_form carry0 c =
  if Lit.is_pos c
  then (match carry0 with
        | Clit l -> eqb0 l c
        | Cand (c1, c2) ->
          (match get t_form (Lit.blit c) with
           | Form.Fand args ->
             if eqb0 (length0 args) (Uint63.of_int (2))
             then if eq_carry_lit t_form c1 (get args (Uint63.of_int (0)))
                  then eq_carry_lit t_form c2 (get args (Uint63.of_int (1)))
                  else false
             else false
           | _ -> false)
        | Cxor (c1, c2) ->
          (match get t_form (Lit.blit c) with
           | Form.Fxor (a1, a2) ->
             if eq_carry_lit t_form c1 a1
             then eq_carry_lit t_form c2 a2
             else false
           | _ -> false)
        | Cor (c1, c2) ->
          (match get t_form (Lit.blit c) with
           | Form.For args ->
             if eqb0 (length0 args) (Uint63.of_int (2))
             then if eq_carry_lit t_form c1 (get args (Uint63.of_int (0)))
                  then eq_carry_lit t_form c2 (get args (Uint63.of_int (1)))
                  else false
             else false
           | _ -> false)
        | Ciff (c1, c2) ->
          (match get t_form (Lit.blit c) with
           | Form.Fiff (a1, a2) ->
             if eq_carry_lit t_form c1 a1
             then eq_carry_lit t_form c2 a2
             else false
           | _ -> false))
  else (match carry0 with
        | Clit l -> eqb0 l c
        | _ -> false)

(** val check_add :
    Form.form array -> int list -> int list -> int list -> carry -> bool **)

let rec check_add t_form bs1 bs2 bsres carry0 =
  match bs1 with
  | Nil ->
    (match bs2 with
     | Nil ->
       (match bsres with
        | Nil -> true
        | Cons (i, l) -> false)
     | Cons (i, l) -> false)
  | Cons (b1, bs3) ->
    (match bs2 with
     | Nil -> false
     | Cons (b2, bs4) ->
       (match bsres with
        | Nil -> false
        | Cons (bres, bsres0) ->
          if Lit.is_pos bres
          then (match get t_form (Lit.blit bres) with
                | Form.Fxor (xab, c) ->
                  if Lit.is_pos xab
                  then (match get t_form (Lit.blit xab) with
                        | Form.Fxor (a1, a2) ->
                          let carry' = Cor ((Cand ((Clit b1), (Clit b2))),
                            (Cand ((Cxor ((Clit b1), (Clit b2))), carry0)))
                          in
                          if if if if eqb0 a1 b1 then eqb0 a2 b2 else false
                                then true
                                else if eqb0 a1 b2 then eqb0 a2 b1 else false
                             then eq_carry_lit t_form carry0 c
                             else false
                          then check_add t_form bs3 bs4 bsres0 carry'
                          else false
                        | _ -> false)
                  else false
                | _ -> false)
          else false))

(** val check_bbAdd :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbAdd t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.FbbT (a, bsres) ->
                           (match get t_atom a with
                            | Atom.Abop (b, a1', a2') ->
                              (match b with
                               | Atom.BO_BVadd n0 ->
                                 if if if if if eqb0 a1 a1'
                                             then eqb0 a2 a2'
                                             else false
                                          then true
                                          else if eqb0 a1 a2'
                                               then eqb0 a2 a1'
                                               else false
                                       then check_add t_form bs1 bs2 bsres
                                              (Clit Lit._false)
                                       else false
                                    then N.eqb (N.of_nat (length bs1)) n0
                                    else false
                                 then Cons (lres, Nil)
                                 else C._true
                               | _ -> C._true)
                            | _ -> C._true)
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val check_neg : Form.form array -> int list -> int list -> bool **)

let check_neg t_form bs br =
  let z0 = map (fun x -> Lit._false) bs in
  let nbs = map (fun l -> Lit.neg l) bs in
  check_add t_form nbs z0 br (Clit Lit._true)

(** val check_bbNeg :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> C.t **)

let check_bbNeg t_atom t_form s pos lres =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       if if Lit.is_pos l then Lit.is_pos lres else false
       then (match get t_form (Lit.blit l) with
             | Form.FbbT (a, bs) ->
               (match get t_form (Lit.blit lres) with
                | Form.FbbT (r, br) ->
                  (match get t_atom r with
                   | Atom.Auop (u, a') ->
                     (match u with
                      | Atom.UO_BVneg n0 ->
                        if if if eqb0 a a'
                              then check_neg t_form bs br
                              else false
                           then N.eqb (N.of_nat (length bs)) n0
                           else false
                        then Cons (lres, Nil)
                        else C._true
                      | _ -> C._true)
                   | _ -> C._true)
                | _ -> C._true)
             | _ -> C._true)
       else C._true
     | Cons (i, l1) -> C._true)

(** val and_with_bit : int list -> int -> carry list **)

let rec and_with_bit a bt =
  match a with
  | Nil -> Nil
  | Cons (ai, a') ->
    Cons ((Cand ((Clit bt), (Clit ai))), (and_with_bit a' bt))

(** val mult_step_k_h :
    carry list -> carry list -> carry -> z -> carry list **)

let rec mult_step_k_h a b c k =
  match a with
  | Nil -> Nil
  | Cons (ai, a') ->
    (match b with
     | Nil -> Cons (ai, (mult_step_k_h a' b c k))
     | Cons (bi, b') ->
       if Z.ltb (Z.sub k (Zpos XH)) Z0
       then let carry_out = Cor ((Cand (ai, bi)), (Cand ((Cxor (ai, bi)),
              c)))
            in
            let curr = Cxor ((Cxor (ai, bi)), c) in
            Cons (curr, (mult_step_k_h a' b' carry_out (Z.sub k (Zpos XH))))
       else Cons (ai, (mult_step_k_h a' b c (Z.sub k (Zpos XH)))))

(** val mult_step :
    int list -> int list -> carry list -> nat -> nat -> carry list **)

let rec mult_step a b res k k' =
  let ak = firstn (S k') a in
  let b' = and_with_bit ak (nth k b Lit._false) in
  let res' = mult_step_k_h res b' (Clit Lit._false) (Z.of_nat k) in
  (match k' with
   | O -> res'
   | S pk' -> mult_step a b res' (S k) pk')

(** val bblast_bvmult : int list -> int list -> nat -> carry list **)

let bblast_bvmult a b n0 =
  let res = and_with_bit a (nth O b Lit._false) in
  (match n0 with
   | O -> res
   | S n1 ->
     (match n1 with
      | O -> res
      | S k -> mult_step a b res (S O) k))

(** val check_mult :
    Form.form array -> int list -> int list -> int list -> bool **)

let check_mult t_form bs1 bs2 bsres =
  if nat_eqb (length bs1) (length bs2)
  then let bvm12 = bblast_bvmult bs1 bs2 (length bs1) in
       forallb2 (eq_carry_lit t_form) bvm12 bsres
  else false

(** val check_bbMult :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbMult t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.FbbT (a, bsres) ->
                           (match get t_atom a with
                            | Atom.Abop (b, a1', a2') ->
                              (match b with
                               | Atom.BO_BVmult n0 ->
                                 if if if if eqb0 a1 a1'
                                          then eqb0 a2 a2'
                                          else false
                                       then check_mult t_form bs1 bs2 bsres
                                       else false
                                    then N.eqb (N.of_nat (length bs1)) n0
                                    else false
                                 then Cons (lres, Nil)
                                 else C._true
                               | _ -> C._true)
                            | _ -> C._true)
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val ult_big_endian_lit_list : int list -> int list -> carry **)

let rec ult_big_endian_lit_list bs1 bs2 =
  match bs1 with
  | Nil -> Clit Lit._false
  | Cons (xi, x') ->
    (match x' with
     | Nil ->
       (match bs2 with
        | Nil -> Clit Lit._false
        | Cons (yi, y') ->
          (match y' with
           | Nil -> Cand ((Clit (Lit.neg xi)), (Clit yi))
           | Cons (i, l) ->
             Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
               (ult_big_endian_lit_list x' y'))), (Cand ((Clit (Lit.neg xi)),
               (Clit yi))))))
     | Cons (i, l) ->
       (match bs2 with
        | Nil -> Clit Lit._false
        | Cons (yi, y') ->
          Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
            (ult_big_endian_lit_list x' y'))), (Cand ((Clit (Lit.neg xi)),
            (Clit yi))))))

(** val ult_lit_list : int list -> int list -> carry **)

let ult_lit_list x y =
  ult_big_endian_lit_list (rev x) (rev y)

(** val check_ult :
    Form.form array -> int list -> int list -> int -> bool **)

let check_ult t_form bs1 bs2 bsres =
  if Lit.is_pos bsres
  then eq_carry_lit t_form (ult_lit_list bs1 bs2) bsres
  else false

(** val check_bbUlt :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbUlt t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.Fiff (llt, lbb) ->
                           if eqb (Lit.is_pos llt) (Lit.is_pos lbb)
                           then (match get t_form (Lit.blit llt) with
                                 | Form.Fatom a ->
                                   (match get t_atom a with
                                    | Atom.Abop (b, a1', a2') ->
                                      (match b with
                                       | Atom.BO_BVult n0 ->
                                         if if if if if eqb0 a1 a1'
                                                     then eqb0 a2 a2'
                                                     else false
                                                  then check_ult t_form bs1
                                                         bs2 lbb
                                                  else false
                                               then N.eqb
                                                      (N.of_nat (length bs1))
                                                      n0
                                               else false
                                            then N.eqb
                                                   (N.of_nat (length bs2)) n0
                                            else false
                                         then Cons (lres, Nil)
                                         else C._true
                                       | _ -> C._true)
                                    | _ -> C._true)
                                 | _ -> C._true)
                           else C._true
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val slt_big_endian_lit_list : int list -> int list -> carry **)

let slt_big_endian_lit_list x y =
  match x with
  | Nil -> Clit Lit._false
  | Cons (xi, x') ->
    (match x' with
     | Nil ->
       (match y with
        | Nil -> Clit Lit._false
        | Cons (yi, y') ->
          (match y' with
           | Nil -> Cand ((Clit xi), (Clit (Lit.neg yi)))
           | Cons (i, l) ->
             Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
               (ult_big_endian_lit_list x' y'))), (Cand ((Clit xi), (Clit
               (Lit.neg yi)))))))
     | Cons (i, l) ->
       (match y with
        | Nil -> Clit Lit._false
        | Cons (yi, y') ->
          Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
            (ult_big_endian_lit_list x' y'))), (Cand ((Clit xi), (Clit
            (Lit.neg yi)))))))

(** val slt_lit_list : int list -> int list -> carry **)

let slt_lit_list x y =
  slt_big_endian_lit_list (rev x) (rev y)

(** val check_slt :
    Form.form array -> int list -> int list -> int -> bool **)

let check_slt t_form bs1 bs2 bsres =
  if Lit.is_pos bsres
  then eq_carry_lit t_form (slt_lit_list bs1 bs2) bsres
  else false

(** val check_bbSlt :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbSlt t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.Fiff (llt, lbb) ->
                           if eqb (Lit.is_pos llt) (Lit.is_pos lbb)
                           then (match get t_form (Lit.blit llt) with
                                 | Form.Fatom a ->
                                   (match get t_atom a with
                                    | Atom.Abop (b, a1', a2') ->
                                      (match b with
                                       | Atom.BO_BVslt n0 ->
                                         if if if if if eqb0 a1 a1'
                                                     then eqb0 a2 a2'
                                                     else false
                                                  then check_slt t_form bs1
                                                         bs2 lbb
                                                  else false
                                               then N.eqb
                                                      (N.of_nat (length bs1))
                                                      n0
                                               else false
                                            then N.eqb
                                                   (N.of_nat (length bs2)) n0
                                            else false
                                         then Cons (lres, Nil)
                                         else C._true
                                       | _ -> C._true)
                                    | _ -> C._true)
                                 | _ -> C._true)
                           else C._true
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val lit_to_carry : int list -> carry list **)

let rec lit_to_carry = function
| Nil -> Nil
| Cons (xbs, xsbs) -> Cons ((Clit xbs), (lit_to_carry xsbs))

(** val check_concat :
    Form.form array -> int list -> int list -> int list -> bool **)

let check_concat t_form bs1 bs2 bsres =
  forallb2 (eq_carry_lit t_form) (lit_to_carry (app bs2 bs1)) bsres

(** val check_bbConcat :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbConcat t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.FbbT (a2, bs2) ->
                        (match get t_form (Lit.blit lres) with
                         | Form.FbbT (a, bsres) ->
                           (match get t_atom a with
                            | Atom.Abop (b, a1', a2') ->
                              (match b with
                               | Atom.BO_BVconcat (n0, m) ->
                                 if if if if if eqb0 a1 a1'
                                             then eqb0 a2 a2'
                                             else false
                                          then check_concat t_form bs1 bs2
                                                 bsres
                                          else false
                                       then N.eqb (N.of_nat (length bs1)) n0
                                       else false
                                    then N.eqb (N.of_nat (length bs2)) m
                                    else false
                                 then Cons (lres, Nil)
                                 else C._true
                               | _ -> C._true)
                            | _ -> C._true)
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val list_diseqb : bool list -> bool list -> bool **)

let rec list_diseqb a b =
  match a with
  | Nil ->
    (match b with
     | Nil -> false
     | Cons (b0, l) -> true)
  | Cons (xa, xsa) ->
    (match b with
     | Nil -> true
     | Cons (xb, xsb) ->
       if eqb xa false
       then if eqb xb false then list_diseqb xsa xsb else true
       else if eqb xb true then list_diseqb xsa xsb else true)

(** val check_bbDiseq : Atom.atom array -> Form.form array -> int -> C.t **)

let check_bbDiseq t_atom t_form lres =
  if negb (Lit.is_pos lres)
  then (match get t_form (Lit.blit lres) with
        | Form.Fatom f ->
          (match get t_atom f with
           | Atom.Abop (b0, a, b) ->
             (match b0 with
              | Atom.BO_eq t0 ->
                (match t0 with
                 | Typ.TBV n0 ->
                   (match get t_atom a with
                    | Atom.Acop c ->
                      (match c with
                       | Atom.CO_BV (bv1, n1) ->
                         (match get t_atom b with
                          | Atom.Acop c0 ->
                            (match c0 with
                             | Atom.CO_BV (bv2, n2) ->
                               if if if if if list_diseqb bv1 bv2
                                           then N.eqb (N.of_nat (length bv1))
                                                  n0
                                           else false
                                        then N.eqb (N.of_nat (length bv2)) n0
                                        else false
                                     then N.eqb n1 n0
                                     else false
                                  then N.eqb n2 n0
                                  else false
                               then Cons (lres, Nil)
                               else C._true
                             | _ -> C._true)
                          | _ -> C._true)
                       | _ -> C._true)
                    | _ -> C._true)
                 | _ -> C._true)
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val extract_lit : int list -> nat -> nat -> int list **)

let rec extract_lit x i j =
  match x with
  | Nil -> Nil
  | Cons (bx, x') ->
    (match i with
     | O ->
       (match j with
        | O -> Nil
        | S j' -> Cons (bx, (extract_lit x' i j')))
     | S i' ->
       (match j with
        | O -> Nil
        | S j' -> extract_lit x' i' j'))

(** val check_extract :
    Form.form array -> int list -> int list -> n -> n -> bool **)

let check_extract t_form bs bsres i j =
  if N.ltb (N.of_nat (length bs)) j
  then false
  else forallb2 (eq_carry_lit t_form)
         (lit_to_carry (extract_lit bs (N.to_nat i) (N.to_nat j))) bsres

(** val check_bbExtract :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> C.t **)

let check_bbExtract t_atom t_form s pos lres =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       if if Lit.is_pos l1 then Lit.is_pos lres else false
       then (match get t_form (Lit.blit l1) with
             | Form.FbbT (a1, bs) ->
               (match get t_form (Lit.blit lres) with
                | Form.FbbT (a, bsres) ->
                  (match get t_atom a with
                   | Atom.Auop (u, a1') ->
                     (match u with
                      | Atom.UO_BVextr (i, n0, n1) ->
                        if if if if eqb0 a1 a1'
                                 then check_extract t_form bs bsres i
                                        (N.add n0 i)
                                 else false
                              then N.eqb (N.of_nat (length bs)) n1
                              else false
                           then N.leb (N.add n0 i) n1
                           else false
                        then Cons (lres, Nil)
                        else C._true
                      | _ -> C._true)
                   | _ -> C._true)
                | _ -> C._true)
             | _ -> C._true)
       else C._true
     | Cons (i, l0) -> C._true)

(** val extend_lit : int list -> nat -> int -> int list **)

let rec extend_lit x i b =
  match i with
  | O -> x
  | S i' -> Cons (b, (extend_lit x i' b))

(** val zextend_lit : int list -> nat -> int list **)

let zextend_lit x i =
  extend_lit x i Lit._false

(** val check_zextend :
    Form.form array -> int list -> int list -> n -> bool **)

let check_zextend t_form bs bsres i =
  forallb2 (eq_carry_lit t_form) (lit_to_carry (zextend_lit bs (N.to_nat i)))
    bsres

(** val check_bbZextend :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> C.t **)

let check_bbZextend t_atom t_form s pos lres =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       if if Lit.is_pos l1 then Lit.is_pos lres else false
       then (match get t_form (Lit.blit l1) with
             | Form.FbbT (a1, bs) ->
               (match get t_form (Lit.blit lres) with
                | Form.FbbT (a, bsres) ->
                  (match get t_atom a with
                   | Atom.Auop (u, a1') ->
                     (match u with
                      | Atom.UO_BVzextn (n0, i) ->
                        if if if eqb0 a1 a1'
                              then check_zextend t_form bs bsres i
                              else false
                           then N.eqb (N.of_nat (length bs)) n0
                           else false
                        then Cons (lres, Nil)
                        else C._true
                      | _ -> C._true)
                   | _ -> C._true)
                | _ -> C._true)
             | _ -> C._true)
       else C._true
     | Cons (i, l0) -> C._true)

(** val mk_list_lit_false : nat -> int list **)

let rec mk_list_lit_false = function
| O -> Nil
| S t' -> Cons (Lit._false, (mk_list_lit_false t'))

(** val sextend_lit : int list -> nat -> int list **)

let sextend_lit x i =
  match x with
  | Nil -> mk_list_lit_false i
  | Cons (xb, x') -> extend_lit x i xb

(** val check_sextend :
    Form.form array -> int list -> int list -> n -> bool **)

let check_sextend t_form bs bsres i =
  forallb2 (eq_carry_lit t_form) (lit_to_carry (sextend_lit bs (N.to_nat i)))
    bsres

(** val check_bbSextend :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> C.t **)

let check_bbSextend t_atom t_form s pos lres =
  match S.get s pos with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       if if Lit.is_pos l1 then Lit.is_pos lres else false
       then (match get t_form (Lit.blit l1) with
             | Form.FbbT (a1, bs) ->
               (match get t_form (Lit.blit lres) with
                | Form.FbbT (a, bsres) ->
                  (match get t_atom a with
                   | Atom.Auop (u, a1') ->
                     (match u with
                      | Atom.UO_BVsextn (n0, i) ->
                        if if if eqb0 a1 a1'
                              then check_sextend t_form bs bsres i
                              else false
                           then N.eqb (N.of_nat (length bs)) n0
                           else false
                        then Cons (lres, Nil)
                        else C._true
                      | _ -> C._true)
                   | _ -> C._true)
                | _ -> C._true)
             | _ -> C._true)
       else C._true
     | Cons (i, l0) -> C._true)

(** val _shl_lit_be : int list -> int list **)

let _shl_lit_be a = match a with
| Nil -> Nil
| Cons (i, l) -> Cons (Lit._false, (removelast a))

(** val nshl_lit_be : int list -> nat -> int list **)

let rec nshl_lit_be a = function
| O -> a
| S n' -> nshl_lit_be (_shl_lit_be a) n'

(** val shl_lit_be : int list -> bool list -> int list **)

let shl_lit_be a b =
  nshl_lit_be a (RAWBITVECTOR_LIST.list2nat_be b)

(** val check_shl :
    Form.form array -> int list -> bool list -> int list -> bool **)

let check_shl t_form bs1 bs2 bsres =
  if nat_eqb0 (length bs1) (length bs2)
  then forallb2 (eq_carry_lit t_form) (lit_to_carry (shl_lit_be bs1 bs2))
         bsres
  else false

(** val check_bbShl :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbShl t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.Fatom a2 ->
                        (match get t_form (Lit.blit lres) with
                         | Form.FbbT (a, bsres) ->
                           (match get t_atom a with
                            | Atom.Abop (b, a1', a2') ->
                              (match b with
                               | Atom.BO_BVshl n0 ->
                                 (match get t_atom a2 with
                                  | Atom.Acop c ->
                                    (match c with
                                     | Atom.CO_BV (bv2, n2) ->
                                       if if if if if if eqb0 a1 a1'
                                                      then eqb0 a2 a2'
                                                      else false
                                                   then check_shl t_form bs1
                                                          bv2 bsres
                                                   else false
                                                then N.eqb
                                                       (N.of_nat
                                                         (length bs1)) n0
                                                else false
                                             then N.eqb
                                                    (N.of_nat (length bv2))
                                                    n0
                                             else false
                                          then N.eqb n2 n0
                                          else false
                                       then Cons (lres, Nil)
                                       else C._true
                                     | _ -> C._true)
                                  | _ -> C._true)
                               | _ -> C._true)
                            | _ -> C._true)
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val _shr_lit_be : int list -> int list **)

let _shr_lit_be = function
| Nil -> Nil
| Cons (xa, xsa) -> app xsa (Cons (Lit._false, Nil))

(** val nshr_lit_be : int list -> nat -> int list **)

let rec nshr_lit_be a = function
| O -> a
| S n' -> nshr_lit_be (_shr_lit_be a) n'

(** val shr_lit_be : int list -> bool list -> int list **)

let shr_lit_be a b =
  nshr_lit_be a (RAWBITVECTOR_LIST.list2nat_be b)

(** val check_shr :
    Form.form array -> int list -> bool list -> int list -> bool **)

let check_shr t_form bs1 bs2 bsres =
  if nat_eqb0 (length bs1) (length bs2)
  then forallb2 (eq_carry_lit t_form) (lit_to_carry (shr_lit_be bs1 bs2))
         bsres
  else false

(** val check_bbShr :
    Atom.atom array -> Form.form array -> S.t -> int -> int -> int -> C.t **)

let check_bbShr t_atom t_form s pos1 pos2 lres =
  match S.get s pos1 with
  | Nil -> C._true
  | Cons (l1, l) ->
    (match l with
     | Nil ->
       (match S.get s pos2 with
        | Nil -> C._true
        | Cons (l2, l0) ->
          (match l0 with
           | Nil ->
             if if if Lit.is_pos l1 then Lit.is_pos l2 else false
                then Lit.is_pos lres
                else false
             then (match get t_form (Lit.blit l1) with
                   | Form.FbbT (a1, bs1) ->
                     (match get t_form (Lit.blit l2) with
                      | Form.Fatom a2 ->
                        (match get t_form (Lit.blit lres) with
                         | Form.FbbT (a, bsres) ->
                           (match get t_atom a with
                            | Atom.Abop (b, a1', a2') ->
                              (match b with
                               | Atom.BO_BVshr n0 ->
                                 (match get t_atom a2 with
                                  | Atom.Acop c ->
                                    (match c with
                                     | Atom.CO_BV (bv2, n2) ->
                                       if if if if if if eqb0 a1 a1'
                                                      then eqb0 a2 a2'
                                                      else false
                                                   then check_shr t_form bs1
                                                          bv2 bsres
                                                   else false
                                                then N.eqb
                                                       (N.of_nat
                                                         (length bs1)) n0
                                                else false
                                             then N.eqb
                                                    (N.of_nat (length bv2))
                                                    n0
                                             else false
                                          then N.eqb n2 n0
                                          else false
                                       then Cons (lres, Nil)
                                       else C._true
                                     | _ -> C._true)
                                  | _ -> C._true)
                               | _ -> C._true)
                            | _ -> C._true)
                         | _ -> C._true)
                      | _ -> C._true)
                   | _ -> C._true)
             else C._true
           | Cons (i, l3) -> C._true))
     | Cons (i, l0) -> C._true)

(** val check_roweq : Form.form array -> Atom.atom array -> int -> C.t **)

let check_roweq t_form t_atom lres =
  if Lit.is_pos lres
  then (match get t_form (Lit.blit lres) with
        | Form.Fatom a ->
          (match get t_atom a with
           | Atom.Abop (b, xa, v) ->
             (match b with
              | Atom.BO_eq te ->
                (match get t_atom xa with
                 | Atom.Abop (b0, sa, i) ->
                   (match b0 with
                    | Atom.BO_select (ti1, te1) ->
                      (match get t_atom sa with
                       | Atom.Atop (t0, fa, j, v2) ->
                         let Atom.TO_store (ti2, te2) = t0 in
                         if if if if if Typ.eqb ti1 ti2
                                     then Typ.eqb te te1
                                     else false
                                  then Typ.eqb te te2
                                  else false
                               then eqb0 i j
                               else false
                            then eqb0 v v2
                            else false
                         then Cons (lres, Nil)
                         else C._true
                       | _ -> C._true)
                    | _ -> C._true)
                 | _ -> C._true)
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val store_of_me :
    Atom.atom array -> int -> int -> ((Typ.coq_type*Typ.coq_type)*int) option **)

let store_of_me t_atom a b =
  match get t_atom b with
  | Atom.Atop (t0, a', i, i0) ->
    let Atom.TO_store (ti, te) = t0 in
    if eqb0 a' a then Some ((ti,te),i) else None
  | _ -> None

(** val check_rowneq :
    Form.form array -> Atom.atom array -> int list -> C.t **)

let check_rowneq t_form t_atom cl = match cl with
| Nil -> C._true
| Cons (leqij, l) ->
  (match l with
   | Nil -> C._true
   | Cons (leqrow, l0) ->
     (match l0 with
      | Nil ->
        if if Lit.is_pos leqij then Lit.is_pos leqrow else false
        then (match get t_form (Lit.blit leqij) with
              | Form.Fatom eqij ->
                (match get t_form (Lit.blit leqrow) with
                 | Form.Fatom eqrow ->
                   (match get t_atom eqij with
                    | Atom.Abop (b, i, j) ->
                      (match b with
                       | Atom.BO_eq ti ->
                         (match get t_atom eqrow with
                          | Atom.Abop (b0, xa, x) ->
                            (match b0 with
                             | Atom.BO_eq te ->
                               (match get t_atom xa with
                                | Atom.Abop (b1, sa, j1) ->
                                  (match b1 with
                                   | Atom.BO_select (ti1, te1) ->
                                     (match get t_atom x with
                                      | Atom.Abop (b2, sa2, j2) ->
                                        (match b2 with
                                         | Atom.BO_select (ti2, te2) ->
                                           if if if if Typ.eqb ti ti1
                                                    then Typ.eqb ti ti2
                                                    else false
                                                 then Typ.eqb te te1
                                                 else false
                                              then Typ.eqb te te2
                                              else false
                                           then (match store_of_me t_atom sa
                                                         sa2 with
                                                 | Some p ->
                                                   let p2,i1 = p in
                                                   let ti3,te3 = p2 in
                                                   (match store_of_me t_atom
                                                            sa2 sa with
                                                    | Some p3 -> C._true
                                                    | None ->
                                                      if if if Typ.eqb ti ti3
                                                            then Typ.eqb te
                                                                   te3
                                                            else false
                                                         then if if if 
                                                                    eqb0 i1 i
                                                                    then 
                                                                    eqb0 j1 j
                                                                    else 
                                                                    false
                                                                 then 
                                                                   eqb0 j2 j
                                                                 else false
                                                              then true
                                                              else if 
                                                                    if 
                                                                    eqb0 i1 j
                                                                    then 
                                                                    eqb0 j1 i
                                                                    else 
                                                                    false
                                                                   then 
                                                                    eqb0 j2 i
                                                                   else false
                                                         else false
                                                      then cl
                                                      else C._true)
                                                 | None ->
                                                   (match store_of_me t_atom
                                                            sa2 sa with
                                                    | Some p ->
                                                      let p2,i1 = p in
                                                      let ti3,te3 = p2 in
                                                      if if if Typ.eqb ti ti3
                                                            then Typ.eqb te
                                                                   te3
                                                            else false
                                                         then if if if 
                                                                    eqb0 i1 i
                                                                    then 
                                                                    eqb0 j1 j
                                                                    else 
                                                                    false
                                                                 then 
                                                                   eqb0 j2 j
                                                                 else false
                                                              then true
                                                              else if 
                                                                    if 
                                                                    eqb0 i1 j
                                                                    then 
                                                                    eqb0 j1 i
                                                                    else 
                                                                    false
                                                                   then 
                                                                    eqb0 j2 i
                                                                   else false
                                                         else false
                                                      then cl
                                                      else C._true
                                                    | None -> C._true))
                                           else C._true
                                         | _ -> C._true)
                                      | _ -> C._true)
                                   | _ -> C._true)
                                | _ -> C._true)
                             | _ -> C._true)
                          | _ -> C._true)
                       | _ -> C._true)
                    | _ -> C._true)
                 | _ -> C._true)
              | _ -> C._true)
        else C._true
      | Cons (y, l1) -> C._true))

(** val eq_sel_sym :
    Atom.atom array -> Typ.coq_type -> Typ.coq_type -> int -> int -> int ->
    int -> bool **)

let eq_sel_sym t_atom ti te a b sela selb =
  match get t_atom sela with
  | Atom.Abop (b0, a', d1) ->
    (match b0 with
     | Atom.BO_select (ti1, te1) ->
       (match get t_atom selb with
        | Atom.Abop (b1, b', d2) ->
          (match b1 with
           | Atom.BO_select (ti2, te2) ->
             if if if if if if if Typ.eqb ti ti1
                               then Typ.eqb ti ti2
                               else false
                            then Typ.eqb te te1
                            else false
                         then Typ.eqb te te2
                         else false
                      then eqb0 a a'
                      else false
                   then eqb0 b b'
                   else false
                then eqb0 d1 d2
                else false
             then (match get t_atom d1 with
                   | Atom.Abop (b2, a3, b3) ->
                     (match b2 with
                      | Atom.BO_diffarray (ti3, te3) ->
                        if if if Typ.eqb ti ti3
                              then Typ.eqb te te3
                              else false
                           then eqb0 a3 a
                           else false
                        then eqb0 b3 b
                        else false
                      | _ -> false)
                   | _ -> false)
             else false
           | _ -> false)
        | _ -> false)
     | _ -> false)
  | _ -> false

(** val check_ext : Form.form array -> Atom.atom array -> int -> C.t **)

let check_ext t_form t_atom lres =
  if Lit.is_pos lres
  then (match get t_form (Lit.blit lres) with
        | Form.For args ->
          if eqb0 (length0 args) (Uint63.of_int (2))
          then let l1 = get args (Uint63.of_int (0)) in
               let l2 = get args (Uint63.of_int (1)) in
               if if Lit.is_pos l1 then negb (Lit.is_pos l2) else false
               then (match get t_form (Lit.blit l1) with
                     | Form.Fatom eqa ->
                       (match get t_form (Lit.blit l2) with
                        | Form.Fatom eqsel ->
                          (match get t_atom eqa with
                           | Atom.Abop (b0, a, b) ->
                             (match b0 with
                              | Atom.BO_eq t0 ->
                                (match t0 with
                                 | Typ.TFArray (ti, te) ->
                                   (match get t_atom eqsel with
                                    | Atom.Abop (b1, sela, selb) ->
                                      (match b1 with
                                       | Atom.BO_eq te' ->
                                         if if Typ.eqb te te'
                                            then if eq_sel_sym t_atom ti te a
                                                      b sela selb
                                                 then true
                                                 else eq_sel_sym t_atom ti te
                                                        b a sela selb
                                            else false
                                         then Cons (lres, Nil)
                                         else C._true
                                       | _ -> C._true)
                                    | _ -> C._true)
                                 | _ -> C._true)
                              | _ -> C._true)
                           | _ -> C._true)
                        | _ -> C._true)
                     | _ -> C._true)
               else C._true
          else C._true
        | _ -> C._true)
  else C._true

type 'step _trace_ = 'step trace

(** val _checker_ :
    (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> int -> bool **)

let _checker_ check_step is_false0 s t0 confl =
  let s' = trace_fold check_step s t0 in is_false0 (S.get s' confl)

module Euf_Checker = 
 struct 
  type step =
  | Res of int * int array
  | Weaken of int * int * int list
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
  | BBVar of int * int
  | BBConst of int * int
  | BBOp of int * int * int * int
  | BBNot of int * int * int
  | BBNeg of int * int * int
  | BBAdd of int * int * int * int
  | BBConcat of int * int * int * int
  | BBMul of int * int * int * int
  | BBUlt of int * int * int * int
  | BBSlt of int * int * int * int
  | BBEq of int * int * int * int
  | BBDiseq of int * int
  | BBExtract of int * int * int
  | BBZextend of int * int * int
  | BBSextend of int * int * int
  | BBShl of int * int * int * int
  | BBShr of int * int * int * int
  | RowEq of int * int
  | RowNeq of int * C.t
  | Ext of int * int
  | Hole of int * int list * C.t list * C.t
  | ForallInst of int * C.t
  
  (** val step_rect :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> (int -> int array -> 'a1) -> (int -> int -> int list -> 'a1)
      -> (int -> int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int
      -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int -> 'a1) ->
      (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int ->
      'a1) -> (int -> int -> int list -> 'a1) -> (int -> int -> int option
      list -> 'a1) -> (int -> int -> int -> int option list -> 'a1) -> (int
      -> int list -> zArithProof list -> 'a1) -> (int -> int -> 'a1) -> (int
      -> int -> int -> zArithProof list -> 'a1) -> (int -> int -> int -> 'a1)
      -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int ->
      int -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> int -> int -> 'a1)
      -> (int -> int -> int -> int -> 'a1) -> (int -> int -> int -> int ->
      'a1) -> (int -> int -> int -> int -> 'a1) -> (int -> int -> int -> int
      -> 'a1) -> (int -> int -> int -> int -> 'a1) -> (int -> int -> int ->
      int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int -> 'a1) ->
      (int -> int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> int
      -> int -> int -> 'a1) -> (int -> int -> int -> int -> 'a1) -> (int ->
      int -> 'a1) -> (int -> C.t -> 'a1) -> (int -> int -> 'a1) -> (int ->
      int list -> C.t list -> C.t -> __ -> 'a1) -> (int -> __ -> __ -> C.t ->
      __ -> 'a1) -> step -> 'a1 **)
  
  let step_rect t_i t_func t_atom t_form f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 = function
  | Res (x, x0) -> f x x0
  | Weaken (x, x0, x1) -> f0 x x0 x1
  | ImmFlatten (x, x0, x1) -> f1 x x0 x1
  | CTrue x -> f2 x
  | CFalse x -> f3 x
  | BuildDef (x, x0) -> f4 x x0
  | BuildDef2 (x, x0) -> f5 x x0
  | BuildProj (x, x0, x1) -> f6 x x0 x1
  | ImmBuildDef (x, x0) -> f7 x x0
  | ImmBuildDef2 (x, x0) -> f8 x x0
  | ImmBuildProj (x, x0, x1) -> f9 x x0 x1
  | EqTr (x, x0, x1) -> f10 x x0 x1
  | EqCgr (x, x0, x1) -> f11 x x0 x1
  | EqCgrP (x, x0, x1, x2) -> f12 x x0 x1 x2
  | LiaMicromega (x, x0, x1) -> f13 x x0 x1
  | LiaDiseq (x, x0) -> f14 x x0
  | SplArith (x, x0, x1, x2) -> f15 x x0 x1 x2
  | SplDistinctElim (x, x0, x1) -> f16 x x0 x1
  | BBVar (x, x0) -> f17 x x0
  | BBConst (x, x0) -> f18 x x0
  | BBOp (x, x0, x1, x2) -> f19 x x0 x1 x2
  | BBNot (x, x0, x1) -> f20 x x0 x1
  | BBNeg (x, x0, x1) -> f21 x x0 x1
  | BBAdd (x, x0, x1, x2) -> f22 x x0 x1 x2
  | BBConcat (x, x0, x1, x2) -> f23 x x0 x1 x2
  | BBMul (x, x0, x1, x2) -> f24 x x0 x1 x2
  | BBUlt (x, x0, x1, x2) -> f25 x x0 x1 x2
  | BBSlt (x, x0, x1, x2) -> f26 x x0 x1 x2
  | BBEq (x, x0, x1, x2) -> f27 x x0 x1 x2
  | BBDiseq (x, x0) -> f28 x x0
  | BBExtract (x, x0, x1) -> f29 x x0 x1
  | BBZextend (x, x0, x1) -> f30 x x0 x1
  | BBSextend (x, x0, x1) -> f31 x x0 x1
  | BBShl (x, x0, x1, x2) -> f32 x x0 x1 x2
  | BBShr (x, x0, x1, x2) -> f33 x x0 x1 x2
  | RowEq (x, x0) -> f34 x x0
  | RowNeq (x, x0) -> f35 x x0
  | Ext (x, x0) -> f36 x x0
  | Hole (x, x0, x1, x2) -> f37 x x0 x1 x2 __
  | ForallInst (x, x0) -> f38 x __ __ x0 __
  
  (** val step_rec :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> (int -> int array -> 'a1) -> (int -> int -> int list -> 'a1)
      -> (int -> int -> int -> 'a1) -> (int -> 'a1) -> (int -> 'a1) -> (int
      -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int -> 'a1) ->
      (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int ->
      'a1) -> (int -> int -> int list -> 'a1) -> (int -> int -> int option
      list -> 'a1) -> (int -> int -> int -> int option list -> 'a1) -> (int
      -> int list -> zArithProof list -> 'a1) -> (int -> int -> 'a1) -> (int
      -> int -> int -> zArithProof list -> 'a1) -> (int -> int -> int -> 'a1)
      -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int ->
      int -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> int -> int -> 'a1)
      -> (int -> int -> int -> int -> 'a1) -> (int -> int -> int -> int ->
      'a1) -> (int -> int -> int -> int -> 'a1) -> (int -> int -> int -> int
      -> 'a1) -> (int -> int -> int -> int -> 'a1) -> (int -> int -> int ->
      int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> int -> 'a1) ->
      (int -> int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> int
      -> int -> int -> 'a1) -> (int -> int -> int -> int -> 'a1) -> (int ->
      int -> 'a1) -> (int -> C.t -> 'a1) -> (int -> int -> 'a1) -> (int ->
      int list -> C.t list -> C.t -> __ -> 'a1) -> (int -> __ -> __ -> C.t ->
      __ -> 'a1) -> step -> 'a1 **)
  
  let step_rec t_i t_func t_atom t_form f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 = function
  | Res (x, x0) -> f x x0
  | Weaken (x, x0, x1) -> f0 x x0 x1
  | ImmFlatten (x, x0, x1) -> f1 x x0 x1
  | CTrue x -> f2 x
  | CFalse x -> f3 x
  | BuildDef (x, x0) -> f4 x x0
  | BuildDef2 (x, x0) -> f5 x x0
  | BuildProj (x, x0, x1) -> f6 x x0 x1
  | ImmBuildDef (x, x0) -> f7 x x0
  | ImmBuildDef2 (x, x0) -> f8 x x0
  | ImmBuildProj (x, x0, x1) -> f9 x x0 x1
  | EqTr (x, x0, x1) -> f10 x x0 x1
  | EqCgr (x, x0, x1) -> f11 x x0 x1
  | EqCgrP (x, x0, x1, x2) -> f12 x x0 x1 x2
  | LiaMicromega (x, x0, x1) -> f13 x x0 x1
  | LiaDiseq (x, x0) -> f14 x x0
  | SplArith (x, x0, x1, x2) -> f15 x x0 x1 x2
  | SplDistinctElim (x, x0, x1) -> f16 x x0 x1
  | BBVar (x, x0) -> f17 x x0
  | BBConst (x, x0) -> f18 x x0
  | BBOp (x, x0, x1, x2) -> f19 x x0 x1 x2
  | BBNot (x, x0, x1) -> f20 x x0 x1
  | BBNeg (x, x0, x1) -> f21 x x0 x1
  | BBAdd (x, x0, x1, x2) -> f22 x x0 x1 x2
  | BBConcat (x, x0, x1, x2) -> f23 x x0 x1 x2
  | BBMul (x, x0, x1, x2) -> f24 x x0 x1 x2
  | BBUlt (x, x0, x1, x2) -> f25 x x0 x1 x2
  | BBSlt (x, x0, x1, x2) -> f26 x x0 x1 x2
  | BBEq (x, x0, x1, x2) -> f27 x x0 x1 x2
  | BBDiseq (x, x0) -> f28 x x0
  | BBExtract (x, x0, x1) -> f29 x x0 x1
  | BBZextend (x, x0, x1) -> f30 x x0 x1
  | BBSextend (x, x0, x1) -> f31 x x0 x1
  | BBShl (x, x0, x1, x2) -> f32 x x0 x1 x2
  | BBShr (x, x0, x1, x2) -> f33 x x0 x1 x2
  | RowEq (x, x0) -> f34 x x0
  | RowNeq (x, x0) -> f35 x x0
  | Ext (x, x0) -> f36 x x0
  | Hole (x, x0, x1, x2) -> f37 x x0 x1 x2 __
  | ForallInst (x, x0) -> f38 x __ __ x0 __
  
  (** val step_checker :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> S.t -> step -> S.t **)
  
  let step_checker t_i t_func t_atom t_form s = function
  | Res (pos, res) -> S.set_resolve s pos res
  | Weaken (pos, cid, cl) -> S.set_weaken s pos cid cl
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
  | BBVar (pos, res) -> S.set_clause s pos (check_bbVar t_atom t_form res)
  | BBConst (pos, res) ->
    S.set_clause s pos (check_bbConst t_atom t_form res)
  | BBOp (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbOp t_atom t_form s orig1 orig2 res)
  | BBNot (pos, orig, res) ->
    S.set_clause s pos (check_bbNot t_atom t_form s orig res)
  | BBNeg (pos, orig, res) ->
    S.set_clause s pos (check_bbNeg t_atom t_form s orig res)
  | BBAdd (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbAdd t_atom t_form s orig1 orig2 res)
  | BBConcat (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbConcat t_atom t_form s orig1 orig2 res)
  | BBMul (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbMult t_atom t_form s orig1 orig2 res)
  | BBUlt (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbUlt t_atom t_form s orig1 orig2 res)
  | BBSlt (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbSlt t_atom t_form s orig1 orig2 res)
  | BBEq (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbEq t_atom t_form s orig1 orig2 res)
  | BBDiseq (pos, res) ->
    S.set_clause s pos (check_bbDiseq t_atom t_form res)
  | BBExtract (pos, orig, res) ->
    S.set_clause s pos (check_bbExtract t_atom t_form s orig res)
  | BBZextend (pos, orig, res) ->
    S.set_clause s pos (check_bbZextend t_atom t_form s orig res)
  | BBSextend (pos, orig, res) ->
    S.set_clause s pos (check_bbSextend t_atom t_form s orig res)
  | BBShl (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbShl t_atom t_form s orig1 orig2 res)
  | BBShr (pos, orig1, orig2, res) ->
    S.set_clause s pos (check_bbShr t_atom t_form s orig1 orig2 res)
  | RowEq (pos, res) -> S.set_clause s pos (check_roweq t_form t_atom res)
  | RowNeq (pos, cl) -> S.set_clause s pos (check_rowneq t_form t_atom cl)
  | Ext (pos, res) -> S.set_clause s pos (check_ext t_form t_atom res)
  | Hole (pos, prem_id, prem, concl) ->
    S.set_clause s pos (check_hole s prem_id prem concl)
  | ForallInst (pos, concl) -> S.set_clause s pos concl
  
  (** val euf_checker :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> (C.t -> bool) -> S.t -> step _trace_ -> int -> bool **)
  
  let euf_checker t_i t_func t_atom t_form s t0 =
    _checker_ (step_checker t_i t_func t_atom t_form) s t0
  
  type certif =
  | Certif of int * step _trace_ * int
  
  (** val certif_rect :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1 **)
  
  let certif_rect t_i t_func t_atom t_form f = function
  | Certif (x, x0, x1) -> f x x0 x1
  
  (** val certif_rec :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1 **)
  
  let certif_rec t_i t_func t_atom t_form f = function
  | Certif (x, x0, x1) -> f x x0 x1
  
  (** val add_roots : S.t -> int array -> int array option -> S.t **)
  
  let add_roots s d = function
  | Some ur ->
    foldi_right (fun i c_index s0 ->
      let c =
        if ltb0 c_index (length0 d)
        then Cons ((get d c_index), Nil)
        else C._true
      in
      S.set_clause s0 i c) ur s
  | None -> foldi_right (fun i c s0 -> S.set_clause s0 i (Cons (c, Nil))) d s
  
  (** val valid :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int array -> bool **)
  
  let valid t_i t_func t_atom t_form d =
    let rho =
      Form.interp_state_var (Atom.interp_form_hatom t_i t_func t_atom)
        (Atom.interp_form_hatom_bv t_i t_func t_atom) t_form
    in
    afold_left true (fun b1 b2 -> if b1 then b2 else false) (Lit.interp rho)
      d
  
  (** val checker :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int array -> int array option -> certif -> bool **)
  
  let checker t_i t_func t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    if if if Form.check_form t_form then Atom.check_atom t_atom else false
       then Atom.wt t_i t_func t_atom
       else false
    then euf_checker t_i t_func t_atom t_form C.is_false
           (add_roots (S.make nclauses) d used_roots) t0 confl
    else false
  
  (** val setup_checker_step_debug :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int array -> int array option -> certif -> S.t*step list **)
  
  let setup_checker_step_debug t_i t_func t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    let s = add_roots (S.make nclauses) d used_roots in s,(trace_to_list t0)
  
  (** val position_of_step :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> step -> int **)
  
  let position_of_step t_i t_func t_atom t_form = function
  | Res (pos, res) -> pos
  | Weaken (pos, cid, cl) -> pos
  | ImmFlatten (pos, cid, lf) -> pos
  | CTrue pos -> pos
  | CFalse pos -> pos
  | BuildDef (pos, l) -> pos
  | BuildDef2 (pos, l) -> pos
  | BuildProj (pos, l, i) -> pos
  | ImmBuildDef (pos, cid) -> pos
  | ImmBuildDef2 (pos, cid) -> pos
  | ImmBuildProj (pos, cid, i) -> pos
  | EqTr (pos, l, fl) -> pos
  | EqCgr (pos, l, fl) -> pos
  | EqCgrP (pos, l1, l2, fl) -> pos
  | LiaMicromega (pos, cl, c) -> pos
  | LiaDiseq (pos, l) -> pos
  | SplArith (pos, orig, res, l) -> pos
  | SplDistinctElim (pos, orig, res) -> pos
  | BBVar (pos, res) -> pos
  | BBConst (pos, res) -> pos
  | BBOp (pos, orig1, orig2, res) -> pos
  | BBNot (pos, orig, res) -> pos
  | BBNeg (pos, orig, res) -> pos
  | BBAdd (pos, orig1, orig2, res) -> pos
  | BBConcat (pos, orig1, orig2, res) -> pos
  | BBMul (pos, orig1, orig2, res) -> pos
  | BBUlt (pos, orig1, orig2, res) -> pos
  | BBSlt (pos, orig1, orig2, res) -> pos
  | BBEq (pos, orig1, orig2, res) -> pos
  | BBDiseq (pos, res) -> pos
  | BBExtract (pos, orig, res) -> pos
  | BBZextend (pos, orig, res) -> pos
  | BBSextend (pos, orig, res) -> pos
  | BBShl (pos, orig1, orig2, res) -> pos
  | BBShr (pos, orig1, orig2, res) -> pos
  | RowEq (pos, res) -> pos
  | RowNeq (pos, cl) -> pos
  | Ext (pos, res) -> pos
  | Hole (pos, prem_id, prem, concl) -> pos
  | ForallInst (pos, concl) -> pos
  
  (** val checker_step_debug :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> S.t -> step -> S.t*bool **)
  
  let checker_step_debug t_i t_func t_atom t_form s step_t =
    let s0 = step_checker t_i t_func t_atom t_form s step_t in
    s0,(C.has_true
         (S.get s0 (position_of_step t_i t_func t_atom t_form step_t)))
  
  (** val ignore_true_step :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> step -> bool **)
  
  let ignore_true_step t_i t_func t_atom t_form = function
  | CTrue pos -> true
  | Hole (pos, prem_id, prem, concl) -> true
  | _ -> false
  
  type name_step =
  | Name_Res
  | Name_Weaken
  | Name_ImmFlatten
  | Name_CTrue
  | Name_CFalse
  | Name_BuildDef
  | Name_BuildDef2
  | Name_BuildProj
  | Name_ImmBuildDef
  | Name_ImmBuildDef2
  | Name_ImmBuildProj
  | Name_EqTr
  | Name_EqCgr
  | Name_EqCgrP
  | Name_LiaMicromega
  | Name_LiaDiseq
  | Name_SplArith
  | Name_SplDistinctElim
  | Name_BBVar
  | Name_BBConst
  | Name_BBOp
  | Name_BBNot
  | Name_BBNeg
  | Name_BBAdd
  | Name_BBConcat
  | Name_BBMul
  | Name_BBUlt
  | Name_BBSlt
  | Name_BBEq
  | Name_BBDiseq
  | Name_BBExtract
  | Name_BBZextend
  | Name_BBSextend
  | Name_BBShl
  | Name_BBShr
  | Name_RowEq
  | Name_RowNeq
  | Name_Ext
  | Name_Hole
  | Name_ForallInst
  
  (** val name_step_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      name_step -> 'a1 **)
  
  let name_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 = function
  | Name_Res -> f
  | Name_Weaken -> f0
  | Name_ImmFlatten -> f1
  | Name_CTrue -> f2
  | Name_CFalse -> f3
  | Name_BuildDef -> f4
  | Name_BuildDef2 -> f5
  | Name_BuildProj -> f6
  | Name_ImmBuildDef -> f7
  | Name_ImmBuildDef2 -> f8
  | Name_ImmBuildProj -> f9
  | Name_EqTr -> f10
  | Name_EqCgr -> f11
  | Name_EqCgrP -> f12
  | Name_LiaMicromega -> f13
  | Name_LiaDiseq -> f14
  | Name_SplArith -> f15
  | Name_SplDistinctElim -> f16
  | Name_BBVar -> f17
  | Name_BBConst -> f18
  | Name_BBOp -> f19
  | Name_BBNot -> f20
  | Name_BBNeg -> f21
  | Name_BBAdd -> f22
  | Name_BBConcat -> f23
  | Name_BBMul -> f24
  | Name_BBUlt -> f25
  | Name_BBSlt -> f26
  | Name_BBEq -> f27
  | Name_BBDiseq -> f28
  | Name_BBExtract -> f29
  | Name_BBZextend -> f30
  | Name_BBSextend -> f31
  | Name_BBShl -> f32
  | Name_BBShr -> f33
  | Name_RowEq -> f34
  | Name_RowNeq -> f35
  | Name_Ext -> f36
  | Name_Hole -> f37
  | Name_ForallInst -> f38
  
  (** val name_step_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      name_step -> 'a1 **)
  
  let name_step_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 = function
  | Name_Res -> f
  | Name_Weaken -> f0
  | Name_ImmFlatten -> f1
  | Name_CTrue -> f2
  | Name_CFalse -> f3
  | Name_BuildDef -> f4
  | Name_BuildDef2 -> f5
  | Name_BuildProj -> f6
  | Name_ImmBuildDef -> f7
  | Name_ImmBuildDef2 -> f8
  | Name_ImmBuildProj -> f9
  | Name_EqTr -> f10
  | Name_EqCgr -> f11
  | Name_EqCgrP -> f12
  | Name_LiaMicromega -> f13
  | Name_LiaDiseq -> f14
  | Name_SplArith -> f15
  | Name_SplDistinctElim -> f16
  | Name_BBVar -> f17
  | Name_BBConst -> f18
  | Name_BBOp -> f19
  | Name_BBNot -> f20
  | Name_BBNeg -> f21
  | Name_BBAdd -> f22
  | Name_BBConcat -> f23
  | Name_BBMul -> f24
  | Name_BBUlt -> f25
  | Name_BBSlt -> f26
  | Name_BBEq -> f27
  | Name_BBDiseq -> f28
  | Name_BBExtract -> f29
  | Name_BBZextend -> f30
  | Name_BBSextend -> f31
  | Name_BBShl -> f32
  | Name_BBShr -> f33
  | Name_RowEq -> f34
  | Name_RowNeq -> f35
  | Name_Ext -> f36
  | Name_Hole -> f37
  | Name_ForallInst -> f38
  
  (** val name_of_step :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> step -> name_step **)
  
  let name_of_step t_i t_func t_atom t_form = function
  | Res (pos, res) -> Name_Res
  | Weaken (pos, cid, cl) -> Name_Weaken
  | ImmFlatten (pos, cid, lf) -> Name_ImmFlatten
  | CTrue pos -> Name_CTrue
  | CFalse pos -> Name_CFalse
  | BuildDef (pos, l) -> Name_BuildDef
  | BuildDef2 (pos, l) -> Name_BuildDef2
  | BuildProj (pos, l, i) -> Name_BuildProj
  | ImmBuildDef (pos, cid) -> Name_ImmBuildDef
  | ImmBuildDef2 (pos, cid) -> Name_ImmBuildDef2
  | ImmBuildProj (pos, cid, i) -> Name_ImmBuildProj
  | EqTr (pos, l, fl) -> Name_EqTr
  | EqCgr (pos, l, fl) -> Name_EqCgr
  | EqCgrP (pos, l1, l2, fl) -> Name_EqCgrP
  | LiaMicromega (pos, cl, c) -> Name_LiaMicromega
  | LiaDiseq (pos, l) -> Name_LiaDiseq
  | SplArith (pos, orig, res, l) -> Name_SplArith
  | SplDistinctElim (pos, orig, res) -> Name_SplDistinctElim
  | BBVar (pos, res) -> Name_BBVar
  | BBConst (pos, res) -> Name_BBConst
  | BBOp (pos, orig1, orig2, res) -> Name_BBOp
  | BBNot (pos, orig, res) -> Name_BBNot
  | BBNeg (pos, orig, res) -> Name_BBNeg
  | BBAdd (pos, orig1, orig2, res) -> Name_BBAdd
  | BBConcat (pos, orig1, orig2, res) -> Name_BBConcat
  | BBMul (pos, orig1, orig2, res) -> Name_BBMul
  | BBUlt (pos, orig1, orig2, res) -> Name_BBUlt
  | BBSlt (pos, orig1, orig2, res) -> Name_BBSlt
  | BBEq (pos, orig1, orig2, res) -> Name_BBEq
  | BBDiseq (pos, res) -> Name_BBDiseq
  | BBExtract (pos, orig, res) -> Name_BBExtract
  | BBZextend (pos, orig, res) -> Name_BBZextend
  | BBSextend (pos, orig, res) -> Name_BBSextend
  | BBShl (pos, orig1, orig2, res) -> Name_BBShl
  | BBShr (pos, orig1, orig2, res) -> Name_BBShr
  | RowEq (pos, res) -> Name_RowEq
  | RowNeq (pos, cl) -> Name_RowNeq
  | Ext (pos, res) -> Name_Ext
  | Hole (pos, prem_id, prem, concl) -> Name_Hole
  | ForallInst (pos, concl) -> Name_ForallInst
  
  (** val checker_debug :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int array -> int array option -> certif -> (nat*name_step)
      option **)
  
  let checker_debug t_i t_func t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    let s = add_roots (S.make nclauses) d used_roots in
    let p,failure =
      trace_fold (fun acc step0 ->
        let y,y0 = acc in
        let s0,nb = y in
        (match y0 with
         | Some y1 -> acc
         | None ->
           let nb0 = S nb in
           let s1 = step_checker t_i t_func t_atom t_form s0 step0 in
           if if negb (ignore_true_step t_i t_func t_atom t_form step0)
              then C.has_true
                     (S.get s1
                       (position_of_step t_i t_func t_atom t_form step0))
              else false
           then (s1,nb0),(Some step0)
           else (s1,nb0),None)) ((s,O),None) t0
    in
    let t1,nb = p in
    (match failure with
     | Some st -> Some (nb,(name_of_step t_i t_func t_atom t_form st))
     | None -> None)
  
  (** val checker_b :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int -> bool -> certif -> bool **)
  
  let checker_b t_i t_func t_atom t_form l b c =
    let l0 = if b then Lit.neg l else l in
    let Certif (nclauses, x, x0) = c in
    checker t_i t_func t_atom t_form (make nclauses l0) None c
  
  (** val checker_eq :
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int -> int -> int -> certif -> bool **)
  
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
      typ_compdec array -> Atom.tval array -> Atom.atom array -> Form.form
      array -> int array -> int array option -> certif -> bool **)
  
  let checker_ext t_i t_func t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    if if Form.check_form t_form then Atom.check_atom t_atom else false
    then euf_checker t_i t_func t_atom t_form C.is_false
           (add_roots (S.make nclauses) d used_roots) t0 confl
    else false
 end


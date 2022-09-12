
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

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

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val compOpp : int -> int **)

let compOpp = function
| 0 -> 0
| (-1) -> 1
| 1 -> (-1)

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

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

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
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
    | XH -> (match y with
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

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

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
    | XH -> (match y with
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

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p2 -> S (size_nat p2)
  | XO p2 -> S (size_nat p2)
  | XH -> S O

  (** val compare_cont : int -> positive -> positive -> int **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont 1 p q
       | XH -> 1)
    | XO p ->
      (match y with
       | XI q -> compare_cont (-1) p q
       | XO q -> compare_cont r p q
       | XH -> 1)
    | XH -> (match y with
             | XH -> r
             | _ -> (-1))

  (** val compare : positive -> positive -> int **)

  let compare =
    compare_cont 0

  (** val max : positive -> positive -> positive **)

  let max p p' =
    match compare p p' with
    | 1 -> p
    | _ -> p'

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p2 -> (match q with
                | XI q0 -> eqb p2 q0
                | _ -> false)
    | XO p2 -> (match q with
                | XO q0 -> eqb p2 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val leb : positive -> positive -> bool **)

  let leb x y =
    match compare x y with
    | 1 -> false
    | _ -> true

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
             | 0 -> a
             | (-1) -> gcdn n1 (sub b' a') a
             | 1 -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI _ -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p2 -> op a (iter_op op p2 (op a a))
    | XO p2 -> iter_op op p2 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p2 -> (match x0 with
                | XI p3 -> eq_dec p2 p3
                | _ -> Right)
    | XO p2 -> (match x0 with
                | XO p3 -> eq_dec p2 p3
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
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

  (** val compare : n -> n -> int **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> 0
             | Npos _ -> (-1))
    | Npos n' -> (match m with
                  | N0 -> 1
                  | Npos m' -> Coq_Pos.compare n' m')

  (** val eqb : n -> n -> bool **)

  let eqb n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos p -> (match m with
                 | N0 -> false
                 | Npos q -> Coq_Pos.eqb p q)

  (** val leb : n -> n -> bool **)

  let leb x y =
    match compare x y with
    | 1 -> false
    | _ -> true

  (** val ltb : n -> n -> bool **)

  let ltb x y =
    match compare x y with
    | (-1) -> true
    | _ -> false

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Coq_Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Coq_Pos.of_succ_nat n')
 end

module Z =
 struct
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

  (** val compare : z -> z -> int **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> 0
             | Zpos _ -> (-1)
             | Zneg _ -> 1)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> 1)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> (-1))

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | 1 -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | (-1) -> true
    | _ -> false

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | 1 -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Coq_Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Coq_Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | (-1) -> m
    | _ -> n0

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Coq_Pos.of_succ_nat n1)

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, Z0)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q

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

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos x0 -> (match y with
                  | Zpos p2 -> Coq_Pos.eq_dec x0 p2
                  | _ -> Right)
    | Zneg x0 -> (match y with
                  | Zneg p2 -> Coq_Pos.eq_dec x0 p2
                  | _ -> Right)
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n0 l default0 =
  match n0 with
  | O -> (match l with
          | Nil -> default0
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default0
            | Cons (_, t0) -> nth m t0 default0)

(** val removelast : 'a1 list -> 'a1 list **)

let rec removelast = function
| Nil -> Nil
| Cons (a, l0) ->
  (match l0 with
   | Nil -> Nil
   | Cons (_, _) -> Cons (a, (removelast l0)))

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | Nil -> l'
  | Cons (a, l0) -> rev_append l0 (Cons (a, l'))

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, t0) -> fold_left f t0 (f a0 b)

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

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | 0 -> true
  | _ -> false

type 'c pExpr =
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

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
  | Pc c -> (match p' with
             | Pc c' -> ceqb c c'
             | _ -> false)
  | Pinj (j, q) ->
    (match p' with
     | Pinj (j', q') ->
       (match Coq_Pos.compare j j' with
        | 0 -> peq ceqb q q'
        | _ -> false)
     | _ -> false)
  | PX (p2, i, q) ->
    (match p' with
     | PX (p'0, i', q') ->
       (match Coq_Pos.compare i i' with
        | 0 -> if peq ceqb p2 p'0 then peq ceqb q q' else false
        | _ -> false)
     | _ -> false)

(** val mkPinj : positive -> 'a1 pol -> 'a1 pol **)

let mkPinj j p = match p with
| Pc _ -> p
| Pinj (j', q) -> Pinj ((Coq_Pos.add j j'), q)
| PX (_, _, _) -> Pinj (j, p)

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
  | Pinj (_, _) -> PX (p, i, q)
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
| Pc _ -> PX (p', i', p)
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
| Pc _ -> PX ((popp copp p'), i', p)
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

type kind =
| IsProp
| IsBool

type ('tA, 'tX, 'aA, 'aF) gFormula =
| TT of kind
| FF of kind
| X of kind * 'tX
| A of kind * 'tA * 'aA
| AND of kind * ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| OR of kind * ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| NOT of kind * ('tA, 'tX, 'aA, 'aF) gFormula
| IMPL of kind * ('tA, 'tX, 'aA, 'aF) gFormula * 'aF option
   * ('tA, 'tX, 'aA, 'aF) gFormula
| IFF of kind * ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula
| EQ of ('tA, 'tX, 'aA, 'aF) gFormula * ('tA, 'tX, 'aA, 'aF) gFormula

type rtyp = __

type eKind = __

type 'a bFormula = ('a, eKind, unit0, unit0) gFormula

type ('x, 'annot) clause = ('x * 'annot) list

type ('x, 'annot) cnf = ('x, 'annot) clause list

(** val cnf_tt : ('a1, 'a2) cnf **)

let cnf_tt =
  Nil

(** val cnf_ff : ('a1, 'a2) cnf **)

let cnf_ff =
  Cons (Nil, Nil)

(** val add_term :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1 * 'a2) -> ('a1, 'a2)
    clause -> ('a1, 'a2) clause option **)

let rec add_term unsat deduce t0 = function
| Nil ->
  (match deduce (fst t0) (fst t0) with
   | Some u -> if unsat u then None else Some (Cons (t0, Nil))
   | None -> Some (Cons (t0, Nil)))
| Cons (t', cl0) ->
  (match deduce (fst t0) (fst t') with
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
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1,
    'a2) clause -> ('a1, 'a2) clause option **)

let rec or_clause unsat deduce cl1 cl2 =
  match cl1 with
  | Nil -> Some cl2
  | Cons (t0, cl) ->
    (match add_term unsat deduce t0 cl2 with
     | Some cl' -> or_clause unsat deduce cl cl'
     | None -> None)

(** val xor_clause_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1,
    'a2) cnf -> ('a1, 'a2) cnf **)

let xor_clause_cnf unsat deduce t0 f =
  fold_left (fun acc e ->
    match or_clause unsat deduce t0 e with
    | Some cl -> Cons (cl, acc)
    | None -> acc) f Nil

(** val or_clause_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) clause -> ('a1,
    'a2) cnf -> ('a1, 'a2) cnf **)

let or_clause_cnf unsat deduce t0 f =
  match t0 with
  | Nil -> f
  | Cons (_, _) -> xor_clause_cnf unsat deduce t0 f

(** val or_cnf :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) cnf -> ('a1,
    'a2) cnf -> ('a1, 'a2) cnf **)

let rec or_cnf unsat deduce f f' =
  match f with
  | Nil -> cnf_tt
  | Cons (e, rst) ->
    rev_append (or_cnf unsat deduce rst f') (or_clause_cnf unsat deduce e f')

(** val and_cnf : ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf **)

let and_cnf =
  rev_append

type ('term, 'annot, 'tX, 'aF) tFormula = ('term, 'tX, 'annot, 'aF) gFormula

(** val is_cnf_tt : ('a1, 'a2) cnf -> bool **)

let is_cnf_tt = function
| Nil -> true
| Cons (_, _) -> false

(** val is_cnf_ff : ('a1, 'a2) cnf -> bool **)

let is_cnf_ff = function
| Nil -> false
| Cons (c0, l) ->
  (match c0 with
   | Nil -> (match l with
             | Nil -> true
             | Cons (_, _) -> false)
   | Cons (_, _) -> false)

(** val and_cnf_opt : ('a1, 'a2) cnf -> ('a1, 'a2) cnf -> ('a1, 'a2) cnf **)

let and_cnf_opt f1 f2 =
  if if is_cnf_ff f1 then true else is_cnf_ff f2
  then cnf_ff
  else if is_cnf_tt f2 then f1 else and_cnf f1 f2

(** val or_cnf_opt :
    ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> ('a1, 'a2) cnf -> ('a1,
    'a2) cnf -> ('a1, 'a2) cnf **)

let or_cnf_opt unsat deduce f1 f2 =
  if if is_cnf_tt f1 then true else is_cnf_tt f2
  then cnf_tt
  else if is_cnf_ff f2 then f1 else or_cnf unsat deduce f1 f2

(** val mk_and :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1,
    'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool -> ('a1, 'a3,
    'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf **)

let mk_and unsat deduce rEC k pol0 f1 f2 =
  if pol0
  then and_cnf_opt (rEC pol0 k f1) (rEC pol0 k f2)
  else or_cnf_opt unsat deduce (rEC pol0 k f1) (rEC pol0 k f2)

(** val mk_or :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1,
    'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool -> ('a1, 'a3,
    'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf **)

let mk_or unsat deduce rEC k pol0 f1 f2 =
  if pol0
  then or_cnf_opt unsat deduce (rEC pol0 k f1) (rEC pol0 k f2)
  else and_cnf_opt (rEC pol0 k f1) (rEC pol0 k f2)

(** val mk_impl :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1,
    'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool -> ('a1, 'a3,
    'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf **)

let mk_impl unsat deduce rEC k pol0 f1 f2 =
  if pol0
  then or_cnf_opt unsat deduce (rEC (negb pol0) k f1) (rEC pol0 k f2)
  else and_cnf_opt (rEC (negb pol0) k f1) (rEC pol0 k f2)

(** val mk_iff :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> (bool -> kind -> ('a1,
    'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf) -> kind -> bool -> ('a1, 'a3,
    'a4, 'a5) tFormula -> ('a1, 'a3, 'a4, 'a5) tFormula -> ('a2, 'a3) cnf **)

let mk_iff unsat deduce rEC k pol0 f1 f2 =
  or_cnf_opt unsat deduce
    (and_cnf_opt (rEC (negb pol0) k f1) (rEC false k f2))
    (and_cnf_opt (rEC pol0 k f1) (rEC true k f2))

(** val is_bool : kind -> ('a1, 'a2, 'a3, 'a4) tFormula -> bool option **)

let is_bool _ = function
| TT _ -> Some true
| FF _ -> Some false
| _ -> None

(** val xcnf :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3)
    cnf) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> bool -> kind -> ('a1, 'a3, 'a4,
    'a5) tFormula -> ('a2, 'a3) cnf **)

let rec xcnf unsat deduce normalise0 negate0 pol0 _ = function
| TT _ -> if pol0 then cnf_tt else cnf_ff
| FF _ -> if pol0 then cnf_ff else cnf_tt
| X (_, _) -> cnf_ff
| A (_, x, t0) -> if pol0 then normalise0 x t0 else negate0 x t0
| AND (k0, e1, e2) ->
  mk_and unsat deduce (fun x x0 x1 ->
    xcnf unsat deduce normalise0 negate0 x x0 x1) k0 pol0 e1 e2
| OR (k0, e1, e2) ->
  mk_or unsat deduce (fun x x0 x1 ->
    xcnf unsat deduce normalise0 negate0 x x0 x1) k0 pol0 e1 e2
| NOT (k0, e) -> xcnf unsat deduce normalise0 negate0 (negb pol0) k0 e
| IMPL (k0, e1, _, e2) ->
  mk_impl unsat deduce (fun x x0 x1 ->
    xcnf unsat deduce normalise0 negate0 x x0 x1) k0 pol0 e1 e2
| IFF (k0, e1, e2) ->
  (match is_bool k0 e2 with
   | Some isb ->
     xcnf unsat deduce normalise0 negate0 (if isb then pol0 else negb pol0)
       k0 e1
   | None ->
     mk_iff unsat deduce (fun x x0 x1 ->
       xcnf unsat deduce normalise0 negate0 x x0 x1) k0 pol0 e1 e2)
| EQ (e1, e2) ->
  (match is_bool IsBool e2 with
   | Some isb ->
     xcnf unsat deduce normalise0 negate0 (if isb then pol0 else negb pol0)
       IsBool e1
   | None ->
     mk_iff unsat deduce (fun x x0 x1 ->
       xcnf unsat deduce normalise0 negate0 x x0 x1) IsBool pol0 e1 e2)

(** val cnf_checker :
    (('a1 * 'a2) list -> 'a3 -> bool) -> ('a1, 'a2) cnf -> 'a3 list -> bool **)

let rec cnf_checker checker0 f l =
  match f with
  | Nil -> true
  | Cons (e, f0) ->
    (match l with
     | Nil -> false
     | Cons (c, l0) ->
       if checker0 e c then cnf_checker checker0 f0 l0 else false)

(** val tauto_checker :
    ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a3 -> ('a2, 'a3)
    cnf) -> ('a1 -> 'a3 -> ('a2, 'a3) cnf) -> (('a2 * 'a3) list -> 'a4 ->
    bool) -> ('a1, rtyp, 'a3, unit0) gFormula -> 'a4 list -> bool **)

let tauto_checker unsat deduce normalise0 negate0 checker0 f w =
  cnf_checker checker0 (xcnf unsat deduce normalise0 negate0 true IsProp f) w

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

type 'c nFormula = 'c polC * op1

(** val opMult : op1 -> op1 -> op1 option **)

let opMult o o' =
  match o with
  | Equal -> Some Equal
  | NonEqual ->
    (match o' with
     | Equal -> Some Equal
     | NonEqual -> Some NonEqual
     | _ -> None)
  | Strict -> (match o' with
               | NonEqual -> None
               | _ -> Some o')
  | NonStrict ->
    (match o' with
     | Equal -> Some Equal
     | NonEqual -> None
     | _ -> Some NonStrict)

(** val opAdd : op1 -> op1 -> op1 option **)

let opAdd o o' =
  match o with
  | Equal -> Some o'
  | NonEqual -> (match o' with
                 | Equal -> Some NonEqual
                 | _ -> None)
  | Strict -> (match o' with
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
  | Some x -> (match o' with
               | Some x' -> f x x'
               | None -> None)
  | None -> None

(** val pexpr_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula option **)

let pexpr_times_nformula cO cI cplus ctimes ceqb e = function
| (ef, o) ->
  (match o with
   | Equal -> Some ((pmul cO cI cplus ctimes ceqb e ef), Equal)
   | _ -> None)

(** val nformula_times_nformula :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option **)

let nformula_times_nformula cO cI cplus ctimes ceqb f1 f2 =
  let (e1, o1) = f1 in
  let (e2, o2) = f2 in
  map_option (fun x -> Some ((pmul cO cI cplus ctimes ceqb e1 e2), x))
    (opMult o1 o2)

(** val nformula_plus_nformula :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1
    nFormula -> 'a1 nFormula option **)

let nformula_plus_nformula cO cplus ceqb f1 f2 =
  let (e1, o1) = f1 in
  let (e2, o2) = f2 in
  map_option (fun x -> Some ((padd cO cplus ceqb e1 e2), x)) (opAdd o1 o2)

(** val eval_Psatz :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1
    nFormula option **)

let rec eval_Psatz cO cI cplus ctimes ceqb cleb l = function
| PsatzIn n0 -> Some (nth n0 l ((Pc cO), Equal))
| PsatzSquare e0 -> Some ((psquare cO cI cplus ctimes ceqb e0), NonStrict)
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
| PsatzC c -> if cltb ceqb cleb cO c then Some ((Pc c), Strict) else None
| PsatzZ -> Some ((Pc cO), Equal)

(** val check_inconsistent :
    'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula ->
    bool **)

let check_inconsistent cO ceqb cleb = function
| (e, op) ->
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

let norm =
  norm_aux

(** val psub0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
    -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol **)

let psub0 =
  psub

(** val padd0 :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol
    -> 'a1 pol **)

let padd0 =
  padd

type zWitness = z psatz

(** val psub1 : z pol -> z pol -> z pol **)

let psub1 =
  psub0 Z0 Z.add Z.sub Z.opp zeq_bool

(** val padd1 : z pol -> z pol -> z pol **)

let padd1 =
  padd0 Z0 Z.add zeq_bool

(** val normZ : z pExpr -> z pol **)

let normZ =
  norm Z0 (Zpos XH) Z.add Z.mul Z.sub Z.opp zeq_bool

(** val zunsat : z nFormula -> bool **)

let zunsat =
  check_inconsistent Z0 zeq_bool Z.leb

(** val zdeduce : z nFormula -> z nFormula -> z nFormula option **)

let zdeduce =
  nformula_plus_nformula Z0 Z.add zeq_bool

(** val xnnormalise : z formula -> z nFormula **)

let xnnormalise t0 =
  let { flhs = lhs; fop = o; frhs = rhs } = t0 in
  let lhs0 = normZ lhs in
  let rhs0 = normZ rhs in
  (match o with
   | OpEq -> ((psub1 rhs0 lhs0), Equal)
   | OpNEq -> ((psub1 rhs0 lhs0), NonEqual)
   | OpLe -> ((psub1 rhs0 lhs0), NonStrict)
   | OpGe -> ((psub1 lhs0 rhs0), NonStrict)
   | OpLt -> ((psub1 rhs0 lhs0), Strict)
   | OpGt -> ((psub1 lhs0 rhs0), Strict))

(** val xnormalise : z nFormula -> z nFormula list **)

let xnormalise = function
| (e, o) ->
  (match o with
   | Equal ->
     Cons (((psub1 e (Pc (Zpos XH))), NonStrict), (Cons
       (((psub1 (Pc (Zneg XH)) e), NonStrict), Nil)))
   | NonEqual -> Cons ((e, Equal), Nil)
   | Strict -> Cons (((psub1 (Pc Z0) e), NonStrict), Nil)
   | NonStrict -> Cons (((psub1 (Pc (Zneg XH)) e), NonStrict), Nil))

(** val cnf_of_list :
    'a1 -> z nFormula list -> (z nFormula * 'a1) list list **)

let cnf_of_list tg l =
  fold_right (fun x acc ->
    if zunsat x then acc else Cons ((Cons ((x, tg), Nil)), acc)) cnf_tt l

(** val normalise : z formula -> 'a1 -> (z nFormula, 'a1) cnf **)

let normalise t0 tg =
  let f = xnnormalise t0 in
  if zunsat f then cnf_ff else cnf_of_list tg (xnormalise f)

(** val xnegate : z nFormula -> z nFormula list **)

let xnegate = function
| (e, o) ->
  (match o with
   | NonEqual ->
     Cons (((psub1 e (Pc (Zpos XH))), NonStrict), (Cons
       (((psub1 (Pc (Zneg XH)) e), NonStrict), Nil)))
   | Strict -> Cons (((psub1 e (Pc (Zpos XH))), NonStrict), Nil)
   | x -> Cons ((e, x), Nil))

(** val negate : z formula -> 'a1 -> (z nFormula, 'a1) cnf **)

let negate t0 tg =
  let f = xnnormalise t0 in
  if zunsat f then cnf_tt else cnf_of_list tg (xnegate f)

(** val ceiling : z -> z -> z **)

let ceiling a b =
  let (q, r) = Z.div_eucl a b in
  (match r with
   | Z0 -> q
   | _ -> Z.add q (Zpos XH))

type zArithProof =
| DoneProof
| RatProof of zWitness * zArithProof
| CutProof of zWitness * zArithProof
| EnumProof of zWitness * zWitness * zArithProof list
| ExProof of positive * zArithProof

(** val zgcdM : z -> z -> z **)

let zgcdM x y =
  Z.max (Z.gcd x y) (Zpos XH)

(** val zgcd_pol : z polC -> z * z **)

let rec zgcd_pol = function
| Pc c -> (Z0, c)
| Pinj (_, p2) -> zgcd_pol p2
| PX (p2, _, q) ->
  let (g1, c1) = zgcd_pol p2 in
  let (g2, c2) = zgcd_pol q in ((zgcdM (zgcdM g1 c1) g2), c2)

(** val zdiv_pol : z polC -> z -> z polC **)

let rec zdiv_pol p x =
  match p with
  | Pc c -> Pc (Z.div c x)
  | Pinj (j, p2) -> Pinj (j, (zdiv_pol p2 x))
  | PX (p2, j, q) -> PX ((zdiv_pol p2 x), j, (zdiv_pol q x))

(** val makeCuttingPlane : z polC -> z polC * z **)

let makeCuttingPlane p =
  let (g, c) = zgcd_pol p in
  if Z.gtb g Z0
  then ((zdiv_pol (psubC Z.sub p c) g), (Z.opp (ceiling (Z.opp c) g)))
  else (p, Z0)

(** val genCuttingPlane : z nFormula -> ((z polC * z) * op1) option **)

let genCuttingPlane = function
| (e, op) ->
  (match op with
   | Equal ->
     let (g, c) = zgcd_pol e in
     if if Z.gtb g Z0
        then if negb (zeq_bool c Z0)
             then negb (zeq_bool (Z.gcd g c) g)
             else false
        else false
     then None
     else Some ((makeCuttingPlane e), Equal)
   | NonEqual -> Some ((e, Z0), op)
   | Strict -> Some ((makeCuttingPlane (psubC Z.sub e (Zpos XH))), NonStrict)
   | NonStrict -> Some ((makeCuttingPlane e), NonStrict))

(** val nformula_of_cutting_plane : ((z polC * z) * op1) -> z nFormula **)

let nformula_of_cutting_plane = function
| (e_z, o) -> let (e, z0) = e_z in ((padd1 e (Pc z0)), o)

(** val is_pol_Z0 : z polC -> bool **)

let is_pol_Z0 = function
| Pc z0 -> (match z0 with
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

(** val bound_var : positive -> z formula **)

let bound_var v =
  { flhs = (PEX v); fop = OpGe; frhs = (PEc Z0) }

(** val mk_eq_pos : positive -> positive -> positive -> z formula **)

let mk_eq_pos x y t0 =
  { flhs = (PEX x); fop = OpEq; frhs = (PEsub ((PEX y), (PEX t0))) }

(** val max_var : positive -> z pol -> positive **)

let rec max_var jmp = function
| Pc _ -> jmp
| Pinj (j, p2) -> max_var (Coq_Pos.add j jmp) p2
| PX (p2, _, q) -> Coq_Pos.max (max_var jmp p2) (max_var (Coq_Pos.succ jmp) q)

(** val max_var_nformulae : z nFormula list -> positive **)

let max_var_nformulae l =
  fold_left (fun acc f -> Coq_Pos.max acc (max_var XH (fst f))) l XH

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
           let (p2, op3) = p in
           let (e1, z1) = p2 in
           (match genCuttingPlane f2 with
            | Some p3 ->
              let (p4, op4) = p3 in
              let (e2, z2) = p4 in
              if if if valid_cut_sign op3 then valid_cut_sign op4 else false
                 then is_pol_Z0 (padd1 e1 e2)
                 else false
              then let rec label pfs lb ub =
                     match pfs with
                     | Nil -> Z.gtb lb ub
                     | Cons (pf1, rsr) ->
                       if zChecker (Cons (((psub1 e1 (Pc lb)), Equal), l)) pf1
                       then label rsr (Z.add lb (Zpos XH)) ub
                       else false
                   in label pf0 (Z.opp z1) z2
              else false
            | None -> true)
         | None -> true)
      | None -> false)
   | None -> false)
| ExProof (x, prf) ->
  let fr = max_var_nformulae l in
  if Coq_Pos.leb x fr
  then let z0 = Coq_Pos.succ fr in
       let t0 = Coq_Pos.succ z0 in
       let nfx = xnnormalise (mk_eq_pos x z0 t0) in
       let posz = xnnormalise (bound_var z0) in
       let post = xnnormalise (bound_var t0) in
       zChecker (Cons (nfx, (Cons (posz, (Cons (post, l)))))) prf
  else false

(** val zTautoChecker : z formula bFormula -> zArithProof list -> bool **)

let zTautoChecker f w =
  tauto_checker zunsat zdeduce normalise negate (fun cl ->
    zChecker (map fst cl)) f w

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val eqb0 : Uint63.t -> Uint63.t -> bool **)

let eqb0 = Uint63.equal

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val leb0 : Uint63.t -> Uint63.t -> bool **)

let leb0 = Uint63.le

(** val digits : Uint63.t **)

let digits =
  (Uint63.of_int (63))

(** val is_zero : Uint63.t -> bool **)

let is_zero i =
  eqb0 i (Uint63.of_int (0))

(** val is_even : Uint63.t -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

(** val bit : Uint63.t -> Uint63.t -> bool **)

let bit i n0 =
  negb (is_zero (lsl0 (lsr0 i n0) (sub0 digits (Uint63.of_int (1)))))

(** val compare0 : Uint63.t -> Uint63.t -> int **)

let compare0 = Uint63.compare

type 'x compare1 =
| LT
| EQ0
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare1

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> Left
    | _ -> Right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> true
    | Right -> false
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    Nil

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | Nil -> true
  | Cons (_, _) -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | Nil -> false
  | Cons (p, l) ->
    let (k', _) = p in
    (match X.compare k k' with
     | LT -> false
     | EQ0 -> true
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t ->
      bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | Nil -> f3 __
     | Cons (p, l) ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ0 -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | Nil -> None
  | Cons (p, s') ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ0 -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
      t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | Nil -> f3 __
     | Cons (p, l) ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = find_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ0 -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | Nil -> Cons ((k, x), Nil)
  | Cons (p, l) ->
    let (k', y) = p in
    (match X.compare k k' with
     | LT -> Cons ((k, x), s)
     | EQ0 -> Cons ((k, x), l)
     | GT -> Cons ((k', y), (add k x l)))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | Nil -> f3 __
     | Cons (p, l) ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ0 -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | Nil -> Nil
  | Cons (p, l) ->
    let (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ0 -> l
     | GT -> Cons ((k', x), (remove k l)))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t
      -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f2 f1 f0 f s =
    let f3 = f2 s in
    let f4 = f1 s in
    let f5 = f0 s in
    let f6 = f s in
    (match s with
     | Nil -> f3 __
     | Cons (p, l) ->
       let (t0, e) = p in
       let f7 = f6 t0 e l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f2 f1 f0 f l in f7 __ __ hrec
       in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match X.compare k t0 with
        | LT -> f10 __ __
        | EQ0 -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | Nil -> acc
    | Cons (p, m') -> let (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | Nil -> f2 __
     | Cons (p, l) ->
       let (t0, e) = p in
       let f4 = f3 t0 e l __ in
       let hrec = fold_rect f1 f0 f l (f1 t0 e acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
      'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | Nil -> (match m' with
              | Nil -> true
              | Cons (_, _) -> false)
    | Cons (p, l) ->
      let (x, e) = p in
      (match m' with
       | Nil -> false
       | Cons (p2, l') ->
         let (x', e') = p2 in
         (match X.compare x x' with
          | EQ0 -> if cmp e e' then equal cmp l l' else false
          | _ -> false))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare1
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) ->
      ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
      'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f2 f1 f0 f m m' =
    let f3 = f2 m m' in
    let f4 = f1 m m' in
    let f5 = f0 m m' in
    let f6 = f m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | Nil ->
       let f9 = f3 __ in (match m' with
                          | Nil -> f9 __
                          | Cons (_, _) -> f8 __)
     | Cons (p, l) ->
       let (t0, e) = p in
       let f9 = f5 t0 e l __ in
       let f10 = f4 t0 e l __ in
       (match m' with
        | Nil -> f8 __
        | Cons (p2, l0) ->
          let (t1, e0) = p2 in
          let f11 = f9 t1 e0 l0 __ in
          let f12 = let _x = X.compare t0 t1 in f11 _x __ in
          let f13 = f10 t1 e0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f2 f1 f0 f l l0 in f13 __ __ hrec
          in
          (match X.compare t0 t1 with
           | EQ0 -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
      -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
      -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1,
      y2, y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | Nil -> Nil
  | Cons (p, m') -> let (k, e) = p in Cons ((k, (f e)), (map f m'))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | Nil -> Nil
  | Cons (p, m') -> let (k, e) = p in Cons ((k, (f k e)), (mapi f m'))

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list **)

  let option_cons k o l =
    match o with
    | Some e -> Cons ((k, e), l)
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | Nil -> Nil
  | Cons (p, l) ->
    let (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | Nil -> Nil
  | Cons (p, l') ->
    let (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | Nil -> map2_r f
  | Cons (p, l) ->
    let (k, e) = p in
    let rec map2_aux m' = match m' with
    | Nil -> map2_l f m
    | Cons (p2, l') ->
      let (k', e') = p2 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ0 -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let rec combine m = match m with
  | Nil -> map (fun e' -> (None, (Some e')))
  | Cons (p, l) ->
    let (k, e) = p in
    let rec combine_aux m' = match m' with
    | Nil -> map (fun e0 -> ((Some e0), None)) m
    | Cons (p2, l') ->
      let (k', e') = p2 in
      (match X.compare k k' with
       | LT -> Cons ((k, ((Some e), None)), (combine l m'))
       | EQ0 -> Cons ((k, ((Some e), (Some e'))), (combine l l'))
       | GT -> Cons ((k', (None, (Some e'))), (combine_aux l')))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 Nil

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> (match o' with
               | Some _ -> Some (o, o')
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> sumbool

  val ge_lt_dec : t -> t -> sumbool

  val eq_dec : t -> t -> sumbool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> sumbool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then Left else Right

  (** val ge_lt_dec : z -> z -> sumbool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then Right else Left

  (** val i2z : t -> z **)

  let i2z n0 =
    n0
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> true
  | Node (_, _, _, _, _) -> false

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> false
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ0 -> true
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ0 -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    (match I.gt_le_dec hl (I.add hr I._2) with
     | Left ->
       (match l with
        | Leaf -> assert_false l x d r
        | Node (ll, lx, ld, lr, _) ->
          (match I.ge_lt_dec (height ll) (height lr) with
           | Left -> create ll lx ld (create lr x d r)
           | Right ->
             (match lr with
              | Leaf -> assert_false l x d r
              | Node (lrl, lrx, lrd, lrr, _) ->
                create (create ll lx ld lrl) lrx lrd (create lrr x d r))))
     | Right ->
       (match I.gt_le_dec hr (I.add hl I._2) with
        | Left ->
          (match r with
           | Leaf -> assert_false l x d r
           | Node (rl, rx, rd, rr, _) ->
             (match I.ge_lt_dec (height rr) (height rl) with
              | Left -> create (create l x d rl) rx rd rr
              | Right ->
                (match rl with
                 | Leaf -> assert_false l x d r
                 | Node (rll, rlx, rld, rlr, _) ->
                   create (create l x d rll) rlx rld (create rlr rx rd rr))))
        | Right -> create l x d r))

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ0 -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1) **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> (r, (x, d))
    | Node (ll, lx, ld, lr, _) ->
      let (l', m) = remove_min ll lx ld lr in ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let (s2', p) = remove_min l2 x2 d2 r2 in
         let (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ0 -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        (match I.gt_le_dec lh (I.add rh I._2) with
         | Left -> bal ll lx ld (join lr x d r)
         | Right ->
           (match I.gt_le_dec rh (I.add lh I._2) with
            | Left -> bal (join_aux rl) rx rd rr
            | Right -> create l x d r))
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ0 -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) ->
    elements_aux (Cons ((x, d), (elements_aux acc r))) l

  (** val elements : 'a1 tree -> (key * 'a1) list **)

  let elements m =
    elements_aux Nil m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> false
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ0 -> if cmp d1 d2 then cont (cons r2 e3) else false
     | _ -> false)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> true
  | More (_, _, _, _) -> false

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
       I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __
        -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ ->
        __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (x, x0, x1, x2) -> f x x0 x1 x2 __ __ __
    | R_bal_1 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f0 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_2 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f1 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_3 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f2 x x0 x1 x2 __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_4 (x, x0, x1, x2) -> f3 x x0 x1 x2 __ __ __ __ __
    | R_bal_5 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f4 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __
    | R_bal_6 (x, x0, x1, x2, x3, x4, x5, x6, x7) ->
      f5 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ __
    | R_bal_7 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f6 x x0 x1 x2 __ __ __ __ x3 x4 x5 x6 x7 __ __ __ x8 x9 x10 x11 x12 __
    | R_bal_8 (x, x0, x1, x2) -> f7 x x0 x1 x2 __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r0) -> f l x d r0 __
    | R_remove_min_1 (l, x, d, r0, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r0 ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (x, x0) -> f x x0 __
    | R_merge_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_merge_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12,
                 x13, x14) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __ x13 x14 __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (x, x0) -> f x x0 __
    | R_concat_1 (x, x0, x1, x2, x3, x4, x5) -> f0 x x0 x1 x2 x3 x4 x5 __ __
    | R_concat_2 (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
      f1 x x0 x1 x2 x3 x4 x5 __ x6 x7 x8 x9 x10 __ x11 x12 __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
       * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res r2
        (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t ->
        __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key ->
        'a2 -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree ->
        __ -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3
        tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree ->
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key * 'a1) list **)

    let rec flatten_e = function
    | End -> Nil
    | More (x, e0, t0, r) -> Cons ((x, e0), (app (elements t0) (flatten_e r)))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module IntOrderedType =
 struct
  type t = Uint63.t

  (** val compare : Uint63.t -> Uint63.t -> Uint63.t compare1 **)

  let compare x y =
    if ltb0 x y then LT else if eqb0 x y then EQ0 else GT

  (** val eq_dec : Uint63.t -> Uint63.t -> sumbool **)

  let eq_dec x y =
    if eqb0 x y then Left else Right
 end

module Map = Make(IntOrderedType)

type 'a array = ('a Map.t * 'a) * Uint63.t

(** val make : Uint63.t -> 'a1 -> 'a1 array **)

let make l d =
  ((Map.empty, d), l)

module Coq__2 = struct
 (** val get : 'a1 array -> Uint63.t -> 'a1 **)
 let get t0 i =
   let (td, l) = t0 in
   let (t1, d) = td in
   if ltb0 i l then (match Map.find i t1 with
                     | Some x -> x
                     | None -> d) else d
end
include Coq__2

(** val default : 'a1 array -> 'a1 **)

let default = function
| (td, _) -> let (_, d) = td in d

(** val set : 'a1 array -> Uint63.t -> 'a1 -> 'a1 array **)

let set t0 i a =
  let (td, l) = t0 in
  if leb0 l i then t0 else let (t1, d) = td in (((Map.add i a t1), d), l)

(** val length0 : 'a1 array -> Uint63.t **)

let length0 = function
| (_, l) -> l

(** val iter_int63_aux : nat -> Uint63.t -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let rec iter_int63_aux n0 i f =
  match n0 with
  | O -> (fun x -> x)
  | S n1 ->
    if eqb0 i (Uint63.of_int (0))
    then (fun x -> x)
    else let g = iter_int63_aux n1 (lsr0 i (Uint63.of_int (1))) f in
         (fun x -> if bit i (Uint63.of_int (0)) then f (g (g x)) else g (g x))

(** val iter_int63 : Uint63.t -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

let iter_int63 i f x =
  iter_int63_aux size i f x

(** val foldi :
    (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let foldi f from to0 a =
  if leb0 to0 from
  then a
  else let (_, r) =
         iter_int63 (sub0 to0 from) (fun jy ->
           let (j, y) = jy in ((add0 j (Uint63.of_int (1))), (f j y))) (from,
           a)
       in
       r

(** val to_list : 'a1 array -> 'a1 list **)

let to_list t0 =
  rev
    (foldi (fun i l -> Cons ((get t0 i), l)) (Uint63.of_int (0)) (length0 t0)
      Nil)

(** val amapi : (Uint63.t -> 'a1 -> 'a2) -> 'a1 array -> 'a2 array **)

let amapi f t0 =
  let l = length0 t0 in
  foldi (fun i tb -> set tb i (f i (get t0 i))) (Uint63.of_int (0)) l
    (make l (f l (default t0)))

(** val amap : ('a1 -> 'a2) -> 'a1 array -> 'a2 array **)

let amap f =
  amapi (fun _ -> f)

(** val afold_left : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 array -> 'a1 **)

let afold_left default0 oP v =
  if eqb0 (length0 v) (Uint63.of_int (0))
  then default0
  else foldi (fun i a -> oP a (get v i)) (Uint63.of_int (1)) (length0 v)
         (get v (Uint63.of_int (0)))

(** val afold_right : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 array -> 'a1 **)

let afold_right default0 oP v =
  if eqb0 (length0 v) (Uint63.of_int (0))
  then default0
  else foldi (fun i ->
         oP (get v (sub0 (sub0 (length0 v) (Uint63.of_int (1))) i)))
         (Uint63.of_int (1)) (length0 v)
         (get v (sub0 (length0 v) (Uint63.of_int (1))))

(** val aexistsbi : (Uint63.t -> 'a1 -> bool) -> 'a1 array -> bool **)

let aexistsbi f t0 =
  afold_left false (fun b1 b2 -> if b1 then true else b2) (amapi f t0)

(** val aforallbi : (Uint63.t -> 'a1 -> bool) -> 'a1 array -> bool **)

let aforallbi f t0 =
  afold_left true (fun b1 b2 -> if b1 then b2 else false) (amapi f t0)

(** val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec forallb2 f l1 l2 =
  match l1 with
  | Nil -> (match l2 with
            | Nil -> true
            | Cons (_, _) -> false)
  | Cons (a, l3) ->
    (match l2 with
     | Nil -> false
     | Cons (b, l4) -> if f a b then forallb2 f l3 l4 else false)

module RAWBITVECTOR_LIST =
 struct
  (** val beq_list : bool list -> bool list -> bool **)

  let rec beq_list l m =
    match l with
    | Nil -> (match m with
              | Nil -> true
              | Cons (_, _) -> false)
    | Cons (x, l') ->
      (match m with
       | Nil -> false
       | Cons (y, m') -> if eqb x y then beq_list l' m' else false)

  (** val pow2 : nat -> nat **)

  let rec pow2 = function
  | O -> S O
  | S n' -> mul (S (S O)) (pow2 n')

  (** val _list2nat_be : bool list -> nat -> nat -> nat **)

  let rec _list2nat_be a n0 i =
    match a with
    | Nil -> n0
    | Cons (xa, xsa) ->
      if xa
      then _list2nat_be xsa (add n0 (pow2 i)) (add i (S O))
      else _list2nat_be xsa n0 (add i (S O))

  (** val list2nat_be : bool list -> nat **)

  let list2nat_be a =
    _list2nat_be a O O
 end

module Lit =
 struct
  (** val is_pos : Uint63.t -> bool **)

  let is_pos =
    is_even

  (** val blit : Uint63.t -> Uint63.t **)

  let blit l =
    lsr0 l (Uint63.of_int (1))

  (** val lit : Uint63.t -> Uint63.t **)

  let lit x =
    lsl0 x (Uint63.of_int (1))

  (** val neg : Uint63.t -> Uint63.t **)

  let neg l =
    lxor0 l (Uint63.of_int (1))

  (** val nlit : Uint63.t -> Uint63.t **)

  let nlit x =
    neg (lit x)

  (** val _true : Uint63.t **)

  let _true =
    (Uint63.of_int (0))

  (** val _false : Uint63.t **)

  let _false =
    (Uint63.of_int (2))
 end

module C =
 struct
  type t = Uint63.t list

  (** val _true : t **)

  let _true =
    Cons (Lit._true, Nil)

  (** val is_false : t -> bool **)

  let is_false = function
  | Nil -> true
  | Cons (_, _) -> false

  (** val or_aux : (t -> t -> t) -> Uint63.t -> t -> t -> Uint63.t list **)

  let rec or_aux or0 l1 c1 c2 = match c2 with
  | Nil -> Cons (l1, c1)
  | Cons (l2, c2') ->
    (match compare0 l1 l2 with
     | 0 -> Cons (l1, (or0 c1 c2'))
     | (-1) -> Cons (l1, (or0 c1 c2))
     | 1 -> Cons (l2, (or_aux or0 l1 c1 c2')))

  (** val coq_or : t -> t -> t **)

  let rec coq_or c1 c2 =
    match c1 with
    | Nil -> c2
    | Cons (l1, c3) ->
      (match c2 with
       | Nil -> c1
       | Cons (l2, c2') ->
         (match compare0 l1 l2 with
          | 0 -> Cons (l1, (coq_or c3 c2'))
          | (-1) -> Cons (l1, (coq_or c3 c2))
          | 1 -> Cons (l2, (or_aux coq_or l1 c3 c2'))))

  (** val resolve_aux : (t -> t -> t) -> Uint63.t -> t -> t -> t **)

  let rec resolve_aux resolve0 l1 c1 c2 = match c2 with
  | Nil -> _true
  | Cons (l2, c2') ->
    (match compare0 l1 l2 with
     | 0 -> Cons (l1, (resolve0 c1 c2'))
     | (-1) ->
       if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
       then coq_or c1 c2'
       else Cons (l1, (resolve0 c1 c2))
     | 1 ->
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
          | 0 -> Cons (l1, (resolve c3 c2'))
          | (-1) ->
            if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
            then coq_or c3 c2'
            else Cons (l1, (resolve c3 c2))
          | 1 ->
            if eqb0 (lxor0 l1 l2) (Uint63.of_int (1))
            then coq_or c3 c2'
            else Cons (l2, (resolve_aux resolve l1 c3 c2'))))
 end

  let stepnum : int ref = assert false (* use the number of the last input clause *)

  let print_clause (c:C.t) : unit =
    incr stepnum;
    Printf.printf "%d : [" !stepnum;
    let rec pp c =
      match c with
        | Nil -> Printf.printf "]\n"
        | Cons (l, c') ->
           (Printf.printf "; %s" (Uint63.to_string l);
            pp c')
    in
    pp c

module S =
 struct
  type t = C.t array

  (** val get : t -> Uint63.t -> C.t **)

  let get =
    get

  (** val internal_set : t -> Uint63.t -> C.t -> t **)

  let internal_set =
    set

  (** val make : Uint63.t -> t **)

  let make nclauses =
    make nclauses C._true

  (** val insert_no_simpl : Uint63.t -> Uint63.t list -> Uint63.t list **)

  let rec insert_no_simpl l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare0 l1 l2 with
     | 0 -> c
     | (-1) -> Cons (l1, c)
     | 1 -> Cons (l2, (insert_no_simpl l1 c')))

  (** val insert_keep : Uint63.t -> Uint63.t list -> Uint63.t list **)

  let rec insert_keep l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare0 l1 l2 with
     | 1 -> Cons (l2, (insert_keep l1 c'))
     | _ -> Cons (l1, c))

  (** val sort : Uint63.t list -> Uint63.t list **)

  let rec sort = function
  | Nil -> Nil
  | Cons (l1, c0) -> insert_no_simpl l1 (sort c0)

  (** val sort_keep : Uint63.t list -> Uint63.t list **)

  let rec sort_keep = function
  | Nil -> Nil
  | Cons (l1, c0) -> insert_keep l1 (sort_keep c0)

  (** val set_clause : t -> Uint63.t -> C.t -> t **)

  let set_clause s pos c =
    set s pos (sort c)

  (** val set_clause_keep : t -> Uint63.t -> C.t -> t **)

  let set_clause_keep s pos c =
    set s pos (sort_keep c)

  (** val set_resolve : t -> Uint63.t -> Uint63.t array -> t **)

  let set_resolve s pos r =
    let len = length0 r in
    if eqb0 len (Uint63.of_int (0))
    then s
    else let c =
           foldi (fun i c' -> C.resolve (get s (Coq__2.get r i)) c')
             (Uint63.of_int (1)) len
             (get s (Coq__2.get r (Uint63.of_int (0))))
         in
         print_clause c;
         internal_set s pos c

  (** val subclause : Uint63.t list -> Uint63.t list -> bool **)

  let subclause cl1 cl2 =
    forallb (fun l1 ->
      if if eqb0 l1 Lit._false then true else eqb0 l1 (Lit.neg Lit._true)
      then true
      else existsb (fun l2 -> eqb0 l1 l2) cl2) cl1

  (** val check_weaken : t -> Uint63.t -> Uint63.t list -> C.t **)

  let check_weaken s cid cl =
    if subclause (get s cid) cl then cl else C._true

  (** val set_weaken : t -> Uint63.t -> Uint63.t -> Uint63.t list -> t **)

  let set_weaken s pos cid cl =
    set_clause_keep s pos (check_weaken s cid cl)
 end

module Form =
 struct
  type form =
  | Fatom of Uint63.t
  | Ftrue
  | Ffalse
  | Fnot2 of Uint63.t * Uint63.t
  | Fand of Uint63.t array
  | For of Uint63.t array
  | Fimp of Uint63.t array
  | Fxor of Uint63.t * Uint63.t
  | Fiff of Uint63.t * Uint63.t
  | Fite of Uint63.t * Uint63.t * Uint63.t
  | FbbT of Uint63.t * Uint63.t list

  (** val is_Ftrue : form -> bool **)

  let is_Ftrue = function
  | Ftrue -> true
  | _ -> false

  (** val is_Ffalse : form -> bool **)

  let is_Ffalse = function
  | Ffalse -> true
  | _ -> false

  (** val lt_form : Uint63.t -> form -> bool **)

  let lt_form i = function
  | Fnot2 (_, l) -> ltb0 (Lit.blit l) i
  | Fand args -> aforallbi (fun _ l -> ltb0 (Lit.blit l) i) args
  | For args -> aforallbi (fun _ l -> ltb0 (Lit.blit l) i) args
  | Fimp args -> aforallbi (fun _ l -> ltb0 (Lit.blit l) i) args
  | Fxor (a, b) -> if ltb0 (Lit.blit a) i then ltb0 (Lit.blit b) i else false
  | Fiff (a, b) -> if ltb0 (Lit.blit a) i then ltb0 (Lit.blit b) i else false
  | Fite (a, b, c) ->
    if if ltb0 (Lit.blit a) i then ltb0 (Lit.blit b) i else false
    then ltb0 (Lit.blit c) i
    else false
  | FbbT (_, ls) -> forallb (fun l -> ltb0 (Lit.blit l) i) ls
  | _ -> true

  (** val wf : form array -> bool **)

  let wf t_form =
    aforallbi lt_form t_form

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
  | Tindex of n
  | TZ
  | Tbool
  | Tpositive
  | TBV of n

  (** val eqb : coq_type -> coq_type -> bool **)

  let rec eqb a b =
    match a with
    | TFArray (k1, e1) ->
      (match b with
       | TFArray (k2, e2) -> if eqb k1 k2 then eqb e1 e2 else false
       | _ -> false)
    | Tindex i -> (match b with
                   | Tindex j -> N.eqb i j
                   | _ -> false)
    | TZ -> (match b with
             | TZ -> true
             | _ -> false)
    | Tbool -> (match b with
                | Tbool -> true
                | _ -> false)
    | Tpositive -> (match b with
                    | Tpositive -> true
                    | _ -> false)
    | TBV n0 -> (match b with
                 | TBV m -> N.eqb n0 m
                 | _ -> false)
 end

(** val list_beq : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_beq eq_A x y =
  match x with
  | Nil -> (match y with
            | Nil -> true
            | Cons (_, _) -> false)
  | Cons (x0, x1) ->
    (match y with
     | Nil -> false
     | Cons (x2, x3) -> if eq_A x0 x2 then list_beq eq_A x1 x3 else false)

module Atom =
 struct
  type cop =
  | CO_xH
  | CO_Z0
  | CO_BV of bool list * n

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
  | BO_BVmult of n
  | BO_BVult of n
  | BO_BVslt of n
  | BO_BVconcat of n * n
  | BO_BVshl of n
  | BO_BVshr of n
  | BO_select of Typ.coq_type * Typ.coq_type
  | BO_diffarray of Typ.coq_type * Typ.coq_type

  type nop =
    Typ.coq_type
    (* singleton inductive, whose constructor was NO_distinct *)

  type terop =
  | TO_store of Typ.coq_type * Typ.coq_type

  type atom =
  | Acop of cop
  | Auop of unop * Uint63.t
  | Abop of binop * Uint63.t * Uint63.t
  | Atop of terop * Uint63.t * Uint63.t * Uint63.t
  | Anop of nop * Uint63.t list
  | Aapp of Uint63.t * Uint63.t list

  (** val cop_eqb : cop -> cop -> bool **)

  let cop_eqb o o' =
    match o with
    | CO_xH -> (match o' with
                | CO_xH -> true
                | _ -> false)
    | CO_Z0 -> (match o' with
                | CO_Z0 -> true
                | _ -> false)
    | CO_BV (bv, s) ->
      (match o' with
       | CO_BV (bv', s') ->
         if N.eqb s s' then RAWBITVECTOR_LIST.beq_list bv bv' else false
       | _ -> false)

  (** val uop_eqb : unop -> unop -> bool **)

  let uop_eqb o o' =
    match o with
    | UO_xO -> (match o' with
                | UO_xO -> true
                | _ -> false)
    | UO_xI -> (match o' with
                | UO_xI -> true
                | _ -> false)
    | UO_Zpos -> (match o' with
                  | UO_Zpos -> true
                  | _ -> false)
    | UO_Zneg -> (match o' with
                  | UO_Zneg -> true
                  | _ -> false)
    | UO_Zopp -> (match o' with
                  | UO_Zopp -> true
                  | _ -> false)
    | UO_BVbitOf (s1, n0) ->
      (match o' with
       | UO_BVbitOf (s2, m) -> if Nat.eqb n0 m then N.eqb s1 s2 else false
       | _ -> false)
    | UO_BVnot s1 -> (match o' with
                      | UO_BVnot s2 -> N.eqb s1 s2
                      | _ -> false)
    | UO_BVneg s1 -> (match o' with
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
    | BO_Zplus -> (match o' with
                   | BO_Zplus -> true
                   | _ -> false)
    | BO_Zminus -> (match o' with
                    | BO_Zminus -> true
                    | _ -> false)
    | BO_Zmult -> (match o' with
                   | BO_Zmult -> true
                   | _ -> false)
    | BO_Zlt -> (match o' with
                 | BO_Zlt -> true
                 | _ -> false)
    | BO_Zle -> (match o' with
                 | BO_Zle -> true
                 | _ -> false)
    | BO_Zge -> (match o' with
                 | BO_Zge -> true
                 | _ -> false)
    | BO_Zgt -> (match o' with
                 | BO_Zgt -> true
                 | _ -> false)
    | BO_eq t0 -> (match o' with
                   | BO_eq t' -> Typ.eqb t0 t'
                   | _ -> false)
    | BO_BVand s1 -> (match o' with
                      | BO_BVand s2 -> N.eqb s1 s2
                      | _ -> false)
    | BO_BVor s1 -> (match o' with
                     | BO_BVor s2 -> N.eqb s1 s2
                     | _ -> false)
    | BO_BVxor s1 -> (match o' with
                      | BO_BVxor s2 -> N.eqb s1 s2
                      | _ -> false)
    | BO_BVadd s1 -> (match o' with
                      | BO_BVadd s2 -> N.eqb s1 s2
                      | _ -> false)
    | BO_BVmult s1 -> (match o' with
                       | BO_BVmult s2 -> N.eqb s1 s2
                       | _ -> false)
    | BO_BVult s1 -> (match o' with
                      | BO_BVult s2 -> N.eqb s1 s2
                      | _ -> false)
    | BO_BVslt s1 -> (match o' with
                      | BO_BVslt s2 -> N.eqb s1 s2
                      | _ -> false)
    | BO_BVconcat (s1, s2) ->
      (match o' with
       | BO_BVconcat (s3, s4) -> if N.eqb s1 s3 then N.eqb s2 s4 else false
       | _ -> false)
    | BO_BVshl s1 -> (match o' with
                      | BO_BVshl s2 -> N.eqb s1 s2
                      | _ -> false)
    | BO_BVshr s1 -> (match o' with
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

  let nop_eqb =
    Typ.eqb

  (** val eqb : atom -> atom -> bool **)

  let eqb t0 t' =
    match t0 with
    | Acop o -> (match t' with
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

  (** val lt_atom : Uint63.t -> atom -> bool **)

  let lt_atom i = function
  | Acop _ -> true
  | Auop (_, h) -> ltb0 h i
  | Abop (_, h1, h2) -> if ltb0 h1 i then ltb0 h2 i else false
  | Atop (_, h1, h2, h3) ->
    if if ltb0 h1 i then ltb0 h2 i else false then ltb0 h3 i else false
  | Anop (_, ha) -> forallb (fun h -> ltb0 h i) ha
  | Aapp (_, args) -> forallb (fun h -> ltb0 h i) args

  (** val wf : atom array -> bool **)

  let wf t_atom =
    aforallbi lt_atom t_atom

  (** val check_atom : atom array -> bool **)

  let check_atom t_atom =
    match default t_atom with
    | Acop c -> (match c with
                 | CO_xH -> wf t_atom
                 | _ -> false)
    | _ -> false
 end

(** val get_eq :
    Form.form array -> Atom.atom array -> Uint63.t -> (Uint63.t -> Uint63.t
    -> C.t) -> C.t **)

let get_eq t_form t_atom x f =
  match get t_form x with
  | Form.Fatom xa ->
    (match get t_atom xa with
     | Atom.Abop (b0, a, b) ->
       (match b0 with
        | Atom.BO_eq _ -> f a b
        | _ -> C._true)
     | _ -> C._true)
  | _ -> C._true

(** val check_trans_aux :
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t -> Uint63.t
    list -> Uint63.t -> C.t -> C.t **)

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
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t list -> C.t **)

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
    Form.form array -> Atom.atom array -> Uint63.t option list -> Uint63.t
    list -> Uint63.t list -> C.t -> C.t **)

let rec build_congr t_form t_atom eqs l r c =
  match eqs with
  | Nil ->
    (match l with
     | Nil -> (match r with
               | Nil -> c
               | Cons (_, _) -> C._true)
     | Cons (_, _) -> C._true)
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
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t option list ->
    C.t **)

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
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t -> Uint63.t
    option list -> C.t **)

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
    (Uint63.t -> positive option) -> Atom.atom -> positive option **)

let build_positive_atom_aux build_positive0 = function
| Atom.Acop c -> (match c with
                  | Atom.CO_xH -> Some XH
                  | _ -> None)
| Atom.Auop (u, a0) ->
  (match u with
   | Atom.UO_xO -> option_map (fun x -> XO x) (build_positive0 a0)
   | Atom.UO_xI -> option_map (fun x -> XI x) (build_positive0 a0)
   | _ -> None)
| _ -> None

(** val build_positive : Atom.atom array -> Uint63.t -> positive option **)

let build_positive t_atom =
  foldi (fun _ cont h -> build_positive_atom_aux cont (get t_atom h))
    (Uint63.of_int (0)) (length0 t_atom) (fun _ -> None)

(** val build_z_atom_aux : Atom.atom array -> Atom.atom -> z option **)

let build_z_atom_aux t_atom = function
| Atom.Acop c -> (match c with
                  | Atom.CO_Z0 -> Some Z0
                  | _ -> None)
| Atom.Auop (u, a0) ->
  (match u with
   | Atom.UO_Zpos -> option_map (fun x -> Zpos x) (build_positive t_atom a0)
   | Atom.UO_Zneg -> option_map (fun x -> Zneg x) (build_positive t_atom a0)
   | _ -> None)
| _ -> None

(** val build_z_atom : Atom.atom array -> Atom.atom -> z option **)

let build_z_atom =
  build_z_atom_aux

type vmap = positive * Atom.atom list

(** val find_var_aux :
    Atom.atom -> positive -> Atom.atom list -> positive option **)

let rec find_var_aux h p = function
| Nil -> None
| Cons (h', l0) ->
  let p2 = Coq_Pos.pred p in
  if Atom.eqb h h' then Some p2 else find_var_aux h p2 l0

(** val find_var : vmap -> Atom.atom -> vmap * positive **)

let find_var vm h =
  let (count, map0) = vm in
  (match find_var_aux h count map0 with
   | Some p -> (vm, p)
   | None -> (((Coq_Pos.succ count), (Cons (h, map0))), count))

(** val empty_vmap : vmap **)

let empty_vmap =
  (XH, Nil)

(** val build_pexpr_atom_aux :
    Atom.atom array -> (vmap -> Uint63.t -> vmap * z pExpr) -> vmap ->
    Atom.atom -> vmap * z pExpr **)

let build_pexpr_atom_aux t_atom build_pexpr0 vm h = match h with
| Atom.Auop (u, a) ->
  (match u with
   | Atom.UO_Zopp -> let (vm0, pe) = build_pexpr0 vm a in (vm0, (PEopp pe))
   | _ ->
     (match build_z_atom t_atom h with
      | Some z0 -> (vm, (PEc z0))
      | None -> let (vm0, p) = find_var vm h in (vm0, (PEX p))))
| Atom.Abop (b, a1, a2) ->
  (match b with
   | Atom.BO_Zplus ->
     let (vm0, pe1) = build_pexpr0 vm a1 in
     let (vm1, pe2) = build_pexpr0 vm0 a2 in (vm1, (PEadd (pe1, pe2)))
   | Atom.BO_Zminus ->
     let (vm0, pe1) = build_pexpr0 vm a1 in
     let (vm1, pe2) = build_pexpr0 vm0 a2 in (vm1, (PEsub (pe1, pe2)))
   | Atom.BO_Zmult ->
     let (vm0, pe1) = build_pexpr0 vm a1 in
     let (vm1, pe2) = build_pexpr0 vm0 a2 in (vm1, (PEmul (pe1, pe2)))
   | _ ->
     (match build_z_atom t_atom h with
      | Some z0 -> (vm, (PEc z0))
      | None -> let (vm0, p) = find_var vm h in (vm0, (PEX p))))
| _ ->
  (match build_z_atom t_atom h with
   | Some z0 -> (vm, (PEc z0))
   | None -> let (vm0, p) = find_var vm h in (vm0, (PEX p)))

(** val build_pexpr :
    Atom.atom array -> vmap -> Uint63.t -> vmap * z pExpr **)

let build_pexpr t_atom =
  foldi (fun _ cont vm h ->
    build_pexpr_atom_aux t_atom cont vm (get t_atom h)) (Uint63.of_int (0))
    (length0 t_atom) (fun vm _ -> (vm, (PEc Z0)))

(** val build_op2 : Atom.binop -> op2 option **)

let build_op2 = function
| Atom.BO_Zlt -> Some OpLt
| Atom.BO_Zle -> Some OpLe
| Atom.BO_Zge -> Some OpGe
| Atom.BO_Zgt -> Some OpGt
| Atom.BO_eq t0 -> (match t0 with
                    | Typ.TZ -> Some OpEq
                    | _ -> None)
| _ -> None

(** val build_formula_atom :
    Atom.atom array -> vmap -> Atom.atom -> (vmap * z formula) option **)

let build_formula_atom t_atom vm = function
| Atom.Abop (op, a1, a2) ->
  (match build_op2 op with
   | Some o ->
     let (vm0, pe1) = build_pexpr t_atom vm a1 in
     let (vm1, pe2) = build_pexpr t_atom vm0 a2 in
     Some (vm1, { flhs = pe1; fop = o; frhs = pe2 })
   | None -> None)
| _ -> None

(** val build_formula :
    Atom.atom array -> vmap -> Uint63.t -> (vmap * z formula) option **)

let build_formula t_atom vm h =
  build_formula_atom t_atom vm (get t_atom h)

(** val build_not2 : Uint63.t -> z formula bFormula -> z formula bFormula **)

let build_not2 i f =
  foldi (fun _ f' -> NOT (IsProp, (NOT (IsProp, f')))) (Uint63.of_int (0)) i f

(** val build_hform :
    Atom.atom array -> (vmap -> Uint63.t -> (vmap * z formula bFormula)
    option) -> vmap -> Form.form -> (vmap * z formula bFormula) option **)

let build_hform t_atom build_var0 vm = function
| Form.Fatom h ->
  (match build_formula t_atom vm h with
   | Some p -> let (vm0, f0) = p in Some (vm0, (A (IsProp, f0, Tt)))
   | None -> None)
| Form.Ftrue -> Some (vm, (TT IsProp))
| Form.Ffalse -> Some (vm, (FF IsProp))
| Form.Fnot2 (i, l) ->
  (match build_var0 vm (Lit.blit l) with
   | Some p ->
     let (vm0, f0) = p in
     let f' = build_not2 i f0 in
     let f'' = if Lit.is_pos l then f' else NOT (IsProp, f') in
     Some (vm0, f'')
   | None -> None)
| Form.Fand args ->
  afold_left (fun vm0 -> Some (vm0, (TT IsProp))) (fun a b vm0 ->
    match a vm0 with
    | Some p ->
      let (vm1, f1) = p in
      (match b vm1 with
       | Some p2 -> let (vm2, f2) = p2 in Some (vm2, (AND (IsProp, f1, f2)))
       | None -> None)
    | None -> None)
    (amap (fun l vm0 ->
      match build_var0 vm0 (Lit.blit l) with
      | Some p ->
        let (vm', f0) = p in
        Some (vm', (if Lit.is_pos l then f0 else NOT (IsProp, f0)))
      | None -> None) args) vm
| Form.For args ->
  afold_left (fun vm0 -> Some (vm0, (FF IsProp))) (fun a b vm0 ->
    match a vm0 with
    | Some p ->
      let (vm1, f1) = p in
      (match b vm1 with
       | Some p2 -> let (vm2, f2) = p2 in Some (vm2, (OR (IsProp, f1, f2)))
       | None -> None)
    | None -> None)
    (amap (fun l vm0 ->
      match build_var0 vm0 (Lit.blit l) with
      | Some p ->
        let (vm', f0) = p in
        Some (vm', (if Lit.is_pos l then f0 else NOT (IsProp, f0)))
      | None -> None) args) vm
| Form.Fimp args ->
  afold_right (fun vm0 -> Some (vm0, (TT IsProp))) (fun a b vm0 ->
    match b vm0 with
    | Some p ->
      let (vm2, f2) = p in
      (match a vm2 with
       | Some p2 ->
         let (vm1, f1) = p2 in Some (vm1, (IMPL (IsProp, f1, None, f2)))
       | None -> None)
    | None -> None)
    (amap (fun l vm0 ->
      match build_var0 vm0 (Lit.blit l) with
      | Some p ->
        let (vm', f0) = p in
        Some (vm', (if Lit.is_pos l then f0 else NOT (IsProp, f0)))
      | None -> None) args) vm
| Form.Fxor (a, b) ->
  (match build_var0 vm (Lit.blit a) with
   | Some p ->
     let (vm1, f1) = p in
     (match build_var0 vm1 (Lit.blit b) with
      | Some p2 ->
        let (vm2, f2) = p2 in
        let f1' = if Lit.is_pos a then f1 else NOT (IsProp, f1) in
        let f2' = if Lit.is_pos b then f2 else NOT (IsProp, f2) in
        Some (vm2, (AND (IsProp, (OR (IsProp, f1', f2')), (OR (IsProp, (NOT
        (IsProp, f1')), (NOT (IsProp, f2')))))))
      | None -> None)
   | None -> None)
| Form.Fiff (a, b) ->
  (match build_var0 vm (Lit.blit a) with
   | Some p ->
     let (vm1, f1) = p in
     (match build_var0 vm1 (Lit.blit b) with
      | Some p2 ->
        let (vm2, f2) = p2 in
        let f1' = if Lit.is_pos a then f1 else NOT (IsProp, f1) in
        let f2' = if Lit.is_pos b then f2 else NOT (IsProp, f2) in
        Some (vm2, (AND (IsProp, (OR (IsProp, f1', (NOT (IsProp, f2')))), (OR
        (IsProp, (NOT (IsProp, f1')), f2')))))
      | None -> None)
   | None -> None)
| Form.Fite (a, b, c) ->
  (match build_var0 vm (Lit.blit a) with
   | Some p ->
     let (vm1, f1) = p in
     (match build_var0 vm1 (Lit.blit b) with
      | Some p2 ->
        let (vm2, f2) = p2 in
        (match build_var0 vm2 (Lit.blit c) with
         | Some p3 ->
           let (vm3, f3) = p3 in
           let f1' = if Lit.is_pos a then f1 else NOT (IsProp, f1) in
           let f2' = if Lit.is_pos b then f2 else NOT (IsProp, f2) in
           let f3' = if Lit.is_pos c then f3 else NOT (IsProp, f3) in
           Some (vm3, (OR (IsProp, (AND (IsProp, f1', f2')), (AND (IsProp,
           (NOT (IsProp, f1')), f3')))))
         | None -> None)
      | None -> None)
   | None -> None)
| Form.FbbT (_, _) -> None

(** val build_var :
    Form.form array -> Atom.atom array -> vmap -> Uint63.t -> (vmap * z
    formula bFormula) option **)

let build_var t_form t_atom =
  foldi (fun _ cont vm h -> build_hform t_atom cont vm (get t_form h))
    (Uint63.of_int (0)) (length0 t_form) (fun _ _ -> None)

(** val build_form :
    Form.form array -> Atom.atom array -> vmap -> Form.form -> (vmap * z
    formula bFormula) option **)

let build_form t_form t_atom =
  build_hform t_atom (build_var t_form t_atom)

(** val build_nlit :
    Form.form array -> Atom.atom array -> vmap -> Uint63.t -> (vmap * z
    formula bFormula) option **)

let build_nlit t_form t_atom vm l =
  let l0 = Lit.neg l in
  (match build_form t_form t_atom vm (get t_form (Lit.blit l0)) with
   | Some p ->
     let (vm0, f) = p in
     let f0 = if Lit.is_pos l0 then f else NOT (IsProp, f) in Some (vm0, f0)
   | None -> None)

(** val build_clause_aux :
    Form.form array -> Atom.atom array -> vmap -> Uint63.t list -> (vmap * z
    formula bFormula) option **)

let rec build_clause_aux t_form t_atom vm = function
| Nil -> None
| Cons (l, cl0) ->
  (match cl0 with
   | Nil -> build_nlit t_form t_atom vm l
   | Cons (_, _) ->
     (match build_nlit t_form t_atom vm l with
      | Some p ->
        let (vm0, bf1) = p in
        (match build_clause_aux t_form t_atom vm0 cl0 with
         | Some p2 ->
           let (vm1, bf2) = p2 in Some (vm1, (AND (IsProp, bf1, bf2)))
         | None -> None)
      | None -> None))

(** val build_clause :
    Form.form array -> Atom.atom array -> vmap -> Uint63.t list -> (vmap * (z
    formula, eKind, unit0, unit0) gFormula) option **)

let build_clause t_form t_atom vm cl =
  match build_clause_aux t_form t_atom vm cl with
  | Some p ->
    let (vm0, bf) = p in Some (vm0, (IMPL (IsProp, bf, None, (FF IsProp))))
  | None -> None

(** val get_eq0 :
    Form.form array -> Atom.atom array -> Uint63.t -> (Uint63.t -> Uint63.t
    -> C.t) -> C.t **)

let get_eq0 t_form t_atom l f =
  if Lit.is_pos l
  then (match get t_form (Lit.blit l) with
        | Form.Fatom xa ->
          (match get t_atom xa with
           | Atom.Abop (b0, a, b) ->
             (match b0 with
              | Atom.BO_eq _ -> f a b
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val get_not_le :
    Form.form array -> Atom.atom array -> Uint63.t -> (Uint63.t -> Uint63.t
    -> C.t) -> C.t **)

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
    Form.form array -> Atom.atom array -> Uint63.t list -> zArithProof list
    -> C.t **)

let check_micromega t_form t_atom cl c =
  match build_clause t_form t_atom empty_vmap cl with
  | Some p -> let (_, bf) = p in if zTautoChecker bf c then cl else C._true
  | None -> C._true

(** val check_diseq :
    Form.form array -> Atom.atom array -> Uint63.t -> C.t **)

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
    Atom.atom array -> (Uint63.t -> Uint63.t -> bool) -> Atom.atom ->
    Atom.atom -> bool **)

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
  | Atom.Atop (_, _, _, _) -> false
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

(** val check_hatom : Atom.atom array -> Uint63.t -> Uint63.t -> bool **)

let check_hatom t_atom h1 h2 =
  foldi (fun _ cont h3 h4 ->
    if eqb0 h3 h4
    then true
    else check_atom_aux t_atom cont (get t_atom h3) (get t_atom h4))
    (Uint63.of_int (0)) (length0 t_atom) (fun _ _ -> false) h1 h2

(** val check_neg_hatom : Atom.atom array -> Uint63.t -> Uint63.t -> bool **)

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

(** val remove_not : Form.form array -> Uint63.t -> Uint63.t **)

let remove_not t_form l =
  match get t_form (Lit.blit l) with
  | Form.Fnot2 (_, l') -> if Lit.is_pos l then l' else Lit.neg l'
  | _ -> l

(** val get_and : Form.form array -> Uint63.t -> Uint63.t array option **)

let get_and t_form l =
  let l0 = remove_not t_form l in
  if Lit.is_pos l0
  then (match get t_form (Lit.blit l0) with
        | Form.Fand args -> Some args
        | _ -> None)
  else None

(** val get_or : Form.form array -> Uint63.t -> Uint63.t array option **)

let get_or t_form l =
  let l0 = remove_not t_form l in
  if Lit.is_pos l0
  then (match get t_form (Lit.blit l0) with
        | Form.For args -> Some args
        | _ -> None)
  else None

(** val flatten_op_body :
    (Uint63.t -> Uint63.t array option) -> (Uint63.t list -> Uint63.t ->
    Uint63.t list) -> Uint63.t list -> Uint63.t -> Uint63.t list **)

let flatten_op_body get_op frec largs l =
  match get_op l with
  | Some a ->
    foldi (fun i x -> frec x (get a i)) (Uint63.of_int (0)) (length0 a) largs
  | None -> Cons (l, largs)

(** val flatten_op_lit :
    (Uint63.t -> Uint63.t array option) -> Uint63.t -> Uint63.t list ->
    Uint63.t -> Uint63.t list **)

let flatten_op_lit get_op max0 =
  foldi (fun _ -> flatten_op_body get_op) (Uint63.of_int (0)) max0
    (fun largs l -> Cons (l, largs))

(** val flatten_and : Form.form array -> Uint63.t array -> Uint63.t list **)

let flatten_and t_form t0 =
  foldi (fun i x ->
    flatten_op_lit (get_and t_form) (length0 t_form) x (get t0 i))
    (Uint63.of_int (0)) (length0 t0) Nil

(** val flatten_or : Form.form array -> Uint63.t array -> Uint63.t list **)

let flatten_or t_form t0 =
  foldi (fun i x ->
    flatten_op_lit (get_or t_form) (length0 t_form) x (get t0 i))
    (Uint63.of_int (0)) (length0 t0) Nil

(** val check_flatten_body :
    Form.form array -> (Uint63.t -> Uint63.t -> bool) -> (Uint63.t ->
    Uint63.t -> bool) -> (Uint63.t -> Uint63.t -> bool) -> Uint63.t ->
    Uint63.t -> bool **)

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
                  then aforallbi (fun i l1 -> frec l1 (get args2 i)) args1
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
    Form.form array -> (Uint63.t -> Uint63.t -> bool) -> (Uint63.t ->
    Uint63.t -> bool) -> Uint63.t -> Uint63.t -> bool **)

let check_flatten_aux t_form check_atom0 check_neg_atom l lf =
  foldi (fun _ -> check_flatten_body t_form check_atom0 check_neg_atom)
    (Uint63.of_int (0)) (length0 t_form) (fun _ _ -> false) l lf

(** val check_flatten :
    Form.form array -> (Uint63.t -> Uint63.t -> bool) -> (Uint63.t ->
    Uint63.t -> bool) -> S.t -> Uint63.t -> Uint63.t -> C.t **)

let check_flatten t_form check_atom0 check_neg_atom s cid lf =
  match S.get s cid with
  | Nil -> C._true
  | Cons (l, l0) ->
    (match l0 with
     | Nil ->
       if check_flatten_aux t_form check_atom0 check_neg_atom l lf
       then Cons (lf, Nil)
       else C._true
     | Cons (_, _) -> C._true)

(** val check_spl_arith :
    Form.form array -> Atom.atom array -> Uint63.t list -> Uint63.t ->
    zArithProof list -> C.t **)

let check_spl_arith t_form t_atom orig res l =
  match orig with
  | Nil -> C._true
  | Cons (li, l0) ->
    (match l0 with
     | Nil ->
       let cl = Cons ((Lit.neg li), (Cons (res, Nil))) in
       (match build_clause t_form t_atom empty_vmap cl with
        | Some p ->
          let (_, bf) = p in
          if zTautoChecker bf l then Cons (res, Nil) else C._true
        | None -> C._true)
     | Cons (_, _) -> C._true)

(** val check_in : Uint63.t -> Uint63.t list -> bool **)

let rec check_in x = function
| Nil -> false
| Cons (t0, q) -> if eqb0 x t0 then true else check_in x q

(** val check_diseqs_complete_aux :
    Uint63.t -> Uint63.t list -> (Uint63.t * Uint63.t) option array -> bool **)

let rec check_diseqs_complete_aux a dist t0 =
  match dist with
  | Nil -> true
  | Cons (b, q) ->
    if aexistsbi (fun _ x ->
         match x with
         | Some p ->
           let (a', b') = p in
           if if eqb0 a a' then eqb0 b b' else false
           then true
           else if eqb0 a b' then eqb0 b a' else false
         | None -> false) t0
    then check_diseqs_complete_aux a q t0
    else false

(** val check_diseqs_complete :
    Uint63.t list -> (Uint63.t * Uint63.t) option array -> bool **)

let rec check_diseqs_complete dist t0 =
  match dist with
  | Nil -> true
  | Cons (a, q) ->
    if check_diseqs_complete_aux a q t0
    then check_diseqs_complete q t0
    else false

(** val check_diseqs :
    Form.form array -> Atom.atom array -> Typ.coq_type -> Uint63.t list ->
    Uint63.t array -> bool **)

let check_diseqs t_form t_atom ty dist diseq =
  let t0 =
    amap (fun t0 ->
      if Lit.is_pos t0
      then None
      else (match get t_form (Lit.blit t0) with
            | Form.Fatom a ->
              (match get t_atom a with
               | Atom.Acop _ -> None
               | Atom.Auop (_, _) -> None
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
                    then Some (h1, h2)
                    else None
                  | _ -> None)
               | _ -> None)
            | _ -> None)) diseq
  in
  if aforallbi (fun _ x -> match x with
                           | Some _ -> true
                           | None -> false) t0
  then check_diseqs_complete dist t0
  else false

(** val check_distinct :
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t array -> bool **)

let check_distinct t_form t_atom ha diseq =
  match get t_atom ha with
  | Atom.Anop (n0, dist) -> check_diseqs t_form t_atom n0 dist diseq
  | _ -> false

(** val check_distinct_two_args :
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t -> bool **)

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
                 | Cons (_, _) -> false)))
        | _ -> false)
     | _ -> false)
  | _ -> false

(** val check_lit :
    Form.form array -> Atom.atom array -> (Uint63.t -> Uint63.t -> bool) ->
    Uint63.t -> Uint63.t -> bool **)

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
    Form.form array -> Atom.atom array -> (Uint63.t -> Uint63.t -> bool) ->
    Form.form -> Form.form -> bool **)

let check_form_aux t_form t_atom check_var a b =
  match a with
  | Form.Fatom a0 ->
    (match b with
     | Form.Fatom b0 -> eqb0 a0 b0
     | Form.Fand diseq -> check_distinct t_form t_atom a0 diseq
     | _ -> false)
  | Form.Ftrue -> (match b with
                   | Form.Ftrue -> true
                   | _ -> false)
  | Form.Ffalse -> (match b with
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
       then aforallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.For a1 ->
    (match b with
     | Form.For a2 ->
       if eqb0 (length0 a1) (length0 a2)
       then aforallbi (fun i l ->
              check_lit t_form t_atom check_var l (get a2 i)) a1
       else false
     | _ -> false)
  | Form.Fimp a1 ->
    (match b with
     | Form.Fimp a2 ->
       if eqb0 (length0 a1) (length0 a2)
       then aforallbi (fun i l ->
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
  | Form.FbbT (_, _) -> false

(** val check_hform :
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t -> bool **)

let check_hform t_form t_atom h1 h2 =
  foldi (fun _ cont h3 h4 ->
    if eqb0 h3 h4
    then true
    else check_form_aux t_form t_atom cont (get t_form h3) (get t_form h4))
    (Uint63.of_int (0)) (length0 t_form) (fun _ _ -> false) h1 h2

(** val check_lit' :
    Form.form array -> Atom.atom array -> Uint63.t -> Uint63.t -> bool **)

let check_lit' t_form t_atom =
  check_lit t_form t_atom (check_hform t_form t_atom)

(** val check_distinct_elim :
    Form.form array -> Atom.atom array -> Uint63.t list -> Uint63.t ->
    Uint63.t list **)

let rec check_distinct_elim t_form t_atom input res =
  match input with
  | Nil -> Nil
  | Cons (l, q) ->
    if check_lit' t_form t_atom l res
    then Cons (res, q)
    else Cons (l, (check_distinct_elim t_form t_atom q res))

(** val or_of_imp : Uint63.t array -> Uint63.t array **)

let or_of_imp args =
  let last = sub0 (length0 args) (Uint63.of_int (1)) in
  amapi (fun i l -> if eqb0 i last then l else Lit.neg l) args

(** val check_True : C.t **)

let check_True =
  C._true

(** val check_False : Uint63.t list **)

let check_False =
  Cons ((Lit.neg Lit._false), Nil)

(** val check_BuildDef : Form.form array -> Uint63.t -> C.t **)

let check_BuildDef t_form l =
  match get t_form (Lit.blit l) with
  | Form.Fand args ->
    if Lit.is_pos l then Cons (l, (map Lit.neg (to_list args))) else C._true
  | Form.For args ->
    if Lit.is_pos l then C._true else Cons (l, (to_list args))
  | Form.Fimp args ->
    if Lit.is_pos l
    then C._true
    else if eqb0 (length0 args) (Uint63.of_int (0))
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
  | Form.Fite (a, _, c) ->
    if Lit.is_pos l
    then Cons (l, (Cons (a, (Cons ((Lit.neg c), Nil)))))
    else Cons (l, (Cons (a, (Cons (c, Nil)))))
  | _ -> C._true

(** val check_ImmBuildDef : Form.form array -> S.t -> Uint63.t -> C.t **)

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
          if eqb0 (length0 args) (Uint63.of_int (0))
          then C._true
          else if Lit.is_pos l
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
        | Form.Fite (a, _, c) ->
          if Lit.is_pos l
          then Cons (a, (Cons (c, Nil)))
          else Cons (a, (Cons ((Lit.neg c), Nil)))
        | _ -> C._true)
     | Cons (_, _) -> C._true)

(** val check_BuildDef2 : Form.form array -> Uint63.t -> C.t **)

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
  | Form.Fite (a, b, _) ->
    if Lit.is_pos l
    then Cons (l, (Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))))
    else Cons (l, (Cons ((Lit.neg a), (Cons (b, Nil)))))
  | _ -> C._true

(** val check_ImmBuildDef2 : Form.form array -> S.t -> Uint63.t -> C.t **)

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
        | Form.Fite (a, b, _) ->
          if Lit.is_pos l
          then Cons ((Lit.neg a), (Cons (b, Nil)))
          else Cons ((Lit.neg a), (Cons ((Lit.neg b), Nil)))
        | _ -> C._true)
     | Cons (_, _) -> C._true)

(** val check_BuildProj : Form.form array -> Uint63.t -> Uint63.t -> C.t **)

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

(** val check_ImmBuildProj :
    Form.form array -> S.t -> Uint63.t -> Uint63.t -> C.t **)

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
     | Cons (_, _) -> C._true)

(** val check_bbc : Form.form array -> bool list -> Uint63.t list -> bool **)

let rec check_bbc t_form a_bv bs =
  match a_bv with
  | Nil -> (match bs with
            | Nil -> true
            | Cons (_, _) -> false)
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

(** val check_bbConst :
    Atom.atom array -> Form.form array -> Uint63.t -> C.t **)

let check_bbConst t_atom t_form lres =
  if Lit.is_pos lres
  then (match get t_form (Lit.blit lres) with
        | Form.FbbT (a, bs) ->
          (match get t_atom a with
           | Atom.Acop c ->
             (match c with
              | Atom.CO_BV (bv, n0) ->
                if if check_bbc t_form bv bs
                   then N.eqb (N.of_nat (length bv)) n0
                   else false
                then Cons (lres, Nil)
                else C._true
              | _ -> C._true)
           | _ -> C._true)
        | _ -> C._true)
  else C._true

(** val check_bb :
    Atom.atom array -> Form.form array -> Uint63.t -> Uint63.t list -> nat ->
    nat -> bool **)

let rec check_bb t_atom t_form a bs i n0 =
  match bs with
  | Nil -> Nat.eqb i n0
  | Cons (b, bs0) ->
    if Lit.is_pos b
    then (match get t_form (Lit.blit b) with
          | Form.Fatom a' ->
            (match get t_atom a' with
             | Atom.Auop (u, a'0) ->
               (match u with
                | Atom.UO_BVbitOf (n1, p) ->
                  if if if eqb0 a a'0 then Nat.eqb i p else false
                     then Nat.eqb n0 (N.to_nat n1)
                     else false
                  then check_bb t_atom t_form a bs0 (S i) n0
                  else false
                | _ -> false)
             | _ -> false)
          | _ -> false)
    else false

(** val check_bbVar :
    Atom.atom array -> Form.form array -> Uint63.t -> C.t **)

let check_bbVar t_atom t_form lres =
  if Lit.is_pos lres
  then (match get t_form (Lit.blit lres) with
        | Form.FbbT (a, bs) ->
          if check_bb t_atom t_form a bs O (length bs)
          then Cons (lres, Nil)
          else C._true
        | _ -> C._true)
  else C._true

(** val check_not : Uint63.t list -> Uint63.t list -> bool **)

let rec check_not bs br =
  match bs with
  | Nil -> (match br with
            | Nil -> true
            | Cons (_, _) -> false)
  | Cons (b, bs0) ->
    (match br with
     | Nil -> false
     | Cons (r, br0) ->
       if eqb0 r (Lit.neg b) then check_not bs0 br0 else false)

(** val check_bbNot :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t -> C.t **)

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
     | Cons (_, _) -> C._true)

(** val check_symopp :
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t list ->
    Atom.binop -> bool **)

let rec check_symopp t_form bs1 bs2 bsres bvop =
  match bs1 with
  | Nil ->
    (match bs2 with
     | Nil -> (match bsres with
               | Nil -> true
               | Cons (_, _) -> false)
     | Cons (_, _) -> false)
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
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val check_eq :
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t list -> bool **)

let rec check_eq t_form bs1 bs2 bsres =
  match bs1 with
  | Nil ->
    (match bs2 with
     | Nil -> (match bsres with
               | Nil -> true
               | Cons (_, _) -> false)
     | Cons (_, _) -> false)
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
           | Cons (_, _) ->
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
              | Cons (_, _) ->
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
                 | Cons (_, _) ->
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
                   else false)))))

(** val check_bbEq :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
                                                         bs2 (Cons (lbb, Nil))
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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

type carry =
| Clit of Uint63.t
| Cand of carry * carry
| Cxor of carry * carry
| Cor of carry * carry
| Ciff of carry * carry

(** val eq_carry_lit : Form.form array -> carry -> Uint63.t -> bool **)

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
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t list ->
    carry -> bool **)

let rec check_add t_form bs1 bs2 bsres carry0 =
  match bs1 with
  | Nil ->
    (match bs2 with
     | Nil -> (match bsres with
               | Nil -> true
               | Cons (_, _) -> false)
     | Cons (_, _) -> false)
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
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val check_neg :
    Form.form array -> Uint63.t list -> Uint63.t list -> bool **)

let check_neg t_form bs br =
  let z0 = map (fun _ -> Lit._false) bs in
  let nbs = map Lit.neg bs in check_add t_form nbs z0 br (Clit Lit._true)

(** val check_bbNeg :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t -> C.t **)

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
     | Cons (_, _) -> C._true)

(** val and_with_bit : Uint63.t list -> Uint63.t -> carry list **)

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
       then let carry_out = Cor ((Cand (ai, bi)), (Cand ((Cxor (ai, bi)), c)))
            in
            let curr = Cxor ((Cxor (ai, bi)), c) in
            Cons (curr, (mult_step_k_h a' b' carry_out (Z.sub k (Zpos XH))))
       else Cons (ai, (mult_step_k_h a' b c (Z.sub k (Zpos XH)))))

(** val mult_step :
    Uint63.t list -> Uint63.t list -> carry list -> nat -> nat -> carry list **)

let rec mult_step a b res k k' =
  let ak = firstn (S k') a in
  let b' = and_with_bit ak (nth k b Lit._false) in
  let res' = mult_step_k_h res b' (Clit Lit._false) (Z.of_nat k) in
  (match k' with
   | O -> res'
   | S pk' -> mult_step a b res' (S k) pk')

(** val bblast_bvmult :
    Uint63.t list -> Uint63.t list -> nat -> carry list **)

let bblast_bvmult a b n0 =
  let res = and_with_bit a (nth O b Lit._false) in
  (match n0 with
   | O -> res
   | S n1 -> (match n1 with
              | O -> res
              | S k -> mult_step a b res (S O) k))

(** val check_mult :
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t list -> bool **)

let check_mult t_form bs1 bs2 bsres =
  if Nat.eqb (length bs1) (length bs2)
  then let bvm12 = bblast_bvmult bs1 bs2 (length bs1) in
       forallb2 (eq_carry_lit t_form) bvm12 bsres
  else false

(** val check_bbMult :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val ult_big_endian_lit_list : Uint63.t list -> Uint63.t list -> carry **)

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
           | Cons (_, _) ->
             Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
               (ult_big_endian_lit_list x' y'))), (Cand ((Clit (Lit.neg xi)),
               (Clit yi))))))
     | Cons (_, _) ->
       (match bs2 with
        | Nil -> Clit Lit._false
        | Cons (yi, y') ->
          Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
            (ult_big_endian_lit_list x' y'))), (Cand ((Clit (Lit.neg xi)),
            (Clit yi))))))

(** val ult_lit_list : Uint63.t list -> Uint63.t list -> carry **)

let ult_lit_list x y =
  ult_big_endian_lit_list (rev x) (rev y)

(** val check_ult :
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t -> bool **)

let check_ult t_form bs1 bs2 bsres =
  if Lit.is_pos bsres
  then eq_carry_lit t_form (ult_lit_list bs1 bs2) bsres
  else false

(** val check_bbUlt :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val slt_big_endian_lit_list : Uint63.t list -> Uint63.t list -> carry **)

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
           | Cons (_, _) ->
             Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
               (ult_big_endian_lit_list x' y'))), (Cand ((Clit xi), (Clit
               (Lit.neg yi)))))))
     | Cons (_, _) ->
       (match y with
        | Nil -> Clit Lit._false
        | Cons (yi, y') ->
          Cor ((Cand ((Ciff ((Clit xi), (Clit yi))),
            (ult_big_endian_lit_list x' y'))), (Cand ((Clit xi), (Clit
            (Lit.neg yi)))))))

(** val slt_lit_list : Uint63.t list -> Uint63.t list -> carry **)

let slt_lit_list x y =
  slt_big_endian_lit_list (rev x) (rev y)

(** val check_slt :
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t -> bool **)

let check_slt t_form bs1 bs2 bsres =
  if Lit.is_pos bsres
  then eq_carry_lit t_form (slt_lit_list bs1 bs2) bsres
  else false

(** val check_bbSlt :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val lit_to_carry : Uint63.t list -> carry list **)

let rec lit_to_carry = function
| Nil -> Nil
| Cons (xbs, xsbs) -> Cons ((Clit xbs), (lit_to_carry xsbs))

(** val check_concat :
    Form.form array -> Uint63.t list -> Uint63.t list -> Uint63.t list -> bool **)

let check_concat t_form bs1 bs2 bsres =
  forallb2 (eq_carry_lit t_form) (lit_to_carry (app bs2 bs1)) bsres

(** val check_bbConcat :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val list_diseqb : bool list -> bool list -> bool **)

let rec list_diseqb a b =
  match a with
  | Nil -> (match b with
            | Nil -> false
            | Cons (_, _) -> true)
  | Cons (xa, xsa) ->
    (match b with
     | Nil -> true
     | Cons (xb, xsb) ->
       if eqb xa false
       then if eqb xb false then list_diseqb xsa xsb else true
       else if eqb xb true then list_diseqb xsa xsb else true)

(** val check_bbDiseq :
    Atom.atom array -> Form.form array -> Uint63.t -> C.t **)

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

(** val extract_lit : Uint63.t list -> nat -> nat -> Uint63.t list **)

let rec extract_lit x i j =
  match x with
  | Nil -> Nil
  | Cons (bx, x') ->
    (match i with
     | O -> (match j with
             | O -> Nil
             | S j' -> Cons (bx, (extract_lit x' i j')))
     | S i' -> (match j with
                | O -> Nil
                | S j' -> extract_lit x' i' j'))

(** val check_extract :
    Form.form array -> Uint63.t list -> Uint63.t list -> n -> n -> bool **)

let check_extract t_form bs bsres i j =
  if N.ltb (N.of_nat (length bs)) j
  then false
  else forallb2 (eq_carry_lit t_form)
         (lit_to_carry (extract_lit bs (N.to_nat i) (N.to_nat j))) bsres

(** val check_bbExtract :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t -> C.t **)

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
     | Cons (_, _) -> C._true)

(** val extend_lit : Uint63.t list -> nat -> Uint63.t -> Uint63.t list **)

let rec extend_lit x i b =
  match i with
  | O -> x
  | S i' -> Cons (b, (extend_lit x i' b))

(** val zextend_lit : Uint63.t list -> nat -> Uint63.t list **)

let zextend_lit x i =
  extend_lit x i Lit._false

(** val check_zextend :
    Form.form array -> Uint63.t list -> Uint63.t list -> n -> bool **)

let check_zextend t_form bs bsres i =
  forallb2 (eq_carry_lit t_form) (lit_to_carry (zextend_lit bs (N.to_nat i)))
    bsres

(** val check_bbZextend :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t -> C.t **)

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
     | Cons (_, _) -> C._true)

(** val mk_list_lit_false : nat -> Uint63.t list **)

let rec mk_list_lit_false = function
| O -> Nil
| S t' -> Cons (Lit._false, (mk_list_lit_false t'))

(** val sextend_lit : Uint63.t list -> nat -> Uint63.t list **)

let sextend_lit x i =
  match x with
  | Nil -> mk_list_lit_false i
  | Cons (xb, _) -> extend_lit x i xb

(** val check_sextend :
    Form.form array -> Uint63.t list -> Uint63.t list -> n -> bool **)

let check_sextend t_form bs bsres i =
  forallb2 (eq_carry_lit t_form) (lit_to_carry (sextend_lit bs (N.to_nat i)))
    bsres

(** val check_bbSextend :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t -> C.t **)

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
     | Cons (_, _) -> C._true)

(** val _shl_lit_be : Uint63.t list -> Uint63.t list **)

let _shl_lit_be a = match a with
| Nil -> Nil
| Cons (_, _) -> Cons (Lit._false, (removelast a))

(** val nshl_lit_be : Uint63.t list -> nat -> Uint63.t list **)

let rec nshl_lit_be a = function
| O -> a
| S n' -> nshl_lit_be (_shl_lit_be a) n'

(** val shl_lit_be : Uint63.t list -> bool list -> Uint63.t list **)

let shl_lit_be a b =
  nshl_lit_be a (RAWBITVECTOR_LIST.list2nat_be b)

(** val check_shl :
    Form.form array -> Uint63.t list -> bool list -> Uint63.t list -> bool **)

let check_shl t_form bs1 bs2 bsres =
  if Nat.eqb (length bs1) (length bs2)
  then forallb2 (eq_carry_lit t_form) (lit_to_carry (shl_lit_be bs1 bs2))
         bsres
  else false

(** val check_bbShl :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
                                                       (N.of_nat (length bs1))
                                                       n0
                                                else false
                                             then N.eqb
                                                    (N.of_nat (length bv2)) n0
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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val _shr_lit_be : Uint63.t list -> Uint63.t list **)

let _shr_lit_be = function
| Nil -> Nil
| Cons (_, xsa) -> app xsa (Cons (Lit._false, Nil))

(** val nshr_lit_be : Uint63.t list -> nat -> Uint63.t list **)

let rec nshr_lit_be a = function
| O -> a
| S n' -> nshr_lit_be (_shr_lit_be a) n'

(** val shr_lit_be : Uint63.t list -> bool list -> Uint63.t list **)

let shr_lit_be a b =
  nshr_lit_be a (RAWBITVECTOR_LIST.list2nat_be b)

(** val check_shr :
    Form.form array -> Uint63.t list -> bool list -> Uint63.t list -> bool **)

let check_shr t_form bs1 bs2 bsres =
  if Nat.eqb (length bs1) (length bs2)
  then forallb2 (eq_carry_lit t_form) (lit_to_carry (shr_lit_be bs1 bs2))
         bsres
  else false

(** val check_bbShr :
    Atom.atom array -> Form.form array -> S.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> C.t **)

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
                                                       (N.of_nat (length bs1))
                                                       n0
                                                else false
                                             then N.eqb
                                                    (N.of_nat (length bv2)) n0
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
           | Cons (_, _) -> C._true))
     | Cons (_, _) -> C._true)

(** val check_roweq :
    Form.form array -> Atom.atom array -> Uint63.t -> C.t **)

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
                       | Atom.Atop (t0, _, j, v2) ->
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
    Atom.atom array -> Uint63.t -> Uint63.t ->
    ((Typ.coq_type * Typ.coq_type) * Uint63.t) option **)

let store_of_me t_atom a b =
  match get t_atom b with
  | Atom.Atop (t0, a', i, _) ->
    let Atom.TO_store (ti, te) = t0 in
    if eqb0 a' a then Some ((ti, te), i) else None
  | _ -> None

(** val check_rowneq :
    Form.form array -> Atom.atom array -> Uint63.t list -> C.t **)

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
                                                   let (p2, i1) = p in
                                                   let (ti3, te3) = p2 in
                                                   (match store_of_me t_atom
                                                            sa2 sa with
                                                    | Some _ -> C._true
                                                    | None ->
                                                      if if if Typ.eqb ti ti3
                                                            then Typ.eqb te
                                                                   te3
                                                            else false
                                                         then if if if 
                                                                    eqb0 i1 i
                                                                    then 
                                                                    eqb0 j1 j
                                                                    else false
                                                                 then 
                                                                   eqb0 j2 j
                                                                 else false
                                                              then true
                                                              else if 
                                                                    if 
                                                                    eqb0 i1 j
                                                                    then 
                                                                    eqb0 j1 i
                                                                    else false
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
                                                      let (p2, i1) = p in
                                                      let (ti3, te3) = p2 in
                                                      if if if Typ.eqb ti ti3
                                                            then Typ.eqb te
                                                                   te3
                                                            else false
                                                         then if if if 
                                                                    eqb0 i1 i
                                                                    then 
                                                                    eqb0 j1 j
                                                                    else false
                                                                 then 
                                                                   eqb0 j2 j
                                                                 else false
                                                              then true
                                                              else if 
                                                                    if 
                                                                    eqb0 i1 j
                                                                    then 
                                                                    eqb0 j1 i
                                                                    else false
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
      | Cons (_, _) -> C._true))

(** val eq_sel_sym :
    Atom.atom array -> Typ.coq_type -> Typ.coq_type -> Uint63.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> bool **)

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
                        if if if Typ.eqb ti ti3 then Typ.eqb te te3 else false
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

(** val check_ext : Form.form array -> Atom.atom array -> Uint63.t -> C.t **)

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

type 'step _trace_ = 'step list * 'step

(** val _checker_ :
    (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> Uint63.t ->
    bool **)

let _checker_ check_step is_false0 s t0 confl =
  let s' = fold_left check_step (fst t0) s in is_false0 (S.get s' confl)

module Euf_Checker =
 struct
  (** val add_roots :
      S.t -> Uint63.t array -> Uint63.t array option -> S.t **)

  let add_roots s d = function
  | Some ur ->
    foldi (fun i s0 ->
      let c =
        if ltb0 (get ur i) (length0 d)
        then Cons ((get d (get ur i)), Nil)
        else C._true
      in
      S.set_clause s0 i c) (Uint63.of_int (0)) (length0 ur) s
  | None ->
    foldi (fun i s0 -> S.set_clause s0 i (Cons ((get d i), Nil)))
      (Uint63.of_int (0)) (length0 d) s
 end

module Checker_Ext =
 struct
  type step =
  | Res of Uint63.t * Uint63.t array
  | Weaken of Uint63.t * Uint63.t * Uint63.t list
  | ImmFlatten of Uint63.t * Uint63.t * Uint63.t
  | CTrue of Uint63.t
  | CFalse of Uint63.t
  | BuildDef of Uint63.t * Uint63.t
  | BuildDef2 of Uint63.t * Uint63.t
  | BuildProj of Uint63.t * Uint63.t * Uint63.t
  | ImmBuildDef of Uint63.t * Uint63.t
  | ImmBuildDef2 of Uint63.t * Uint63.t
  | ImmBuildProj of Uint63.t * Uint63.t * Uint63.t
  | EqTr of Uint63.t * Uint63.t * Uint63.t list
  | EqCgr of Uint63.t * Uint63.t * Uint63.t option list
  | EqCgrP of Uint63.t * Uint63.t * Uint63.t * Uint63.t option list
  | LiaMicromega of Uint63.t * Uint63.t list * zArithProof list
  | LiaDiseq of Uint63.t * Uint63.t
  | SplArith of Uint63.t * Uint63.t * Uint63.t * zArithProof list
  | SplDistinctElim of Uint63.t * Uint63.t * Uint63.t
  | BBVar of Uint63.t * Uint63.t
  | BBConst of Uint63.t * Uint63.t
  | BBOp of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBNot of Uint63.t * Uint63.t * Uint63.t
  | BBNeg of Uint63.t * Uint63.t * Uint63.t
  | BBAdd of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBConcat of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBMul of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBUlt of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBSlt of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBEq of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBDiseq of Uint63.t * Uint63.t
  | BBExtract of Uint63.t * Uint63.t * Uint63.t
  | BBZextend of Uint63.t * Uint63.t * Uint63.t
  | BBSextend of Uint63.t * Uint63.t * Uint63.t
  | BBShl of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | BBShr of Uint63.t * Uint63.t * Uint63.t * Uint63.t
  | RowEq of Uint63.t * Uint63.t
  | RowNeq of Uint63.t * C.t
  | Ext of Uint63.t * Uint63.t

  (** val step_checker :
      Atom.atom array -> Form.form array -> S.t -> step -> S.t **)

  let step_checker t_atom t_form s = function
  | Res (pos, res) -> S.set_resolve s pos res
  | Weaken (pos, cid, cl) -> S.set_weaken s pos cid cl
  | ImmFlatten (pos, cid, lf) ->
     let c = check_flatten t_form (check_hatom t_atom) (check_neg_hatom t_atom) s
        cid lf in
     print_clause c;
    S.set_clause s pos c
  | CTrue pos -> S.set_clause s pos check_True
  | CFalse pos -> S.set_clause s pos check_False
  | BuildDef (pos, l) -> let c = check_BuildDef t_form l in print_clause c; S.set_clause s pos c
  | BuildDef2 (pos, l) -> let c = check_BuildDef2 t_form l in print_clause c; S.set_clause s pos c
  | BuildProj (pos, l, i) -> let c = check_BuildProj t_form l i in print_clause c; S.set_clause s pos c
  | ImmBuildDef (pos, cid) -> let c = check_ImmBuildDef t_form s cid in print_clause c;
    S.set_clause s pos c
  | ImmBuildDef2 (pos, cid) -> let c = check_ImmBuildDef2 t_form s cid in print_clause c;
    S.set_clause s pos c
  | ImmBuildProj (pos, cid, i) -> let c = check_ImmBuildProj t_form s cid i in print_clause c;
    S.set_clause s pos c
  | EqTr (pos, l, fl) -> let c = check_trans t_form t_atom l fl in print_clause c;  S.set_clause s pos c
  | EqCgr (pos, l, fl) -> let c = check_congr t_form t_atom l fl in print_clause c;  S.set_clause s pos c
  | EqCgrP (pos, l1, l2, fl) -> let c = check_congr_pred t_form t_atom l1 l2 fl in print_clause c;
    S.set_clause s pos c
  | LiaMicromega (pos, cl, c) -> let c = check_micromega t_form t_atom cl c in print_clause c;
    S.set_clause s pos c
  | LiaDiseq (pos, l) -> let c = check_diseq t_form t_atom l in print_clause c;  S.set_clause s pos c
  | SplArith (pos, orig, res, l) -> let c = check_spl_arith t_form t_atom (S.get s orig) res l in print_clause c;
    S.set_clause s pos c
  | SplDistinctElim (pos, orig, res) -> let c = check_distinct_elim t_form t_atom (S.get s orig) res in print_clause c;
    S.set_clause s pos c
  | BBVar (pos, res) -> S.set_clause s pos (check_bbVar t_atom t_form res)
  | BBConst (pos, res) -> S.set_clause s pos (check_bbConst t_atom t_form res)
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
  | BBDiseq (pos, res) -> S.set_clause s pos (check_bbDiseq t_atom t_form res)
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

  (** val checker :
      Atom.atom array -> Form.form array -> (C.t -> bool) -> S.t -> step
      _trace_ -> Uint63.t -> bool **)

  let checker t_atom t_form s t0 =
    _checker_ (step_checker t_atom t_form) s t0

  type certif =
  | Certif of Uint63.t * step _trace_ * Uint63.t

  (** val checker_ext :
      Atom.atom array -> Form.form array -> Uint63.t array -> Uint63.t array
      option -> certif -> bool **)

  let checker_ext t_atom t_form d used_roots = function
  | Certif (nclauses, t0, confl) ->
    if if Form.check_form t_form then Atom.check_atom t_atom else false
    then checker t_atom t_form C.is_false
           (Euf_Checker.add_roots (S.make nclauses) d used_roots) t0 confl
    else false
 end

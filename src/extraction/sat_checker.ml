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


(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type 'a list =
| Nil
| Cons of 'a * 'a list

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

(** val sub : int -> int -> int **)

let sub = ExtrNative.sub

(** val eqb : int -> int -> bool **)

let eqb = fun i j -> ExtrNative.compare i j = ExtrNative.Eq

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
  eqb i (Uint63.of_int (0))

(** val is_even : int -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

(** val compare : int -> int -> ExtrNative.comparison **)

let compare = ExtrNative.compare

(** val foldi : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 **)

let foldi f from to0 =
  foldi_cont (fun i cont a -> cont (f i a)) from to0 (fun a -> a)

(** val foldi_down : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 **)

let foldi_down f from downto0 =
  foldi_down_cont (fun i cont a -> cont (f i a)) from downto0 (fun a -> a)

type 'a array = 'a ExtrNative.parray

(** val make : int -> 'a1 -> 'a1 array **)

let make = ExtrNative.parray_make

module Coq__1 = struct 
 (** val get : 'a1 array -> int -> 'a1 **)
 
 let get = ExtrNative.parray_get
end
let get = Coq__1.get

(** val set : 'a1 array -> int -> 'a1 -> 'a1 array **)

let set = ExtrNative.parray_set

(** val length : 'a1 array -> int **)

let length = ExtrNative.parray_length

(** val to_list : 'a1 array -> 'a1 list **)

let to_list t0 =
  let len = length t0 in
  if eqb (Uint63.of_int (0)) len
  then Nil
  else foldi_down (fun i l -> Cons ((get t0 i), l))
         (sub len (Uint63.of_int (1))) (Uint63.of_int (0)) Nil

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1 **)

let fold_left f a t0 =
  let len = length t0 in
  if eqb (Uint63.of_int (0)) len
  then a
  else foldi (fun i a0 -> f a0 (get t0 i)) (Uint63.of_int (0))
         (sub (length t0) (Uint63.of_int (1))) a

(** val foldi_right :
    (int -> 'a1 -> 'a2 -> 'a2) -> 'a1 array -> 'a2 -> 'a2 **)

let foldi_right f t0 b =
  let len = length t0 in
  if eqb (Uint63.of_int (0)) len
  then b
  else foldi_down (fun i b0 -> f i (get t0 i) b0)
         (sub len (Uint63.of_int (1))) (Uint63.of_int (0)) b

(** val afold_left :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1 **)

let afold_left default oP f v =
  let n = length v in
  if eqb n (Uint63.of_int (0))
  then default
  else foldi (fun i a -> oP a (f (get v i))) (Uint63.of_int (1))
         (sub n (Uint63.of_int (1))) (f (get v (Uint63.of_int (0))))

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
    eqb l l'
  
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
  | Cons (l, c0) -> if eqb l Lit._true then true else has_true c0
  
  (** val or_aux : (t -> t -> t) -> int -> t -> t -> int list **)
  
  let rec or_aux or0 l1 c1 c2 = match c2 with
  | Nil -> Cons (l1, c1)
  | Cons (l2, c2') ->
    (match compare l1 l2 with
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
         (match compare l1 l2 with
          | ExtrNative.Eq -> Cons (l1, (coq_or c3 c2'))
          | ExtrNative.Lt -> Cons (l1, (coq_or c3 c2))
          | ExtrNative.Gt -> Cons (l2, (or_aux coq_or l1 c3 c2'))))
  
  (** val resolve_aux : (t -> t -> t) -> int -> t -> t -> t **)
  
  let rec resolve_aux resolve0 l1 c1 c2 = match c2 with
  | Nil -> _true
  | Cons (l2, c2') ->
    (match compare l1 l2 with
     | ExtrNative.Eq -> Cons (l1, (resolve0 c1 c2'))
     | ExtrNative.Lt ->
       if eqb (lxor0 l1 l2) (Uint63.of_int (1))
       then coq_or c1 c2'
       else Cons (l1, (resolve0 c1 c2))
     | ExtrNative.Gt ->
       if eqb (lxor0 l1 l2) (Uint63.of_int (1))
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
         (match compare l1 l2 with
          | ExtrNative.Eq -> Cons (l1, (resolve c3 c2'))
          | ExtrNative.Lt ->
            if eqb (lxor0 l1 l2) (Uint63.of_int (1))
            then coq_or c3 c2'
            else Cons (l1, (resolve c3 c2))
          | ExtrNative.Gt ->
            if eqb (lxor0 l1 l2) (Uint63.of_int (1))
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
    (match compare l1 l2 with
     | ExtrNative.Eq -> c
     | ExtrNative.Lt ->
       if eqb (lxor0 l1 l2) (Uint63.of_int (1))
       then C._true
       else Cons (l1, c)
     | ExtrNative.Gt ->
       if eqb (lxor0 l1 l2) (Uint63.of_int (1))
       then C._true
       else Cons (l2, (insert l1 c')))
  
  (** val insert_no_simpl : int -> int list -> int list **)
  
  let rec insert_no_simpl l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare l1 l2 with
     | ExtrNative.Eq -> c
     | ExtrNative.Lt -> Cons (l1, c)
     | ExtrNative.Gt -> Cons (l2, (insert_no_simpl l1 c')))
  
  (** val insert_keep : int -> int list -> int list **)
  
  let rec insert_keep l1 c = match c with
  | Nil -> Cons (l1, Nil)
  | Cons (l2, c') ->
    (match compare l1 l2 with
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
    let len = length r in
    if eqb len (Uint63.of_int (0))
    then s
    else let c =
           foldi (fun i c' -> C.resolve (get s (Coq__1.get r i)) c')
             (Uint63.of_int (1)) (sub len (Uint63.of_int (1)))
             (get s (Coq__1.get r (Uint63.of_int (0))))
         in
         internal_set s pos c
  
  (** val subclause : int list -> int list -> bool **)
  
  let subclause cl1 cl2 =
    forallb (fun l1 ->
      if if eqb l1 Lit._false then true else eqb l1 (Lit.neg Lit._true)
      then true
      else existsb (fun l2 -> eqb l1 l2) cl2) cl1
  
  (** val check_weaken : t -> int -> int list -> C.t **)
  
  let check_weaken s cid cl =
    if subclause (get s cid) cl then cl else C._true
  
  (** val set_weaken : t -> int -> int -> int list -> t **)
  
  let set_weaken s pos cid cl =
    set_clause_keep s pos (check_weaken s cid cl)
 end

type 'step trace = 'step array array

(** val trace_fold : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 trace -> 'a1 **)

let trace_fold transition s0 t0 =
  fold_left (fold_left transition) s0 t0

type 'step _trace_ = 'step trace

(** val _checker_ :
    (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> int -> bool **)

let _checker_ check_step is_false0 s t0 confl =
  let s' = trace_fold check_step s t0 in is_false0 (S.get s' confl)

module Sat_Checker = 
 struct 
  type step =
  | Res of int * int array
  
  (** val step_rect : (int -> int array -> 'a1) -> step -> 'a1 **)
  
  let step_rect f = function
  | Res (x, x0) -> f x x0
  
  (** val step_rec : (int -> int array -> 'a1) -> step -> 'a1 **)
  
  let step_rec f = function
  | Res (x, x0) -> f x x0
  
  (** val resolution_checker :
      (C.t -> bool) -> S.t -> step _trace_ -> int -> bool **)
  
  let resolution_checker s t0 =
    _checker_ (fun s0 st -> let Res (pos, r) = st in S.set_resolve s0 pos r)
      s t0
  
  type dimacs = int array array
  
  (** val coq_C_interp_or : Valuation.t -> int array -> bool **)
  
  let coq_C_interp_or rho c =
    afold_left false (fun b1 b2 -> if b1 then true else b2) (Lit.interp rho)
      c
  
  (** val valid : Valuation.t -> dimacs -> bool **)
  
  let valid rho d =
    afold_left true (fun b1 b2 -> if b1 then b2 else false)
      (coq_C_interp_or rho) d
  
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
  
  (** val add_roots : S.t -> dimacs -> S.t **)
  
  let add_roots s d =
    foldi_right (fun i c s0 -> S.set_clause s0 i (to_list c)) d s
  
  (** val checker : dimacs -> certif -> bool **)
  
  let checker d = function
  | Certif (nclauses, t0, confl_id) ->
    resolution_checker C.is_false (add_roots (S.make nclauses) d) t0 confl_id
  
  (** val interp_var : (int -> bool) -> int -> bool **)
  
  let interp_var rho x =
    match compare x (Uint63.of_int (1)) with
    | ExtrNative.Eq -> false
    | ExtrNative.Lt -> true
    | ExtrNative.Gt -> rho (sub x (Uint63.of_int (1)))
 end


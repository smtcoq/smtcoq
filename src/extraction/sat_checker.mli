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


val negb : bool -> bool

type 'a list =
| Nil
| Cons of 'a * 'a list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

type int = ExtrNative.uint

val lsl0 : int -> int -> int

val lsr0 : int -> int -> int

val land0 : int -> int -> int

val lxor0 : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val foldi_cont :
  (int -> ('a1 -> 'a2) -> 'a1 -> 'a2) -> int -> int -> ('a1 -> 'a2) -> 'a1 ->
  'a2

val foldi_down_cont :
  (int -> ('a1 -> 'a2) -> 'a1 -> 'a2) -> int -> int -> ('a1 -> 'a2) -> 'a1 ->
  'a2

val is_zero : int -> bool

val is_even : int -> bool

val compare : int -> int -> ExtrNative.comparison

val foldi : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1

val foldi_down : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1

type 'a array = 'a ExtrNative.parray

val make : int -> 'a1 -> 'a1 array

val get : 'a1 array -> int -> 'a1

val set : 'a1 array -> int -> 'a1 -> 'a1 array

val length : 'a1 array -> int

val to_list : 'a1 array -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1

val foldi_right : (int -> 'a1 -> 'a2 -> 'a2) -> 'a1 array -> 'a2 -> 'a2

module Valuation : 
 sig 
  type t = int -> bool
 end

module Var : 
 sig 
  val _true : int
  
  val _false : int
  
  val interp : Valuation.t -> int -> bool
 end

module Lit : 
 sig 
  val is_pos : int -> bool
  
  val blit : int -> int
  
  val lit : int -> int
  
  val neg : int -> int
  
  val nlit : int -> int
  
  val _true : int
  
  val _false : int
  
  val eqb : int -> int -> bool
  
  val interp : Valuation.t -> int -> bool
 end

module C : 
 sig 
  type t = int list
  
  val interp : Valuation.t -> t -> bool
  
  val _true : t
  
  val is_false : t -> bool
  
  val or_aux : (t -> t -> t) -> int -> t -> t -> int list
  
  val coq_or : t -> t -> t
  
  val resolve_aux : (t -> t -> t) -> int -> t -> t -> t
  
  val resolve : t -> t -> t
 end

module S : 
 sig 
  type t = C.t array
  
  val get : t -> int -> C.t
  
  val internal_set : t -> int -> C.t -> t
  
  val make : int -> t
  
  val insert : int -> int list -> int list
  
  val sort_uniq : int list -> int list
  
  val set_clause : t -> int -> C.t -> t
  
  val set_resolve : t -> int -> int array -> t
 end

val afold_left :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1

type 'step _trace_ = 'step array array

val _checker_ :
  (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> int -> bool

module Sat_Checker : 
 sig 
  type step =
  | Res of int * int array
  
  val step_rect : (int -> int array -> 'a1) -> step -> 'a1
  
  val step_rec : (int -> int array -> 'a1) -> step -> 'a1
  
  val resolution_checker :
    (C.t -> bool) -> S.t -> step _trace_ -> int -> bool
  
  type dimacs = int array array
  
  val coq_C_interp_or : Valuation.t -> int array -> bool
  
  val valid : Valuation.t -> dimacs -> bool
  
  type certif =
  | Certif of int * step _trace_ * int
  
  val certif_rect : (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1
  
  val certif_rec : (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1
  
  val add_roots : S.t -> dimacs -> S.t
  
  val checker : dimacs -> certif -> bool
  
  val interp_var : (int -> bool) -> int -> bool
 end


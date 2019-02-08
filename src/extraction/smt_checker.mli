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

type unit0 =
| Tt

val implb : bool -> bool -> bool

val xorb : bool -> bool -> bool

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val compOpp : ExtrNative.comparison -> ExtrNative.comparison

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : ExtrNative.comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> ExtrNative.comparison -> 'a1 compSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

val plus : nat -> nat -> nat

val nat_iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

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

val eqb : bool -> bool -> bool

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module type TotalOrder' = 
 sig 
  type t 
 end

module MakeOrderTac : 
 functor (O:TotalOrder') ->
 sig 
  
 end

module MaxLogicalProperties : 
 functor (O:TotalOrder') ->
 functor (M:sig 
  val max : O.t -> O.t -> O.t
 end) ->
 sig 
  module Private_Tac : 
   sig 
    
   end
 end

module Pos : 
 sig 
  type t = positive
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont :
    positive -> positive -> ExtrNative.comparison -> ExtrNative.comparison
  
  val compare : positive -> positive -> ExtrNative.comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
    positive*mask
  
  val sqrtrem : positive -> positive*mask
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn : nat -> positive -> positive -> positive*(positive*positive)
  
  val ggcd : positive -> positive -> positive*(positive*positive)
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
 end

module Coq_Pos : 
 sig 
  module Coq__1 : sig 
   type t = positive
  end
  type t = Coq__1.t
  
  val succ : positive -> positive
  
  val add : positive -> positive -> positive
  
  val add_carry : positive -> positive -> positive
  
  val pred_double : positive -> positive
  
  val pred : positive -> positive
  
  val pred_N : positive -> n
  
  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg
  
  val mask_rect : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val mask_rec : 'a1 -> (positive -> 'a1) -> 'a1 -> mask -> 'a1
  
  val succ_double_mask : mask -> mask
  
  val double_mask : mask -> mask
  
  val double_pred_mask : positive -> mask
  
  val pred_mask : mask -> mask
  
  val sub_mask : positive -> positive -> mask
  
  val sub_mask_carry : positive -> positive -> mask
  
  val sub : positive -> positive -> positive
  
  val mul : positive -> positive -> positive
  
  val iter : positive -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pow : positive -> positive -> positive
  
  val square : positive -> positive
  
  val div2 : positive -> positive
  
  val div2_up : positive -> positive
  
  val size_nat : positive -> nat
  
  val size : positive -> positive
  
  val compare_cont :
    positive -> positive -> ExtrNative.comparison -> ExtrNative.comparison
  
  val compare : positive -> positive -> ExtrNative.comparison
  
  val min : positive -> positive -> positive
  
  val max : positive -> positive -> positive
  
  val eqb : positive -> positive -> bool
  
  val leb : positive -> positive -> bool
  
  val ltb : positive -> positive -> bool
  
  val sqrtrem_step :
    (positive -> positive) -> (positive -> positive) -> (positive*mask) ->
    positive*mask
  
  val sqrtrem : positive -> positive*mask
  
  val sqrt : positive -> positive
  
  val gcdn : nat -> positive -> positive -> positive
  
  val gcd : positive -> positive -> positive
  
  val ggcdn : nat -> positive -> positive -> positive*(positive*positive)
  
  val ggcd : positive -> positive -> positive*(positive*positive)
  
  val coq_Nsucc_double : n -> n
  
  val coq_Ndouble : n -> n
  
  val coq_lor : positive -> positive -> positive
  
  val coq_land : positive -> positive -> n
  
  val ldiff : positive -> positive -> n
  
  val coq_lxor : positive -> positive -> n
  
  val shiftl_nat : positive -> nat -> positive
  
  val shiftr_nat : positive -> nat -> positive
  
  val shiftl : positive -> n -> positive
  
  val shiftr : positive -> n -> positive
  
  val testbit_nat : positive -> nat -> bool
  
  val testbit : positive -> n -> bool
  
  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1
  
  val to_nat : positive -> nat
  
  val of_nat : nat -> positive
  
  val of_succ_nat : nat -> positive
  
  val eq_dec : positive -> positive -> sumbool
  
  val peano_rect : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  val peano_rec : 'a1 -> (positive -> 'a1 -> 'a1) -> positive -> 'a1
  
  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of positive * coq_PeanoView
  
  val coq_PeanoView_rect :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val coq_PeanoView_rec :
    'a1 -> (positive -> coq_PeanoView -> 'a1 -> 'a1) -> positive ->
    coq_PeanoView -> 'a1
  
  val peanoView_xO : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView_xI : positive -> coq_PeanoView -> coq_PeanoView
  
  val peanoView : positive -> coq_PeanoView
  
  val coq_PeanoView_iter :
    'a1 -> (positive -> 'a1 -> 'a1) -> positive -> coq_PeanoView -> 'a1
  
  val eqb_spec : positive -> positive -> reflect
  
  val switch_Eq :
    ExtrNative.comparison -> ExtrNative.comparison -> ExtrNative.comparison
  
  val mask2cmp : mask -> ExtrNative.comparison
  
  val leb_spec0 : positive -> positive -> reflect
  
  val ltb_spec0 : positive -> positive -> reflect
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Rev : 
   sig 
    module ORev : 
     sig 
      type t = Coq__1.t
     end
    
    module MRev : 
     sig 
      val max : t -> t -> t
     end
    
    module MPRev : 
     sig 
      module Private_Tac : 
       sig 
        
       end
     end
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : t -> t -> sumbool
    
    val min_case_strong :
      t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      t -> t -> (t -> t -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : t -> t -> sumbool
   end
  
  val max_case_strong : t -> t -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : t -> t -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : t -> t -> sumbool
  
  val min_case_strong : t -> t -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : t -> t -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : t -> t -> sumbool
 end

module N : 
 sig 
  type t = n
  
  val zero : n
  
  val one : n
  
  val two : n
  
  val succ_double : n -> n
  
  val double : n -> n
  
  val succ : n -> n
  
  val pred : n -> n
  
  val succ_pos : n -> positive
  
  val add : n -> n -> n
  
  val sub : n -> n -> n
  
  val mul : n -> n -> n
  
  val compare : n -> n -> ExtrNative.comparison
  
  val eqb : n -> n -> bool
  
  val leb : n -> n -> bool
  
  val ltb : n -> n -> bool
  
  val min : n -> n -> n
  
  val max : n -> n -> n
  
  val div2 : n -> n
  
  val even : n -> bool
  
  val odd : n -> bool
  
  val pow : n -> n -> n
  
  val square : n -> n
  
  val log2 : n -> n
  
  val size : n -> n
  
  val size_nat : n -> nat
  
  val pos_div_eucl : positive -> n -> n*n
  
  val div_eucl : n -> n -> n*n
  
  val div : n -> n -> n
  
  val modulo : n -> n -> n
  
  val gcd : n -> n -> n
  
  val ggcd : n -> n -> n*(n*n)
  
  val sqrtrem : n -> n*n
  
  val sqrt : n -> n
  
  val coq_lor : n -> n -> n
  
  val coq_land : n -> n -> n
  
  val ldiff : n -> n -> n
  
  val coq_lxor : n -> n -> n
  
  val shiftl_nat : n -> nat -> n
  
  val shiftr_nat : n -> nat -> n
  
  val shiftl : n -> n -> n
  
  val shiftr : n -> n -> n
  
  val testbit_nat : n -> nat -> bool
  
  val testbit : n -> n -> bool
  
  val to_nat : n -> nat
  
  val of_nat : nat -> n
  
  val iter : n -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val eq_dec : n -> n -> sumbool
  
  val discr : n -> positive sumor
  
  val binary_rect : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val binary_rec : 'a1 -> (n -> 'a1 -> 'a1) -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rect : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val peano_rec : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  val leb_spec0 : n -> n -> reflect
  
  val ltb_spec0 : n -> n -> reflect
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val recursion : 'a1 -> (n -> 'a1 -> 'a1) -> n -> 'a1
  
  module Private_OrderTac : 
   sig 
    module Elts : 
     sig 
      type t = n
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  module Private_NZPow : 
   sig 
    
   end
  
  module Private_NZSqrt : 
   sig 
    
   end
  
  val sqrt_up : n -> n
  
  val log2_up : n -> n
  
  module Private_NZDiv : 
   sig 
    
   end
  
  val lcm : n -> n -> n
  
  val eqb_spec : n -> n -> reflect
  
  val b2n : bool -> n
  
  val setbit : n -> n -> n
  
  val clearbit : n -> n -> n
  
  val ones : n -> n
  
  val lnot : n -> n -> n
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Rev : 
   sig 
    module ORev : 
     sig 
      type t = n
     end
    
    module MRev : 
     sig 
      val max : n -> n -> n
     end
    
    module MPRev : 
     sig 
      module Private_Tac : 
       sig 
        
       end
     end
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : n -> n -> sumbool
    
    val min_case_strong :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      n -> n -> (n -> n -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : n -> n -> sumbool
   end
  
  val max_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : n -> n -> sumbool
  
  val min_case_strong : n -> n -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : n -> n -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : n -> n -> sumbool
 end

module Z : 
 sig 
  type t = z
  
  val zero : z
  
  val one : z
  
  val two : z
  
  val double : z -> z
  
  val succ_double : z -> z
  
  val pred_double : z -> z
  
  val pos_sub : positive -> positive -> z
  
  val add : z -> z -> z
  
  val opp : z -> z
  
  val succ : z -> z
  
  val pred : z -> z
  
  val sub : z -> z -> z
  
  val mul : z -> z -> z
  
  val pow_pos : z -> positive -> z
  
  val pow : z -> z -> z
  
  val square : z -> z
  
  val compare : z -> z -> ExtrNative.comparison
  
  val sgn : z -> z
  
  val leb : z -> z -> bool
  
  val ltb : z -> z -> bool
  
  val geb : z -> z -> bool
  
  val gtb : z -> z -> bool
  
  val eqb : z -> z -> bool
  
  val max : z -> z -> z
  
  val min : z -> z -> z
  
  val abs : z -> z
  
  val abs_nat : z -> nat
  
  val abs_N : z -> n
  
  val to_nat : z -> nat
  
  val to_N : z -> n
  
  val of_nat : nat -> z
  
  val of_N : n -> z
  
  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1
  
  val pos_div_eucl : positive -> z -> z*z
  
  val div_eucl : z -> z -> z*z
  
  val div : z -> z -> z
  
  val modulo : z -> z -> z
  
  val quotrem : z -> z -> z*z
  
  val quot : z -> z -> z
  
  val rem : z -> z -> z
  
  val even : z -> bool
  
  val odd : z -> bool
  
  val div2 : z -> z
  
  val quot2 : z -> z
  
  val log2 : z -> z
  
  val sqrtrem : z -> z*z
  
  val sqrt : z -> z
  
  val gcd : z -> z -> z
  
  val ggcd : z -> z -> z*(z*z)
  
  val testbit : z -> z -> bool
  
  val shiftl : z -> z -> z
  
  val shiftr : z -> z -> z
  
  val coq_lor : z -> z -> z
  
  val coq_land : z -> z -> z
  
  val ldiff : z -> z -> z
  
  val coq_lxor : z -> z -> z
  
  val eq_dec : z -> z -> sumbool
  
  module Private_BootStrap : 
   sig 
    
   end
  
  val leb_spec0 : z -> z -> reflect
  
  val ltb_spec0 : z -> z -> reflect
  
  module Private_OrderTac : 
   sig 
    module Elts : 
     sig 
      type t = z
     end
    
    module Tac : 
     sig 
      
     end
   end
  
  val sqrt_up : z -> z
  
  val log2_up : z -> z
  
  module Private_NZDiv : 
   sig 
    
   end
  
  module Private_Div : 
   sig 
    module Quot2Div : 
     sig 
      val div : z -> z -> z
      
      val modulo : z -> z -> z
     end
    
    module NZQuot : 
     sig 
      
     end
   end
  
  val lcm : z -> z -> z
  
  val eqb_spec : z -> z -> reflect
  
  val b2z : bool -> z
  
  val setbit : z -> z -> z
  
  val clearbit : z -> z -> z
  
  val lnot : z -> z
  
  val ones : z -> z
  
  module Private_Tac : 
   sig 
    
   end
  
  module Private_Rev : 
   sig 
    module ORev : 
     sig 
      type t = z
     end
    
    module MRev : 
     sig 
      val max : z -> z -> z
     end
    
    module MPRev : 
     sig 
      module Private_Tac : 
       sig 
        
       end
     end
   end
  
  module Private_Dec : 
   sig 
    val max_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val max_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : z -> z -> sumbool
    
    val min_case_strong :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1
    
    val min_case :
      z -> z -> (z -> z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : z -> z -> sumbool
   end
  
  val max_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : z -> z -> sumbool
  
  val min_case_strong : z -> z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : z -> z -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : z -> z -> sumbool
 end

val zeq_bool : z -> z -> bool

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type int = ExtrNative.uint

val lsl0 : int -> int -> int

val lsr0 : int -> int -> int

val land0 : int -> int -> int

val lxor0 : int -> int -> int

val sub0 : int -> int -> int

val eqb0 : int -> int -> bool

val ltb0 : int -> int -> bool

val leb0 : int -> int -> bool

val foldi_cont :
  (int -> ('a1 -> 'a2) -> 'a1 -> 'a2) -> int -> int -> ('a1 -> 'a2) -> 'a1 ->
  'a2

val foldi_down_cont :
  (int -> ('a1 -> 'a2) -> 'a1 -> 'a2) -> int -> int -> ('a1 -> 'a2) -> 'a1 ->
  'a2

val is_zero : int -> bool

val is_even : int -> bool

val compare0 : int -> int -> ExtrNative.comparison

val foldi : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1

val fold : ('a1 -> 'a1) -> int -> int -> 'a1 -> 'a1

val foldi_down : (int -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1

val forallb0 : (int -> bool) -> int -> int -> bool

val existsb0 : (int -> bool) -> int -> int -> bool

val cast : int -> int -> (__ -> __ -> __) option

val reflect_eqb : int -> int -> reflect

type 'a array = 'a ExtrNative.parray

val make : int -> 'a1 -> 'a1 array

val get : 'a1 array -> int -> 'a1

val default : 'a1 array -> 'a1

val set : 'a1 array -> int -> 'a1 -> 'a1 array

val length : 'a1 array -> int

val to_list : 'a1 array -> 'a1 list

val forallbi : (int -> 'a1 -> bool) -> 'a1 array -> bool

val forallb1 : ('a1 -> bool) -> 'a1 array -> bool

val existsb1 : ('a1 -> bool) -> 'a1 array -> bool

val mapi : (int -> 'a1 -> 'a2) -> 'a1 array -> 'a2 array

val foldi_left : (int -> 'a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 array -> 'a1

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

val afold_right :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a2 -> 'a1) -> 'a2 array -> 'a1

val rev_aux : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val distinct_aux2 : ('a1 -> 'a1 -> bool) -> bool -> 'a1 -> 'a1 list -> bool

val distinct_aux : ('a1 -> 'a1 -> bool) -> bool -> 'a1 list -> bool

val distinct : ('a1 -> 'a1 -> bool) -> 'a1 list -> bool

val forallb2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

module Form : 
 sig 
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
  
  val form_rect :
    (int -> 'a1) -> 'a1 -> 'a1 -> (int -> int -> 'a1) -> (int array -> 'a1)
    -> (int array -> 'a1) -> (int array -> 'a1) -> (int -> int -> 'a1) ->
    (int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> form -> 'a1
  
  val form_rec :
    (int -> 'a1) -> 'a1 -> 'a1 -> (int -> int -> 'a1) -> (int array -> 'a1)
    -> (int array -> 'a1) -> (int array -> 'a1) -> (int -> int -> 'a1) ->
    (int -> int -> 'a1) -> (int -> int -> int -> 'a1) -> form -> 'a1
  
  val is_Ftrue : form -> bool
  
  val is_Ffalse : form -> bool
  
  val interp_aux : (int -> bool) -> (int -> bool) -> form -> bool
  
  val t_interp : (int -> bool) -> form array -> bool array
  
  val lt_form : int -> form -> bool
  
  val wf : form array -> bool
  
  val interp_state_var : (int -> bool) -> form array -> int -> bool
  
  val interp : (int -> bool) -> form array -> form -> bool
  
  val check_form : form array -> bool
 end

type typ_eqb = { te_eqb : (__ -> __ -> bool);
                 te_reflect : (__ -> __ -> reflect) }

type te_carrier = __

val te_eqb : typ_eqb -> te_carrier -> te_carrier -> bool

module Typ : 
 sig 
  type coq_type =
  | Tindex of int
  | TZ
  | Tbool
  | Tpositive
  
  val type_rect : (int -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_type -> 'a1
  
  val type_rec : (int -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> coq_type -> 'a1
  
  type ftype = coq_type list*coq_type
  
  type interp = __
  
  type interp_ftype = __
  
  val i_eqb : typ_eqb array -> coq_type -> interp -> interp -> bool
  
  val reflect_i_eqb :
    typ_eqb array -> coq_type -> interp -> interp -> reflect
  
  type cast_result =
  | Cast of (__ -> __ -> __)
  | NoCast
  
  val cast_result_rect :
    coq_type -> coq_type -> ((__ -> __ -> __) -> 'a1) -> 'a1 -> cast_result
    -> 'a1
  
  val cast_result_rec :
    coq_type -> coq_type -> ((__ -> __ -> __) -> 'a1) -> 'a1 -> cast_result
    -> 'a1
  
  val cast : coq_type -> coq_type -> cast_result
  
  val eqb : coq_type -> coq_type -> bool
  
  val reflect_eqb : coq_type -> coq_type -> reflect
 end

val list_beq : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val reflect_list_beq :
  ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> reflect) -> 'a1 list -> 'a1 list ->
  reflect

module Atom : 
 sig 
  type cop =
  | CO_xH
  | CO_Z0
  
  val cop_rect : 'a1 -> 'a1 -> cop -> 'a1
  
  val cop_rec : 'a1 -> 'a1 -> cop -> 'a1
  
  type unop =
  | UO_xO
  | UO_xI
  | UO_Zpos
  | UO_Zneg
  | UO_Zopp
  
  val unop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> unop -> 'a1
  
  val unop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> unop -> 'a1
  
  type binop =
  | BO_Zplus
  | BO_Zminus
  | BO_Zmult
  | BO_Zlt
  | BO_Zle
  | BO_Zge
  | BO_Zgt
  | BO_eq of Typ.coq_type
  
  val binop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (Typ.coq_type -> 'a1) ->
    binop -> 'a1
  
  val binop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (Typ.coq_type -> 'a1) ->
    binop -> 'a1
  
  type nop =
    Typ.coq_type
    (* singleton inductive, whose constructor was NO_distinct *)
  
  val nop_rect : (Typ.coq_type -> 'a1) -> nop -> 'a1
  
  val nop_rec : (Typ.coq_type -> 'a1) -> nop -> 'a1
  
  type atom =
  | Acop of cop
  | Auop of unop * int
  | Abop of binop * int * int
  | Anop of nop * int list
  | Aapp of int * int list
  
  val atom_rect :
    (cop -> 'a1) -> (unop -> int -> 'a1) -> (binop -> int -> int -> 'a1) ->
    (nop -> int list -> 'a1) -> (int -> int list -> 'a1) -> atom -> 'a1
  
  val atom_rec :
    (cop -> 'a1) -> (unop -> int -> 'a1) -> (binop -> int -> int -> 'a1) ->
    (nop -> int list -> 'a1) -> (int -> int list -> 'a1) -> atom -> 'a1
  
  val cop_eqb : cop -> cop -> bool
  
  val uop_eqb : unop -> unop -> bool
  
  val bop_eqb : binop -> binop -> bool
  
  val nop_eqb : nop -> nop -> bool
  
  val eqb : atom -> atom -> bool
  
  val reflect_cop_eqb : cop -> cop -> reflect
  
  val reflect_uop_eqb : unop -> unop -> reflect
  
  val reflect_bop_eqb : binop -> binop -> reflect
  
  val reflect_nop_eqb : nop -> nop -> reflect
  
  val reflect_eqb : atom -> atom -> reflect
  
  type ('t, 'i) coq_val = { v_type : 't; v_val : 'i }
  
  val val_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_val -> 'a3
  
  val val_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) coq_val -> 'a3
  
  val v_type : ('a1, 'a2) coq_val -> 'a1
  
  val v_val : ('a1, 'a2) coq_val -> 'a2
  
  type bval = (Typ.coq_type, Typ.interp) coq_val
  
  val coq_Bval :
    typ_eqb array -> Typ.coq_type -> Typ.interp -> (Typ.coq_type, Typ.interp)
    coq_val
  
  type tval = (Typ.ftype, Typ.interp_ftype) coq_val
  
  val coq_Tval :
    typ_eqb array -> Typ.ftype -> Typ.interp_ftype -> (Typ.ftype,
    Typ.interp_ftype) coq_val
  
  val bvtrue : typ_eqb array -> bval
  
  val bvfalse : typ_eqb array -> bval
  
  val typ_cop : cop -> Typ.coq_type
  
  val typ_uop : unop -> Typ.coq_type*Typ.coq_type
  
  val typ_bop : binop -> (Typ.coq_type*Typ.coq_type)*Typ.coq_type
  
  val typ_nop : nop -> Typ.coq_type*Typ.coq_type
  
  val check_args :
    (int -> Typ.coq_type) -> int list -> Typ.coq_type list -> bool
  
  val check_aux :
    typ_eqb array -> tval array -> (int -> Typ.coq_type) -> atom ->
    Typ.coq_type -> bool
  
  val check_args_dec :
    (int -> Typ.coq_type) -> Typ.coq_type -> int list -> Typ.coq_type list ->
    sumbool
  
  val check_aux_dec :
    typ_eqb array -> tval array -> (int -> Typ.coq_type) -> atom -> sumbool
  
  val apply_unop :
    typ_eqb array -> Typ.coq_type -> Typ.coq_type -> (Typ.interp ->
    Typ.interp) -> bval -> (Typ.coq_type, Typ.interp) coq_val
  
  val apply_binop :
    typ_eqb array -> Typ.coq_type -> Typ.coq_type -> Typ.coq_type ->
    (Typ.interp -> Typ.interp -> Typ.interp) -> bval -> bval ->
    (Typ.coq_type, Typ.interp) coq_val
  
  val apply_func :
    typ_eqb array -> Typ.coq_type list -> Typ.coq_type -> Typ.interp_ftype ->
    bval list -> bval
  
  val interp_cop : typ_eqb array -> cop -> (Typ.coq_type, Typ.interp) coq_val
  
  val interp_uop :
    typ_eqb array -> unop -> bval -> (Typ.coq_type, Typ.interp) coq_val
  
  val interp_bop :
    typ_eqb array -> binop -> bval -> bval -> (Typ.coq_type, Typ.interp)
    coq_val
  
  val compute_interp :
    typ_eqb array -> (int -> bval) -> Typ.coq_type -> Typ.interp list -> int
    list -> Typ.interp list option
  
  val interp_aux :
    typ_eqb array -> tval array -> (int -> bval) -> atom -> bval
  
  val interp_bool : typ_eqb array -> bval -> bool
  
  val t_interp : typ_eqb array -> tval array -> atom array -> bval array
  
  val lt_atom : int -> atom -> bool
  
  val wf : atom array -> bool
  
  val get_type' : typ_eqb array -> bval array -> int -> Typ.coq_type
  
  val get_type :
    typ_eqb array -> tval array -> atom array -> int -> Typ.coq_type
  
  val wt : typ_eqb array -> tval array -> atom array -> bool
  
  val interp_hatom : typ_eqb array -> tval array -> atom array -> int -> bval
  
  val interp : typ_eqb array -> tval array -> atom array -> atom -> bval
  
  val interp_form_hatom :
    typ_eqb array -> tval array -> atom array -> int -> bool
  
  val check_atom : atom array -> bool
 end

val or_of_imp : int array -> int array

val check_True : C.t

val check_False : int list

val check_BuildDef : Form.form array -> int -> C.t

val check_ImmBuildDef : Form.form array -> S.t -> int -> C.t

val check_BuildDef2 : Form.form array -> int -> C.t

val check_ImmBuildDef2 : Form.form array -> S.t -> int -> C.t

val check_BuildProj : Form.form array -> int -> int -> C.t

val check_ImmBuildProj : Form.form array -> S.t -> int -> int -> C.t

val get_eq :
  Form.form array -> Atom.atom array -> int -> (int -> int -> C.t) -> C.t

val check_trans_aux :
  Form.form array -> Atom.atom array -> int -> int -> int list -> int -> C.t
  -> C.t

val check_trans :
  Form.form array -> Atom.atom array -> int -> int list -> C.t

val build_congr :
  Form.form array -> Atom.atom array -> int option list -> int list -> int
  list -> C.t -> C.t

val check_congr :
  Form.form array -> Atom.atom array -> int -> int option list -> C.t

val check_congr_pred :
  Form.form array -> Atom.atom array -> int -> int -> int option list -> C.t

type 'c pol =
| Pc of 'c
| Pinj of positive * 'c pol
| PX of 'c pol * positive * 'c pol

val p0 : 'a1 -> 'a1 pol

val p1 : 'a1 -> 'a1 pol

val peq : ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> bool

val mkPinj : positive -> 'a1 pol -> 'a1 pol

val mkPinj_pred : positive -> 'a1 pol -> 'a1 pol

val mkPX :
  'a1 -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val mkXi : 'a1 -> 'a1 -> positive -> 'a1 pol

val mkX : 'a1 -> 'a1 -> 'a1 pol

val popp : ('a1 -> 'a1) -> 'a1 pol -> 'a1 pol

val paddC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val psubC : ('a1 -> 'a1 -> 'a1) -> 'a1 pol -> 'a1 -> 'a1 pol

val paddI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol ->
  positive -> 'a1 pol -> 'a1 pol

val psubI :
  ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 pol -> 'a1 pol -> 'a1 pol) ->
  'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val paddX :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1 pol) -> 'a1 pol
  -> positive -> 'a1 pol -> 'a1 pol

val psubX :
  'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol -> 'a1 pol -> 'a1
  pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val padd :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol ->
  'a1 pol

val psub :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
  -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val pmulC_aux :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 -> 'a1
  pol

val pmulC :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1
  -> 'a1 pol

val pmulI :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 pol ->
  'a1 pol -> 'a1 pol) -> 'a1 pol -> positive -> 'a1 pol -> 'a1 pol

val pmul :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val psquare :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 pol -> 'a1 pol

type 'c pExpr =
| PEc of 'c
| PEX of positive
| PEadd of 'c pExpr * 'c pExpr
| PEsub of 'c pExpr * 'c pExpr
| PEmul of 'c pExpr * 'c pExpr
| PEopp of 'c pExpr
| PEpow of 'c pExpr * n

val mk_X : 'a1 -> 'a1 -> positive -> 'a1 pol

val ppow_pos :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> 'a1 pol -> positive -> 'a1 pol

val ppow_N :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 pol -> 'a1 pol) -> 'a1 pol -> n -> 'a1 pol

val norm_aux :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

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

val tt : 'a1 cnf

val ff : 'a1 cnf

val add_term :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 -> 'a1 clause -> 'a1
  clause option

val or_clause :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 clause ->
  'a1 clause option

val or_clause_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 clause -> 'a1 cnf -> 'a1
  cnf

val or_cnf :
  ('a1 -> bool) -> ('a1 -> 'a1 -> 'a1 option) -> 'a1 cnf -> 'a1 cnf -> 'a1
  cnf

val and_cnf : 'a1 cnf -> 'a1 cnf -> 'a1 cnf

val xcnf :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1 ->
  'a2 cnf) -> bool -> 'a1 bFormula -> 'a2 cnf

val cnf_checker : ('a1 list -> 'a2 -> bool) -> 'a1 cnf -> 'a2 list -> bool

val tauto_checker :
  ('a2 -> bool) -> ('a2 -> 'a2 -> 'a2 option) -> ('a1 -> 'a2 cnf) -> ('a1 ->
  'a2 cnf) -> ('a2 list -> 'a3 -> bool) -> 'a1 bFormula -> 'a3 list -> bool

val cneqb : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

val cltb : ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 -> bool

type 'c polC = 'c pol

type op1 =
| Equal
| NonEqual
| Strict
| NonStrict

type 'c nFormula = 'c polC*op1

val opMult : op1 -> op1 -> op1 option

val opAdd : op1 -> op1 -> op1 option

type 'c psatz =
| PsatzIn of nat
| PsatzSquare of 'c polC
| PsatzMulC of 'c polC * 'c psatz
| PsatzMulE of 'c psatz * 'c psatz
| PsatzAdd of 'c psatz * 'c psatz
| PsatzC of 'c
| PsatzZ

val map_option : ('a1 -> 'a2 option) -> 'a1 option -> 'a2 option

val map_option2 :
  ('a1 -> 'a2 -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option

val pexpr_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 polC -> 'a1 nFormula -> 'a1 nFormula option

val nformula_times_nformula :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> 'a1 nFormula -> 'a1 nFormula -> 'a1 nFormula option

val nformula_plus_nformula :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> 'a1
  nFormula -> 'a1 nFormula option

val eval_Psatz :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula list -> 'a1 psatz -> 'a1
  nFormula option

val check_inconsistent :
  'a1 -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 -> bool) -> 'a1 nFormula -> bool

type op2 =
| OpEq
| OpNEq
| OpLe
| OpGe
| OpLt
| OpGt

type 't formula = { flhs : 't pExpr; fop : op2; frhs : 't pExpr }

val norm :
  'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 ->
  'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pExpr -> 'a1 pol

val psub0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1
  -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol -> 'a1 pol

val padd0 :
  'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> 'a1 pol -> 'a1 pol ->
  'a1 pol

type zWitness = z psatz

val psub1 : z pol -> z pol -> z pol

val padd1 : z pol -> z pol -> z pol

val norm0 : z pExpr -> z pol

val xnormalise : z formula -> z nFormula list

val normalise : z formula -> z nFormula cnf

val xnegate : z formula -> z nFormula list

val negate : z formula -> z nFormula cnf

val zunsat : z nFormula -> bool

val zdeduce : z nFormula -> z nFormula -> z nFormula option

val ceiling : z -> z -> z

type zArithProof =
| DoneProof
| RatProof of zWitness * zArithProof
| CutProof of zWitness * zArithProof
| EnumProof of zWitness * zWitness * zArithProof list

val zgcdM : z -> z -> z

val zgcd_pol : z polC -> z*z

val zdiv_pol : z polC -> z -> z polC

val makeCuttingPlane : z polC -> z polC*z

val genCuttingPlane : z nFormula -> ((z polC*z)*op1) option

val nformula_of_cutting_plane : ((z polC*z)*op1) -> z nFormula

val is_pol_Z0 : z polC -> bool

val eval_Psatz0 : z nFormula list -> zWitness -> z nFormula option

val valid_cut_sign : op1 -> bool

val zChecker : z nFormula list -> zArithProof -> bool

val zTautoChecker : z formula bFormula -> zArithProof list -> bool

val build_positive_atom_aux :
  (int -> positive option) -> Atom.atom -> positive option

val build_positive : Atom.atom array -> int -> positive option

val build_z_atom_aux : Atom.atom array -> Atom.atom -> z option

val build_z_atom : Atom.atom array -> Atom.atom -> z option

type vmap = positive*Atom.atom list

val find_var_aux : Atom.atom -> positive -> Atom.atom list -> positive option

val find_var : vmap -> Atom.atom -> vmap*positive

val empty_vmap : vmap

val build_pexpr_atom_aux :
  Atom.atom array -> (vmap -> int -> vmap*z pExpr) -> vmap -> Atom.atom ->
  vmap*z pExpr

val build_pexpr : Atom.atom array -> vmap -> int -> vmap*z pExpr

val build_op2 : Atom.binop -> op2 option

val build_formula_atom :
  Atom.atom array -> vmap -> Atom.atom -> (vmap*z formula) option

val build_formula : Atom.atom array -> vmap -> int -> (vmap*z formula) option

val build_not2 : int -> z formula bFormula -> z formula bFormula

val build_hform :
  Atom.atom array -> (vmap -> int -> (vmap*z formula bFormula) option) ->
  vmap -> Form.form -> (vmap*z formula bFormula) option

val build_var :
  Form.form array -> Atom.atom array -> vmap -> int -> (vmap*z formula
  bFormula) option

val build_form :
  Form.form array -> Atom.atom array -> vmap -> Form.form -> (vmap*z formula
  bFormula) option

val build_nlit :
  Form.form array -> Atom.atom array -> vmap -> int -> (vmap*z formula
  bFormula) option

val build_clause_aux :
  Form.form array -> Atom.atom array -> vmap -> int list -> (vmap*z formula
  bFormula) option

val build_clause :
  Form.form array -> Atom.atom array -> vmap -> int list -> (vmap*z formula
  bFormula) option

val get_eq0 :
  Form.form array -> Atom.atom array -> int -> (int -> int -> C.t) -> C.t

val get_not_le :
  Form.form array -> Atom.atom array -> int -> (int -> int -> C.t) -> C.t

val check_micromega :
  Form.form array -> Atom.atom array -> int list -> zArithProof list -> C.t

val check_diseq : Form.form array -> Atom.atom array -> int -> C.t

val check_atom_aux :
  Atom.atom array -> (int -> int -> bool) -> Atom.atom -> Atom.atom -> bool

val check_hatom : Atom.atom array -> int -> int -> bool

val check_neg_hatom : Atom.atom array -> int -> int -> bool

val remove_not : Form.form array -> int -> int

val get_and : Form.form array -> int -> int array option

val get_or : Form.form array -> int -> int array option

val flatten_op_body :
  (int -> int array option) -> (int list -> int -> int list) -> int list ->
  int -> int list

val flatten_op_lit :
  (int -> int array option) -> int -> int list -> int -> int list

val flatten_and : Form.form array -> int array -> int list

val flatten_or : Form.form array -> int array -> int list

val check_flatten_body :
  Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> (int ->
  int -> bool) -> int -> int -> bool

val check_flatten_aux :
  Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> int ->
  int -> bool

val check_flatten :
  Form.form array -> (int -> int -> bool) -> (int -> int -> bool) -> S.t ->
  int -> int -> C.t

val check_spl_arith :
  Form.form array -> Atom.atom array -> int list -> int -> zArithProof list
  -> C.t

val check_in : int -> int list -> bool

val check_diseqs_complete_aux :
  int -> int list -> (int*int) option array -> bool

val check_diseqs_complete : int list -> (int*int) option array -> bool

val check_diseqs :
  Form.form array -> Atom.atom array -> Typ.coq_type -> int list -> int array
  -> bool

val check_distinct :
  Form.form array -> Atom.atom array -> int -> int array -> bool

val check_distinct_two_args :
  Form.form array -> Atom.atom array -> int -> int -> bool

val check_lit :
  Form.form array -> Atom.atom array -> (int -> int -> bool) -> int -> int ->
  bool

val check_form_aux :
  Form.form array -> Atom.atom array -> (int -> int -> bool) -> Form.form ->
  Form.form -> bool

val check_hform : Form.form array -> Atom.atom array -> int -> int -> bool

val check_lit' : Form.form array -> Atom.atom array -> int -> int -> bool

val check_distinct_elim :
  Form.form array -> Atom.atom array -> int list -> int -> int list

type 'step _trace_ = 'step array array

val _checker_ :
  (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> int -> bool

module Euf_Checker : 
 sig 
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
  
  val step_rect :
    (int -> int array -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> 'a1)
    -> (int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int ->
    int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int
    -> int -> int -> 'a1) -> (int -> int -> int list -> 'a1) -> (int -> int
    -> int option list -> 'a1) -> (int -> int -> int -> int option list ->
    'a1) -> (int -> int list -> zArithProof list -> 'a1) -> (int -> int ->
    'a1) -> (int -> int -> int -> zArithProof list -> 'a1) -> (int -> int ->
    int -> 'a1) -> step -> 'a1
  
  val step_rec :
    (int -> int array -> 'a1) -> (int -> int -> int -> 'a1) -> (int -> 'a1)
    -> (int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int ->
    int -> int -> 'a1) -> (int -> int -> 'a1) -> (int -> int -> 'a1) -> (int
    -> int -> int -> 'a1) -> (int -> int -> int list -> 'a1) -> (int -> int
    -> int option list -> 'a1) -> (int -> int -> int -> int option list ->
    'a1) -> (int -> int list -> zArithProof list -> 'a1) -> (int -> int ->
    'a1) -> (int -> int -> int -> zArithProof list -> 'a1) -> (int -> int ->
    int -> 'a1) -> step -> 'a1
  
  val step_checker : Atom.atom array -> Form.form array -> S.t -> step -> S.t
  
  val euf_checker :
    Atom.atom array -> Form.form array -> (C.t -> bool) -> S.t -> step
    _trace_ -> int -> bool
  
  type certif =
  | Certif of int * step _trace_ * int
  
  val certif_rect : (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1
  
  val certif_rec : (int -> step _trace_ -> int -> 'a1) -> certif -> 'a1
  
  val add_roots : S.t -> int array -> int array option -> S.t
  
  val valid :
    typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array ->
    int array -> bool
  
  val checker :
    typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array ->
    int array -> int array option -> certif -> bool
  
  val checker_b :
    typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array ->
    int -> bool -> certif -> bool
  
  val checker_eq :
    typ_eqb array -> Atom.tval array -> Atom.atom array -> Form.form array ->
    int -> int -> int -> certif -> bool
  
  val checker_ext :
    Atom.atom array -> Form.form array -> int array -> int array option ->
    certif -> bool
 end


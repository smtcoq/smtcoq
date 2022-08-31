
type __ = Obj.t

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val compOpp : int -> int

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac :
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 sig
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : int -> positive -> positive -> int

  val compare : positive -> positive -> int

  val eqb : positive -> positive -> bool

  val eq_dec : positive -> positive -> sumbool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> int

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val size : nat

val lsl0 : Uint63.t -> Uint63.t -> Uint63.t

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val lxor0 : Uint63.t -> Uint63.t -> Uint63.t

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb0 : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val leb0 : Uint63.t -> Uint63.t -> bool

val digits : Uint63.t

val is_zero : Uint63.t -> bool

val bit : Uint63.t -> Uint63.t -> bool

val compare0 : Uint63.t -> Uint63.t -> int

type 'x compare1 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare1

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts :
 functor (O:OrderedType) ->
 sig
  module TO :
   sig
    type t = O.t
   end

  module IsTO :
   sig
   end

  module OrderTac :
   sig
   end

  val eq_dec : O.t -> O.t -> sumbool

  val lt_dec : O.t -> O.t -> sumbool

  val eqb : O.t -> O.t -> bool
 end

module KeyOrderedType :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module TO :
     sig
      type t = O.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : O.t -> O.t -> sumbool

    val lt_dec : O.t -> O.t -> sumbool

    val eqb : O.t -> O.t -> bool
   end
 end

module Raw :
 functor (X:OrderedType) ->
 sig
  module MX :
   sig
    module TO :
     sig
      type t = X.t
     end

    module IsTO :
     sig
     end

    module OrderTac :
     sig
     end

    val eq_dec : X.t -> X.t -> sumbool

    val lt_dec : X.t -> X.t -> sumbool

    val eqb : X.t -> X.t -> bool
   end

  module PX :
   sig
    module MO :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end
   end

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  val coq_R_mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
    'a1 coq_R_mem -> 'a2

  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
    'a1 coq_R_mem -> 'a2

  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

  val find : key -> 'a1 t -> 'a1 option

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
    'a1 option -> 'a1 coq_R_find -> 'a2

  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
    'a1 option -> 'a1 coq_R_find -> 'a2

  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_add

  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
    -> 'a1 t -> 'a1 coq_R_add -> 'a2

  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
    -> 'a1 t -> 'a1 coq_R_add -> 'a2

  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
    list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

  val remove : key -> 'a1 t -> 'a1 t

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
    -> 'a1 coq_R_remove -> 'a2

  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
    -> 'a1 coq_R_remove -> 'a2

  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  val coq_R_fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
    coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3

  val coq_R_fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
    coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
    -> 'a3

  val fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
    'a2 -> 'a3

  val fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
    'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t ->
    'a2 -> 'a3

  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * X.t
     * 'elt * (X.t * 'elt) list * X.t compare1
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  val coq_R_equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t ->
    'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1
    t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
    -> bool -> 'a1 coq_R_equal -> 'a2

  val coq_R_equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
    'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t ->
    'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1
    t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t
    -> bool -> 'a1 coq_R_equal -> 'a2

  val equal_rect :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __
    -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val equal_rec :
    ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
    'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
    (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1) list ->
    __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __
    -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

  val coq_R_equal_correct :
    ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

  val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val fold_right_pair :
    ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

  val map2_alt :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3)
    list

  val at_least_one :
    'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
    'a3 option
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

module Z_as_Int :
 sig
  type t = z

  val _0 : z

  val _1 : z

  val _2 : z

  val _3 : z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val max : z -> z -> z

  val eqb : z -> z -> bool

  val ltb : z -> z -> bool

  val leb : z -> z -> bool

  val eq_dec : z -> z -> sumbool

  val gt_le_dec : z -> z -> sumbool

  val ge_lt_dec : z -> z -> sumbool

  val i2z : t -> z
 end

module Coq_Raw :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val tree_rec :
    'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
    -> 'a1 tree -> 'a2

  val height : 'a1 tree -> I.t

  val cardinal : 'a1 tree -> nat

  val empty : 'a1 tree

  val is_empty : 'a1 tree -> bool

  val mem : X.t -> 'a1 tree -> bool

  val find : X.t -> 'a1 tree -> 'a1 option

  val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

  val remove_min :
    'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

  val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

  val remove : X.t -> 'a1 tree -> 'a1 tree

  val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  val t_left : 'a1 triple -> 'a1 tree

  val t_opt : 'a1 triple -> 'a1 option

  val t_right : 'a1 triple -> 'a1 tree

  val split : X.t -> 'a1 tree -> 'a1 triple

  val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

  val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

  val elements : 'a1 tree -> (key * 'a1) list

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  val enumeration_rect :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val enumeration_rec :
    'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
    enumeration -> 'a2

  val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

  val equal_more :
    ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_cont :
    ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
    enumeration -> bool

  val equal_end : 'a1 enumeration -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

  val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

  val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

  val map2_opt :
    (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
    ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
    tree

  module Proofs :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = X.t
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : X.t -> X.t -> sumbool

      val lt_dec : X.t -> X.t -> sumbool

      val eqb : X.t -> X.t -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end
     end

    module L :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end

      type key = X.t

      type 'elt t = (X.t * 'elt) list

      val empty : 'a1 t

      val is_empty : 'a1 t -> bool

      val mem : key -> 'a1 t -> bool

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt t
      | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
         * 'elt coq_R_mem

      val coq_R_mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
        t -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
        t -> bool -> 'a1 coq_R_mem -> 'a2

      val mem_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val mem_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

      val find : key -> 'a1 t -> 'a1 option

      type 'elt coq_R_find =
      | R_find_0 of 'elt t
      | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
         * 'elt coq_R_find

      val coq_R_find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
        -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2)
        -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val find_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val find_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

      val add : key -> 'a1 -> 'a1 t -> 'a1 t

      type 'elt coq_R_add =
      | R_add_0 of 'elt t
      | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
         * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
        -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
        -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

      val add_rect :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val add_rec :
        key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

      val remove : key -> 'a1 t -> 'a1 t

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt t
      | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
      | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
         * 'elt coq_R_remove

      val coq_R_remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
        'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

      val remove_rect :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val remove_rec :
        key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

      val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

      val elements : 'a1 t -> 'a1 t

      val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

      type ('elt, 'a) coq_R_fold =
      | R_fold_0 of 'elt t * 'a
      | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
         * ('elt, 'a) coq_R_fold

      val coq_R_fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val coq_R_fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold -> 'a3

      val fold_rect :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
        t -> 'a2 -> 'a3

      val fold_rec :
        (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
        -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
        t -> 'a2 -> 'a3

      val coq_R_fold_correct :
        (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
        coq_R_fold

      val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

      type 'elt coq_R_equal =
      | R_equal_0 of 'elt t * 'elt t
      | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
         X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
      | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
         X.t * 'elt * (X.t * 'elt) list * X.t compare1
      | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

      val coq_R_equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
        -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
        X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ ->
        'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
        -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val coq_R_equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2
        -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
        X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ ->
        'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
        -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

      val equal_rect :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
        -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
        'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val equal_rec :
        ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t
        -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
        (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t
        -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 -> (X.t * 'a1)
        list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t ->
        'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

      val coq_R_equal_correct :
        ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

      val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

      val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

      val option_cons :
        key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

      val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

      val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

      val map2 :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

      val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

      val fold_right_pair :
        ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

      val map2_alt :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
        (key * 'a3) list

      val at_least_one :
        'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

      val at_least_one_then_f :
        ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option
        -> 'a3 option
     end

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    val coq_R_mem_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    val coq_R_mem_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
      'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1
      tree -> bool -> 'a1 coq_R_mem -> 'a2

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    val coq_R_find_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

    val coq_R_find_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

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

    val coq_R_bal_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    val coq_R_bal_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 ->
      'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
      -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1
      tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
      key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key ->
      'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
      'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
      __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      'a1 tree -> 'a1 coq_R_bal -> 'a2

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
      -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
      coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
       * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

    val coq_R_remove_min_rect :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree
      -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

    val coq_R_remove_min_rec :
      ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
      -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
      -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1 tree
      -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
      ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key * 'elt) * key * 'elt

    val coq_R_merge_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree
      -> 'a1 coq_R_merge -> 'a2

    val coq_R_merge_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree
      -> 'a1 coq_R_merge -> 'a2

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'elt tree * 'elt coq_R_remove

    val coq_R_remove_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    val coq_R_remove_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove ->
      'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t
      -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * (key * 'elt)

    val coq_R_concat_rect :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat
      -> 'a2

    val coq_R_concat_rec :
      ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
      tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key * 'a1)
      -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat
      -> 'a2

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    val coq_R_split_rect :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    val coq_R_split_rec :
      X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
      -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2)
      -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __
      -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option
      -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split
      -> 'a2

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    val coq_R_map_option_rect :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

    val coq_R_map_option_rec :
      (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
      'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
      tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
      -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
      coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
      'a3

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

    val coq_R_map2_opt_rect :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val coq_R_map2_opt_rec :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
      tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
      __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
      tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __ ->
      'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree ->
      ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
      coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree ->
      key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
      tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ ->
      'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1,
      'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3
      tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

    val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    val flatten_e : 'a1 enumeration -> (key * 'a1) list
   end
 end

module IntMake :
 functor (I:Int) ->
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare1

    val eq_dec : t -> t -> sumbool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * I.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2

    val height : 'a1 tree -> I.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> sumbool

            val lt_dec : X.t -> X.t -> sumbool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * X.t compare1
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * 
         I.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
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
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
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
        tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * I.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2 -> 'a1
        tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree
        -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
         * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree ->
        (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
         I.t * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option
         * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree ->
        'a1 option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 
         'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
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
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
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
        'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module E :
   sig
    type t = X.t

    val compare : t -> t -> t compare1

    val eq_dec : t -> t -> sumbool
   end

  module Raw :
   sig
    type key = X.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : X.t -> 'a1 tree -> bool

    val find : X.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : X.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : X.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = X.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : X.t -> X.t -> sumbool

        val lt_dec : X.t -> X.t -> sumbool

        val eqb : X.t -> X.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = X.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : X.t -> X.t -> sumbool

          val lt_dec : X.t -> X.t -> sumbool

          val eqb : X.t -> X.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = X.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : X.t -> X.t -> sumbool

            val lt_dec : X.t -> X.t -> sumbool

            val eqb : X.t -> X.t -> bool
           end
         end

        type key = X.t

        type 'elt t = (X.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_mem_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem ->
          'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_find_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
          coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
          -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_add_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t ->
          'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t
          -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
        | R_remove_3 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove
          -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
          -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) ->
          'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t * 'elt) list * 
           X.t * 'elt * (X.t * 'elt) list * X.t compare1
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal ->
          'a2 -> 'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
          __ -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t compare1 -> __ ->
          __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __
          -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1
          t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> X.t -> 'a1 ->
          (X.t * 'a1) list -> __ -> X.t compare1 -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t ->
          'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option -> 'a1
        coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option ->
        'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = E.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module IntOrderedType :
 sig
  type t = Uint63.t

  val compare : Uint63.t -> Uint63.t -> Uint63.t compare1

  val eq_dec : Uint63.t -> Uint63.t -> sumbool
 end

module Map :
 sig
  module E :
   sig
    type t = Uint63.t

    val compare : Uint63.t -> Uint63.t -> Uint63.t compare1

    val eq_dec : Uint63.t -> Uint63.t -> sumbool
   end

  module Raw :
   sig
    type key = Uint63.t

    type 'elt tree =
    | Leaf
    | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t

    val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> Z_as_Int.t
      -> 'a2) -> 'a1 tree -> 'a2

    val height : 'a1 tree -> Z_as_Int.t

    val cardinal : 'a1 tree -> nat

    val empty : 'a1 tree

    val is_empty : 'a1 tree -> bool

    val mem : Uint63.t -> 'a1 tree -> bool

    val find : Uint63.t -> 'a1 tree -> 'a1 option

    val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    val add : key -> 'a1 -> 'a1 tree -> 'a1 tree

    val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree * (key * 'a1)

    val merge : 'a1 tree -> 'a1 tree -> 'a1 tree

    val remove : Uint63.t -> 'a1 tree -> 'a1 tree

    val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree

    type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                         t_right : 'elt tree }

    val t_left : 'a1 triple -> 'a1 tree

    val t_opt : 'a1 triple -> 'a1 option

    val t_right : 'a1 triple -> 'a1 tree

    val split : Uint63.t -> 'a1 tree -> 'a1 triple

    val concat : 'a1 tree -> 'a1 tree -> 'a1 tree

    val elements_aux : (key * 'a1) list -> 'a1 tree -> (key * 'a1) list

    val elements : 'a1 tree -> (key * 'a1) list

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

    type 'elt enumeration =
    | End
    | More of key * 'elt * 'elt tree * 'elt enumeration

    val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2

    val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration

    val equal_more :
      ('a1 -> 'a1 -> bool) -> Uint63.t -> 'a1 -> ('a1 enumeration -> bool) ->
      'a1 enumeration -> bool

    val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool

    val equal_end : 'a1 enumeration -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool

    val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree

    val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree

    val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree

    module Proofs :
     sig
      module MX :
       sig
        module TO :
         sig
          type t = Uint63.t
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : Uint63.t -> Uint63.t -> sumbool

        val lt_dec : Uint63.t -> Uint63.t -> sumbool

        val eqb : Uint63.t -> Uint63.t -> bool
       end

      module PX :
       sig
        module MO :
         sig
          module TO :
           sig
            type t = Uint63.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Uint63.t -> Uint63.t -> sumbool

          val lt_dec : Uint63.t -> Uint63.t -> sumbool

          val eqb : Uint63.t -> Uint63.t -> bool
         end
       end

      module L :
       sig
        module MX :
         sig
          module TO :
           sig
            type t = Uint63.t
           end

          module IsTO :
           sig
           end

          module OrderTac :
           sig
           end

          val eq_dec : Uint63.t -> Uint63.t -> sumbool

          val lt_dec : Uint63.t -> Uint63.t -> sumbool

          val eqb : Uint63.t -> Uint63.t -> bool
         end

        module PX :
         sig
          module MO :
           sig
            module TO :
             sig
              type t = Uint63.t
             end

            module IsTO :
             sig
             end

            module OrderTac :
             sig
             end

            val eq_dec : Uint63.t -> Uint63.t -> sumbool

            val lt_dec : Uint63.t -> Uint63.t -> sumbool

            val eqb : Uint63.t -> Uint63.t -> bool
           end
         end

        type key = Uint63.t

        type 'elt t = (Uint63.t * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_mem_2 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_mem_3 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list * 
           bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
          'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
          'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_find_2 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_find_3 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
           * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
          'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
          'a1 option -> 'a1 coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_add_2 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_add_3 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
           * 'elt t * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
          'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
          'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_remove_2 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
        | R_remove_3 of 'elt t * Uint63.t * 'elt * (Uint63.t * 'elt) list
           * 'elt t * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
          -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
          -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2)
          -> ('a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __
          -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * Uint63.t * 'elt * (Uint63.t * 'elt) list
           * 'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> 'a2 ->
          ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
          ('a1, 'a2) coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> 'a2 ->
          ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 ->
          ('a1, 'a2) coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> 'a3 ->
          'a3) -> 'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t
          -> 'a2 -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> 'a3 ->
          'a3) -> 'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
          coq_R_fold

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        type 'elt coq_R_equal =
        | R_equal_0 of 'elt t * 'elt t
        | R_equal_1 of 'elt t * 'elt t * Uint63.t * 'elt
           * (Uint63.t * 'elt) list * Uint63.t * 'elt
           * (Uint63.t * 'elt) list * bool * 'elt coq_R_equal
        | R_equal_2 of 'elt t * 'elt t * Uint63.t * 'elt
           * (Uint63.t * 'elt) list * Uint63.t * 'elt
           * (Uint63.t * 'elt) list * Uint63.t compare1
        | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

        val coq_R_equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> bool
          -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> Uint63.t ->
          'a1 -> (Uint63.t * 'a1) list -> __ -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> Uint63.t compare1 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val coq_R_equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> bool
          -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t -> Uint63.t ->
          'a1 -> (Uint63.t * 'a1) list -> __ -> Uint63.t -> 'a1 ->
          (Uint63.t * 'a1) list -> __ -> Uint63.t compare1 -> __ -> __ ->
          'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2)
          -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2

        val equal_rect :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1)
          list -> __ -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ ->
          Uint63.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
          -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val equal_rec :
          ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1
          t -> 'a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ ->
          Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ -> __ -> __ -> 'a2
          -> 'a2) -> ('a1 t -> 'a1 t -> Uint63.t -> 'a1 -> (Uint63.t * 'a1)
          list -> __ -> Uint63.t -> 'a1 -> (Uint63.t * 'a1) list -> __ ->
          Uint63.t compare1 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t
          -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2

        val coq_R_equal_correct :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val option_cons :
          key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2_l :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

        val map2_r :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

        val map2_alt :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
          (key * 'a3) list

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
          option -> 'a3 option
       end

      type 'elt coq_R_mem =
      | R_mem_0 of 'elt tree
      | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem
      | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * bool * 'elt coq_R_mem

      val coq_R_mem_rect :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
        bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2

      val coq_R_mem_rec :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> bool -> 'a1
        coq_R_mem -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
        bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
        coq_R_mem -> 'a2

      type 'elt coq_R_find =
      | R_find_0 of 'elt tree
      | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find
      | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt option * 'elt coq_R_find

      val coq_R_find_rect :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
        'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option
        -> 'a1 coq_R_find -> 'a2

      val coq_R_find_rec :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 option ->
        'a1 coq_R_find -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ ->
        'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option
        -> 'a1 coq_R_find -> 'a2

      type 'elt coq_R_bal =
      | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
      | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t
      | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key
         * 'elt * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

      val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
        key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree
        -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2

      type 'elt coq_R_add =
      | R_add_0 of 'elt tree
      | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add
      | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.t
      | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_add

      val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_add -> 'a2

      type 'elt coq_R_remove_min =
      | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
      | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree
         * key * 'elt * 'elt tree * Z_as_Int.t * ('elt tree * (key * 'elt))
         * 'elt coq_R_remove_min * 'elt tree * (key * 'elt)

      val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2 -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> ('a1 tree * (key * 'a1)) -> 'a1 coq_R_remove_min
        -> 'a2

      type 'elt coq_R_merge =
      | R_merge_0 of 'elt tree * 'elt tree
      | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt) * key * 'elt

      val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> key -> 'a1 -> __ -> 'a2) ->
        'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_merge -> 'a2

      type 'elt coq_R_remove =
      | R_remove_0 of 'elt tree
      | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove
      | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * 'elt coq_R_remove

      val coq_R_remove_rect :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      val coq_R_remove_rec :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_remove -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1
        tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree ->
        'a1 coq_R_remove -> 'a2

      type 'elt coq_R_concat =
      | R_concat_0 of 'elt tree * 'elt tree
      | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt tree * (key * 'elt)

      val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2) ->
        ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        Z_as_Int.t -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a1 tree -> (key * 'a1) -> __ -> 'a2) -> 'a1 tree -> 'a1
        tree -> 'a1 tree -> 'a1 coq_R_concat -> 'a2

      type 'elt coq_R_split =
      | R_split_0 of 'elt tree
      | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree
      | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t
      | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'elt triple * 'elt coq_R_split * 'elt tree
         * 'elt option * 'elt tree

      val coq_R_split_rect :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
        'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      val coq_R_split_rec :
        Uint63.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple ->
        'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> Z_as_Int.t -> __ -> __ -> __ -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ ->
        'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split -> 'a2

      type ('elt, 'x) coq_R_map_option =
      | R_map_option_0 of 'elt tree
      | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 
         'x tree * ('elt, 'x) coq_R_map_option
      | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
         * Z_as_Int.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
         * ('elt, 'x) coq_R_map_option

      val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 -> __
        -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree
        -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> __ -> 'a2 tree ->
        ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3

      type ('elt, 'x0, 'x) coq_R_map2_opt =
      | R_map2_opt_0 of 'elt tree * 'x0 tree
      | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t
      | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt
      | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
         * 'elt tree * Z_as_Int.t * 'x0 tree * key * 'x0 * 'x0 tree
         * Z_as_Int.t * 'x0 tree * 'x0 option * 'x0 tree * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt * 'x tree
         * ('elt, 'x0, 'x) coq_R_map2_opt

      val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key ->
        'a1 -> 'a1 tree -> Z_as_Int.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2
        tree -> Z_as_Int.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> 'a3 -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
        'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.t
        -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.t -> __ ->
        'a2 tree -> 'a2 option -> 'a2 tree -> __ -> __ -> 'a3 tree -> ('a1,
        'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2, 'a3)
        coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2 tree -> 'a3 tree ->
        ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4

      val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2

      val flatten_e : 'a1 enumeration -> (key * 'a1) list
     end
   end

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  val this : 'a1 bst -> 'a1 Raw.tree

  type 'elt t = 'elt bst

  type key = Uint63.t

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val find : key -> 'a1 t -> 'a1 option

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

type 'a array = ('a Map.t * 'a) * Uint63.t

val make : Uint63.t -> 'a1 -> 'a1 array

val get : 'a1 array -> Uint63.t -> 'a1

val set : 'a1 array -> Uint63.t -> 'a1 -> 'a1 array

val length : 'a1 array -> Uint63.t

val iter_int63_aux : nat -> Uint63.t -> ('a1 -> 'a1) -> 'a1 -> 'a1

val iter_int63 : Uint63.t -> ('a1 -> 'a1) -> 'a1 -> 'a1

val foldi : (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val to_list : 'a1 array -> 'a1 list

module Lit :
 sig
  val _true : Uint63.t
 end

module C :
 sig
  type t = Uint63.t list

  val _true : t

  val is_false : t -> bool

  val or_aux : (t -> t -> t) -> Uint63.t -> t -> t -> Uint63.t list

  val coq_or : t -> t -> t

  val resolve_aux : (t -> t -> t) -> Uint63.t -> t -> t -> t

  val resolve : t -> t -> t
 end

module S :
 sig
  type t = C.t array

  val get : t -> Uint63.t -> C.t

  val internal_set : t -> Uint63.t -> C.t -> t

  val make : Uint63.t -> t

  val insert_no_simpl : Uint63.t -> Uint63.t list -> Uint63.t list

  val sort : Uint63.t list -> Uint63.t list

  val set_clause : t -> Uint63.t -> C.t -> t

  val set_resolve : t -> Uint63.t -> Uint63.t array -> t
 end

type 'step _trace_ = 'step list * 'step

val _checker_ :
  (S.t -> 'a1 -> S.t) -> (C.t -> bool) -> S.t -> 'a1 _trace_ -> Uint63.t ->
  bool

module Sat_Checker :
 sig
  type step =
  | Res of Uint63.t * Uint63.t array

  val resolution_checker :
    (C.t -> bool) -> S.t -> step _trace_ -> Uint63.t -> bool

  type dimacs = Uint63.t array array

  type certif =
  | Certif of Uint63.t * step _trace_ * Uint63.t

  val add_roots : S.t -> dimacs -> S.t

  val checker : dimacs -> certif -> bool
 end

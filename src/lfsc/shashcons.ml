
(*s Hash tables for hash-consing. (Some code is borrowed from the ocaml
    standard library, which is copyright 1996 INRIA.) *)

module type HashedType =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
    val tag : int -> t -> t
  end

module type S =
  sig
    type t
    val hashcons : t -> t
    val iter : (t -> unit) -> unit
    val stats : unit -> int * int * int * int * int * int
  end

module Make(H : HashedType) : (S with type t = H.t) =
struct
  type t = H.t

  module WH = Weak.Make (H)

  let next_tag = ref 0

  let htable = WH.create 5003

  let hashcons d =
    let d = H.tag !next_tag d in
    let o = WH.merge htable d in
    if o == d then incr next_tag;
    o

  let iter f = WH.iter f htable

  let stats () = WH.stats htable
end


type 'a hash_consed = {
  tag : int;
  node : 'a }

module type HashedType_consed =
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type S_consed =
  sig
    type key
    val hashcons : key -> key hash_consed
    val iter : (key hash_consed -> unit) -> unit
    val stats : unit -> int * int * int * int * int * int
  end

module Make_consed(H : HashedType_consed) : (S_consed with type key = H.t) =
struct
  module M = Make(struct
    type t = H.t hash_consed
    let hash x = H.hash x.node
    let equal x y = H.equal x.node y.node
    let tag i x = {x with tag = i}
  end)
  include M
  type key = H.t
  let hashcons x = M.hashcons {tag = -1; node = x}
end

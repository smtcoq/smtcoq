type t = Atom of string | List of t list
val print : Format.formatter -> t -> unit
val print_list : Format.formatter -> t list -> unit
val size : t -> int
val size_list : t list -> int

type solver = Zchaff | Verit
val usage : string
val string_of_solver : solver -> string
val verifier_of_solver : solver -> string -> string -> bool
val run : solver -> string -> string -> unit

val parse_certif : Names.Id.t -> Names.Id.t -> string -> string -> unit
val checker : string -> string -> unit
val theorem : Names.Id.t -> string -> string -> unit
val tactic : unit -> Structures.tactic
val tactic_no_check : unit -> Structures.tactic

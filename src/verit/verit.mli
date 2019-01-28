val parse_certif :
  Names.Id.t ->
  Names.Id.t ->
  Names.Id.t ->
  Names.Id.t ->
  Names.Id.t -> Names.Id.t -> Names.Id.t -> string -> string -> unit
val checker : string -> string -> unit
val checker_debug : string -> string -> unit
val theorem : Names.Id.t -> string -> string -> unit
val tactic : Term.constr list -> Structures.constr_expr list -> Structures.tactic
val tactic_no_check : Term.constr list -> Structures.constr_expr list -> Structures.tactic

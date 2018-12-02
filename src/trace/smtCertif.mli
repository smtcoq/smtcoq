type used = int
type clause_id = int
type 'hform rule =
    ImmFlatten of 'hform clause * 'hform
  | True
  | False
  | BuildDef of 'hform
  | BuildDef2 of 'hform
  | BuildProj of 'hform * int
  | ImmBuildDef of 'hform clause
  | ImmBuildDef2 of 'hform clause
  | ImmBuildProj of 'hform clause * int
  | EqTr of 'hform * 'hform list
  | EqCgr of 'hform * 'hform option list
  | EqCgrP of 'hform * 'hform * 'hform option list
  | LiaMicromega of 'hform list *
      Structures.Micromega_plugin_Certificate.Mc.zArithProof list
  | LiaDiseq of 'hform
  | SplArith of 'hform clause * 'hform *
      Structures.Micromega_plugin_Certificate.Mc.zArithProof list
  | SplDistinctElim of 'hform clause * 'hform
  | Hole of 'hform clause list * 'hform list
  | Forall_inst of 'hform clause * 'hform
  | Qf_lemma of 'hform clause * 'hform

and 'hform clause = {
    mutable id    : clause_id;
    mutable kind  : 'hform clause_kind;
    mutable pos   : int option;
    mutable used  : used;
    mutable prev  : 'hform clause option;
    mutable next  : 'hform clause option;
    mutable value : 'hform list option;
}
and 'hform clause_kind =
    Root
  | Same of 'hform clause
  | Res of 'hform resolution
  | Other of 'hform rule
and 'hform resolution = {
  mutable rc1 : 'hform clause;
  mutable rc2 : 'hform clause;
  mutable rtail : 'hform clause list;
}
val used_clauses : 'a rule -> 'a clause list
val to_string : 'a clause_kind -> string
val print_certif : ('a -> Format.formatter -> 'b -> 'c) -> 'a -> 'b clause -> string -> unit

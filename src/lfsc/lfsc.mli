module C :
  sig
    module MTerm :
      sig
        type key = Ast.Term.t
        type 'a t = 'a Map.Make(Ast.Term).t
        val empty : 'a t
        val is_empty : 'a t -> bool
        val mem : key -> 'a t -> bool
        val add : key -> 'a -> 'a t -> 'a t
        val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
        val singleton : key -> 'a -> 'a t
        val remove : key -> 'a t -> 'a t
        val merge :
          (key -> 'a option -> 'b option -> 'c option) ->
          'a t -> 'b t -> 'c t
        val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
        val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
        val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
        val iter : (key -> 'a -> unit) -> 'a t -> unit
        val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
        val for_all : (key -> 'a -> bool) -> 'a t -> bool
        val exists : (key -> 'a -> bool) -> 'a t -> bool
        val filter : (key -> 'a -> bool) -> 'a t -> 'a t
        val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
        val cardinal : 'a t -> int
        val bindings : 'a t -> (key * 'a) list
        val min_binding : 'a t -> key * 'a
        val min_binding_opt : 'a t -> (key * 'a) option
        val max_binding : 'a t -> key * 'a
        val max_binding_opt : 'a t -> (key * 'a) option
        val choose : 'a t -> key * 'a
        val choose_opt : 'a t -> (key * 'a) option
        val split : key -> 'a t -> 'a t * 'a option * 'a t
        val find : key -> 'a t -> 'a
        val find_opt : key -> 'a t -> 'a option
        val find_first : (key -> bool) -> 'a t -> key * 'a
        val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
        val find_last : (key -> bool) -> 'a t -> key * 'a
        val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
        val map : ('a -> 'b) -> 'a t -> 'b t
        val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
        val to_seq : 'a t -> (key * 'a) Seq.t
        val to_seq_from : key -> 'a t -> (key * 'a) Seq.t
        val add_seq : (key * 'a) Seq.t -> 'a t -> 'a t
        val of_seq : (key * 'a) Seq.t -> 'a t
      end
    type env =
      Converter.Make(Tosmtcoq).env = {
      clauses : int list;
      ax : bool;
      mpred : bool MTerm.t;
      assum : Hstring.t list;
    }
    val empty : env
    val th_res : Ast.term -> Ast.term
    val ignore_all_decls : Ast.term -> Ast.term
    val ignore_decls : Ast.term -> Ast.term
    val ignore_preproc : Ast.term -> Ast.term
    val produce_inputs_preproc : Ast.term -> Ast.term
    val produce_inputs : Ast.term -> Ast.term
    val dvar_of_v : Ast.term -> Ast.term
    val trust_vareq_as_alias : Ast.term -> bool
    val admit_preproc : Ast.term -> Ast.term
    val deferred : Ast.term -> Ast.term
    val register_prop_vars : Ast.term -> Ast.term
    val get_assumptions :
      Hstring.t list -> Ast.term -> Hstring.t list * Ast.term
    val rm_used' : Hstring.t list -> Ast.term -> Hstring.t list
    val rm_used : env -> Ast.term -> env
    val rm_duplicates : ('a -> 'a -> bool) -> 'a list -> 'a list
    val mk_inter_resolution : int list -> int
    val is_ty_Bool : Ast.term -> bool
    val cong : Ast.Term.t list -> env -> Ast.term -> Ast.Term.t list * env
    val trans : Ast.term list -> env -> Ast.term -> Ast.term list * env
    val lem : ?toplevel:bool -> env -> Ast.term -> env
    val result_satlem : Ast.term -> Hstring.t * Ast.term * Ast.term
    val clause_qr : Ast.term -> int
    val reso_of_QR : Ast.term -> int list
    val satlem_simplify : Ast.term -> int option * Ast.term
    val many_satlem_simplify :
      int option -> Ast.term -> int option * Ast.term
    val satlem_simplifies_c : Ast.term -> Ast.term
    val reso_of_satlem_simplify : Ast.term -> int
    val bb_trim_intro_unit : env -> Ast.term -> env * Ast.term
    val is_last_bbres : Ast.term -> bool
    val bb_lem_res : int option -> Ast.term -> int
    val bb_lem : env -> Ast.term -> env
    exception ArithLemma
    val trim_junk_satlem : Ast.term -> Ast.term list
    val continuation_satlem : Ast.term -> Hstring.t * Ast.term
    val is_bbr_satlem_lam : Ast.term -> bool
    val has_intro_bv : Ast.term -> bool
    val has_prefix : string -> string -> bool
    val satlem : ?prefix_cont:string -> Ast.term -> Ast.term
    val bbt : Ast.term -> int option
    val bblast_decls : Ast.term -> Ast.term
    val bv_pred : Hstring.t -> Translator_sig.rule
    val bblast_eqs : Ast.term -> Ast.term
    val bb_proof : Ast.term -> Ast.term
    val convert : Ast.term -> int
    val convert_pt : Ast.term -> int
    val clear : unit -> unit
  end
exception No_proof
val signatures : string list
val process_signatures_once : unit -> unit
val lfsc_parse_last : Lexing.lexbuf -> Ast.command option
val lfsc_parse_one : Lexing.lexbuf -> Ast.command option
val import_trace :
  (SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t) option ->
  ('a -> Ast.command option) -> 'a -> int * SmtAtom.Form.t SmtCertif.clause
val import_trace_from_file :
  (SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t) option ->
  string -> int * SmtAtom.Form.t SmtCertif.clause
val clear_all : unit -> unit
val import_all :
  string ->
  string ->
  SmtBtype.reify_tbl * SmtAtom.Op.reify_tbl * SmtAtom.Atom.reify_tbl *
  SmtAtom.Form.reify * SmtAtom.Form.t list * int *
  SmtAtom.Form.t SmtCertif.clause
val parse_certif :
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id ->
  CoqInterface.id -> CoqInterface.id -> string -> string -> unit
val checker_debug : string -> string -> 'a
val theorem : CoqInterface.id -> string -> string -> unit
val checker : string -> string -> unit
val string_logic : SmtAtom.Op.reify_tbl -> SmtAtom.Form.t -> string
val call_cvc4 :
  Environ.env ->
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  'a ->
  'b ->
  SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
  'c -> int * SmtAtom.Form.t SmtCertif.clause
val export :
  out_channel ->
  SmtBtype.reify_tbl -> SmtAtom.Op.reify_tbl -> SmtAtom.Form.t -> unit
val get_model_from_file : string -> SExpr.t
val call_cvc4_file :
  Environ.env ->
  SmtBtype.reify_tbl ->
  SmtAtom.Op.reify_tbl ->
  'a ->
  'b ->
  SmtAtom.Form.t SmtCertif.clause * SmtAtom.Form.t ->
  int * SmtAtom.Form.t SmtCertif.clause
val cvc4_logic : SmtMisc.SL.t
val tactic_gen :
  (Environ.env -> CoqInterface.constr -> CoqInterface.constr) ->
  CoqInterface.tactic
val tactic : unit -> CoqInterface.tactic
val tactic_no_check : unit -> CoqInterface.tactic

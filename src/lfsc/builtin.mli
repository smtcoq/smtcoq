module H :
  sig
    val mp_add : Hstring.t
    val mp_mul : Hstring.t
    val mp_is_neg : Hstring.t
    val mp_is_zero : Hstring.t
    val uminus : Hstring.t
    val bool_lfsc : Hstring.t
    val tt : Hstring.t
    val ff : Hstring.t
    val var : Hstring.t
    val lit : Hstring.t
    val clause : Hstring.t
    val cln : Hstring.t
    val okay : Hstring.t
    val ok : Hstring.t
    val pos : Hstring.t
    val neg : Hstring.t
    val clc : Hstring.t
    val concat_cl : Hstring.t
    val clr : Hstring.t
    val formula : Hstring.t
    val not_ : Hstring.t
    val and_ : Hstring.t
    val or_ : Hstring.t
    val impl_ : Hstring.t
    val iff_ : Hstring.t
    val xor_ : Hstring.t
    val ifte_ : Hstring.t
    val ite : Hstring.t
    val iff : Hstring.t
    val flet : Hstring.t
    val impl : Hstring.t
    val gt_Int : Hstring.t
    val ge_Int : Hstring.t
    val lt_Int : Hstring.t
    val le_Int : Hstring.t
    val plus_Int : Hstring.t
    val minus_Int : Hstring.t
    val times_Int : Hstring.t
    val div_Int : Hstring.t
    val uminus_Int : Hstring.t
    val sort : Hstring.t
    val term : Hstring.t
    val tBool : Hstring.t
    val p_app : Hstring.t
    val arrow : Hstring.t
    val apply : Hstring.t
    val bitVec : Hstring.t
    val bit : Hstring.t
    val b0 : Hstring.t
    val b1 : Hstring.t
    val bv : Hstring.t
    val bvn : Hstring.t
    val bvc : Hstring.t
    val bblt : Hstring.t
    val bbltn : Hstring.t
    val bbltc : Hstring.t
    val var_bv : Hstring.t
    val a_bv : Hstring.t
    val a_int : Hstring.t
    val bitof : Hstring.t
    val bblast_term : Hstring.t
    val bvand : Hstring.t
    val bvor : Hstring.t
    val bvxor : Hstring.t
    val bvnand : Hstring.t
    val bvnor : Hstring.t
    val bvxnor : Hstring.t
    val bvmul : Hstring.t
    val bvadd : Hstring.t
    val bvsub : Hstring.t
    val bvudiv : Hstring.t
    val bvurem : Hstring.t
    val bvsdiv : Hstring.t
    val bvsrem : Hstring.t
    val bvsmod : Hstring.t
    val bvshl : Hstring.t
    val bvlshr : Hstring.t
    val bvashr : Hstring.t
    val bvnot : Hstring.t
    val bvneg : Hstring.t
    val bvult : Hstring.t
    val bvslt : Hstring.t
    val bvule : Hstring.t
    val bvsle : Hstring.t
    val concat : Hstring.t
    val extract : Hstring.t
    val zero_extend : Hstring.t
    val sign_extend : Hstring.t
    val array : Hstring.t
    val read : Hstring.t
    val write : Hstring.t
    val diff : Hstring.t
    val append : Hstring.t
    val simplify_clause : Hstring.t
    val bv_constants_are_disequal : Hstring.t
    val bblt_len : Hstring.t
    val bblast_const : Hstring.t
    val bblast_var : Hstring.t
    val bblast_concat : Hstring.t
    val bblast_extract : Hstring.t
    val bblast_zextend : Hstring.t
    val bblast_sextend : Hstring.t
    val bblast_bvand : Hstring.t
    val bblast_bvnot : Hstring.t
    val bblast_bvor : Hstring.t
    val bblast_bvxor : Hstring.t
    val bblast_bvadd : Hstring.t
    val bblast_zero : Hstring.t
    val bblast_bvneg : Hstring.t
    val bblast_bvmul : Hstring.t
    val bblast_eq : Hstring.t
    val bblast_bvult : Hstring.t
    val bblast_bvslt : Hstring.t
    val th_let_pf : Hstring.t
    val th_holds : Hstring.t
    val ttrue : Hstring.t
    val tfalse : Hstring.t
    val a_var_bv : Hstring.t
    val eq : Hstring.t
    val ext : Hstring.t
    val decl_atom : Hstring.t
    val asf : Hstring.t
    val ast : Hstring.t
    val cong : Hstring.t
    val symm : Hstring.t
    val negsymm : Hstring.t
    val trans : Hstring.t
    val negtrans : Hstring.t
    val negtrans1 : Hstring.t
    val negtrans2 : Hstring.t
    val refl : Hstring.t
    val or_elim_1 : Hstring.t
    val or_elim_2 : Hstring.t
    val iff_elim_1 : Hstring.t
    val impl_elim : Hstring.t
    val not_and_elim : Hstring.t
    val xor_elim_1 : Hstring.t
    val xor_elim_2 : Hstring.t
    val ite_elim_1 : Hstring.t
    val ite_elim_2 : Hstring.t
    val ite_elim_3 : Hstring.t
    val not_ite_elim_1 : Hstring.t
    val not_ite_elim_2 : Hstring.t
    val not_ite_elim_3 : Hstring.t
    val not_iff_elim : Hstring.t
    val not_xor_elim : Hstring.t
    val iff_elim_2 : Hstring.t
    val and_elim_1 : Hstring.t
    val not_impl_elim : Hstring.t
    val not_or_elim : Hstring.t
    val and_elim_2 : Hstring.t
    val not_not_elim : Hstring.t
    val not_not_intro : Hstring.t
    val pred_eq_t : Hstring.t
    val pred_eq_f : Hstring.t
    val trust_f : Hstring.t
    val tInt : Hstring.t
    val eq_transitive : Hstring.t
    val row1 : Hstring.t
    val row : Hstring.t
    val negativerow : Hstring.t
    val bv_disequal_constants : Hstring.t
    val truth : Hstring.t
    val holds : Hstring.t
    val q : Hstring.t
    val r : Hstring.t
    val satlem_simplify : Hstring.t
    val intro_assump_f : Hstring.t
    val intro_assump_t : Hstring.t
    val clausify_false : Hstring.t
    val trust : Hstring.t
    val contra : Hstring.t
    val bb_cl : Hstring.t
    val satlem : Hstring.t
    val bv_bbl_var : Hstring.t
    val bv_bbl_const : Hstring.t
    val bv_bbl_bvand : Hstring.t
    val bv_bbl_bvor : Hstring.t
    val bv_bbl_bvxor : Hstring.t
    val bv_bbl_bvnot : Hstring.t
    val bv_bbl_bvneg : Hstring.t
    val bv_bbl_bvadd : Hstring.t
    val bv_bbl_bvmul : Hstring.t
    val bv_bbl_concat : Hstring.t
    val bv_bbl_extract : Hstring.t
    val bv_bbl_zero_extend : Hstring.t
    val bv_bbl_sign_extend : Hstring.t
    val decl_bblast : Hstring.t
    val decl_bblast_with_alias : Hstring.t
    val bv_bbl_eq : Hstring.t
    val bv_bbl_eq_swap : Hstring.t
    val bv_bbl_bvult : Hstring.t
    val bv_bbl_bvslt : Hstring.t
  end
val scope : string list ref
val declare_get : string -> Ast.term -> Ast.term
val define : string -> Ast.term -> unit
val pi : string -> Ast.term -> Ast.term -> Ast.term
val pi_d : string -> Ast.term -> (Ast.term -> Ast.term) -> Ast.term
val mp_add_s : Ast.term
val mp_add : Ast.term -> Ast.term -> Ast.term
val mp_mul_s : Ast.term
val mp_mul : Ast.term -> Ast.term -> Ast.term
val eval_arg : Ast.term -> Ast.term
val mp_isneg : Ast.term -> bool
val mp_iszero : Ast.term -> bool
val uminus : Ast.term
val bool_lfsc : Ast.term
val tt : Ast.term
val ff : Ast.term
val var : Ast.term
val lit : Ast.term
val clause : Ast.term
val cln : Ast.term
val okay : Ast.term
val ok : Ast.term
val pos_s : Ast.term
val neg_s : Ast.term
val clc_s : Ast.term
val concat_cl_s : Ast.term
val clr_s : Ast.term
val formula : Ast.term
val th_holds_s : Ast.term
val th_holds : Ast.term -> Ast.term
val ttrue : Ast.term
val tfalse : Ast.term
val not_s : Ast.term
val and_s : Ast.term
val or_s : Ast.term
val impl_s : Ast.term
val iff_s : Ast.term
val xor_s : Ast.term
val ifte_s : Ast.term
val sort : Ast.term
val term_s : Ast.term
val term : Ast.term -> Ast.term
val tBool : Ast.term
val p_app_s : Ast.term
val p_app : Ast.term -> Ast.term
val arrow_s : Ast.term
val arrow : Ast.term -> Ast.term -> Ast.term
val apply_s : Ast.term
val apply : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val eq_s : Ast.term
val eq : Ast.term -> Ast.term -> Ast.term -> Ast.term
val pos : Ast.term -> Ast.term
val neg : Ast.term -> Ast.term
val clc : Ast.term -> Ast.term -> Ast.term
val clr : Ast.term -> Ast.term -> Ast.term
val concat_cl : Ast.term -> Ast.term -> Ast.term
val not_ : Ast.term -> Ast.term
val and_ : Ast.term -> Ast.term -> Ast.term
val or_ : Ast.term -> Ast.term -> Ast.term
val impl_ : Ast.term -> Ast.term -> Ast.term
val iff_ : Ast.term -> Ast.term -> Ast.term
val xor_ : Ast.term -> Ast.term -> Ast.term
val ifte_ : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bitVec_s : Ast.term
val bitVec : Ast.term -> Ast.term
val bit : Ast.term
val b0 : Ast.term
val b1 : Ast.term
val bv : Ast.term
val bvn : Ast.term
val bvc_s : Ast.term
val bvc : Ast.term -> Ast.term -> Ast.term
val bblt : Ast.term
val bbltn : Ast.term
val bbltc_s : Ast.term
val bbltc : Ast.term -> Ast.term -> Ast.term
val var_bv : Ast.term
val a_var_bv_s : Ast.term
val a_var_bv : Ast.term -> Ast.term -> Ast.term
val a_bv_s : Ast.term
val a_bv : Ast.term -> Ast.term -> Ast.term
val bitof_s : Ast.term
val bitof : Ast.term -> Ast.term -> Ast.term
val bblast_term_s : Ast.term
val bblast_term : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvand_s : Ast.term
val bvor_s : Ast.term
val bvxor_s : Ast.term
val bvnand_s : Ast.term
val bvnor_s : Ast.term
val bvxnor_s : Ast.term
val bvmul_s : Ast.term
val bvadd_s : Ast.term
val bvsub_s : Ast.term
val bvudiv_s : Ast.term
val bvurem_s : Ast.term
val bvsdiv_s : Ast.term
val bvsrem_s : Ast.term
val bvsmod_s : Ast.term
val bvshl_s : Ast.term
val bvlshr_s : Ast.term
val bvashr_s : Ast.term
val bvand : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvor : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvxor : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvnand : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvnor : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvxnor : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvmul : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvadd : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvsub : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvudiv : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvurem : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvsdiv : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvsrem : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvsmod : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvshl : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvlshr : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvashr : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvnot_s : Ast.term
val bvneg_s : Ast.term
val bvnot : Ast.term -> Ast.term -> Ast.term
val bvneg : Ast.term -> Ast.term -> Ast.term
val bvult_s : Ast.term
val bvslt_s : Ast.term
val bvult : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvslt : Ast.term -> Ast.term -> Ast.term -> Ast.term
val concat_s : Ast.term
val concat :
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val extract_s : Ast.term
val extract :
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val zero_extend_s : Ast.term
val zero_extend : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val sign_extend_s : Ast.term
val sign_extend : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val array_s : Ast.term
val array : Ast.term -> Ast.term -> Ast.term
val read_s : Ast.term
val read : Ast.term -> Ast.term -> Ast.term
val write_s : Ast.term
val write : Ast.term -> Ast.term -> Ast.term
val diff_s : Ast.term
val diff : Ast.term -> Ast.term -> Ast.term
val apply_read : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val apply_write :
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val apply_diff : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val refl_s : Ast.term
val refl : Ast.term -> Ast.term -> Ast.term
val cong_s : Ast.term
val cong :
  Ast.term ->
  Ast.term ->
  Ast.term ->
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
module MInt :
  sig
    type key = int
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
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
module STerm :
  sig
    type elt = Ast.Term.t
    type t = Set.Make(Ast.Term).t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val disjoint : t -> t -> bool
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val map : (elt -> elt) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val min_elt_opt : t -> elt option
    val max_elt : t -> elt
    val max_elt_opt : t -> elt option
    val choose : t -> elt
    val choose_opt : t -> elt option
    val split : elt -> t -> t * bool * t
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t
    val to_seq_from : elt -> t -> elt Seq.t
    val to_seq : t -> elt Seq.t
    val add_seq : elt Seq.t -> t -> t
    val of_seq : elt Seq.t -> t
  end
type mark_map = STerm.t MInt.t
val empty_marks : 'a MInt.t
val is_marked : MInt.key -> STerm.t MInt.t -> STerm.elt -> bool
val if_marked_do :
  MInt.key ->
  STerm.t MInt.t ->
  STerm.elt -> (STerm.t MInt.t -> 'a) -> (STerm.t MInt.t -> 'a) -> 'a
val markvar_with : MInt.key -> STerm.t MInt.t -> STerm.elt -> STerm.t MInt.t
val ifmarked :
  STerm.t MInt.t ->
  STerm.elt -> (STerm.t MInt.t -> 'a) -> (STerm.t MInt.t -> 'a) -> 'a
val ifmarked1 :
  STerm.t MInt.t ->
  STerm.elt -> (STerm.t MInt.t -> 'a) -> (STerm.t MInt.t -> 'a) -> 'a
val ifmarked2 :
  STerm.t MInt.t ->
  STerm.elt -> (STerm.t MInt.t -> 'a) -> (STerm.t MInt.t -> 'a) -> 'a
val ifmarked3 :
  STerm.t MInt.t ->
  STerm.elt -> (STerm.t MInt.t -> 'a) -> (STerm.t MInt.t -> 'a) -> 'a
val ifmarked4 :
  STerm.t MInt.t ->
  STerm.elt -> (STerm.t MInt.t -> 'a) -> (STerm.t MInt.t -> 'a) -> 'a
val markvar : STerm.t MInt.t -> STerm.elt -> STerm.t MInt.t
val markvar1 : STerm.t MInt.t -> STerm.elt -> STerm.t MInt.t
val markvar2 : STerm.t MInt.t -> STerm.elt -> STerm.t MInt.t
val markvar3 : STerm.t MInt.t -> STerm.elt -> STerm.t MInt.t
val markvar4 : STerm.t MInt.t -> STerm.elt -> STerm.t MInt.t
val append : Ast.term -> Ast.term -> Ast.term
val simplify_clause : Ast.term -> Ast.term
val mpz_sub : Ast.term -> Ast.term -> Ast.term
val bv_constants_are_disequal : Ast.term -> Ast.term -> Ast.term
val bblt_len : Ast.term -> Ast.term
val bblast_const : Ast.term -> Ast.term -> Ast.term
val bblast_var : Ast.term -> Ast.term -> Ast.term
val bblast_concat : Ast.term -> Ast.term -> Ast.term
val bblast_extract_rec :
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_extract : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val extend_rec : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_zextend : Ast.term -> Ast.term -> Ast.term
val bblast_sextend : Ast.term -> Ast.term -> Ast.term
val bblast_bvand : Ast.term -> Ast.term -> Ast.term
val bblast_bvnot : Ast.term -> Ast.term
val bblast_bvor : Ast.term -> Ast.term -> Ast.term
val bblast_bvxor : Ast.term -> Ast.term -> Ast.term
val bblast_bvadd_carry : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_bvadd : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_zero : Ast.term -> Ast.term
val bblast_bvneg : Ast.term -> Ast.term -> Ast.term
val reverse_help : Ast.term -> Ast.term -> Ast.term
val reverseb : Ast.term -> Ast.term
val top_k_bits : Ast.term -> Ast.term -> Ast.term
val bottom_k_bits : Ast.term -> Ast.term -> Ast.term
val k_bit : Ast.term -> Ast.term -> Ast.term
val and_with_bit : Ast.term -> Ast.term -> Ast.term
val mult_step_k_h :
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val mult_step :
  Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_bvmul : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_eq_rec : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_eq : Ast.term -> Ast.term -> Ast.term
val bblast_bvult : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bblast_bvslt : Ast.term -> Ast.term -> Ast.term -> Ast.term
val mk_ones : Ast.term -> Ast.term
val mk_zero : Ast.term -> Ast.term

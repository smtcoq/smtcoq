(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


module H :
sig
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


val mp_mul_s : Ast.term
val eval_arg : Ast.term -> Ast.term
val uminus : Ast.term
val ok : Ast.term
val p_app : Ast.term -> Ast.term
val eq : Ast.term -> Ast.term -> Ast.term -> Ast.term
val pos : Ast.term -> Ast.term
val neg : Ast.term -> Ast.term
val clr : Ast.term -> Ast.term -> Ast.term
val concat_cl : Ast.term -> Ast.term -> Ast.term
val ttrue : Ast.term
val tfalse : Ast.term
val not_ : Ast.term -> Ast.term
val and_ : Ast.term -> Ast.term -> Ast.term
val or_ : Ast.term -> Ast.term -> Ast.term
val xor_ : Ast.term -> Ast.term -> Ast.term
val impl_ : Ast.term -> Ast.term -> Ast.term
val iff_ : Ast.term -> Ast.term -> Ast.term
val ifte_ : Ast.term -> Ast.term -> Ast.term -> Ast.term
val a_var_bv : Ast.term -> Ast.term -> Ast.term
val a_bv : Ast.term -> Ast.term -> Ast.term
val bblast_term : Ast.term -> Ast.term -> Ast.term -> Ast.term
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
val bvnot : Ast.term -> Ast.term -> Ast.term
val bvneg : Ast.term -> Ast.term -> Ast.term
val bvult : Ast.term -> Ast.term -> Ast.term -> Ast.term
val bvslt : Ast.term -> Ast.term -> Ast.term -> Ast.term
val concat : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val extract : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val zero_extend : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val sign_extend : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val apply_read : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val apply_write : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val apply_diff : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val refl : Ast.term -> Ast.term -> Ast.term
val cong : Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term -> Ast.term
val bottom_k_bits : Ast.term -> Ast.term -> Ast.term
val mk_ones : Ast.term -> Ast.term
val mk_zero : Ast.term -> Ast.term
val array : Ast.term -> Ast.term -> Ast.term


module MInt :
sig
  type 'a t
end


module STerm :
sig
  type t
  type elt
end


type mark_map = STerm.t MInt.t

val ifmarked1 : mark_map -> STerm.elt -> (mark_map -> 'a) -> (mark_map -> 'a) -> 'a
val markvar1 : mark_map -> STerm.elt -> mark_map

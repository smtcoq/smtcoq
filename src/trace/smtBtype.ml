open SmtMisc
open CoqTerms

(** Syntaxified version of Coq type *)

type indexed_type = Term.constr gen_hashed

let dummy_indexed_type i = {index = i; hval = Term.mkProp}
let indexed_type_index i = i.index
let indexed_type_hval i = i.hval

type btype =
  | TZ
  | Tbool
  | Tpositive
  | Tindex of indexed_type

let index_tbl = Hashtbl.create 17

let index_to_coq i =
  try Hashtbl.find index_tbl i
  with Not_found ->
    let interp = mklApp cTindex [|mkInt i|] in
    Hashtbl.add index_tbl i interp;
    interp

let indexed_type_of_int i =
  {index = i; hval = index_to_coq i }
      
let equal t1 t2 =
  match t1,t2 with
  | Tindex i, Tindex j -> i.index == j.index
  | _ -> t1 == t2

let to_coq = function
  | TZ -> Lazy.force cTZ
  | Tbool -> Lazy.force cTbool
  | Tpositive -> Lazy.force cTpositive
  | Tindex i -> index_to_coq i.index

let to_string = function
  | TZ -> "Int"
  | Tbool -> "Bool"
  | Tpositive -> "Int"
  | Tindex i -> "Tindex_" ^ string_of_int i.index

let to_smt fmt b = Format.fprintf fmt "%s" (to_string b)

(* reify table *)
type reify_tbl =
  { mutable count : int;
    tbl : (Term.constr, btype) Hashtbl.t;
    mutable cuts : (Structures.names_id_t * Term.types) list
  }

let create () =
  let htbl = Hashtbl.create 17 in
  Hashtbl.add htbl (Lazy.force cZ) TZ;
  Hashtbl.add htbl (Lazy.force cbool) Tbool;
  (* Hashtbl.add htbl (Lazy.force cpositive) Tpositive; *)
  { count = 0;
    tbl = htbl;
    cuts = [] }

let get_cuts reify = reify.cuts

let declare reify t typ_eqb =
  (* TODO: allows to have only typ_eqb *)
  assert (not (Hashtbl.mem reify.tbl t));
  let res = Tindex {index = reify.count; hval = typ_eqb} in
  Hashtbl.add reify.tbl t res;
  reify.count <- reify.count + 1;
  res

let of_coq reify t =
  try
    Hashtbl.find reify.tbl t
  with | Not_found ->
          let n = string_of_int (List.length reify.cuts) in
          let eq_name = Names.id_of_string ("eq"^n) in
          let eq_var = Term.mkVar eq_name in

          let eq_ty = Term.mkArrow t (Term.mkArrow t (Lazy.force cbool)) in

          let eq = mkName "eq" in
          let x = mkName "x" in
          let y = mkName "y" in
          let req = Term.mkRel 3 in
          let rx = Term.mkRel 2 in
          let ry = Term.mkRel 1 in
          let refl_ty = Term.mkLambda (eq, eq_ty, Term.mkProd (x,t,Term.mkProd (y,t,mklApp creflect [|mklApp ceq [|t;rx;ry|]; Term.mkApp (req, [|rx;ry|])|]))) in

          let pair_ty = mklApp csigT [|eq_ty; refl_ty|] in

          reify.cuts <- (eq_name, pair_ty)::reify.cuts;
          let ce = mklApp ctyp_eqb_of_typ_eqb_param [|t; eq_var|] in
          declare reify t ce

let interp_tbl reify =
  let t = Array.make (reify.count + 1) (Lazy.force cunit_typ_eqb) in
  let set _ = function
    | Tindex it -> t.(it.index) <- it.hval
    | _ -> () in
  Hashtbl.iter set reify.tbl;
  Structures.mkArray (Lazy.force ctyp_eqb, t)

let to_list reify =
  let set _ t acc = match t with
    | Tindex it -> (it.index,it)::acc
    | _ -> acc in
  Hashtbl.fold set reify.tbl []

let interp_to_coq reify = function
  | TZ -> Lazy.force cZ
  | Tbool -> Lazy.force cbool
  | Tpositive -> Lazy.force cpositive
  | Tindex c -> mklApp cte_carrier [|c.hval|]

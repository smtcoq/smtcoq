open Format

type mpz = Big_int.big_int
type mpq = Num.num
             

type symbol_name = Name of string | S_Hole
type symbol = { name : symbol_name; s_ty : term }

and pterm =
  | Type
  | Kind
  | Mpz
  | Mpq
  | App of symbol * term list
  | Int of mpz
  | Rat of mpq
  | Pi of symbol * term
  | Lambda of symbol * term
  | Hole

and term = { value: pterm; ty: term }


type command =
  | Check of term
  | Define of string * term
  | Declare of string * term


type proof = command list


let symbols = Hashtbl.create 21

exception TypingError of term * term

let rec kind = { value = Kind; ty = kind }

let lfsc_type = { value = Type; ty = kind }

let mpz = { value = Mpz; ty = lfsc_type }

let mpq = { value = Mpq; ty = lfsc_type }

let mk_mpz n = { value = Int n; ty = mpz }

let mk_mpq n = { value = Rat n; ty = mpq }


let mk_symbol n s_ty = { name = Name n; s_ty }

let mk_symbol_hole s_ty = { name = S_Hole; s_ty }


let fresh_alpha =
  let cpt = ref 0 in
  fun ty -> incr cpt;
    mk_symbol ("'a"^string_of_int !cpt) ty

let rec rename s s' t =
  if t.value = Kind then t else
  let ty = rename s s' t.ty in
  let t = if t.ty == ty then t else {t with ty} in
  match t.value with
  | Type | Kind | Mpz | Mpq | Int _ | Rat _ | Hole -> t
    
  | App (x, args) ->
    let nargs = List.map (rename s s') args in
    if x.name = s.name then {t with value = App(s', nargs)}
    else if nargs == args then t
    else {t with value = App(x, nargs)}
      
  | Pi (x, ty) ->
    if x.name = s.name then t
    else
      let nty = rename s s' ty in
      if nty == ty then t
      else {t with value = Pi (x, nty)}
      
  | Lambda (x, ty) ->
    if x.name = s.name then t
    else
      let nty = rename s s' ty in
      if nty == ty then t
      else {t with value = Lambda (x, nty)}


let rec equal t1 t2 = match t1.value, t2.value with
  | Type, Type  
  | Kind, Kind
  | Mpz, Mpz
  | Mpq, Mpz
  | Hole, Hole -> true
  | Int z1, Int z2 -> Big_int.eq_big_int z1 z2
  | Rat q1, Rat q2 -> Num.eq_num q1 q2
    
  | App (s1, args1), App (s2, args2) ->
    s1.name = s2.name &&
    List.for_all2 equal args1 args2
      
  | Pi (s1, t1), Pi (s2, t2) ->
    let a = fresh_alpha s1.s_ty in
    equal (rename s1 a t1) (rename s2 a t2)

  | Lambda (s1, t1), Lambda (s2, t2) ->
    let a = fresh_alpha s1.s_ty in
    equal (rename s1 a t1) (rename s2 a t2)

  | _ -> false
  

let unify ty1 ty2 =
  if not (equal ty1 ty2) then raise (TypingError (ty1, ty2))


let rec ty_of_app ty args = match ty.value, args with
  | Pi (s, t), a :: rargs ->
    (* eprintf "tyapp1@."; *)
    unify s.s_ty a.ty;
    (* eprintf "tyapp2@."; *)
    ty_of_app t rargs
  | _, [] -> ty
  | _ -> raise (TypingError (ty, ty)) (* KLUDGE *)


let mk_app x args =
  (* eprintf "@.mk_App : %s ...@.@." x; *)
  let s_ty = Hashtbl.find symbols (Name x) in
  let s = mk_symbol x s_ty in
  { value = App (s, args); ty = ty_of_app s.s_ty args }

let mk_hole ty = { value = Hole; ty }

let mk_hole_hole () = { value = Hole; ty = mk_hole lfsc_type }


let mk_pi s t =
  Hashtbl.add symbols s.name s.s_ty;
  let x = { value = Pi (s, t); ty = lfsc_type } in
  Hashtbl.remove symbols s.name;
  x


let mk_lambda s t =
  Hashtbl.add symbols s.name s.s_ty;
  let x = { value = Lambda (s, t);
            ty = mk_pi (mk_symbol_hole s.s_ty) t.ty } in
  Hashtbl.remove symbols s.name;
  x


let mk_ascr ty t =
  eprintf "mkascr@.";
  unify ty t.ty;
  eprintf "mkascrend@.";
  { t with ty }


let rec print_symbol fmt { name } = match name with
  | Name n -> pp_print_string fmt n
  | S_Hole -> pp_print_string fmt "_"

and print_term fmt { value } = match value with
  | Type -> fprintf fmt "type"
  | Kind -> fprintf fmt "kind"
  | Mpz -> fprintf fmt "mpz"
  | Mpq -> fprintf fmt "mpz"
  | App (s, []) -> print_symbol fmt s
  | App (s, args) ->
    fprintf fmt "(%a%a)"
      print_symbol s
      (fun fmt -> List.iter (fprintf fmt "@ %a" print_term)) args
  | Int n -> pp_print_string fmt (Big_int.string_of_big_int n)
  | Rat q -> pp_print_string fmt (Num.string_of_num q)
  | Pi (s, t) ->
    fprintf fmt "(! %a@ %a@ %a)"
      print_symbol s
      print_term s.s_ty
      print_term t
  | Lambda (s, t) ->
    fprintf fmt "(\\ %a@ %a)" print_symbol s print_term t
  | Hole ->  pp_print_string fmt "_"


let print_command fmt = function
  | Check t ->
    fprintf fmt "(check@ %a)" print_term t
  | Define (s, t) ->
    fprintf fmt "(define %s@ %a)" s print_term t
  | Declare (s, t) ->
    fprintf fmt "(declare %s@ %a)" s print_term t

let print_proof fmt =
  List.iter (fprintf fmt "@[<hov 1>%a@]@\n@." print_command) 


let register_symbol s =
  Hashtbl.add symbols s.name s.s_ty

let remove_symbol s =
  Hashtbl.remove symbols s.name

let sort =
  let s = mk_symbol "sort" lfsc_type in
  register_symbol s;
  mk_app "sort" []

let term x =
  let t = mk_symbol "t" sort in
  let s = mk_symbol "term" (mk_pi t lfsc_type) in
  register_symbol s;
  mk_app "term" [x]


(* (declare arrow (! s1 sort (! s2 sort sort)))	 *)

let arrow x y =
  let s1 = mk_symbol "s1" sort in
  let s2 = mk_symbol "s1" sort in
  let s = mk_symbol "arrow" (mk_pi s1 (mk_pi s2 sort)) in
  register_symbol s;
  mk_app "arrow" [x; y]



let mk_declare n ty =
  let s = mk_symbol n ty in
  register_symbol s


let mk_check t = ()


let mk_command = function
  | Check t -> mk_check t
  | Declare (n, ty) -> mk_declare n ty
  | _ -> assert false

let mk_proof = List.iter mk_command


(* TODO:
   - defines
   - type inferrence
   - fill holes (mutable fields)
   - side conditions
*)

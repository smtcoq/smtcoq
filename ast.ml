open Format

type mpz = Big_int.big_int
type mpq = Num.num             

type name = Name of string | S_Hole
type symbol = { sname : name; stype : term }

and dterm =
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

and term = { tname: dterm; ttype: term }


type command =
  | Check of term
  | Define of string * term
  | Declare of string * term


type proof = command list


let symbols = Hashtbl.create 21

exception TypingError of term * term

let rec kind = { tname = Kind; ttype = kind }

let lfsc_type = { tname = Type; ttype = kind }

let mpz = { tname = Mpz; ttype = lfsc_type }

let mpq = { tname = Mpq; ttype = lfsc_type }

let mk_mpz n = { tname = Int n; ttype = mpz }

let mk_mpq n = { tname = Rat n; ttype = mpq }


let mk_symbol n strm = { sname = Name n; stype = strm }

let mk_symbol_hole strm = { sname = S_Hole; stype = strm }


let fresh_alpha =
  let cpt = ref 0 in
  fun ty -> incr cpt;
    mk_symbol ("'a"^string_of_int !cpt) ty

let rec rename s s' t =
  if t.tname = Kind then t else
  let ttype = rename s s' t.ttype in
  let t = if t.ttype == ttype then t else {t with ttype} in
  match t.tname with
  | Type | Kind | Mpz | Mpq | Int _ | Rat _ | Hole -> t
    
  | App (x, args) ->
    let nargs = List.map (rename s s') args in
    if x.sname = s.sname then {t with tname = App(s', nargs)}
    else if nargs == args then t
    else {t with tname = App(x, nargs)}
      
  | Pi (x, ty) ->
    if x.sname = s.sname then t
    else
      let nty = rename s s' ty in
      if nty == ty then t
      else {t with tname = Pi (x, nty)}
      
  | Lambda (x, ty) ->
    if x.sname = s.sname then t
    else
      let nty = rename s s' ty in
      if nty == ty then t
      else {t with tname = Lambda (x, nty)}


let rec equal t1 t2 = match t1.tname, t2.tname with
  | Type, Type  
  | Kind, Kind
  | Mpz, Mpz
  | Mpq, Mpq
  | Hole, Hole -> true
  | Int z1, Int z2 -> Big_int.eq_big_int z1 z2
  | Rat q1, Rat q2 -> Num.eq_num q1 q2
    
  | App (s1, args1), App (s2, args2) ->
    s1.sname = s2.sname &&
    List.for_all2 equal args1 args2
      
  | Pi (s1, t1), Pi (s2, t2) ->
    let a = fresh_alpha s1.stype in
    equal (rename s1 a t1) (rename s2 a t2)

  | Lambda (s1, t1), Lambda (s2, t2) ->
    let a = fresh_alpha s1.stype in
    equal (rename s1 a t1) (rename s2 a t2)

  | _ -> false
  

let unify ty1 ty2 =
  if not (equal ty1 ty2) then raise (TypingError (ty1, ty2))


let rec ty_of_app ty args = match ty.tname, args with
  | Pi (s, t), a :: rargs ->
    (* eprintf "tyapp1@."; *)
    unify s.stype a.ttype;
    (* eprintf "tyapp2@."; *)
    ty_of_app t rargs
  | _, [] -> ty
  | _ -> raise (TypingError (ty, ty)) (* KLUDGE *)


let mk_app x args =
  (* eprintf "@.mk_App : %s ...@.@." x; *)
  let sy_ty = Hashtbl.find symbols (Name x) in
  let s = mk_symbol x sy_ty in
  { tname = App (s, args); ttype = ty_of_app s.stype args }

(* let mk_hole ty = { tname = Hole; ty } *)

let mk_hole_hole () = { tname = Hole; ttype = lfsc_type }


let mk_pi s t =
  Hashtbl.add symbols s.sname s.stype;
  let x = { tname = Pi (s, t); ttype = lfsc_type } in
  Hashtbl.remove symbols s.sname;
  x


let mk_lambda s t =
  Hashtbl.add symbols s.sname s.stype;
  let x = { tname = Lambda (s, t);
            ttype = mk_pi (mk_symbol_hole s.stype) t.ttype } in
  Hashtbl.remove symbols s.sname;
  x


let mk_ascr ttype t =
  eprintf "mkascr@.";
  unify ttype t.ttype;
  eprintf "mkascrend@.";
  { t with ttype }


let rec print_symbol fmt { sname } = match sname with
  | Name n -> pp_print_string fmt n
  | S_Hole -> pp_print_string fmt "_"

and print_term fmt { tname } = match tname with
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
      print_term s.stype
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
  Hashtbl.add symbols s.sname s.stype

let remove_symbol s =
  Hashtbl.remove symbols s.sname

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

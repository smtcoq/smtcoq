open Format

(********************************)
(* Type definitions for the AST *)
(********************************)

type mpz = Big_int.big_int
type mpq = Num.num
             

type symbol_name = Name of string | S_Hole of int
type symbol = { name : symbol_name; s_ty : term }

and pterm =
  | Type
  | Kind
  | Mpz
  | Mpq
  | Const of symbol
  | App of term * term list
  | Int of mpz
  | Rat of mpq
  | Pi of symbol * term
  | Lambda of symbol * term
  | Hole of int

and term = { mutable value: pterm; ty: term }


type command =
  | Check of term
  | Define of string * term
  | Declare of string * term


type proof = command list


(*******************)
(* Pretty printing *)
(*******************)

let rec print_symbol fmt { name } = match name with
  | Name n -> pp_print_string fmt n
  | S_Hole i -> fprintf fmt "_s%d" i

and print_tval pty fmt { value } = match value with
  | Type -> fprintf fmt "type"
  | Kind -> fprintf fmt "kind"
  | Mpz -> fprintf fmt "mpz"
  | Mpq -> fprintf fmt "mpz"
  | Const s -> print_symbol fmt s
  | App (f, args) ->
    fprintf fmt "(%a%a)"
      (print_tval false) f
      (fun fmt -> List.iter (fprintf fmt "@ %a" (print_term pty))) args
  | Int n -> pp_print_string fmt (Big_int.string_of_big_int n)
  | Rat q -> pp_print_string fmt (Num.string_of_num q)
  | Pi (s, t) ->
    fprintf fmt "(! %a@ %a@ %a)"
      print_symbol s
      (print_term false) s.s_ty
      (print_term pty) t
  | Lambda (s, t) ->
    fprintf fmt "(\\ %a@ %a)" print_symbol s (print_term pty) t
  | Hole i -> fprintf fmt "_%d" i


and print_term pty fmt t = match t with
  | {value = Type | Kind}
  | {ty = {value = Type | Kind} } ->
    print_tval pty fmt t
  | _  when t.ty == t ->
    print_tval pty fmt t
  | _ when pty ->
    fprintf fmt "[@[%a:%a@]]" (print_tval pty) t (print_term pty) t.ty
  | _ ->
    fprintf fmt "@[%a@]" (print_tval pty) t


let print_term_type = print_term true
let print_term = print_term false

let print_command fmt = function
  | Check t ->
    fprintf fmt "(check@ (: %a@ %a))" print_term t.ty print_term t
  | Define (s, t) ->
    fprintf fmt ";; (define %s@ %a)" s print_term t
  | Declare (s, t) ->
    fprintf fmt "(declare %s@ %a)" s print_term t

let print_proof fmt =
  List.iter (fprintf fmt "@[<hov 1>%a@]@\n@." print_command) 




let symbols = Hashtbl.create 21
let definitions = Hashtbl.create 21

let add_definition s t =
  Hashtbl.add definitions s t


exception TypingError of term * term


(**************************)
(* Predefined terms/types *)
(**************************)


let rec kind = { value = Kind; ty = kind }

let lfsc_type = { value = Type; ty = kind }

let mpz = { value = Mpz; ty = lfsc_type }

let mpq = { value = Mpq; ty = lfsc_type }

let mk_mpz n = { value = Int n; ty = mpz }

let mk_mpq n = { value = Rat n; ty = mpq }


let mk_symbol n s_ty = { name = Name n; s_ty }

let mk_symbol_hole =
  let cpt = ref 0 in
  fun s_ty ->
    { name = S_Hole !cpt; s_ty }

let is_hole = function { value = Hole _ } -> true | _ -> false

let is_hole_symbol = function { name = S_Hole _ } -> true | _ -> false

let mk_hole =
  let cpt = ref 0 in
  fun ty ->
    incr cpt;
    { value = Hole !cpt; ty }

(* let mk_rec_hole () = *)
(*   let rec h = { value = Hole !cpt; ty = h } in *)
(*   h *)

let mk_hole_hole () =
  mk_hole (mk_hole lfsc_type)


(**********************************)
(* Smart constructors for the AST *)
(**********************************)

let fresh_alpha =
  let cpt = ref 0 in
  fun ty -> incr cpt;
    mk_symbol ("'a"^string_of_int !cpt) ty

let rec rename s s' t =
  if t.value = Kind then t else
  let ty = rename s s' t.ty in
  let t = if t.ty == ty then t else {t with ty} in
  match t.value with
  | Type | Kind | Mpz | Mpq | Int _ | Rat _ | Hole _ -> t
    
  | Const x ->
    if x.name = s.name then {t with value = Const s'}
    else t

  | App (x, args) ->
    let nx = rename s s' x in
    let nargs = List.map (rename s s') args in
    if nx == x && nargs == args then t
    else {t with value = App(nx, nargs)}
      
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



let get_t ?(gen=true) sigma s =
  try
    let x = List.assoc s sigma in
    if not gen && is_hole x then raise Not_found;
    x
  with Not_found -> try
      Hashtbl.find definitions s
    with Not_found ->
      { value = Const s; ty = s.s_ty }


let print_subst fmt sigma =
  fprintf fmt "@[<v 1>[";
  List.iter (fun (s, t) ->
      fprintf fmt "@ %a -> %a;" print_symbol s print_term t) sigma;
  fprintf fmt " ]@]"


let rec apply_subst sigma t = match t.value with
  | Type | Kind |  Mpz | Mpq | Int _ | Rat _ | Hole _ -> t
  | Const s -> get_t sigma s
  | App (f, args) ->
    { t with value = App(apply_subst sigma f,
                         List.map (apply_subst sigma) args) }
  | Pi (s, x) ->
    { t with value = Pi (s, apply_subst sigma x) }

  | Lambda (s, x) ->
    { t with value = Lambda (s, apply_subst sigma x) }
    

let rec fill_hole sigma h t =
  match h.value with
  | Hole _ ->
    eprintf ">>>>> Fill hole @[%a@] with @[%a@]@."
      print_term_type h print_term_type t;
    let t' = (* apply_subst sigma *) t in
    h.value <- t'.value;
    eprintf ">>>>>>>>> @[%a@]@." print_term_type h;
    (* fill_hole sigma h.ty t'.ty; *)
    (try compat_with sigma t'.ty h.ty with _ -> ());
  | _ -> ()


(* Raise TypingError if t2 is not compatible with t1 *)
(* apsub is false if we want to prevent application of substitutions *)
and compat_with ?(apsub=true) sigma t1 t2 =
  eprintf "compat_with(%b): @[<hov>%a@] and @[<hov>%a@]@."
    apsub print_term t1 print_term t2;
  eprintf "  with sigma = %a@." print_subst sigma;
  try
    match t1.value, t2.value with
    | Type, Type  
    | Kind, Kind
    | Mpz, Mpz
    | Mpq, Mpz -> ()

    | Int z1, Int z2 -> if not (Big_int.eq_big_int z1 z2) then raise Exit
    | Rat q1, Rat q2 -> if not (Num.eq_num q1 q2) then raise Exit

    | Const s1, Const s2 ->
      if apsub then
        let a2 = get_t sigma s2 in
        let a1 = get_t ~gen:(not (is_hole a2)) sigma s1 in
        compat_with sigma ~apsub:false a1 a2
      else
        if s1.name <> s2.name then raise Exit

    | App (f1, args1), App (f2, args2) ->
      compat_with sigma f1 f2;
      List.iter2 (compat_with sigma) args1 args2

    | Pi (s1, t1), Pi (s2, t2) ->
      let a = fresh_alpha s1.s_ty in
      compat_with sigma (rename s1 a t1) (rename s2 a t2)

    | Lambda (s1, t1), Lambda (s2, t2) ->
      let a = fresh_alpha s1.s_ty in
      compat_with sigma (rename s1 a t1) (rename s2 a t2)

    | Hole _, Hole _ ->
      failwith ("Cannot infer type of holes, too many holes.")

    | Hole _, _ -> fill_hole sigma t1 t2
    | _, Hole _ -> fill_hole sigma t2 t1


    | Const s, _ ->
      if apsub then
        let a = get_t sigma s in
        compat_with sigma ~apsub:false a t2
      else
        raise Exit

    | _, Const s ->
      if apsub then
        let a = get_t sigma s in
        compat_with sigma ~apsub:false a t1
      else
        raise Exit

    | _ -> raise Exit

  with Exit ->
    raise (TypingError (apply_subst sigma t1, apply_subst sigma t2))




let empty_subst = []


let rec ty_of_app sigma ty args = match ty.value, args with
  | Pi (s, t), a :: rargs ->
    let sigma = (s, a) :: sigma in
    compat_with sigma s.s_ty a.ty;
    ty_of_app sigma t rargs
  | _, [] -> apply_subst sigma ty
  | _ -> failwith ("Type of function not a pi-type.")


let mk_const x =
  let s_ty = Hashtbl.find symbols (Name x) in
  let s = mk_symbol x s_ty in
  { value = Const s; ty = s_ty }
  

let rec mk_app ?(lookup=true) sigma f args =
  (* eprintf "mk_App : %a@." (print_tval true) *)
  (*   { value = App (f, args); ty = lfsc_type } *)
  (* ; *)
  (* find the definition if it has one *)
  match f.value, args with
  | Lambda (x, r), a :: rargs ->
    (* eprintf "LAMBDA@."; *)
    mk_app ((x, a) :: sigma) r rargs
      
  | Const s, _ when lookup ->
    (* eprintf "CONST@."; *)
    let f = get_t sigma s in
    (* eprintf "........... found %a ----> %a@." print_symbol s print_term f; *)
    mk_app ~lookup:false sigma f args

  | x, [] ->

    (* Delayed beta-reduction *)
    let r = apply_subst sigma f in
    let r = { r with ty = apply_subst sigma f.ty } in
    (* eprintf "BETA ::: %a@.@." print_term_type r; *)
    r
      
  | _ ->
    (* eprintf "APP normal@."; *)
    (* TODO: check if empty_subst or sigma *)
    { value = App (f, args); ty = ty_of_app empty_subst f.ty args }

let mk_app = mk_app empty_subst


let mk_pi s t =
  let s = if is_hole_symbol s then fresh_alpha s.s_ty else s in
  { value = Pi (s, t); ty = lfsc_type }

let mk_lambda s t =
  let s = if is_hole_symbol s then fresh_alpha s.s_ty else s in
  { value = Lambda (s, t);
    ty = mk_pi (mk_symbol_hole s.s_ty) t.ty }

  
let mk_ascr ty t =
  compat_with empty_subst ty t.ty;
  { t with ty }


let register_symbol s =
  Hashtbl.add symbols s.name s.s_ty

let remove_symbol s =
  Hashtbl.remove symbols s.name


let mk_declare n ty =
  (* eprintf "@.declare : %s @.@." n; *)
  let s = mk_symbol n ty in
  register_symbol s

let mk_define n t =
  (* eprintf "@.declare : %s @.@." n; *)
  let s = mk_symbol n t.ty in
  register_symbol s;
  add_definition s t


let mk_check t =
  (* eprintf "@.check : %a @.@." print_term t; *)
  ()


let mk_command = function
  | Check t ->
    mk_check t
  | Declare (n, ty) ->
    mk_declare n ty
  | _ -> assert false

let mk_proof = List.iter mk_command


(* TODO:
   - side conditions
   - lazy alpha renaming
*)



(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

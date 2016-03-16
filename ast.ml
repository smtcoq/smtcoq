open Format

let debug = false

(********************************)
(* Type definitions for the AST *)
(********************************)

type mpz = Big_int.big_int
type mpq = Num.num
             

type name = Name of string | S_Hole of int
type symbol = { sname : name; stype : term }

and dterm =
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

and term = { mutable value: dterm; ttype: term }


type command =
  | Check of term
  | Define of string * term
  | Declare of string * term


type proof = command list


(*******************)
(* Pretty printing *)
(*******************)

let address_of (x:'a) : nativeint =
  if Obj.is_block (Obj.repr x) then
    Nativeint.shift_left (Nativeint.of_int (Obj.magic x)) 1 (* magic *)
  else
    invalid_arg "Can only find address of boxed values.";;
 
let rec print_symbol fmt { sname } = match sname with
  | Name n -> pp_print_string fmt n
  | S_Hole i -> fprintf fmt "_s%d" i

and print_tval pty fmt t = match t.value with
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
      (print_term false) s.stype
      (print_term pty) t
  | Lambda (s, t) ->
    fprintf fmt "(%% %a@ %a@ %a)" print_symbol s (print_term pty) s.stype
      (print_term pty) t
  | Hole i ->
    if debug then
      fprintf fmt "_%d[%nd]" i (address_of t)
    else 
      fprintf fmt "_%d" i


and print_term pty fmt t = match t with
  | {value = Type | Kind}
  | {ttype = {value = Type | Kind} } ->
    print_tval pty fmt t
  | _  when t.ttype == t ->
    print_tval pty fmt t
  | _ when pty ->
    fprintf fmt "[@[%a:%a@]]" (print_tval pty) t (print_term pty) t.ttype
  | _ ->
    fprintf fmt "@[%a@]" (print_tval pty) t


let print_term_type = print_term true
let print_term = print_term false

let print_command fmt = function
  | Check t ->
    fprintf fmt "(check@ (: %a@ %a))" print_term t.ttype print_term t
  | Define (s, t) ->
    fprintf fmt "(define %s@ %a)" s print_term t
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


let rec kind = { value = Kind; ttype = kind }

let lfsc_type = { value = Type; ttype = kind }

let mpz = { value = Mpz; ttype = lfsc_type }

let mpq = { value = Mpq; ttype = lfsc_type }

let mk_mpz n = { value = Int n; ttype = mpz }

let mk_mpq n = { value = Rat n; ttype = mpq }


let mk_symbol n stype =
  { sname = Name n ; stype }
  (* { sname = Name (String.concat "." (List.rev (n :: scope))) ; stype } *)

let mk_symbol_hole =
  let cpt = ref 0 in
  fun stype ->
    incr cpt;
    { sname = S_Hole !cpt; stype }

let is_hole = function { value = Hole _ } -> true | _ -> false

let is_hole_symbol = function { sname = S_Hole _ } -> true | _ -> false

let mk_hole =
  let cpt = ref 0 in
  fun ttype ->
    incr cpt;
    { value = Hole !cpt; ttype }

(* let mk_rec_hole () = *)
(*   let rec h = { value = Hole !cpt; ttype = h } in *)
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



let get_t ?(gen=true) sigma s =
  try
    let x = List.assoc s sigma in
    if not gen && is_hole x then raise Not_found;
    x
  with Not_found -> try
      Hashtbl.find definitions s
    with Not_found ->
      { value = Const s; ttype = s.stype }


let print_subst fmt sigma =
  fprintf fmt "@[<v 1>[";
  List.iter (fun (s, t) ->
      fprintf fmt "@ %a -> %a;" print_symbol s print_term t) sigma;
  fprintf fmt " ]@]"


type substres = T of term | V of dterm

let rec apply_subst_val sigma tval = match tval with
  | Type | Kind |  Mpz | Mpq | Int _ | Rat _ | Hole _ -> raise Exit
  | Const s when is_hole_symbol s -> raise Exit
  | Const s -> T (get_t sigma s)
  | App (f, args) ->
    let nf = apply_subst sigma f in
    let nargs = List.map (apply_subst sigma) args in
    if nf == f && List.for_all2 (==) nargs args then V tval
    else V (App(nf, nargs))
      
  | Pi (s, x) ->
    let s = { s with stype = apply_subst sigma s.stype } in
    let sigma = List.remove_assoc s sigma in
    let newx = apply_subst sigma x in
    if x == newx then V tval
    else V (Pi (s, newx))

  | Lambda (s, x) ->
    let s = { s with stype = apply_subst sigma s.stype } in
    let sigma = List.remove_assoc s sigma in
    let newx = apply_subst sigma x in
    if x == newx then V tval
    else V (Lambda (s, newx))


and apply_subst sigma t =
  try
    match apply_subst_val sigma t.value with
    | T t -> t
    | V value ->
      let ttype = apply_subst sigma t.ttype in
      if value == t.value && ttype == t.ttype then t
      else { value; ttype }
  with Exit -> t


let rec fill_hole sigma h t =
  match h.value with
  | Hole _ ->
    if debug then
      eprintf ">>>>> Fill hole @[%a@] with @[%a@]@."
        print_term_type h print_term_type t;
    let t' = apply_subst sigma t in
    h.value <- t'.value;
    if debug then
      eprintf ">>>>>>>>> @[%a@]@." print_term_type h;
    fill_hole sigma h.ttype t'.ttype;
    (* (try compat_with sigma t'.ttype h.ttype with _ -> ()); *)
  | _ -> ()


(* Raise TypingError if t2 is not compatible with t1 *)
(* apsub is false if we want to prevent application of substitutions *)
and compat_with ?(apsub=true) sigma t1 t2 =
  if debug then (
    eprintf "compat_with(%b): @[<hov>%a@] and @[<hov>%a@]@."
      apsub print_term t1 print_term t2;
    eprintf "  with sigma = %a@." print_subst sigma
  );
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
        if s1.sname <> s2.sname then raise Exit

    | App (f1, args1), App (f2, args2) ->
      compat_with sigma f1 f2;
      List.iter2 (compat_with sigma) args1 args2

    | Pi (s1, t1), Pi (s2, t2) ->
      compat_with sigma s1.stype s2.stype;
      let a = s2 in
      let ta = { value = Const a; ttype = a.stype } in
      compat_with ((s1, ta) :: sigma) t1 t2;

    | Lambda (s1, t1), Lambda (s2, t2) ->
      compat_with sigma s1.stype s2.stype;
      let a = s2 in
      let ta = { value = Const a; ttype = a.stype } in
      compat_with ((s1, ta) :: sigma) t1 t2;
        
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
    compat_with sigma s.stype a.ttype;
    ty_of_app sigma t rargs
  | _, [] -> apply_subst sigma ty
  | _ -> failwith ("Type of function not a pi-type.")


let mk_const x =
  if debug then eprintf "mk_const %s@." x;
  try
    let stype = Hashtbl.find symbols (Name x) in
    let s = mk_symbol x stype in
    try Hashtbl.find definitions s
    with Not_found -> { value = Const s; ttype = stype }
  with Not_found -> failwith ("Symbol " ^ x ^ " is not declared.")



let rec mk_app ?(lookup=true) sigma f args =
  if debug then
    eprintf "mk_App : %a@." (print_tval true)
      { value = App (f, args); ttype = lfsc_type } ;
  (* find the definition if it has one *)
  match f.value, args with
  | Lambda (x, r), a :: rargs ->
    let sigma = List.remove_assoc x sigma in
    mk_app ((x, a) :: sigma) r rargs
      
  | Const s, _ when lookup ->
    let f = get_t sigma s in
    mk_app ~lookup:false sigma f args

  | x, [] ->
    (* Delayed beta-reduction *)
    apply_subst sigma f
      
  | _ ->
    (* TODO: check if empty_subst or sigma *)
    { value = App (f, args); ttype = ty_of_app empty_subst f.ttype args }

let mk_app = mk_app empty_subst

let mk_pi s t =
  (* let s = if is_hole_symbol s then fresh_alpha s.stype else s in *)
  { value = Pi (s, t); ttype = lfsc_type }

let mk_lambda s t =
  (* let s = if is_hole_symbol s then fresh_alpha s.stype else s in *)
  { value = Lambda (s, t);
    ttype = mk_pi s t.ttype }

  
let mk_ascr ty t =
  compat_with empty_subst ty t.ttype; t
  (* { t with ttype = ty } *)


let register_symbol s =
  Hashtbl.add symbols s.sname s.stype

let remove_symbol s =
  Hashtbl.remove symbols s.sname


let mk_declare n ty =
  let s = mk_symbol n ty in
  register_symbol s

let mk_define n t =
  let s = mk_symbol n t.ttype in
  register_symbol s;
  add_definition s t

let mk_check t = ()


(* TODO:
   - side conditions
*)



(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

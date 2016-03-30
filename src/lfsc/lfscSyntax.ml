(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtAtom
open SmtForm
open SmtCertif
open SmtTrace


open Format

let debug =
  (* true *)
  false

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
  | Ptr of term
  | SideCond of string * term list * term * term

and term = { mutable value: dterm; ttype: term }


type command =
  | Check of term
  | Define of string * term
  | Declare of string * term


type proof = command list



let is_rule t =
  match t.ttype.value with
  | App ({value=Const{sname=Name ("holds"|"th_holds")}}, _) -> true
  | _ -> false


(*******************)
(* Pretty printing *)
(*******************)

let address_of (x:'a) : nativeint =
  if Obj.is_block (Obj.repr x) then
    Nativeint.shift_left (Nativeint.of_int (Obj.magic x)) 1 (* magic *)
  else
    invalid_arg "Can only find address of boxed values."
 
let rec print_symbol fmt { sname } = match sname with
  | Name n -> pp_print_string fmt n
  | S_Hole i -> fprintf fmt "_s%d" i

and print_tval pty fmt t = match t.value with
  | Type -> fprintf fmt "type"
  | Kind -> fprintf fmt "kind"
  | Mpz -> fprintf fmt "mpz"
  | Mpq -> fprintf fmt "mpz"
  | Const s -> print_symbol fmt s
  | App (f, args) when pty && is_rule t ->
    let color = (Hashtbl.hash f.value mod 216) + 16 in
    let op, cl = sprintf "\x1b[38;5;%dm" color, "\x1b[0m" in
    fprintf fmt "@[@<0>%s(%a@<0>%s%a@<0>%s)@,@<0>%s@]"
      op
      (print_tval false) f
      cl
      (fun fmt -> List.iter (fprintf fmt "@ %a" (print_term pty))) args
      op cl
  | App (f, args) ->
    fprintf fmt "@[(%a%a)@,@]"
      (print_tval false) f
      (fun fmt -> List.iter (fprintf fmt "@ %a" (print_term pty))) args

  | Int n -> pp_print_string fmt (Big_int.string_of_big_int n)
  | Rat q -> pp_print_string fmt (Num.string_of_num q)
  | Pi (s, t) ->
    fprintf fmt "(! %a@ %a@ %a)@,"
      print_symbol s
      (print_term false) s.stype
      (print_term pty) t
  | Lambda (s, t) ->
    fprintf fmt "(%% %a@ %a@ %a)@," print_symbol s (print_term pty) s.stype
      (print_term pty) t
  | Hole i ->
    if false && debug then
      fprintf fmt "_%d[%nx]" i (address_of t)
    else 
      fprintf fmt "_%d" i
        
  | Ptr t when (* true || *) debug -> fprintf fmt "*%a" (print_term pty) t

  | Ptr t -> print_term pty fmt t
    
  | SideCond (name, args, expected, t) ->
    fprintf fmt "(! _ (^ (%s%a)@ %a)@ %a)"
      name
      (fun fmt -> List.iter (fprintf fmt "@ %a" (print_term pty))) args
      (print_term pty) expected
      (print_term pty) t


and print_term pty fmt t = match t with
  | {value = Type | Kind | Ptr _ | Const _}
  | {ttype = {value = Type | Kind | Const _ | Ptr _}} ->
    print_tval pty fmt t
  | _  when t.ttype == t ->
    print_tval pty fmt t
  (* | _ when pty -> *)
  (*   fprintf fmt "[@[%a:%a@]]" (print_tval pty) t (print_term pty) t.ttype *)
  | _ when pty && is_rule t ->
    let op, cl = "\x1b[30m", "\x1b[0m" in
    fprintf fmt "@\n@[@<0>%s(: %a@<0>%s@\n%a@<0>%s)@<0>%s@,@]"
      op (print_term false) t.ttype cl (print_tval pty) t op cl
  (* | _ when pty -> *)
  (*   fprintf fmt "@[(:@ %a@ %a)@]" *)
  (*     (print_term false) t.ttype (print_tval pty) t *)
  (* | _ when pty -> *)
  (*   fprintf fmt "@[%a\x1b[30m:%a\x1b[0m)@]" *)
  (*     (print_tval pty) t (print_term false) t.ttype *)
  | _ ->
    fprintf fmt "@[%a@]" (print_tval pty) t


let print_term_type = print_term true
let print_term = print_term false

let print_command fmt = function
  | Check t ->
    fprintf fmt "(check@ (:@\n@\n %a@ @\n@\n%a))"
      print_term t.ttype print_term_type t
  | Define (s, t) ->
    fprintf fmt "(define %s@ %a)" s print_term t
  | Declare (s, t) ->
    fprintf fmt "(declare %s@ %a)" s print_term t

let print_proof fmt =
  List.iter (fprintf fmt "@[<1>%a@]@\n@." print_command) 



let compare_symbol s1 s2 = match s1.sname, s2.sname with
  | Name n1, Name n2 -> String.compare n1 n2
  | Name _, _ -> -1
  | _, Name _ -> 1
  | S_Hole i1, S_Hole i2 -> Pervasives.compare i1 i2


let rec compare_term t1 t2 = match t1.value, t2.value with
  | Type, Type | Kind, Kind | Mpz, Mpz | Mpq, Mpz -> 0
  | Type, _ -> -1 | _, Type -> 1
  | Kind, _ -> -1 | _, Kind -> 1
  | Mpz, _ -> -1 | _, Mpz -> 1
  | Mpq, _ -> -1 | _, Mpq -> 1
  | Int n1, Int n2 -> Big_int.compare_big_int n1 n2
  | Int _, _ -> -1 | _, Int _ -> 1
  | Rat q1, Rat q2 -> Num.compare_num q1 q2
  | Rat _, _ -> -1 | _, Rat _ -> 1
  | Const s1, Const s2 -> compare_symbol s1 s2
  | Const _, _ -> -1 | _, Const _ -> 1
  | App (f1, l1), App (f2, l2) ->
    compare_term_list (f1 :: l1) (f2 :: l2)
  | App _, _ -> -1 | _, App _ -> 1
    
  | Pi (s1, t1), Pi (s2, t2) ->
    let c = compare_symbol s1 s2 in
    if c <> 0 then c
    else compare_term t1 t2
  | Pi _, _ -> -1 | _, Pi _ -> 1

  | Lambda (s1, t1), Lambda (s2, t2) ->
    let c = compare_symbol s1 s2 in
    if c <> 0 then c
    else compare_term t1 t2
  | Lambda _, _ -> -1 | _, Lambda _ -> 1

  (* ignore side conditions *)
  | SideCond (_, _, _, t), _ -> compare_term t t2
  | _, SideCond (_, _, _, t) -> compare_term t1 t

  | Ptr t1, _ -> compare_term t1 t2
  | _, Ptr t2 -> compare_term t1 t2

  | Hole i1, Hole i2 -> Pervasives.compare i1 i2


and compare_term_list l1 l2 = match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | t1 :: r1, t2 :: r2 ->
    let c = compare_term t1 t2 in
    if c <> 0 then c
    else compare_term_list r1 r2



let rec holes_address acc t = match t.value with
  | Hole i -> (i, t) :: acc
  | Type | Kind |  Mpz | Mpq | Int _ | Rat _  -> acc
  | SideCond (name, args, exp, t) -> acc
  | Const _ -> acc
  | App (f, args) ->
    List.fold_left holes_address acc args 
  | Pi (s, x) -> holes_address acc x
  | Lambda (s, x) -> holes_address acc x
  | Ptr t -> holes_address acc t

let holes_address = holes_address []


let check_holes_integrity where h1 h2 =
  List.iter (fun (i, a) ->
      List.iter (fun (j, b) ->
          if j = i && a != b then
            (
              eprintf "\n%s: Hole _%d was at %nx, now at %nx\n@." where i
                (address_of a) (address_of b);
              (* eprintf "\n%s: Hole _%d has changed\n@." where i; *)
              assert false)
        ) h2
    ) h1

let check_term_integrity where t = 
  let h = holes_address t in
  check_holes_integrity (where ^ "term has != _") h h
    

let symbols = Hashtbl.create 21
let register_symbol s = Hashtbl.add symbols s.sname s.stype
let remove_symbol s = Hashtbl.remove symbols s.sname


let definitions = Hashtbl.create 21
let add_definition s t = Hashtbl.add definitions s t
let remove_definition s = Hashtbl.remove definitions s


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


(*****************************)
(* Side conditions callbacks *)
(*****************************)

let callbacks_table = Hashtbl.create 7


let callback name l =
  try
    let f = Hashtbl.find callbacks_table name in
    f l
  with Not_found ->
    failwith ("No side condition for " ^ name)


let sc_to_check = ref []


(**********************************)
(* Smart constructors for the AST *)
(**********************************)

let empty_subst = []

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


type substres = T of term | V of dterm | Same


let apply_subst_sym sigma s =
  try
    let x = List.assoc s sigma in
    T x
  with Not_found -> Same
    (* try *)
    (*   T (Hashtbl.find definitions s) *)
    (* with Not_found -> Same *)


let print_subst fmt sigma =
  fprintf fmt "@[<v 1>[";
  List.iter (fun (s, t) ->
      fprintf fmt "@ %a -> %a;" print_symbol s print_term t) sigma;
  fprintf fmt " ]@]"


let rec apply_subst_val sigma tval = match tval with
  | Type | Kind |  Mpz | Mpq | Int _ | Rat _ | Hole _ -> Same
    
  (* | Ptr t -> *)
  (*   V (Ptr (apply_subst sigma t)) *)
  (* | Ptr t -> apply_subst_val sigma t.value *)

  | Ptr t ->
    T (apply_subst sigma t)
               
  | Const s when is_hole_symbol s -> Same (* raise Exit *)
  | Const s -> apply_subst_sym sigma s
  | App (f, args) ->
    let nf = apply_subst sigma f in
    let nargs = List.rev_map (apply_subst sigma) args |> List.rev in
    if nf == f && List.for_all2 (==) nargs args then (* V tval *) Same
    else
    V (App(nf, nargs))
      
  | Pi (s, x) ->
    let s = { s with stype = apply_subst sigma s.stype } in
    let sigma = List.remove_assoc s sigma in
    let newx = apply_subst sigma x in
    if x == newx then (* V tval *) Same
    else
    V (Pi (s, newx))

  | Lambda (s, x) ->
    let s = { s with stype = apply_subst sigma s.stype } in
    let sigma = List.remove_assoc s sigma in
    let newx = apply_subst sigma x in
    if x == newx then (* V tval *) Same
    else
    V (Lambda (s, newx))

  | SideCond (name, args, exp, t) ->
    let nt = apply_subst sigma t in
    let nexp = apply_subst sigma exp in
    let nargs = List.rev_map (apply_subst sigma) args |> List.rev in
    if nt == t && nexp == exp && List.for_all2 (==) nargs args then (* V tval *) Same
    else
    V (SideCond (name, nargs, nexp, nt))



and apply_subst sigma t =
  match apply_subst_val sigma t.value with
  | Same -> t
  | T t -> t
  | V value ->
    let ttype = apply_subst sigma t.ttype in
    if value == t.value && ttype == t.ttype then t
    else { value; ttype }



let get_real t =
  apply_subst [] t
  (* match t.value with *)
  (* | Ptr t -> get_real t *)
  (* | _ -> t *)


let add_subst x v sigma =
  (x, v) :: sigma
  (* let sigma = List.rev_map (fun (y, w) -> y, apply_subst [x,v] w) sigma |> List.rev in *)
  (* (x, apply_subst sigma v) :: sigma *)



let rec occur_check subt t =
  compare_term t subt = 0
  ||
  match t.value with
  | Type | Kind |  Mpz | Mpq | Int _ | Rat _ | Hole _ | Const _ -> false

  | Ptr t -> occur_check subt t

  | App (f, args) ->
    occur_check subt f ||
    List.exists (occur_check subt) args
      
  | Pi (s, x) -> occur_check subt x

  | Lambda (s, x) -> occur_check subt x

  | SideCond (name, args, exp, t) ->
    occur_check subt exp ||
    occur_check subt t ||
    List.exists (occur_check subt) args
 

let rec fill_hole sigma h t =
  match h.value with
  | Hole _ ->
    if debug then
      eprintf ">>>>> Fill hole @[%a@] with @[%a@]@."
        print_term h print_term t;
    let t' = apply_subst sigma t in
    (* h.value <- t'.value; (\* KLUDGE *\) *)
    if not (occur_check h t') then h.value <- Ptr t';
    if debug then
      eprintf ">>>>>>>>> @[%a@]@." print_term_type h;
    fill_hole sigma h.ttype t'.ttype;
    (* (try compat_with sigma t'.ttype h.ttype with _ -> ()); *)
  | _ -> ()




(* Raise TypingError if t2 is not compatible with t1 *)
(* apsub is false if we want to prevent application of substitutions *)
and compat_with1 ?(apsub=true) sigma t1 t2 =
  if debug then (
    eprintf "compat_with(%b): @[<hov>%a@] and @[<hov>%a@]@."
      apsub print_term t1 print_term t2;
    eprintf "  with sigma = %a@." print_subst sigma
  );

  match t1.value, t2.value with
  | Type, Type  
  | Kind, Kind
  | Mpz, Mpz
  | Mpq, Mpz -> ()

  | Int z1, Int z2 -> if not (Big_int.eq_big_int z1 z2) then raise Exit
  | Rat q1, Rat q2 -> if not (Num.eq_num q1 q2) then raise Exit

  | Ptr t, _ -> compat_with1 ~apsub sigma t t2
  | _, Ptr t -> compat_with1 ~apsub sigma t1 t

  | Const s1, Const s2 ->
    if apsub then
      let a2 = get_t sigma s2 in
      let a1 = get_t ~gen:(not (is_hole a2)) sigma s1 in
      compat_with1 sigma ~apsub:false a1 a2
    else
    if s1.sname <> s2.sname then raise Exit

  | App (f1, args1), App (f2, args2) ->
    compat_with1 sigma f1 f2;
    List.iter2 (compat_with sigma) args1 args2

  | Pi (s1, t1), Pi (s2, t2) ->
    compat_with1 sigma s1.stype s2.stype;
    let a = s2 in
    let ta = { value = Const a; ttype = a.stype } in
    compat_with1 (add_subst s1 ta sigma) t1 t2;

  | Lambda (s1, t1), Lambda (s2, t2) ->
    compat_with sigma s1.stype s2.stype;
    let a = s2 in
    let ta = { value = Const a; ttype = a.stype } in
    compat_with1 (add_subst s1 ta sigma) t1 t2;


  | SideCond (name, args, expected, t1), _ ->
    check_side_condition name
      (List.rev_map (apply_subst sigma) args |> List.rev)
      (apply_subst sigma expected);
    compat_with1 sigma t1 t2

  (* ignore side conditions on the right *)
  | _, SideCond (name, args, expected, t2) ->
    compat_with1 sigma t1 t2

  | Hole i, Hole j when i = j -> ()
  (* failwith ("Cannot infer type of holes, too many holes.") *)

  | _, Hole _ -> fill_hole sigma t2 t1
  | Hole _, _ -> fill_hole sigma t1 t2


  | Const s, _ ->
    if apsub then
      let a = get_t sigma s in
      compat_with1 sigma ~apsub:false a t2
    else
      raise Exit

  | _, Const s ->
    if apsub then
      let a = get_t sigma s in
      compat_with1 sigma ~apsub:false a t1
    else
      raise Exit

  | _ -> raise Exit


and compat_with sigma t1 t2 =
  try compat_with1 sigma t1 t2 
  with Exit ->
    raise (TypingError (apply_subst sigma t1, apply_subst sigma t2))



and term_equal t1 t2 =
  try
    compat_with empty_subst t1 t2;
    true
  with
  | TypingError _ | Failure _ -> false



and check_side_condition name l expected =
  if debug then
    eprintf "Adding side condition : (%s%a) =?= %a@."
      name
      (fun fmt -> List.iter (fprintf fmt "@ %a" print_term)) l
      print_term expected;
  (* if not (term_equal (callback name l) expected) then *)
  (*   failwith ("Side condition " ^ name ^ " failed"); *)
  sc_to_check := (name, l, expected) :: !sc_to_check



let rec ty_of_app sigma ty args = match ty.value, args with
  | Pi (s, t), a :: rargs ->
    let sigma = add_subst s a sigma in
    compat_with sigma s.stype a.ttype;
    ty_of_app sigma t rargs

  | SideCond (name, scargs, expected, t), args ->
      check_side_condition name
        (List.rev_map (apply_subst sigma) scargs |> List.rev)
        (apply_subst sigma expected);
      ty_of_app sigma t args

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


let symbol_to_const s = { value = Const s; ttype = s.stype }
  


let rec mk_app ?(lookup=true) sigma f args =
  if debug then
    eprintf "mk_App : %a@." (print_tval false)
      { value = App (f, args); ttype = lfsc_type } ;

  match f.value, args with
  | Lambda (x, r), a :: rargs ->
    let sigma = List.remove_assoc x sigma in
    mk_app (add_subst x a sigma) r rargs
      
  | Const s, _ when lookup ->
    (* find the definition if it has one *)
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
  if debug then
    eprintf "\nMK ASCR:: should have type %a, has type %a\n@."
      print_term ty print_term t.ttype;
  compat_with empty_subst ty t.ttype; t
  (* { t with ttype = ty } *)


let add_sc name args expected t =
  { value = SideCond (name, args, expected, t);
    ttype = t.ttype }


let mk_declare n ty =
  let s = mk_symbol n ty in
  register_symbol s

let mk_define n t =
  let s = mk_symbol n t.ttype in
  register_symbol s;
  add_definition s t

let mk_check t =
  List.iter (fun (name, l, expected) ->
              if not (term_equal (callback name l) expected) then
    failwith ("Side condition " ^ name ^ " failed");
    ) (!sc_to_check);
  sc_to_check := [];
  ()






(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

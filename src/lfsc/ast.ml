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


open Format

exception CVC4Sat

let debug =
  (* true *)
  false

(********************************)
(* Type definitions for the AST *)
(********************************)

type mpz = Big_int.big_int
type mpq = Num.num


type name = Name of Hstring.t | S_Hole of int
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
  | SideCond of Hstring.t * term list * term * term

and term = { mutable value: dterm; ttype: term }
(* TODO: remove type annotations in terms *)

type command =
  | Check of term
  | Define of Hstring.t * term
  | Declare of Hstring.t * term


type proof = command list


module H = struct
  let holds = Hstring.make "holds"
  let th_holds = Hstring.make "th_holds"
  let mp_add = Hstring.make "mp_add"
  let mp_mul = Hstring.make "mp_mul"
  let uminus = Hstring.make "~"
  let eq = Hstring.make "="
end


let is_rule t =
  match t.ttype.value with
  | App ({value=Const{sname=Name n}}, _) -> n == H.holds || n == H.th_holds
  | _ -> false


let rec deref t = match t.value with
  | Ptr t -> deref t
  | _ -> t


let value t = (deref t).value


let ttype t = deref (deref t).ttype


let name c = match value c with
  | Const {sname=Name n} -> Some n
  | _ -> None


let app_name r = match value r with
  | App ({value=Const{sname=Name n}}, args) -> Some (n, args)
  | _ -> None


(*******************)
(* Pretty printing *)
(*******************)

let address_of (x:'a) : nativeint =
  if Obj.is_block (Obj.repr x) then
    Nativeint.shift_left (Nativeint.of_int (Obj.magic x)) 1 (* magic *)
  else
    invalid_arg "Can only find address of boxed values."
 
let rec print_symbol fmt { sname } = match sname with
  | Name n -> Hstring.print fmt n
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
    fprintf fmt "(! _ (^ (%a%a)@ %a)@ %a)"
      Hstring.print name
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
    fprintf fmt "(define %a@ %a)" Hstring.print s print_term t
  | Declare (s, t) ->
    fprintf fmt "(declare %a@ %a)" Hstring.print s print_term t

let print_proof fmt =
  List.iter (fprintf fmt "@[<1>%a@]@\n@." print_command) 



let compare_symbol s1 s2 = match s1.sname, s2.sname with
  | Name n1, Name n2 -> Hstring.compare n1 n2
  | Name _, _ -> -1
  | _, Name _ -> 1
  | S_Hole i1, S_Hole i2 -> Stdlib.compare i1 i2


let rec compare_term ?(mod_eq=false) t1 t2 = match t1.value, t2.value with
  | Ptr t1, _ -> compare_term ~mod_eq t1 t2
  | _, Ptr t2 -> compare_term ~mod_eq t1 t2
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
  | App ({value=Const{sname=Name n1}}, [ty1; a1; b1]),
    App ({value=Const{sname=Name n2}}, [ty2; a2; b2])
    when n1 == H.eq && n2 == H.eq && mod_eq ->
    let c = compare_term ~mod_eq ty1 ty2 in
    if c <> 0 then c
    else
      let ca1a2 = compare_term ~mod_eq a1 a2 in
      let ca1b2 = compare_term ~mod_eq a1 b2 in
      let cb1b2 = compare_term ~mod_eq b1 b2 in
      let cb1a2 = compare_term ~mod_eq b1 a2 in
      if ca1a2 = 0 && cb1b2 = 0 then 0
      else if ca1b2 = 0 && cb1a2 = 0 then 0
      else if ca1a2 <> 0 then ca1a2 else cb1b2
  | App (f1, l1), App (f2, l2) ->
    let c = compare_term ~mod_eq f1 f2 in
    if c <> 0 then c else
    compare_term_list ~mod_eq l1 l2
  | App _, _ -> -1 | _, App _ -> 1
    
  | Pi (s1, t1), Pi (s2, t2) ->
    let c = compare_symbol s1 s2 in
    if c <> 0 then c
    else compare_term ~mod_eq t1 t2
  | Pi _, _ -> -1 | _, Pi _ -> 1

  | Lambda (s1, t1), Lambda (s2, t2) ->
    let c = compare_symbol s1 s2 in
    if c <> 0 then c
    else compare_term ~mod_eq t1 t2
  | Lambda _, _ -> -1 | _, Lambda _ -> 1

  (* ignore side conditions *)
  | SideCond (_, _, _, t), _ -> compare_term ~mod_eq t t2
  | _, SideCond (_, _, _, t) -> compare_term ~mod_eq t1 t

  | Hole i1, Hole i2 -> Stdlib.compare i1 i2


and compare_term_list ?(mod_eq=false) l1 l2 = match l1, l2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | t1 :: r1, t2 :: r2 ->
    let c = compare_term ~mod_eq t1 t2 in
    if c <> 0 then c
    else compare_term_list ~mod_eq r1 r2


let rec hash_term t = match t.value with
  | Ptr t -> hash_term t
  | v -> Hashtbl.hash_param 100 500 v


module Term = struct
  type t = term
  let compare = compare_term ~mod_eq:false
  let equal x y = compare_term x y = 0
  let hash t = Hashtbl.hash_param 10 100 t.value (* hash_term *)
  (* let hasht = Hashtbl.hash *)
  (* let rec hash = *)
  (*   let cpt = ref 0 in *)
  (*   fun hh t -> *)
  (*   incr cpt; *)
  (*   if !cpt > 10 then hh else *)
  (*   hh + *)
  (*   let v = t.value in *)
  (*   match v with *)
  (*   | Hole _ | Type | Kind |  Mpz | Mpq | Int _ | Rat _ | Const _ -> hasht v *)
  (*   | SideCond (_, args, exp, t) -> *)
  (*     List.fold_left (fun acc t -> hash hh t + 31*acc) (hash hh t) args *)
  (*   | App (f, args) -> *)
  (*     List.fold_left (fun acc t -> hash hh t + 31*acc) (hash hh f) args *)
  (*   | Pi (s, x) -> ((Hashtbl.hash s) + 31*(hash hh x)) * 7 *)
  (*   | Lambda (s, x) -> ((Hashtbl.hash s) + 31*(hash hh x)) * 9 *)
  (*   | Ptr t' -> 0 *)
  (*     (\* t.value <- t'.value; *\) *)
  (*     (\* hash hh (deref t') *\) *)
  (* let hash = hash 0 *)
end




(* let rec holes_address acc t = match t.value with
 *   | Hole i -> (i, t) :: acc
 *   | Type | Kind |  Mpz | Mpq | Int _ | Rat _  -> acc
 *   | SideCond (name, args, exp, t) -> acc
 *   | Const _ -> acc
 *   | App (f, args) ->
 *     List.fold_left holes_address acc args
 *   | Pi (s, x) -> holes_address acc x
 *   | Lambda (s, x) -> holes_address acc x
 *   | Ptr t -> holes_address acc t *)

(* let holes_address = holes_address [] *)


(* let check_holes_integrity where h1 h2 =
 *   List.iter (fun (i, a) ->
 *       List.iter (fun (j, b) ->
 *           if j = i && a != b then
 *             (
 *               eprintf "\n%s: Hole _%d was at %nx, now at %nx\n@." where i
 *                 (address_of a) (address_of b);
 *               (\* eprintf "\n%s: Hole _%d has changed\n@." where i; *\)
 *               assert false)
 *         ) h2
 *     ) h1 *)

(* let check_term_integrity where t =
 *   let h = holes_address t in
 *   check_holes_integrity (where ^ "term has != _") h h *)



let eq_name s1 s2 = match s1, s2 with
  | S_Hole i1, S_Hole i2 -> i1 == i2
  | Name n1, Name n2 -> n1 == n2
  | _ -> false

module HN = Hashtbl.Make (struct
    type t = name
    let equal = eq_name
    let hash = function
      | S_Hole i -> i * 7
      | Name n -> Hstring.hash n * 9
  end)

let symbols = HN.create 21
let register_symbol s = HN.add symbols s.sname s.stype
let remove_symbol s = HN.remove symbols s.sname

let definitions = HN.create 21
let add_definition n t = HN.add definitions n t
let remove_definition n = HN.remove definitions n


exception TypingError of term * term


(**************************)
(* Predefined terms/types *)
(**************************)


let rec kind = { value = Kind; ttype = kind }

let lfsc_type = { value = Type; ttype = kind }

let mpz = { value = Mpz; ttype = lfsc_type }

let mpq = { value = Mpq; ttype = lfsc_type }

let mk_mpz n = { value = Int n; ttype = mpz }

let mpz_of_int n = { value = Int (Big_int.big_int_of_int n); ttype = mpz }

let mk_mpq n = { value = Rat n; ttype = mpq }


let mk_symbol s stype =
  { sname = Name (Hstring.make s) ; stype }
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

let callbacks_table = Hstring.H.create 7


let mp_add x y =
  (* eprintf "mp_add %a %a@." print_term x print_term y;  *)
  match value x, value y with
  | Int xi, Int yi -> mk_mpz (Big_int.add_big_int xi yi)
  | _ -> assert false

let mp_mul x y = match value x, value y with
  | Int xi, Int yi -> mk_mpz (Big_int.mult_big_int xi yi)
  | _ -> assert false

let uminus x = match value x with
  | Int xi -> mk_mpz (Big_int.minus_big_int xi)
  | _ -> assert false


let rec eval_arg x = match app_name x with
  | Some (n, [x]) when n == H.uminus -> uminus (eval_arg x)
  | Some (n, [x; y]) when n == H.mp_add -> mp_add (eval_arg x) (eval_arg y)
  | Some (n, [x; y]) when n == H.mp_mul -> mp_mul (eval_arg x) (eval_arg y)
  | _ -> x


let callback name l =
  try
    let f = Hstring.H.find callbacks_table name in
    (* eprintf "apply %s ... @." name; *)
    let l = List.map eval_arg l in
    f l
  with Not_found ->
    failwith ("No side condition for " ^ Hstring.view name)



(* type sc_check = String * term list * term *)


(* type sc_tree = *)
(*   | SCEmpty *)
(*   (\* | SCLeaf of sc_check *\) *)
(*   | SCBranches of sc_check * sc_tree list *)


(* let sct = ref (SCEmpty) *)


let sc_to_check = ref []
  


(**********************************)
(* Smart constructors for the AST *)
(**********************************)

module MSym = Map.Make (struct
    type t = symbol
    let compare = compare_symbol
  end)


let empty_subst = MSym.empty

(* let fresh_alpha =
 *   let cpt = ref 0 in
 *   fun ty -> incr cpt;
 *     mk_symbol ("'a"^string_of_int !cpt) ty *)


let get_t ?(gen=true) sigma s =
  try
    let x = MSym.find s sigma in
    if not gen && is_hole x then raise Not_found;
    x
  with Not_found -> try
      HN.find definitions s.sname
    with Not_found ->
      { value = Const s; ttype = s.stype }


type substres = T of term | V of dterm | Same


let apply_subst_sym sigma s =
  try
    let x = MSym.find s sigma in
    T x
  with Not_found -> Same
    (* try *)
    (*   T (Hashtbl.find definitions s) *)
    (* with Not_found -> Same *)


let print_subst fmt sigma =
  fprintf fmt "@[<v 1>[";
  MSym.iter (fun s t ->
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
    let sigma = MSym.remove s sigma in
    let newx = apply_subst sigma x in
    if x == newx then (* V tval *) Same
    else
    V (Pi (s, newx))

  | Lambda (s, x) ->
    let s = { s with stype = apply_subst sigma s.stype } in
    let sigma = MSym.remove s sigma in
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



let get_real t = apply_subst MSym.empty t


let rec flatten_term_value t = match t.value with
  | Hole _ | Type | Kind |  Mpz | Mpq | Int _ | Rat _  -> ()
  | SideCond (_, args, exp, t) ->
    List.iter flatten_term args;
    flatten_term exp;
    flatten_term t
  | Const s -> flatten_term s.stype
  | App (f, args) ->
    flatten_term f;
    List.iter flatten_term args 
  | Pi (s, x) | Lambda (s, x) ->
    flatten_term s.stype;
    flatten_term x    
  | Ptr t' ->
    t.value <- (deref t').value
    (* flatten_term t *)


and flatten_term t =
  flatten_term_value t
  (* ; *)
  (* match t.value with *)
  (* | Type | Kind -> () *)
  (* | _ -> flatten_term t.ttype *)


let rec has_ptr_val t = match t.value with
  | Hole _ | Type | Kind |  Mpz | Mpq | Int _ | Rat _  -> false
  | SideCond (_, args, exp, t) ->
    List.exists has_ptr args || has_ptr exp || has_ptr t
  | Const s -> has_ptr s.stype
  | App (f, args) -> has_ptr f || List.exists has_ptr args
  | Pi (s, x) | Lambda (s, x) -> has_ptr s.stype || has_ptr x    
  | Ptr _ -> true

and has_ptr t = 
  has_ptr_val t ||
  match t.value with
  | Type | Kind -> false
  | _ -> has_ptr t.ttype


let add_subst x v sigma = MSym.add x v sigma
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
    if not (occur_check h t') then h.value <- Ptr (deref t');
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
    if not (eq_name s1.sname s2.sname) then raise Exit

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
    eprintf "Adding side condition : (%a%a) =?= %a@."
      Hstring.print name
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
    let stype = HN.find symbols (Name (Hstring.make x)) in
    let s = mk_symbol x stype in
    try
      HN.find definitions s.sname
    with Not_found -> { value = Const s; ttype = stype }
  with Not_found -> failwith ("Symbol " ^ x ^ " is not declared.")


let symbol_to_const s = { value = Const s; ttype = s.stype }
  

let rec mk_app ?(lookup=true) sigma f args =
  if debug then
    eprintf "mk_App : %a@." (print_tval false)
      { value = App (f, args); ttype = lfsc_type } ;

  match f.value, args with
  | Lambda (x, r), a :: rargs ->
    let sigma = MSym.remove x sigma in
    mk_app (add_subst x a sigma) r rargs
      
  (* | Const {sname = Name "mp_add"}, [x; y] -> mp_add x y *)

  (* | Const {sname = Name "mp_mul"}, [x; y] -> mp_mul x y *)
      
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


let rec hole_nbs acc t = match value t with
  | Hole nb -> nb :: acc
  | App (f, args) -> List.fold_left hole_nbs (hole_nbs acc f) args 
  | Pi (s, x) | Lambda (s, x) -> hole_nbs acc x
  | Ptr t -> hole_nbs acc t
  | _ -> acc


(* let rec min_hole acc t = match value t with
 *   | Hole nb ->
 *     (match acc with Some n when nb < n -> Some nb  | None -> Some nb | _ -> acc)
 *   | App (f, args) -> List.fold_left min_hole (min_hole acc f) args
 *   | Pi (s, x) | Lambda (s, x) -> min_hole acc x
 *   | Ptr t -> min_hole acc t
 *   | _ -> acc *)


(* let compare_int_opt m1 m2 = match m1, m2 with
 *   | None, None -> 0
 *   | Some _, None -> -1
 *   | None, Some _ -> 1
 *   | Some n1, Some n2 -> compare n1 n2 *)


let compare_sc_checks (_, args1, exp1) (_, args2, exp2) =
  let el1 = hole_nbs [] exp1 in
  let el2 = hole_nbs [] exp2 in

  let al1 = List.fold_left hole_nbs [] args1 in
  let al2 = List.fold_left hole_nbs [] args2 in

  if List.exists (fun n -> List.mem n al1) el2 then 1
  else if List.exists (fun n -> List.mem n al2) el1 then -1
  else if el1 = [] then 1
  else if el2 = [] then -1
  else compare el1 el2


let sort_sc_checks l = List.fast_sort compare_sc_checks l


let run_side_conditions () =
  (* List.iter (fun (name, l, expected)  -> *)
  (*     eprintf "\nSorted side condition : (%s%a) =?= %a@." *)
  (*       name *)
  (*       (fun fmt -> List.iter (fprintf fmt "@ %a" print_term)) l *)
  (*       print_term expected; *)
  (*   ) (List.flatten !all_scs |> sort_sc_checks); *)

  List.iter (fun (name, l, expected) ->
      let res = callback name l in
      if not (term_equal res expected) then
        failwith (asprintf "Side condition %a failed: Got %a, expected %a"
                    Hstring.print name print_term res print_term expected);
    ) (sort_sc_checks !sc_to_check);
  sc_to_check := [];
  ()


let mk_pi s t =
  (* let s = if is_hole_symbol s then fresh_alpha s.stype else s in *)
  { value = Pi (s, t); ttype = lfsc_type }

let mk_lambda s t =
  (* sc_to_check := List.rev !sc_to_check; *)
  (* run_side_conditions (); *)
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
  { value = SideCond (Hstring.make name, args, expected, t);
    ttype = t.ttype }


let mk_declare n ty =
  let s = mk_symbol n ty in
  register_symbol s

let mk_define n t =
  let s = mk_symbol n t.ttype in
  register_symbol s;
  add_definition s.sname t



let mk_check t = run_side_conditions ()


let clear_sc () = sc_to_check := []



let rec hash_term_mod_eq p = match p.value with
  | App ({value=Const{sname=Name n}} as f, [ty; a; b])
    when n == H.eq &&
         compare_term ~mod_eq:true a b > 0 ->
    Term.hash (mk_app f [ty; b; a])
  | App (f, args) ->
    List.fold_left
      (fun acc t -> 7*(acc + hash_term_mod_eq f)) 1 (f:: args)
  | Pi (s, x) ->
    (Hashtbl.hash_param 100 500 s + hash_term_mod_eq x) * 11
  | Lambda (s, x) ->
    (Hashtbl.hash_param 100 500 s + hash_term_mod_eq x) * 13
  | _ -> Hashtbl.hash_param 100 500 p


module Term_modeq = struct
  type t = term
  let compare = compare_term ~mod_eq:true
  let equal x y = compare_term ~mod_eq:true x y = 0
  let hash t =
    (* eprintf "HASH: %a@." print_term t; *)
    hash_term_mod_eq t 
end


(* 
   Local Variables:
   compile-command: "make"
   indent-tabs-mode: nil
   End: 
*)

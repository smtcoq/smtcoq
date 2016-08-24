(**************************************************************************)
(*                                                                        *)
(*                            LFSCtoSmtCoq                                *)
(*                                                                        *)
(*                         Copyright (C) 2016                             *)
(*          by the Board of Trustees of the University of Iowa            *)
(*                                                                        *)
(*                    Alain Mebsout and Burak Ekici                       *)
(*                       The University of Iowa                           *)
(*                                                                        *)
(*                                                                        *)
(*  This file is distributed under the terms of the Apache Software       *)
(*  License version 2.0                                                   *)
(*                                                                        *)
(**************************************************************************)

open Ast
open Format

let scope = ref []


let declare_get s =
  scope := [s];
  fun ty ->
  mk_declare s ty;
  let c = mk_const s in
  scope := [];
  c


let define s =
  scope := [s];
  fun t ->
    mk_define s t;
    scope := []


let pi n ty =
  let n = String.concat "." (List.rev (n :: !scope)) in
  let s = mk_symbol n ty in
  register_symbol s;
  fun t ->
    let pi_abstr = mk_pi s t in
    remove_symbol s;
    pi_abstr


let pi_d n ty ft =
  let n = String.concat "." (List.rev (n :: !scope)) in
  let s = mk_symbol n ty in
  register_symbol s;
  let pi_abstr = mk_pi s (ft (symbol_to_const s)) in
  remove_symbol s;
  pi_abstr


let mp_add_s = declare_get "mp_add" (pi "a" mpz (pi "b" mpz mpz))
let mp_add x y = match value x, value y with
  | Int xi, Int yi -> mk_mpz (Big_int.add_big_int xi yi)
  | _ -> mk_app mp_add_s [x; y]

let mp_mul_s = declare_get "mp_mul" (pi "a" mpz (pi "b" mpz mpz))
let mp_mul x y = match value x, value y with
  | Int xi, Int yi -> mk_mpz (Big_int.mult_big_int xi yi)
  | _ -> mk_app mp_add_s [x; y]



let rec eval_arg x = match app_name x with
  | Some ("mp_add", [x; y]) -> mp_add (eval_arg x) (eval_arg y)
  | Some ("mp_mul", [x; y]) -> mp_mul (eval_arg x) (eval_arg y)
  | _ -> x


let mp_isneg x =
  (* eprintf "mp_isneg %a .@." print_term x; *)
  match value x with
  | Int n -> Big_int.sign_big_int n < 0
  | _ -> failwith ("mp_isneg")

let mp_iszero x = match value x with
  | Int n -> Big_int.sign_big_int n = 0
  | _ -> failwith ("mp_iszero")


let uminus = declare_get "~" (pi "a" mpz mpz)

let bool_lfsc = declare_get "bool_lfsc" lfsc_type
let tt = declare_get "tt" bool_lfsc
let ff = declare_get "ff" bool_lfsc

let var = declare_get "var" lfsc_type
let lit = declare_get "lit" lfsc_type
let clause = declare_get "clause" lfsc_type
let cln = declare_get "cln" clause

let okay = declare_get "okay" lfsc_type
let ok = declare_get "ok" okay

let pos_s = declare_get "pos" (pi "x" var lit)
let neg_s = declare_get "neg" (pi "x" var lit)
let clc_s = declare_get "clc" (pi "x" lit (pi "c" clause clause))

let concat_cl_s = declare_get "concat_cl"
    (pi "c1" clause (pi "c2" clause clause))

let clr_s = declare_get "clr" (pi "l" lit (pi "c" clause clause))

let formula = declare_get "formula" lfsc_type
let th_holds_s = declare_get "th_holds" (pi "f" formula lfsc_type)

let ttrue = declare_get "true" formula
let tfalse = declare_get "false" formula

(* some definitions *)
let _ =
  define "formula_op1" (pi "f" formula formula);
  define "formula_op2"
    (pi "f1" formula
    (pi "f2" formula formula));
  define "formula_op3"
    (pi "f1" formula
    (pi "f2" formula
    (pi "f3" formula formula)))

let not_s = declare_get "not" (mk_const "formula_op1")
let and_s = declare_get "and" (mk_const "formula_op2")
let or_s = declare_get "or" (mk_const "formula_op2")
let impl_s = declare_get "impl" (mk_const "formula_op2")
let iff_s = declare_get "iff" (mk_const "formula_op2")
let xor_s = declare_get "xor" (mk_const "formula_op2")
let ifte_s = declare_get "ifte" (mk_const "formula_op3")


let sort = declare_get "sort" lfsc_type
let term_s = declare_get "term" (pi "t" sort lfsc_type)
let term x = mk_app term_s [x] 
let tBool = declare_get "Bool" sort
let p_app_s = declare_get "p_app" (pi "x" (term tBool) formula)
let p_app b = mk_app p_app_s [b]
let arrow_s = declare_get "arrow" (pi "s1" sort (pi "s2" sort sort))
let arrow s1 s2 = mk_app arrow_s [s1; s2]
let apply_s = declare_get "apply"
    (pi_d "s1" sort (fun s1 ->
    (pi_d "s2" sort (fun s2 ->
    (pi "t1" (term (arrow s1 s2))
    (pi "t2" (term s1)
       (term s2)))))))
let apply s1 s2 f x = mk_app apply_s [s1; s2; f; x]


let eq_s = declare_get "="
    (pi_d "s" sort (fun s ->
    (pi "x" (term s)
    (pi "y" (term s) formula))))

let eq ty x y = mk_app eq_s [ty; x; y]

let pos v = mk_app pos_s [v] 
let neg v = mk_app neg_s [v] 
let clc x c = mk_app clc_s [x; c]
let clr l c = mk_app clr_s [l; c]
let concat_cl c1 c2 = mk_app concat_cl_s [c1; c2]


let not_ a = mk_app not_s [a]
let and_ a b = mk_app and_s [a; b]
let or_ a b = mk_app or_s [a; b]
let impl_ a b = mk_app impl_s [a; b]
let iff_ a b = mk_app iff_s [a; b]
let xor_ a b = mk_app xor_s [a; b]
let ifte_ a b c = mk_app ifte_s [a; b; c]

(* Bit vector syntax / symbols *)

let bitVec_s = declare_get "BitVec" (pi "n" mpz sort)
let bitVec n = mk_app bitVec_s [n]

let bit = declare_get "bit" lfsc_type
let b0 = declare_get "b0" bit
let b1 = declare_get "b1" bit

let bv = declare_get "bv" lfsc_type
let bvn = declare_get "bvn" bv
let bvc_s = declare_get "bvc" (pi "b" bit (pi "v" bv bv))
let bvc b v = mk_app bvc_s [b; v]


let bblt = declare_get "bblt" lfsc_type
let bbltn = declare_get "bbltn" bblt
let bbltc_s = declare_get "bbltc" (pi "f" formula (pi "v" bblt bblt))
let bbltc f v = mk_app bbltc_s [f; v]

let var_bv = declare_get "var_bv" lfsc_type

let a_var_bv_s = declare_get "a_var_bv"
    (pi_d "n" mpz (fun n ->
         (pi "v" var_bv (term (bitVec n)))))
let a_var_bv n v = mk_app a_var_bv_s [n; v]

let a_bv_s = declare_get "a_bv"
    (pi_d "n" mpz (fun n ->
         (pi "v" bv (term (bitVec n)))))
let a_bv n v = mk_app a_bv_s [n; v]



let bitof_s = declare_get "bitof" (pi "x" var_bv (pi "n" mpz formula))
let bitof x n =  mk_app bitof_s [x; n]

let bblast_term_s = declare_get "bblast_term"
    (pi_d "n" mpz (fun n ->
    (pi "x" (term (bitVec n))
    (pi "y" bblt lfsc_type))))        
let bblast_term n x y = mk_app bblast_term_s [n; x; y]

let _ = 
  define "bvop2"
	(pi_d "n" mpz (fun n ->
	(pi "x" (term (bitVec n))
        (pi "y" (term (bitVec n))
           (term (bitVec n))))))

let bvand_s = declare_get "bvand" (mk_const "bvop2")
let bvor_s = declare_get "bvor" (mk_const "bvop2")
let bvxor_s = declare_get "bvxor" (mk_const "bvop2")
let bvnand_s = declare_get "bvnand" (mk_const "bvop2")
let bvnor_s = declare_get "bvnor" (mk_const "bvop2")
let bvxnor_s = declare_get "bvxnor" (mk_const "bvop2")
let bvmul_s = declare_get "bvmul" (mk_const "bvop2")
let bvadd_s = declare_get "bvadd" (mk_const "bvop2")
let bvsub_s = declare_get "bvsub" (mk_const "bvop2")
let bvudiv_s = declare_get "bvudiv" (mk_const "bvop2")
let bvurem_s = declare_get "bvurem" (mk_const "bvop2")
let bvsdiv_s = declare_get "bvsdiv" (mk_const "bvop2")
let bvsrem_s = declare_get "bvsrem" (mk_const "bvop2")
let bvsmod_s = declare_get "bvsmod" (mk_const "bvop2")
let bvshl_s = declare_get "bvshl" (mk_const "bvop2")
let bvlshr_s = declare_get "bvlshr" (mk_const "bvop2")
let bvashr_s = declare_get "bvashr" (mk_const "bvop2")

let bvand n a b = mk_app bvand_s [n; a; b]
let bvor n a b = mk_app bvor_s [n; a; b]
let bvxor n a b = mk_app bvxor_s [n; a; b]
let bvnand n a b = mk_app bvnand_s [n; a; b]
let bvnor n a b = mk_app bvnor_s [n; a; b]
let bvxnor n a b = mk_app bvxnor_s [n; a; b]
let bvmul n a b = mk_app bvmul_s [n; a; b]
let bvadd n a b = mk_app bvadd_s [n; a; b]
let bvsub n a b = mk_app bvsub_s [n; a; b]
let bvudiv n a b = mk_app bvudiv_s [n; a; b]
let bvurem n a b = mk_app bvurem_s [n; a; b]
let bvsdiv n a b = mk_app bvsdiv_s [n; a; b]
let bvsrem n a b = mk_app bvsrem_s [n; a; b]
let bvsmod n a b = mk_app bvsmod_s [n; a; b]
let bvshl n a b = mk_app bvshl_s [n; a; b]
let bvlshr n a b = mk_app bvlshr_s [n; a; b]
let bvashr n a b = mk_app bvashr_s [n; a; b]

let _ = 
  define "bvop1"
	(pi_d "n" mpz (fun n ->
	(pi "x" (term (bitVec n))
           (term (bitVec n)))))

let bvnot_s = declare_get "bvnot" (mk_const "bvop1")
let bvneg_s = declare_get "bvneg" (mk_const "bvop1")

let bvnot n a = mk_app bvnot_s [n; a]
let bvneg n a = mk_app bvneg_s [n; a]


let _ = 
  define "bvpred"
	(pi_d "n" mpz (fun n ->
	(pi "x" (term (bitVec n))
        (pi "y" (term (bitVec n))
           formula))))

let bvult_s = declare_get "bvult" (mk_const "bvpred")
let bvslt_s = declare_get "bvslt" (mk_const "bvpred")

let bvult n a b = mk_app bvult_s [n; a; b]
let bvslt n a b = mk_app bvslt_s [n; a; b]


let concat_s = declare_get "concat"
    (pi_d "n" mpz (fun n ->
    (pi_d "m" mpz (fun m -> 
    (pi_d "m'" mpz (fun m' ->
    (pi "t1" (term (bitVec m))
    (pi "t2" (term (bitVec m'))
       (term (bitVec n))))))))))

let concat n m m' a b = mk_app concat_s [n; m; m'; a; b]


(* arrays constructors and functions *)

let array_s = declare_get "Array" (pi "s1" sort (pi "s2" sort sort))
let array s1 s2 = mk_app array_s [s1; s2]
let read_s = declare_get "read"
    (pi_d "s1" sort (fun s1 ->
    (pi_d "s2" sort (fun s2 ->
     (term (arrow (array s1 s2) (arrow s1 s2)))))))           
let read s1 s2 = mk_app read_s [s1; s2]
let write_s = declare_get "write"
    (pi_d "s1" sort (fun s1 ->
    (pi_d "s2" sort (fun s2 ->
     (term (arrow (array s1 s2) (arrow s1 (arrow s2 (array s1 s2)))))))))
let write s1 s2 = mk_app write_s [s1; s2]
let diff_s = declare_get "diff"
    (pi_d "s1" sort (fun s1 ->
    (pi_d "s2" sort (fun s2 ->
     (term (arrow (array s1 s2) (arrow (array s1 s2) s1)))))))
let diff s1 s2 = mk_app diff_s [s1; s2]

(* sortcuts *)
let apply_read s1 s2 a i =
  apply s1 s2 (apply (array s1 s2) (arrow s1 s2) (read s1 s2) a) i
let apply_write s1 s2 a i v =
  apply s2 (array s1 s2)
  (apply s1 (arrow s2 (array s1 s2))
    (apply (array s1 s2) (arrow s1 (arrow s2 (array s1 s2))) (write s1 s2) a)
    i) v
let apply_diff s1 s2 a b =
  apply (array s1 s2) s1
    (apply (array s1 s2) (arrow (array s1 s2) s1) (diff s1 s2) a) b


module MInt = Map.Make (struct
    type t = int
    let compare = Pervasives.compare
  end)

module STerm = Set.Make (Term)

type mark_map = STerm.t MInt.t

let empty_marks = MInt.empty

let is_marked i m v =
  try
    STerm.mem v (MInt.find i m)
  with Not_found -> false

let if_marked_do i m v then_v else_v =
  if is_marked i m v then (then_v m) else (else_v m)

let markvar_with i m v =
  let set = try MInt.find i m with Not_found -> STerm.empty in
  MInt.add i (STerm.add v set) m


let ifmarked m v = if_marked_do 1 m v
let ifmarked1 m v = ifmarked m v 
let ifmarked2 m v = if_marked_do 2 m v
let ifmarked3 m v = if_marked_do 3 m v
let ifmarked4 m v = if_marked_do 4 m v

let markvar m v = markvar_with 1 m v
let markvar1 m v = markvar m v
let markvar2 m v = markvar_with 2 m v
let markvar3 m v = markvar_with 3 m v
let markvar4 m v = markvar_with 4 m v 


(*******************)
(* Side conditions *)
(*******************)
                

let rec append c1 c2 =
  match value c1 with
  | Const _ when term_equal c1 cln -> c2
  | App (f, [l; c1']) when term_equal f clc_s ->
    clc l (append c1' c2)
  | _ -> failwith "Match failure"



(* we use marks as follows:
   - mark 1 to record if we are supposed to remove a positive occurrence of
     the variable.
   - mark 2 to record if we are supposed to remove a negative occurrence of
     the variable.
   - mark 3 if we did indeed remove the variable positively
   - mark 4 if we did indeed remove the variable negatively *)
let rec simplify_clause mark_map c =
  (* eprintf "simplify_clause[rec] %a@." print_term c; *)
  match value c with
  | Const _ when term_equal c cln -> cln, mark_map

  | App(f, [l; c1]) when term_equal f clc_s ->

    begin match value l with
      (* Set mark 1 on v if it is not set, to indicate we should remove it.
         After processing the rest of the clause, set mark 3 if we were already
         supposed to remove v (so if mark 1 was set when we began).  Clear mark3
         if we were not supposed to be removing v when we began this call. *)

      | App (f, [v]) when term_equal f pos_s -> let v = deref v in

        let m, mark_map = ifmarked mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar mark_map v) in

        let c', mark_map = simplify_clause mark_map c1 in

        begin match value m with
          | Const _ when term_equal m tt ->
            let mark_map = ifmarked3 mark_map v
                (fun mark_map -> mark_map)
                (fun mark_map -> markvar3 mark_map v) in
            c', mark_map

          | Const _ when term_equal m ff ->
            let mark_map = ifmarked3 mark_map v
                (fun mark_map -> markvar3 mark_map v)
                (fun mark_map -> mark_map) in
            let mark_map = markvar mark_map v in
            clc l c', mark_map

          | _ -> failwith "Match failure1"
        end


      | App (f, [v]) when term_equal f neg_s -> let v = deref v in

        let m, mark_map = ifmarked2 mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar2 mark_map v) in

        let c', mark_map = simplify_clause mark_map c1 in

        begin match value m with
          | Const _ when term_equal m tt ->
            let mark_map = ifmarked4 mark_map v
                (fun mark_map -> mark_map)
                (fun mark_map -> markvar4 mark_map v) in
            c', mark_map

          | Const _ when term_equal m ff ->
            let mark_map = ifmarked4 mark_map v
                (fun mark_map -> markvar4 mark_map v)
                (fun mark_map -> mark_map) in
            let mark_map = markvar2 mark_map v in
            clc l c', mark_map

          | _ -> failwith "Match failure2"
        end

      | _ -> failwith "Match failure3"

    end

  | App(f, [c1; c2]) when term_equal f concat_cl_s ->
    let new_c1, mark_map = simplify_clause mark_map c1 in
    let new_c2, mark_map = simplify_clause mark_map c2 in
    append new_c1 new_c2, mark_map

  | App(f, [l; c1]) when term_equal f clr_s ->

    begin match value l with
      (* set mark 1 to indicate we should remove v, and fail if
         mark 3 is not set after processing the rest of the clause
         (we will set mark 3 if we remove a positive occurrence of v). *)

      | App (f, [v]) when term_equal f pos_s -> let v = deref v in

        let m, mark_map = ifmarked mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar mark_map v) in

        let m3, mark_map = ifmarked3 mark_map v
            (fun mark_map -> tt, markvar3 mark_map v)
            (fun mark_map -> ff, mark_map) in

        let c', mark_map = simplify_clause mark_map c1 in

        let mark_map = ifmarked3 mark_map v
            (fun mark_map ->
               let mark_map = match value m3 with
                 | Const _ when term_equal m3 tt -> mark_map
                 | Const _ when term_equal m3 ff -> markvar3 mark_map v
                 | _ -> failwith "Match failure4"
               in
               let mark_map = match value m with
                 | Const _ when term_equal m tt -> mark_map
                 | Const _ when term_equal m ff -> markvar mark_map v
                 | _ -> failwith "Match failure5"
               in
               mark_map
            )
            (fun _ -> failwith "Match failure6")
        in

        c', mark_map

      | App (f, [v]) when term_equal f neg_s -> let v = deref v in

        let m2, mark_map = ifmarked2 mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar2 mark_map v) in

        let m4, mark_map = ifmarked4 mark_map v
            (fun mark_map -> tt, markvar4 mark_map v)
            (fun mark_map -> ff, mark_map) in

        let c', mark_map = simplify_clause mark_map c1 in

        let mark_map = ifmarked4 mark_map v
            (fun mark_map ->
               let mark_map = match value m4 with
                 | Const _ when term_equal m4 tt -> mark_map
                 | Const _ when term_equal m4 ff -> markvar4 mark_map v
                 | _ -> failwith "Match failure7"
               in
               let mark_map = match value m2 with
                 | Const _ when term_equal m2 tt -> mark_map
                 | Const _ when term_equal m2 ff -> markvar2 mark_map v
                 | _ -> failwith "Match failure8"
               in
               mark_map
            )
            (fun _ -> failwith "Match failure9")
        in

        c', mark_map

      | _ -> failwith "Match failure10"

    end

  | _ -> failwith "Match failure11"


let simplify_clause c =
  let c', _ = simplify_clause empty_marks c in
  c'



let () =
  List.iter (fun (s, f) -> Hashtbl.add callbacks_table s f)
    [

      "append",
      (function
        | [c1; c2] -> append c1 c2
        | _ -> failwith "append: Wrong number of arguments");

      "simplify_clause",
      (function
        | [c] -> simplify_clause c
        | _ -> failwith "simplify_clause: Wrong number of arguments");

    ]
    



let mpz_sub x y = mp_add x (mp_mul (mpz_of_int (-1)) y)



let rec bv_constants_are_disequal x y =
  match value x with
  | Const _ when term_equal x bvn -> failwith "bv_constants_are_disequal"
  | App (f, [bx; x']) when term_equal f bvc_s ->
    (match value y with
     | Const _ when term_equal y bvn -> failwith "bv_constants_are_disequal"
     | App (f, [by; y']) when term_equal f bvc_s ->
       if term_equal bx b0 then
         if term_equal by b0 then
           bv_constants_are_disequal x' y'
         else ttrue
       else if term_equal bx b1 then
         if term_equal by b1 then
           bv_constants_are_disequal x' y'
         else ttrue
       else failwith "bv_constants_are_disequal"
     | _ -> failwith "bv_constants_are_disequal")
  | _ -> failwith "bv_constants_are_disequal"



(* calculate the length of a bit-blasted term *)
let rec bblt_len v =
  (* eprintf "bblt_len %a@." print_term v; *)
  match value v with
  | Const _ when term_equal v bbltn -> mpz_of_int 0
  | App (f, [b; v']) when term_equal f bbltc_s ->
    mp_add (bblt_len v') (mpz_of_int 1)
  | _ -> failwith "bblt_len"
             

let rec bblast_const v n =
  if mp_isneg n then
    match value v with
    | Const _ when term_equal v bvn -> bbltn
    | _ -> failwith "blast_const"
  else
    match value v with
    | App (f, [b; v']) when term_equal f bvc_s ->
      bbltc
        (match value b with
         | Const _ when term_equal b b0 -> tfalse
         | Const _ when term_equal b b1 -> ttrue
         | _ -> failwith "bblast_const")
        (bblast_const v' (mp_add n (mpz_of_int (-1))))
    | _ -> failwith "bblast_const"


let rec bblast_var x n =
  if mp_isneg n then bbltn
  else
    bbltc (bitof x n) (bblast_var x (mp_add n (mpz_of_int (-1))))


let rec bblast_concat x y =
  match value x with
  | Const _ when term_equal x bbltn ->
    (match value y with
     | App (f, [by; y']) when term_equal f bbltc_s ->
       bbltc by (bblast_concat x y')
     | Const _ when term_equal y bbltn -> bbltn
     | _ -> failwith "bblast_concat: wrong application")
  | App (f, [bx; x']) when term_equal f bbltc_s ->
    bbltc bx (bblast_concat x' y)
  | _ -> failwith "bblast_concat: wrong application"


let rec bblast_extract_rec x i j n =
  match value x with
  | App (f, [bx; x']) when term_equal f bbltc_s ->
    if mp_isneg (mpz_sub (mpz_sub j n) (mpz_of_int 1)) then
      if mp_isneg (mpz_sub (mpz_sub n i) (mpz_of_int 1)) then
        bbltc bx (bblast_extract_rec x' i j (mpz_sub n (mpz_of_int 1)))
      else bblast_extract_rec x' i j (mpz_sub n (mpz_of_int 1))
    else bbltn
  | Const _ when term_equal x bbltn -> bbltn
  | _ -> failwith "bblast_extract_rec: wrong application"


let bblast_extract x i j n = bblast_extract_rec x i j (mpz_sub n (mpz_of_int 1))


let rec extend_rec x i b =
  if mp_isneg i then x
  else bbltc b (extend_rec x (mpz_sub i (mpz_of_int 1)) b)


let bblast_zextend x i = extend_rec x (mpz_sub i (mpz_of_int 1)) tfalse


let bblast_sextend x i =
  match value x with
  | App (f, [xb; x']) when term_equal f bbltc_s ->
    extend_rec x (mpz_sub i (mpz_of_int 1)) xb
  | _ -> failwith "bblast_sextend"


let rec bblast_bvand x y =
  (* eprintf "bblast_bvand %a %a@." print_term x print_term y; *)
  match value x with
  | Const _ when term_equal x bbltn ->
    (match value y with
     | Const _ when term_equal y bbltn -> bbltn
     | _ -> failwith "bblast_bvand1")
  | App (f, [bx; x']) when term_equal f bbltc_s ->
    (match value y with
     | App (f, [by; y']) when term_equal f bbltc_s ->
       bbltc (and_ bx by) (bblast_bvand x' y') 
     | _ -> failwith "bblast_bvand2")
  | _ -> failwith "bblast_bvand3"
           

let rec bblast_bvnot x =
  match value x with
  | Const _ when term_equal x bbltn -> bbltn
  | App (f, [bx; x']) when term_equal f bbltc_s ->
    bbltc (not_ bx) (bblast_bvnot x')
  | _ -> failwith "bblast_bnot"


let rec bblast_bvor x y =
  match value x with
  | Const _ when term_equal x bbltn ->
    (match value y with
     | Const _ when term_equal y bbltn -> bbltn
     | _ -> failwith "bblast_bvor")
  | App (f, [bx; x']) when term_equal f bbltc_s ->
    (match value y with
     | App (f, [by; y']) when term_equal f bbltc_s ->
       bbltc (or_ bx by) (bblast_bvor x' y') 
     | _ -> failwith "bblast_bvor")
  | _ -> failwith "bblast_bvor"
           

let rec bblast_bvxor x y =
  match value x with
  | Const _ when term_equal x bbltn ->
    (match value y with
     | Const _ when term_equal y bbltn -> bbltn
     | _ -> failwith "bblast_bvxor")
  | App (f, [bx; x']) when term_equal f bbltc_s ->
    (match value y with
     | App (f, [by; y']) when term_equal f bbltc_s ->
       bbltc (xor_ bx by) (bblast_bvxor x' y') 
     | _ -> failwith "bblast_bvxor")
  | _ -> failwith "bblast_bvxor"


(*
;; return the carry bit after adding x y
;; FIXME: not the most efficient thing in the world
*)

let rec bblast_bvadd_carry a b carry =
  match value a with
  | Const _ when term_equal a bbltn ->
    (match value b with
     | Const _ when term_equal b bbltn -> carry
     | _ -> failwith "bblast_bvadd_carry")
  | App (f, [ai; a']) when term_equal f bbltc_s ->
    (match value b with
     | App (f, [bi; b']) when term_equal f bbltc_s ->
     (or_ (and_ ai bi) (and_ (xor_ ai bi) (bblast_bvadd_carry a' b' carry)))
     | _ -> failwith "bblast_bvadd_carry")
  | _ -> failwith "bblast_bvadd_carry"


let rec bblast_bvadd a b carry =
  match value a with
  | Const _ when term_equal a bbltn ->
    (match value b with
     | Const _ when term_equal b bbltn -> bbltn
     | _ -> failwith "bblast_bvadd")
  | App (f, [ai; a']) when term_equal f bbltc_s ->
    (match value b with
     | App (f, [bi; b']) when term_equal f bbltc_s ->
       bbltc
         (xor_ (xor_ ai bi) (bblast_bvadd_carry a' b' carry))
         (bblast_bvadd a' b' carry)
     | _ -> failwith "bblast_bvadd")
  | _ -> failwith "bblast_bvadd"
  

let rec bblast_zero n =
  if mp_iszero n then bbltn
  else bbltc tfalse (bblast_zero (mp_add n (mpz_of_int (-1))))


let bblast_bvneg x n = bblast_bvadd (bblast_bvnot x) (bblast_zero n) ttrue


let rec reverse_help x acc =
  match value x with
  | Const _ when term_equal x bbltn -> acc
  | App (f, [xi; x']) when term_equal f bbltc_s ->
    reverse_help x' (bbltc xi acc)
  | _ -> failwith "reverse_help"

let reverseb x = reverse_help x bbltn


let rec top_k_bits a k =
  if mp_iszero k then bbltn
  else match value a with
    | App (f, [ai; a']) when term_equal f bbltc_s ->
      bbltc ai (top_k_bits a' (mpz_sub k (mpz_of_int 1)))
    | _ -> failwith "top_k_bits"


let bottom_k_bits a k = reverseb (top_k_bits (reverseb a) k)


(* assumes the least signigicant bit is at the beginning of the list *)
let rec k_bit a k =
  if mp_isneg k then failwith "k_bit"
  else match value a with
    | App (f, [ai; a']) when term_equal f bbltc_s ->
      if mp_iszero k then ai else k_bit a' (mpz_sub k (mpz_of_int 1))
    | _ -> failwith "k_bit"


let rec and_with_bit a bt =
  match value a with
  | Const _ when term_equal a bbltn -> bbltn
  | App (f, [ai; a']) when term_equal f bbltc_s ->
    bbltc (and_ bt ai) (and_with_bit a' bt)
  | _ -> failwith "add_with_bit"
  

(*
;; a is going to be the current result
;; carry is going to be false initially
;; b is the and of a and b[k]
;; res is going to be bbltn initially
*)
let rec mult_step_k_h a b res carry k =
  match value a with
  | Const _ when term_equal a bbltn ->
    (match value b with
     | Const _ when term_equal b bbltn -> res
     | _ -> failwith "mult_step_k_h")
  | App (f, [ai; a']) when term_equal f bbltc_s ->
    (match value b with
     | App (f, [bi; b']) when term_equal f bbltc_s ->
       if mp_isneg (mpz_sub k (mpz_of_int 1)) then
         let carry_out = (or_ (and_ ai bi) (and_ (xor_ ai bi) carry)) in
         let curr = (xor_ (xor_ ai bi) carry) in
         mult_step_k_h a' b'
           (bbltc curr res) carry_out (mpz_sub k (mpz_of_int 1))
       else
         mult_step_k_h a' b (bbltc ai res) carry (mpz_sub k (mpz_of_int 1))
     | _ -> failwith "mult_step_k_h")
  | _ -> failwith "mult_step_k_h"



(*  assumes that a, b and res have already been reversed *)
let rec mult_step a b res n k =
  let k' = mpz_sub n k in
  let ak = top_k_bits a k' in
  let b' = and_with_bit ak (k_bit b k) in
  if mp_iszero (mpz_sub k' (mpz_of_int 1)) then
    mult_step_k_h res b' bbltn tfalse k
  else
    let res' = mult_step_k_h res b' bbltn tfalse k in
    mult_step a b (reverseb res') n (mp_add k (mpz_of_int 1))


let bblast_bvmul a b n =
  let ar = reverseb a in (* reverse a and b so that we can build the circuit *)
  let br = reverseb b in (* from the least significant bit up *)
  let res = and_with_bit ar (k_bit br (mpz_of_int 0)) in
  if mp_iszero (mpz_sub n (mpz_of_int 1)) then res
  else
    (* if multiplying 1 bit numbers no need to call mult_step *)
    mult_step ar br res n (mpz_of_int 1)

  
(*
; bit blast  x = y
; for x,y of size n, it will return a conjuction (x.0 = y.0 ^ ( ... ^ (x.{n-1} = y.{n-1})))
; f is the accumulator formula that builds the equality in the right order
*)
let rec bblast_eq_rec x y f =
  match value x with
  | Const _ when term_equal x bbltn ->
    (match value y with
     | Const _ when term_equal x bbltn -> f
     | _ -> failwith "bblast_eq_rec")
  | App (ff, [fx; x']) when term_equal ff bbltc_s ->
    (match value y with
     | App (ff, [fy; y']) when term_equal ff bbltc_s ->
       bblast_eq_rec x' y' (and_ (iff_ fx fy) f)
     | _ -> failwith "bblast_eq_rec")
  | _ -> failwith "bblast_eq_rec"



let bblast_eq x y =
  match value x with
  | App (ff, [bx; x']) when term_equal ff bbltc_s ->
    (match value y with
     | App (ff, [by; y']) when term_equal ff bbltc_s ->
       bblast_eq_rec x' y' (iff_ bx by)
     | _ -> failwith "bblast_eq")
  | _ -> failwith "bblast_eq"


let rec bblast_bvult x y n =
  match value x with
  | App (ff, [xi; x']) when term_equal ff bbltc_s ->
    (match value y with
     | App (ff, [yi; y']) when term_equal ff bbltc_s ->
       if mp_iszero n then (and_ (not_ xi) yi)
       else (or_ (and_ (iff_ xi yi)
                    (bblast_bvult x' y' (mp_add n (mpz_of_int (-1)))))
               (and_ (not_ xi) yi))
     | _ -> failwith "bblast_bvult")
  | _ -> failwith "bblast_bvult"


let rec bblast_bvslt x y n =
  match value x with
  | App (ff, [xi; x']) when term_equal ff bbltc_s ->
    (match value y with
     | App (ff, [yi; y']) when term_equal ff bbltc_s ->
       if mp_iszero (mpz_sub n (mpz_of_int 1)) then (and_ xi (not_ yi))
       else (or_ (and_ (iff_ xi yi)
                    (bblast_bvult x' y' (mpz_sub n (mpz_of_int 2))))
               (and_ xi (not_ yi)))
     | _ -> failwith "bblast_bvslt")
  | _ -> failwith "bblast_bvslt"


let rec mk_ones n =
  if mp_iszero n then bvn
  else bvc b1 (mk_ones (mpz_sub n (mpz_of_int 1)))


let rec mk_zero n =
  if mp_iszero n then bvn
  else bvc b0 (mk_zero (mpz_sub n (mpz_of_int 1)))





(** Registering callbacks for side conditions *)


let () =
  List.iter (fun (s, f) -> Hashtbl.add callbacks_table s f)
    [

      "append",
      (function
        | [c1; c2] -> append c1 c2
        | _ -> failwith "append: Wrong number of arguments");

      "simplify_clause",
      (function
        | [c] -> simplify_clause c
        | _ -> failwith "simplify_clause: Wrong number of arguments");

      "bv_constants_are_disequal",
      (function
        | [x; y] -> bv_constants_are_disequal x y
        | _ -> failwith "bv_constants_are_disequal: Wrong number of arguments");

      "bblt_len",
      (function
        | [v] -> bblt_len v
        | _ -> failwith "bblt_len: Wrong number of arguments");

      "bblast_const",
      (function
        | [v; n] -> bblast_const v n
        | _ -> failwith "bblast_const: Wrong number of arguments");

      "bblast_var",
      (function
        | [v; n] -> bblast_var v n
        | _ -> failwith "bblast_var: Wrong number of arguments");
      
      "bblast_concat",
      (function
        | [x; y] -> bblast_concat x y
        | _ -> failwith "bblast_concat: Wrong number of arguments");

      "bblast_extract",
      (function
        | [x; i; j; n] -> bblast_extract x i j n
        | _ -> failwith "bblast_extract: Wrong number of arguments");

      "bblast_zextend",
      (function
        | [x; i] -> bblast_zextend x i
        | _ -> failwith "bblast_zextend: Wrong number of arguments");

      "bblast_sextend",
      (function
        | [x; i] -> bblast_sextend x i
        | _ -> failwith "bblast_sextend: Wrong number of arguments");

      "bblast_bvand",
      (function
        | [x; y] -> bblast_bvand x y
        | _ -> failwith "bblast_bvand: Wrong number of arguments");

      "bblast_bvnot",
      (function
        | [x] -> bblast_bvnot x
        | _ -> failwith "bblast_bvnot: Wrong number of arguments");

      "bblast_bvor",
      (function
        | [x; y] -> bblast_bvor x y
        | _ -> failwith "bblast_bvor: Wrong number of arguments");

      "bblast_bvxor",
      (function
        | [x; y] -> bblast_bvxor x y
        | _ -> failwith "bblast_bvxor: Wrong number of arguments");

      "bblast_bvadd",
      (function
        | [x; y; c] -> bblast_bvadd x y c
        | _ -> failwith "bblast_bvadd: Wrong number of arguments");

      "bblast_zero",
      (function
        | [n] -> bblast_zero n
        | _ -> failwith "bblast_zero: Wrong number of arguments");

      "bblast_bvneg",
      (function
        | [v; n] -> bblast_bvneg v n
        | _ -> failwith "bblast_bvneg: Wrong number of arguments");

      "bblast_bvmul",
      (function
        | [x; y; n] -> bblast_bvmul x y n
        | _ -> failwith "bblast_bvmul: Wrong number of arguments");

      "bblast_eq",
      (function
        | [x; y] -> bblast_eq x y
        | _ -> failwith "bblast_eq: Wrong number of arguments");

      "bblast_bvult",
      (function
        | [x; y; n] -> bblast_bvult x y n
        | _ -> failwith "bblast_bvult: Wrong number of arguments");

      "bblast_bvslt",
      (function
        | [x; y; n] -> bblast_bvslt x y n
        | _ -> failwith "bblast_bvslt: Wrong number of arguments");

    ]

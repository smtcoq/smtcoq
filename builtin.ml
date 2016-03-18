open Ast
open Format

let declare_get s ty =
  mk_declare s ty;
  mk_const s

let pi n ty t =
  let s = mk_symbol n ty in
  register_symbol s;
  let pi_abstr = mk_pi s (Lazy.force t) in
  remove_symbol s;
  pi_abstr


let bool_lfsc = declare_get "bool" lfsc_type
let tt = declare_get "tt" bool_lfsc
let ff = declare_get "ff" bool_lfsc

let var = declare_get "var" lfsc_type
let lit = declare_get "lit" lfsc_type
let clause = declare_get "clause" lfsc_type
let cln = declare_get "cln" clause

let pos_s = declare_get "pos" (pi "x" var (lazy lit))
let neg_s = declare_get "neg" (pi "x" var (lazy lit))
let clc_s = declare_get "clc" (pi "x" lit (lazy (pi "c" clause (lazy clause))))

let concat_s = declare_get "concat"
    (pi "c1" clause (lazy (pi "c2" clause (lazy clause))))

let clr_s = declare_get "clr" (pi "l" lit (lazy (pi "c" clause (lazy clause))))



let pos v = mk_app pos_s [v] 
let neg v = mk_app neg_s [v] 
let clc x c = mk_app clc_s [x; c]
let clr l c = mk_app clr_s [l; c]
let concat c1 c2 = mk_app concat_s [c1; c2]


module Int = struct
  type t = int
  let compare = Pervasives.compare
end

module Term = struct
  type t = term
  let compare = compare_term
end

module MInt = Map.Make (Int)
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
(* let ifmarked5 = if_marked_do 5 *)
(* let ifmarked6 = if_marked_do 6 *)
(* let ifmarked7 = if_marked_do 7 *)
(* let ifmarked8 = if_marked_do 8 *)
(* let ifmarked9 = if_marked_do 9 *)
(* let ifmarked10 = if_marked_do 10 *)
(* let ifmarked11 = if_marked_do 11 *)
(* let ifmarked12 = if_marked_do 12 *)
(* let ifmarked13 = if_marked_do 13 *)
(* let ifmarked14 = if_marked_do 14 *)
(* let ifmarked14 = if_marked_do 15 *)
(* let ifmarked16 = if_marked_do 16 *)
(* let ifmarked17 = if_marked_do 17 *)
(* let ifmarked18 = if_marked_do 18 *)
(* let ifmarked19 = if_marked_do 19 *)
(* let ifmarked20 = if_marked_do 20 *)
(* let ifmarked21 = if_marked_do 21 *)
(* let ifmarked22 = if_marked_do 22 *)
(* let ifmarked23 = if_marked_do 23 *)
(* let ifmarked24 = if_marked_do 24 *)
(* let ifmarked25 = if_marked_do 25 *)
(* let ifmarked26 = if_marked_do 26 *)
(* let ifmarked27 = if_marked_do 27 *)
(* let ifmarked28 = if_marked_do 28 *)
(* let ifmarked29 = if_marked_do 29 *)
(* let ifmarked30 = if_marked_do 30 *)
(* let ifmarked31 = if_marked_do 31 *)
(* let ifmarked32 = if_marked_do 32 *)

let markvar m v = markvar_with 1 m v
let markvar1 m v = markvar m v
let markvar2 m v = markvar_with 2 m v
let markvar3 m v = markvar_with 3 m v
let markvar4 m v = markvar_with 4 m v 
(* let markvar5 = markvar_with 5 *)
(* let markvar6 = markvar_with 6 *)
(* let markvar7 = markvar_with 7 *)
(* let markvar8 = markvar_with 8 *)
(* let markvar9 = markvar_with 9 *)
(* let markvar10 = markvar_with 10 *)
(* let markvar11 = markvar_with 11 *)
(* let markvar12 = markvar_with 12 *)
(* let markvar13 = markvar_with 13 *)
(* let markvar14 = markvar_with 14 *)
(* let markvar14 = markvar_with 15 *)
(* let markvar16 = markvar_with 16 *)
(* let markvar17 = markvar_with 17 *)
(* let markvar18 = markvar_with 18 *)
(* let markvar19 = markvar_with 19 *)
(* let markvar20 = markvar_with 20 *)
(* let markvar21 = markvar_with 21 *)
(* let markvar22 = markvar_with 22 *)
(* let markvar23 = markvar_with 23 *)
(* let markvar24 = markvar_with 24 *)
(* let markvar25 = markvar_with 25 *)
(* let markvar26 = markvar_with 26 *)
(* let markvar27 = markvar_with 27 *)
(* let markvar28 = markvar_with 28 *)
(* let markvar29 = markvar_with 29 *)
(* let markvar30 = markvar_with 30 *)
(* let markvar31 = markvar_with 31 *)
(* let markvar32 = markvar_with 32 *)


(*******************)
(* Side conditions *)
(*******************)

let rec append c1 c2 =
  match c1.value with
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
  match c.value with
  | Const _ when term_equal c cln -> cln, mark_map

  | App(f, [l; c1]) when term_equal f clc_s ->

    begin match l.value with
      (* Set mark 1 on v if it is not set, to indicate we should remove it.
         After processing the rest of the clause, set mark 3 if we were already
         supposed to remove v (so if mark 1 was set when we began).  Clear mark3
         if we were not supposed to be removing v when we began this call. *)

      | App (f, [v]) when term_equal f pos_s ->

        let m, mark_map = ifmarked mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar mark_map v) in

        let c', mark_map = simplify_clause mark_map c1 in

        begin match m.value with
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

          | _ -> failwith "Match failure"
        end


      | App (f, [v]) when term_equal f neg_s ->

        let m, mark_map = ifmarked2 mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar2 mark_map v) in

        let c', mark_map = simplify_clause mark_map c1 in

        begin match m.value with
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

          | _ -> failwith "Match failure"
        end

      | _ -> failwith "Match failure"

    end

  | App(f, [c1; c2]) when term_equal f concat_s ->
    let new_c1, mark_map = simplify_clause mark_map c1 in
    let new_c2, mark_map = simplify_clause mark_map c2 in
    append new_c1 new_c2, mark_map

  | App(f, [l; c1]) when term_equal f clr_s ->

    begin match l.value with
      (* set mark 1 to indicate we should remove v, and fail if
         mark 3 is not set after processing the rest of the clause
         (we will set mark 3 if we remove a positive occurrence of v). *)

      | App (f, [v]) when term_equal f pos_s ->

        let m, mark_map = ifmarked mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar mark_map v) in

        let m3, mark_map = ifmarked3 mark_map v
            (fun mark_map -> tt, markvar3 mark_map v)
            (fun mark_map -> ff, mark_map) in

        let c', mark_map = simplify_clause mark_map c1 in

        let mark_map = ifmarked3 mark_map v
            (fun mark_map ->
               let mark_map = match m3.value with
                 | Const _ when term_equal m3 tt -> mark_map
                 | Const _ when term_equal m3 ff -> markvar3 mark_map v
                 | _ -> failwith "Match failure"
               in
               let mark_map = match m.value with
                 | Const _ when term_equal m tt -> mark_map
                 | Const _ when term_equal m ff -> markvar mark_map v
                 | _ -> failwith "Match failure"
               in
               mark_map
            )
            (fun _ -> failwith "Match failure")
        in

        c', mark_map

      | App (f, [v]) when term_equal f neg_s ->

        let m2, mark_map = ifmarked2 mark_map v
            (fun mark_map -> tt, mark_map)
            (fun mark_map -> ff, markvar2 mark_map v) in

        let m4, mark_map = ifmarked4 mark_map v
            (fun mark_map -> tt, markvar4 mark_map v)
            (fun mark_map -> ff, mark_map) in

        let c', mark_map = simplify_clause mark_map c1 in

        let mark_map = ifmarked4 mark_map v
            (fun mark_map ->
               let mark_map = match m4.value with
                 | Const _ when term_equal m4 tt -> mark_map
                 | Const _ when term_equal m4 ff -> markvar4 mark_map v
                 | _ -> failwith "Match failure"
               in
               let mark_map = match m2.value with
                 | Const _ when term_equal m2 tt -> mark_map
                 | Const _ when term_equal m2 ff -> markvar2 mark_map v
                 | _ -> failwith "Match failure"
               in
               mark_map
            )
            (fun _ -> failwith "Match failure")
        in

        c', mark_map

      | _ -> failwith "Match failure"

    end

  | _ -> failwith "Match failure"



let simplify_clause c =
  let c', _ = simplify_clause empty_marks c in
  c'



let callbacks_table =
  let h = Hashtbl.create 7 in
  List.iter (fun (s, f) -> Hashtbl.add h s f)
    [

      "append",
      (function
        | [c1; c2] -> append c1 c2
        | _ -> failwith "append: Wrong number of arguments");

      "simplify_clause",
      (function
        | [c] -> simplify_clause c
        | _ -> failwith "simplify_clause: Wrong number of arguments");

    ];
  h


let callback name l =
  try
    let f = Hashtbl.find callbacks_table name in
    f l
  with Not_found ->
    failwith ("No side condition for " ^ name)


let check_side_condition name l expected =
  if not (term_equal (callback name l) expected) then
    failwith ("Side condition " ^ name ^ " failed")



(* For testing *)

let v1 = declare_get "v1" var
let v2 = declare_get "v2" var
let v3 = declare_get "v3" var

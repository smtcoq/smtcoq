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


let bool_lfsc = declare_get "bool_lfsc" lfsc_type
let tt = declare_get "tt" bool_lfsc
let ff = declare_get "ff" bool_lfsc

let var = declare_get "var" lfsc_type
let lit = declare_get "lit" lfsc_type
let clause = declare_get "clause" lfsc_type
let cln = declare_get "cln" clause

let okay = declare_get "okay" lfsc_type
let ok = declare_get "ok" okay

let pos_s = declare_get "pos" (pi "x" var (lazy lit))
let neg_s = declare_get "neg" (pi "x" var (lazy lit))
let clc_s = declare_get "clc" (pi "x" lit (lazy (pi "c" clause (lazy clause))))

let concat_s = declare_get "concat_cl"
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

let markvar m v = markvar_with 1 m v
let markvar1 m v = markvar m v
let markvar2 m v = markvar_with 2 m v
let markvar3 m v = markvar_with 3 m v
let markvar4 m v = markvar_with 4 m v 


(*******************)
(* Side conditions *)
(*******************)

(* follow pointers *)

let rec deref t = match t.value with
  | Ptr t -> deref t
  | _ -> t

let value t = (deref t).value
                

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

  | App(f, [c1; c2]) when term_equal f concat_s ->
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

let lit_term l =
  match l.value with
    | App (p, [x]) when term_equal p pos_s -> x
    | App (p, [x]) when term_equal p neg_s -> x
    | _ -> failwith "No match found"
    

(**
(program eqvar ((v1 var) (v2 var)) bool
  (do (markvar v1)
    (let s (ifmarked v2 tt ff)
  (do (markvar v1) s))))
**)

let eqvar mark_map v1 v2 = 
  let mark_map = markvar mark_map v1 in
    let s, mark_map = (ifmarked mark_map v2
      (fun mark_map -> tt, mark_map)
      (fun mark_map -> ff, mark_map)) in
        let mark_map = markvar mark_map v1 in
          s, mark_map 
            
let eqvar v1 v2 =
  let c', _ = eqvar empty_marks v1 v2 in
  c'  
  

(**
(program eqlit ((l1 lit) (l2 lit)) bool
(match l1 (
  (pos v1)
    (match l2
      ((pos v2) (eqvar v1 v2))
      ((neg v2) ff)))
  ((neg v1)
    (match l2
      ((pos v2) ff)
      ((neg v2) (eqvar v1 v2))))))

let eqlit l1 l2 =
  match l1.value with
    | App (p1, [v1]) when term_equal p1 pos_s -> (
    match l2.value with
      | App (p2, [v2]) when term_equal p2 pos_s -> term_equal v1 v2
      | App (n2, [v2]) when term_equal n2 neg_s -> false
    )
    | App (n1, [v1]) when term_equal n1 neg_s -> (
    match l2.value with
      | App (p3, [v2]) when term_equal p3 pos_s -> false
      | App (n3, [v2]) when term_equal n3 neg_s -> term_equal v1 v2
    )
**)
    
let eqlit l1 l2 =
  match l1.value with
    | App (p1, [v1]) when term_equal p1 pos_s -> (
    match l2.value with
      | App (p2, [v2]) when term_equal p2 pos_s -> eqvar v1 v2
      | App (n2, [v2]) when term_equal n2 neg_s -> ff
    )
    | App (n1, [v1]) when term_equal n1 neg_s -> (
    match l2.value with
      | App (p3, [v2]) when term_equal p3 pos_s -> ff
      | App (n3, [v2]) when term_equal n3 neg_s -> eqvar v1 v2
    )



(**
(program in ((l lit) (c clause)) Ok
(match c
  ((clc l' c')
    (match (eqlit l l')
      (tt ok) (ff (in l c'))))
(cln (fail Ok)))
)
**)

let rec includes l c =
  match c.value with
    | App (f, [l'; c']) when term_equal f clc_s -> (
    let u = eqlit l l' in
      match u.value with
        | Const _ when term_equal u tt -> ok
        | Const _ when term_equal u ff -> (includes l c')
    )
    | Const _ when term_equal c cln -> failwith "Not found"

(**
(program remove ((l lit) (c clause)) clause
(match c
  (cln cln)
  ((clc l' c') 
    (let u (remove l c')
      (match (eqlit l l')
        (tt u)
        (ff (clc l' u)))))))
**)

let rec remove l c =
  match c.value with
    | Const _ when term_equal c cln -> cln
    | App (f, [l'; c']) when term_equal f clc_s -> (
    let u = remove l c' in
      let v = eqlit l l' in
        match v.value with
          | Const _ when term_equal v tt -> u
          | Const _ when term_equal v ff -> clc l' u
    )




(**
(program dropdups ((c1 clause)) clause
(match c1 
  (cln cln)
  ((clc l c1’)
    (let v (litvar l) (ifmarked v (dropdups c1’) (do (markvar v) (let r (clc l (dropdups c1’)) (do (markvar v) r)))))
  )))
**)


let rec dropdups mark_map c1 =
  match c1.value with
    | Const _ when term_equal c1 cln -> cln, mark_map
    | App (f, [l; c1']) when term_equal f clc_s -> 
    (   
        let v = lit_term l in 
          (ifmarked mark_map v
            (fun mark_map -> dropdups mark_map c1')
            (fun mark_map ->
            let mark_map = markvar mark_map v in
            let d, mark_map = dropdups mark_map c1' in
            let r = clc l d in
            let mark_map = markvar mark_map v in
            r, mark_map))
     )
     

let dropdups c =
  let c', _ = dropdups empty_marks c in
  c'

     
(**
(program resolve ((c1 clause) (c2 clause) (v var)) clause
  (let pl (pos v) (let nl (neg v)
    (do (in pl c1) (in nl c2) 
      (let d (append (remove pl c1) (remove nl c2))
(drop_dups d)))))) 
**)

let resolve mark_map c1 c2 v =
  let pl = pos v in
    let nl = neg v in
      (includes pl c1); (includes nl c2);
	  let d = append (remove pl c1) (remove nl c2) in
	    dropdups d

let resolve c1 c2 v =
  let c' = resolve empty_marks c1 c2 v in
  c';;
  
  
(* For testing *)

let v1 = declare_get "v1" var
let v2 = declare_get "v2" var
let v3 = declare_get "v3" var

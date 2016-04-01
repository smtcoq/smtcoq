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

open Format
open Ast
open Builtin


module MTerm = Map.Make (Term)
module HT = Hashtbl.Make (Term)
module HCl = Hashtbl.Make (struct
    type t = term list
    let equal c1 c2 = compare_term_list c1 c2 = 0
    let hash = List.fold_left (fun acc t -> Term.hash t + acc) 0 
  end)


let fmt = std_formatter

let clauses_ids = HCl.create 201
let ids_clauses = Hashtbl.create 201
let propvars = HT.create 201
let sharp_tbl = HT.create 13

let cpt = ref 0
let cl_cpt = ref 0



let value t = (deref t).value


let rec name c = match value c with
  | Const {sname=Name n} -> Some n
  | _ -> None


let rec app_name r = match value r with
  | App ({value=Const{sname=Name n}}, args) -> Some (n, args)
  | _ -> None



let smt2_of_lfsc = function
  | "iff" -> "="
  | "ifte" -> "ite"
  | "flet" -> "let"
  | "impl" -> "=>"
  | t -> t


let rec print_apply fmt t = match app_name t with
  | Some ("apply", [_; _; f; a]) ->
    fprintf fmt "%a %a" print_apply f print_term a
  | _ -> print_term fmt t
  

and print_term fmt t =
  try HT.find sharp_tbl t |> fprintf fmt "#%d"
  with Not_found ->
    match name t with
    | Some n -> pp_print_string fmt (smt2_of_lfsc n)
    | None -> match app_name t with

      | Some ("=", [ty; a; b]) ->
        let eqt = match value t with App (eqt, _ ) -> eqt | _ -> assert false in
        incr cpt;
        let eq_b_a = mk_app eqt [ty; b; a] in
        HT.add sharp_tbl t !cpt;
        HT.add sharp_tbl eq_b_a !cpt;
        (* let a, b = if compare_term a b <= 0 then a, b else b, a in *)
        fprintf fmt "#%d:(= %a %a)" !cpt print_term a print_term b


      | Some ("not", [a]) -> fprintf fmt "(not %a)" print_term a
                               
      | Some ("apply", _) ->
        incr cpt;
        HT.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(%a)" !cpt print_apply t

      | Some ("p_app", [a]) -> print_term fmt a

      | Some (n, l) ->
        let n = smt2_of_lfsc n in
        incr cpt;
        HT.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(%s%a)" !cpt n
          (fun fmt -> List.iter (fprintf fmt " %a" print_term)) l

      | _ -> assert false

let print_term fmt t = print_term fmt (get_real t) (* TODO not great *)


(* let print_term = Ast.print_term *)


let rec print_clause elim_or fmt t = match name t with
  | Some "cln" | Some "false" -> ()
  | Some n -> pp_print_string fmt (smt2_of_lfsc n)
  | None ->
    match app_name t with
    | Some ("pos", [v]) ->
      let t = HT.find propvars (deref v) in
      fprintf fmt "%a" print_term t
    | Some ("neg", [v]) ->
      let t = HT.find propvars (deref v) in
      fprintf fmt "(not %a)" print_term t
    | Some ("clc", [a; cl]) ->
      fprintf fmt "%a %a" (print_clause elim_or) a (print_clause elim_or) cl
    | Some ("or", [a; b]) when elim_or ->
      fprintf fmt "%a %a" (print_clause elim_or) a (print_clause elim_or) b
    | _ -> fprintf fmt "%a" print_term t


let print_clause_elim_or fmt t = fprintf fmt "(%a)" (print_clause true) t

let print_clause fmt t = fprintf fmt "(%a)" (print_clause false) t
  

let rec to_clause acc t = match name t with
  | Some "cln" | Some "false" -> acc
  | Some n -> t :: acc
  | None ->
    match app_name t with
    | Some ("pos", [v]) ->
      let t = HT.find propvars (deref v) in
      t :: acc
    | Some ("neg", [v]) ->
      let t = HT.find propvars (deref v) |> not_ in
      t :: acc
    | Some ("clc", [a; cl]) ->
      to_clause (to_clause acc a) cl
    | Some ("or", [a; b]) ->
      to_clause (to_clause acc a) b
    | _ -> t :: acc


let to_clause = to_clause [] 


let rec print_clause fmt = function
  | [] -> ()
  | [t] -> print_term fmt t
  | t :: cl -> fprintf fmt "%a %a" print_term t print_clause cl

let print_clause fmt = fprintf fmt "(%a)" print_clause


let th_res p = match app_name (deref p).ttype with
  | Some ("th_holds", [r]) -> r
  | _ -> assert false


type clause_res_id = NewCl of int | OldCl of int


let register_clause_id cl id =
  HCl.add clauses_ids cl id;
  Hashtbl.add ids_clauses id cl


let register_termclause_id t id =
  register_clause_id (to_clause t) id



let new_clause_id ?(reuse=true) cl =
  let cl = List.map get_real cl in (* KLUDGE: bleh *)
  try
    if not reuse then raise Not_found;
    OldCl (HCl.find clauses_ids cl)
  with Not_found ->
    (* eprintf "new clause : [%a]@." (fun fmt -> List.iter (fprintf fmt "%a, " Ast.print_term)) cl; *)
    incr cl_cpt;
    let id = !cl_cpt in
    register_clause_id cl id;
    NewCl id


let new_termclause_id ?(reuse=true) t =
  let cl = to_clause t in
  new_clause_id ~reuse cl


let rec ignore_all_decls p = match value p with
  | Lambda (s, p) -> ignore_all_decls p
  | _ -> p


let rec ignore_decls p = match value p with
  | Lambda (s, p) ->
    (match s.sname with
     | Name n when n.[0] = 'A' -> p
     | _ -> ignore_decls p
    )
  | _ -> p


let rec ignore_preproc p = match app_name p with
  | Some ("th_let_pf", [_; _; p]) ->
    begin match value p with
      | Lambda (_, p) -> ignore_preproc p
      | _ -> assert false
    end
  | _ -> p


let rec produce_inputs_preproc p = match app_name p with
  | Some ("th_let_pf", [_; _; p]) ->
    begin match value p with
      | Lambda ({sname = Name h; stype}, p) ->
        begin match app_name stype with
          | Some ("th_holds", [formula]) ->
            (match new_clause_id [formula] with
             | NewCl id ->
               register_termclause_id formula id;
               fprintf fmt "%d:(input (%a))@." id print_term formula
             | OldCl _ -> ()
            );
            produce_inputs_preproc p
          | _ -> assert false
        end
      | _ -> assert false
    end
  | _ -> p


let rec produce_inputs p = match value p with
  | Lambda (s, p) ->
    begin match app_name s.stype with
      | Some ("th_holds", [formula])
        when (match name formula with Some "true" -> false | _ -> true)
        ->
        (match new_clause_id [formula] with
         | NewCl id ->
           register_termclause_id formula id;
           fprintf fmt "%d:(input (%a))@." id print_term formula
         | OldCl _ -> ()
        );
        produce_inputs p
      | _ -> produce_inputs p
    end
  | _ -> p



    

let rec register_prop_vars p = match app_name p with
  | Some ("decl_atom", [formula; p]) ->
    begin match value p with
      | Lambda (v, p) ->
        HT.add propvars (symbol_to_const v) formula;
        begin match value p with
          | Lambda (_, p) -> register_prop_vars p
          | _ -> assert false
        end
      | _ -> assert false
    end
  | _ -> p
    





let rec trim_junk_satlem p = match app_name p with
  | Some (("asf"|"ast"), [_; _; _; _; p]) ->
    begin match value p with
      | Lambda (_, p) -> trim_junk_satlem p
      | _ -> assert false
    end

  | Some ("clausify_false", [p]) -> trim_junk_satlem p
                                      
  | Some ("contra", [_; p1; p2]) ->
    begin match name p1, name p2 with
      | None, Some _ -> trim_junk_satlem p1
      | Some _, None -> trim_junk_satlem p2
      | Some _, Some _ -> trim_junk_satlem p2
      | _ -> assert false
    end

  | _ -> p



type howtores = Keep | Reso of term * term * term


let rec generic_clause_elim p = match app_name p with
  | Some (("or_elim_1"|"or_elim_2"), [_; _; _; p]) -> generic_clause_elim p

  | Some ("impl_elim", [_; _; r]) ->
    to_clause (th_res p), "implies", r

  | Some ("not_and_elim", [_; _; r]) ->
    to_clause (th_res p), "not_and", r

  | _ -> to_clause (th_res p), "or", p

  

let rec cnf_conversion p = match app_name p with
  
  | Some ("and_elim_1", [_; _; r]) ->
    begin match app_name r with

      | Some ("not_impl_elim", [_; _; w]) ->
        let arg_id = cnf_conversion w in
        let cl = [th_res p] in
        (match new_clause_id cl with
         | NewCl id ->
           fprintf fmt "%d:(not_implies1 %a %d)@." id print_clause cl arg_id;
           id
         | OldCl id -> id)

      | Some ("not_or_elim", [_; _; w]) ->
        let arg_id = cnf_conversion w in
        let cl = [th_res p] in
        (match new_clause_id cl with
         | NewCl id ->
           fprintf fmt "%d:(not_or %a %d 0)@." id print_clause cl arg_id;
           id
         | OldCl id -> id)
           
      | _ ->
        let arg_id = cnf_conversion r in
        if arg_id <> -1 then
          let cl = [th_res p] in
          match new_clause_id cl with
          | NewCl id ->
            fprintf fmt "%d:(and %a %d 0)@." id print_clause cl arg_id;
            id
          | OldCl id -> id

        else
          let cl = [not_ (th_res r); th_res p] in
          match new_clause_id cl with
          | NewCl id ->
            fprintf fmt "%d:(and_pos %a 0)@." id print_clause cl;
            id
          | OldCl id -> id

    end

  | Some ("and_elim_2", [_; _; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [_; _; w]) ->
        let arg_id = cnf_conversion w in
        let cl = [th_res p] in
        (match new_clause_id cl with
         | NewCl id ->
           fprintf fmt "%d:(not_implies2 %a %d)@." id print_clause cl arg_id;
           id
         | OldCl id -> id)
        
      | Some ("not_or_elim", [_; _; w]) ->
        let arg_id = cnf_conversion w in
        let cl = [th_res p] in
        (match new_clause_id cl with
         | NewCl id ->
           fprintf fmt "%d:(not_or %a %d 1)@." id print_clause cl arg_id;
           id
         | OldCl id -> id)

      | _ ->
        let arg_id = cnf_conversion r in
        if arg_id <> -1 then
          let cl = [th_res p] in
          match new_clause_id cl with
          | NewCl id ->
            fprintf fmt "%d:(and %a %d 1)@." id print_clause cl arg_id;
            id
          | OldCl id -> id
        else
          let cl = [not_ (th_res r); th_res p] in
          match new_clause_id cl with
          | NewCl id ->
            fprintf fmt "%d:(and_pos %a 1)@." id print_clause cl;
            id
          | OldCl id -> id

    end

  | Some (("or_elim_1"|"or_elim_2"|"impl_elim"|"not_and_elim"), _) ->

    let cl, rule, r = generic_clause_elim p in
    let arg_id = cnf_conversion r in
    (match rule, Hashtbl.find ids_clauses arg_id with
      | _, [] -> assert false
      | "not_and", na :: ( _::_ as r) ->
        let a = match app_name na with Some ("not",[a]) -> a | _ -> not_ na in
        let cltmp = a :: cl in
        let clres = cl @ r in
        let tmpid = match new_clause_id cltmp with
          | NewCl id ->
            fprintf fmt "%d:(and_neg %a)@." id print_clause cltmp; id
          | OldCl id -> id in
        (match new_clause_id clres with
          | NewCl id ->
            fprintf fmt "%d:(resolution %a %d %d)@."
              id print_clause clres tmpid arg_id;
            id
          | OldCl id -> id)
      | _ ->
        match new_clause_id ~reuse:false cl with
        | NewCl id ->
          fprintf fmt "%d:(%s %a %d)@." id rule print_clause cl arg_id;
          id
        | OldCl id -> assert false
    )

  | Some (("symm"|"negsymm"), [_; _; _; r]) ->
    let id = cnf_conversion r in
    id
    (* let cl = [th_res p] in *)
    (* if id <> -1 then register_clause_id cl id; *)
    (* id *)
      
    (* ignore symmetry of equality rules *)
    (* (match new_clause_id cl with *)
    (*  | NewCl id -> *)
    (*    fprintf fmt "%d:(eq_symmetry %a %d)@." id print_clause cl aid; *)
    (*    id *)
    (*  | OldCl id -> id) *)

  | Some (("pred_eq_t"|"pred_eq_f"), [_; r]) ->
    cnf_conversion r
    (* let cl = th_res p in *)
    (* if id <> -1 then register_clause_id cl id; *)
    (* id *)

  | Some ("trans", [_; _; _; z; p_x_eq_y; p_y_eq_z]) ->

    begin match name z with
    | Some ("t_true"|"t_false") ->
      let id1 = cnf_conversion p_x_eq_y in
      (* let id2 = cnf_conversion p_y_eq_z in *)
      let cl = [th_res p] in
      if id1 <> -1 then register_clause_id cl id1;
      (* if id2 <> -1 then register_clause_id cl id2; *)
      (* if id1 <> -1 || id2 <> -1 then -1 else *)
      id1

    | _ ->
      let id1 = cnf_conversion p_x_eq_y in
      let id2 = cnf_conversion p_y_eq_z in
      let x_eq_y = th_res p_x_eq_y in
      let y_eq_z = th_res p_y_eq_z in
      let x_eq_z = th_res p in

      let cl = [not_ x_eq_y; not_ y_eq_z; x_eq_z] in
      let id3 = match new_clause_id ~reuse:true cl with
        | NewCl id ->
          fprintf fmt "%d:(eq_transitive %a)@." id print_clause cl;
          id
        | OldCl id -> id
      in

      (match id1, id2 with
       | -1, -1 -> id3
       | -1, _ ->
         (let clres = match List.rev (Hashtbl.find ids_clauses id2) with
            | [] -> assert false
            | [_] -> [not_ x_eq_y; x_eq_z]
            | _ :: r -> List.rev (x_eq_z :: not_ x_eq_y :: r)
          in
          match new_clause_id clres with
          | NewCl id ->
            fprintf fmt "%d:(resolution %a %d %d)@."
              id print_clause clres id2 id3;
            id (* -1 *)
          | OldCl id -> id (* -1 *))
       | _, -1 ->
         (let clres = match List.rev (Hashtbl.find ids_clauses id1) with
            | [] -> assert false
            | [_] -> [not_ y_eq_z; x_eq_z]
            | _ :: r -> List.rev (x_eq_z :: not_ y_eq_z :: r)
          in
          match new_clause_id clres with
          | NewCl id ->
            fprintf fmt "%d:(resolution %a %d %d)@."
              id print_clause clres id1 id3;
            id (* -1 *)
          | OldCl id -> id (* -1 *))
       | _ ->
         let clres =
           match List.rev (Hashtbl.find ids_clauses id1),
                 List.rev (Hashtbl.find ids_clauses id2) with
           | [], _ | _, [] -> assert false
           | [_], [_] -> [x_eq_z]
           | _ :: r, [_] -> List.rev (x_eq_z :: r)
           | [_], _ :: r -> List.rev (x_eq_z :: r)
           | _ :: r1, _ :: r2 -> List.rev (x_eq_z :: r1 @ r2)
         in
         match new_clause_id clres with
         | NewCl id ->
           fprintf fmt "%d:(resolution %a %d %d %d)@."
             id print_clause clres id1 id2 id3;
           id
         | OldCl id -> id
      )

    end
    
  | Some ("cong", [_; rty; pp; _; _; _; p_pp_eq_pp; p_x_eq_y])
    when (match name rty with Some "Bool" -> true | _ -> false) -> 
    let id1 = cnf_conversion p_x_eq_y in
    (* ignore proof of f = f, they should be the same symbol. TODO:add assert *)
    (match name pp with
     | Some _ -> ()
     | _ -> cnf_conversion p_pp_eq_pp |> ignore);
    let x_eq_y = th_res p_x_eq_y in
    let px, py = match app_name (th_res p) with
      | Some ("=", [_; apx; apy]) -> p_app apx, p_app apy
      | _ -> assert false
    in

    let cl = [not_ x_eq_y; not_ px; py] in
    let id2 = match new_clause_id ~reuse:true cl with
     | NewCl id ->
       fprintf fmt "%d:(eq_congruent_pred %a)@." id print_clause cl;
       id
     | OldCl id -> id
    in

    (if id1 = -1 then id2
     else
       let clres = match List.rev (Hashtbl.find ids_clauses id1) with
         | [] -> assert false
         | [_] -> [not_ px; py]
         | _ :: r -> List.rev (py :: not_ px :: r)
       in
       match new_clause_id clres with
       | NewCl id ->
         fprintf fmt "%d:(resolution %a %d %d)@."
           id print_clause clres id1 id2;
         id
       | OldCl id -> id)


  | Some ("cong", [_; _; f; _; _; _; p_f_eq_f; p_x_eq_y]) ->
    let id1 = cnf_conversion p_x_eq_y in
    (* ignore proof of f = f, they should be the same symbol. TODO:add assert *)
    (match name f with
     | Some _ -> ()
     | _ -> cnf_conversion p_f_eq_f |> ignore);
    let x_eq_y = th_res p_x_eq_y in
    let fx_eq_fy = th_res p in

    let cl = [not_ x_eq_y; fx_eq_fy] in
    let id2 = match new_clause_id ~reuse:true cl with
     | NewCl id ->
       fprintf fmt "%d:(eq_congruent %a)@." id print_clause cl;
       id
     | OldCl id -> id
    in

    (if id1 = -1 then id2
     else
       let clres = match List.rev (Hashtbl.find ids_clauses id1) with
         | [] -> assert false
         | [_] -> [fx_eq_fy]
         | _ :: r -> List.rev (fx_eq_fy :: r)
       in
       match new_clause_id clres with
       | NewCl id ->
         fprintf fmt "%d:(resolution %a %d %d)@."
           id print_clause clres id1 id2;
         id
       | OldCl id -> id)


  | Some ("refl", [_; _]) ->
    let clx_eq_x = [th_res p] in
    (match new_clause_id clx_eq_x with
     | NewCl id ->
       fprintf fmt "%d:(eq_reflexive %a)@." id print_clause clx_eq_x;
       id
     | OldCl id -> id)

  | Some (rule, _) ->

    (* TODO *)
    (* (-2) *)
    failwith (sprintf "Rule %s not implemented" rule)

  | None ->
    
    let cl = th_res p |> to_clause in
    (* should be an input clause *)
    try HCl.find clauses_ids cl
    with Not_found -> -1
      (* eprintf "Did not find %a@." Ast.print_term p; *)
      (* raise Not_found *)




let mk_clause rule cl args =
  match new_clause_id ~reuse:false cl with
  | NewCl id ->
    fprintf fmt "%d:(%s %a%a)@." id rule print_clause cl
      (fun fmt -> List.iter (fprintf fmt " %d")) args;
    id
  | OldCl id -> id



let mk_inter_resolution cl clauses = match clauses with
  | [id] -> id
  | _ -> mk_clause "resolution" cl (List.rev clauses)



let is_ty_Bool ty = match name ty with
  | Some "Bool" -> true
  | _ -> false


let rec cong neqs mpred clauses p = match app_name p with
  | Some ("cong", [ty; rty; f; f'; x; y; p_f_eq_f'; r]) ->

    let neqs = not_ (eq ty x y) :: neqs in
    let clauses = lem mpred clauses r in
    
    begin match name f, name f' with
      | Some n, Some n' when n = n' -> neqs, clauses
      | None, None -> cong neqs mpred clauses p_f_eq_f'
      | _ -> assert false
    end

  | Some (("symm"|"negsymm"), [_; _; _; r])
  | Some ("trans", [_; _; _; _; r; _])
  | Some ("refl", [_; r]) -> cong neqs mpred clauses r

  | _ ->
    eprintf "something went wrong in congruence@.";
    neqs, clauses


and trans neqs mpred clauses p = match app_name p with
  | Some ("trans", [ty; x; y; z; p1; p2]) ->

    (* let clauses = lem mpred (lem mpred clauses p1) p2 in *)

    let neqs1, clauses = trans neqs mpred clauses p1 in
    let neqs2, clauses = trans neqs mpred clauses p2 in
    
    let x_y = th_res p1 in
    let y_z = th_res p2 in

    let neqs = match neqs1, neqs2 with
      | [], [] -> [not_ x_y; not_ y_z]
      | [], _ -> not_ x_y :: neqs2
      | _, [] -> neqs1 @ [not_ y_z]
      | _, _ -> neqs1 @ neqs2
    in

    neqs, clauses
    
    (* let x_z = eq ty x z in *)
    (* let clauses = mk_clause "eq_transitive" [not_ x_y; not_ y_z; x_z] [] :: clauses in *)

  | Some (("symm"|"negsymm"), [_; _; _; r]) -> trans neqs mpred clauses r

  | _ ->
    
    let clauses = lem mpred clauses p in
    neqs, clauses

    (* let clauses = lem mpred clauses p in *)
    (* mk_clause "eq_transitive" neqs [] :: clauses *)


and lem mpred clauses p = match app_name p with
  | Some (("or_elim_1"|"or_elim_2"), [_; _; _; r])
    when (match app_name r with
          Some (("impl_elim"|"not_and_elim"), _) -> true | _ -> false)
    ->
    lem mpred clauses r

  | Some (("or_elim_1"|"or_elim_2"), [a; b; _; r]) ->
    let clauses = lem mpred clauses r in
    let a_or_b = th_res r in
    mk_clause "or_pos" [not_ a_or_b; a; b] [] :: clauses

  | Some ("impl_elim", [a; b; r]) ->
    let clauses = lem mpred clauses r in
    let a_impl_b = th_res r in
    mk_clause "implies_pos" [not_ a_impl_b; not_ a; b] [] :: clauses

  | Some ("not_and_elim", [a; b; r]) ->
    let clauses = lem mpred clauses r in
    let a_and_b = and_ a b in
    mk_clause "and_neg" [a_and_b; not_ a; not_ b] [] :: clauses

  | Some ("and_elim_1", [a; _; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [a; b; r]) ->
        let clauses = lem mpred clauses r in
        let a_impl_b = impl_ a b in
        mk_clause "implies_neg1" [not_ a_impl_b; a] [] :: clauses

      | Some ("not_or_elim", [a; b; r]) ->
        let clauses = lem mpred clauses r in
        let a_or_b = or_ a b in
        mk_clause "or_neg" [a_or_b; not_ a] [0] :: clauses

      | _ ->
        let clauses = lem mpred clauses r in
        let a_and_b = th_res r in
        mk_clause "and_pos" [not_ a_and_b; a] [0] :: clauses
    end

  | Some ("and_elim_2", [a; b; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [a; b; r]) ->
        let clauses = lem mpred clauses r in
        let a_impl_b = impl_ a b in
        mk_clause "implies_neg2" [not_ a_impl_b; not_ b] [] :: clauses

      | Some ("not_or_elim", [a; b; r]) ->
        let clauses = lem mpred clauses r in
        let a_or_b = or_ a b in
        mk_clause "or_neg" [a_or_b; not_ b] [1] :: clauses

      | _ ->
        let clauses = lem mpred clauses r in
        let a_and_b = th_res r in
        mk_clause "and_pos" [not_ a_and_b; b] [1] :: clauses
    end

  (* Ignore symmetry of equlity rules *)
  | Some (("symm"|"negsymm"), [_; _; _; r]) -> lem mpred clauses r

  (* Should not be traversed anyway *)
  | Some (("pred_eq_t"|"pred_eq_f"), [_; r]) -> lem mpred clauses r

  | Some ("trans", [_; _; _; _; r; w])
    when (match app_name w with
          Some (("pred_eq_t"|"pred_eq_f"), _) -> true | _ -> false)
    ->

    (* Remember which direction of the implication we want for congruence over
       predicates *)
    let mpred = match app_name w with
      | Some ("pred_eq_t", [pt; _]) -> MTerm.add pt false mpred
      | Some ("pred_eq_f", [pt; _]) -> MTerm.add pt true mpred
      | _ -> assert false
    in
    
    lem mpred clauses r

  | Some ("trans", [ty; x; y; z; p1; p2]) ->
    
    let neqs, clauses = trans [] mpred clauses p in
    let x_z = eq ty x z in
    mk_clause "eq_transitive" (neqs @ [x_z]) [] :: clauses

  (* | Some ("trans", [ty; x; y; z; p1; p2]) -> *)
    
  (*   (\* let clauses1 = lem mpred clauses p1 in *\) *)
  (*   (\* let clauses2 = lem mpred clauses p2 in *\) *)
    
  (*   (\* TODO: intermediate resolution step *\) *)
  (*   let clauses = lem mpred (lem mpred clauses p1) p2 in *)
    
  (*   let x_y = th_res p1 in *)
  (*   let y_z = th_res p2 in *)
  (*   let x_z = eq ty x z in *)
  (*   let clauses = mk_clause "eq_transitive" [not_ x_y; not_ y_z; x_z] [] :: clauses in *)

  (*   (\* let cl1 = [th_res p1] in *\) *)
  (*   (\* let cl2 = [th_res p2] in *\) *)
  (*   (\* let clauses = [ *\) *)
  (*   (\*   mk_inter_resolution cl1 clauses1; *\) *)
  (*   (\*   mk_inter_resolution cl2 clauses2] *\) *)
  (*   (\* in *\) *)
  (*   clauses *)
    
  (* Congruence with predicates *)
  | Some ("cong", [_; rty; pp; _; x; y; _; _]) when is_ty_Bool rty ->
    let neqs, clauses = cong [] mpred clauses p in
    let cptr, cpfa = match app_name (th_res p) with
      | Some ("=", [_; apx; apy]) ->
        (match MTerm.find apx mpred, MTerm.find apy mpred with
         | true, false -> p_app apx, not_ (p_app apy)
         | false, true -> p_app apy, not_ (p_app apx)
         | true, true -> p_app apx, p_app apy
         | false, false -> not_ (p_app apx), not_ (p_app apy)
        )
      | _ -> assert false
    in
    let cl = neqs @ [cpfa; cptr] in
    mk_clause "eq_congruent_pred" cl [] :: clauses

  (* Congruence *)
  | Some ("cong", [_; _; pp; _; x; y; _; _]) ->
    let neqs, clauses = cong [] mpred clauses p in
    let fx_fy = th_res p in
    let cl = List.rev (fx_fy :: neqs) in
    mk_clause "eq_congruent" cl [] :: clauses
    
  | Some ("refl", [_; _]) ->
    let x_x = th_res p in
    mk_clause "eq_reflexive" [x_x] [] :: clauses


  | Some (rule, _) ->
    (* TODO *)
    failwith (sprintf "Rule %s not implemented" rule)

  | None ->

    let cl = th_res p |> to_clause in
    (* should be an input clause *)
    try HCl.find clauses_ids cl :: clauses
    with Not_found -> clauses



type resores = RStep of string * term * term | Stop


let result_satlem p = match value p with
  | Lambda ({sname=Name n} as s, r) ->

    begin match app_name s.stype with
      | Some ("holds", [cl]) -> n, to_clause cl, r
      | _ -> assert false
    end
    
  | _ -> assert false


let rec satlem p = match app_name p with
  
  | Some ("satlem", [_; _; l; p]) ->
    let _, cl, p = result_satlem p in
    let clauses = trim_junk_satlem l |> lem MTerm.empty [] in
    eprintf "SATLEM ---@.";
    let satlem_id = mk_inter_resolution cl clauses in
    register_clause_id cl satlem_id;
    eprintf "--- SATLEM@.";
    satlem p
    
  | _ -> p



let clause_qr p = match app_name (deref p).ttype with
  | Some ("holds", [cl]) -> HCl.find clauses_ids (to_clause cl)
  | _ -> raise Not_found


let rec reso_of_QR acc qr = match app_name qr with
  | Some (("Q"|"R"), [_; _; u1; u2; _]) -> reso_of_QR (reso_of_QR acc u1) u2
  | _ -> clause_qr qr :: acc

let reso_of_QR qr = reso_of_QR [] qr |> List.rev


let rec reso_of_satlem_simplify p = match app_name p with

  | Some ("satlem_simplify", [_; _; _; qr; p]) ->

    let clauses = reso_of_QR qr in
    let _, res, p = result_satlem p in

    incr cl_cpt;
    let id = !cl_cpt in
    
    register_clause_id res id;
    fprintf fmt "%d:(resolution %a%a)@." id print_clause res
      (fun fmt -> List.iter (fprintf fmt " %d")) clauses;

    reso_of_satlem_simplify  p
    
  | None when name p <> None -> ()

  | _ -> assert false


let convert p =
  p
  |> ignore_all_decls
  |> produce_inputs_preproc
  (* |> ignore_decls *)
  (* |> produce_inputs *)
  (* |> ignore_preproc *)
  |> register_prop_vars
  |> satlem
  |> reso_of_satlem_simplify

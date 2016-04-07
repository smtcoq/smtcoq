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


module HS = Hashtbl
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
let inputs = HS.create 13

let cpt = ref 0
let cl_cpt = ref 0


let print_sharps () =
  HT.iter (fun t id ->
      printf "#%d --> %a@." id Ast.print_term_type t) sharp_tbl


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

let print_term fmt t = print_term fmt t (* (get_real t) *)


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


let mk_clause rule cl args =
  match new_clause_id ~reuse:true cl with
  | NewCl id ->
    fprintf fmt "%d:(%s %a%a)@." id rule print_clause cl
      (fun fmt -> List.iter (fprintf fmt " %d")) args;
    id
  | OldCl id -> id


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

let mk_input name formula =
  match new_clause_id [formula] with
   | NewCl id ->
     register_termclause_id formula id;
     HS.add inputs name id;
     fprintf fmt "%d:(input (%a))@." id print_term formula
   | OldCl _ -> ()


let rec produce_inputs_preproc p = match app_name p with
  | Some ("th_let_pf", [_; _; p]) ->
    begin match value p with
      | Lambda ({sname = Name h; stype}, p) ->
        begin match app_name stype with
          | Some ("th_holds", [formula]) ->
            mk_input h formula;
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
        let vt = (symbol_to_const v) in
        (* eprintf "register prop var: %a@." print_term_type vt; *)
        HT.add propvars vt formula;
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
    trim_junk_satlem p1 @ trim_junk_satlem p2
    (* begin match name p1, name p2 with *)
    (*   | None, Some _ -> trim_junk_satlem p1 *)
    (*   | Some _, None -> trim_junk_satlem p2 *)
    (*   | Some _, Some _ -> trim_junk_satlem p2 *)
    (*   | _ -> assert false *)
    (* end *)

  | _ -> [p]




let mk_inter_resolution cl clauses = match clauses with
  | [id] -> id
  | _ -> mk_clause "resolution" cl clauses



let is_ty_Bool ty = match name ty with
  | Some "Bool" -> true
  | _ -> false


let rec cong neqs ax mpred clauses p = match app_name p with
  | Some ("cong", [ty; rty; f; f'; x; y; p_f_eq_f'; r]) ->

    let neqs = not_ (eq ty x y) :: neqs in
    let clauses, ax = lem ax mpred clauses r in
    
    begin match name f, name f' with
      | Some n, Some n' when n = n' -> neqs, clauses
      | None, None -> cong neqs ax mpred clauses p_f_eq_f'
      | _ -> assert false
    end

  | Some (("symm"|"negsymm"), [_; _; _; r])
  | Some ("trans", [_; _; _; _; r; _])
  | Some ("refl", [_; r]) -> cong neqs ax mpred clauses r

  | _ ->
    eprintf "something went wrong in congruence@.";
    neqs, clauses


and trans neqs ax mpred clauses p = match app_name p with
  | Some ("trans", [ty; x; y; z; p1; p2]) ->

    (* let clauses = lem mpred (lem mpred clauses p1) p2 in *)

    let neqs1, clauses = trans neqs ax mpred clauses p1 in
    let neqs2, clauses = trans neqs ax mpred clauses p2 in
    
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

  | Some (("symm"|"negsymm"), [_; _; _; r]) -> trans neqs ax mpred clauses r

  | _ ->
    
    let clauses, ax = lem ax mpred clauses p in
    neqs, clauses

    (* let clauses = lem mpred clauses p in *)
    (* mk_clause "eq_transitive" neqs [] :: clauses *)


and lem ax mpred clauses p = match app_name p with
  | Some (("or_elim_1"|"or_elim_2"), [_; _; _; r])
    when (match app_name r with
          Some (("impl_elim"|"not_and_elim"), _) -> true | _ -> false)
    ->
    let clauses, _ = lem ax mpred clauses r in
    clauses, true

  | Some (("or_elim_1"|"or_elim_2"), [a; b; _; r]) ->
    let clauses, ax = lem ax mpred clauses r in
    (match clauses with
     | [_] when not ax -> mk_clause "or" [a; b] clauses :: [], true
     | _ ->
       let a_or_b = th_res r in
       mk_clause "or_pos" [not_ a_or_b; a; b] [] :: clauses, true
    )

  | Some ("impl_elim", [a; b; r]) ->
    let clauses, ax = lem ax mpred clauses r in
    (match clauses with
     | [_] when not ax -> mk_clause "implies" [not_ a; b] clauses :: [], ax
     | _ ->
       let a_impl_b = th_res r in
       mk_clause "implies_pos" [not_ a_impl_b; not_ a; b] [] :: clauses, ax
    )
    
  | Some ("not_and_elim", [a; b; r]) ->
    let clauses, ax = lem ax mpred clauses r in
    (match clauses with
     | [_] when not ax -> mk_clause "not_and" [not_ a; not_ b] clauses :: [], ax
     | _ ->
       let a_and_b = and_ a b in
       mk_clause "and_neg" [a_and_b; not_ a; not_ b] [] :: clauses, ax
    )

  | Some ("and_elim_1", [a; _; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [a; b; r]) ->
        let clauses, ax = lem ax mpred clauses r in
        (match clauses with
         | [_] when not ax -> mk_clause "not_implies1" [a] clauses :: [], ax
         | _ ->
           let a_impl_b = impl_ a b in
           mk_clause "implies_neg1" [a_impl_b; a] [] :: clauses, ax
        )
        
      | Some ("not_or_elim", [a; b; r]) ->
        let clauses, ax = lem ax mpred clauses r in
        (match clauses with
         | [id] when not ax -> mk_clause "not_or" [not_ a] [id; 0] :: [], ax
         | _ ->
           let a_or_b = or_ a b in
           mk_clause "or_neg" [a_or_b; not_ a] [0] :: clauses, ax
        )
        
      | _ ->
        let clauses, ax = lem ax mpred clauses r in
        (match clauses with
         | [id] when not ax -> mk_clause "and" [a] [id; 0] :: [], ax
         | _ ->
           let a_and_b = th_res r in
           mk_clause "and_pos" [not_ a_and_b; a] [0] :: clauses, ax
        )
    end

  | Some ("and_elim_2", [a; b; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [a; b; r]) ->
        let clauses, ax = lem ax mpred clauses r in
        (match clauses with
         | [_] when not ax -> mk_clause "not_implies2" [not_ b] clauses :: [], ax
         | _ ->
           let a_impl_b = impl_ a b in
           mk_clause "implies_neg2" [a_impl_b; not_ b] [] :: clauses, ax
        )

      | Some ("not_or_elim", [a; b; r]) ->
        let clauses, ax = lem ax mpred clauses r in
        (match clauses with
         | [id] when not ax -> mk_clause "not_or" [not_ b] [id; 1] :: [], ax
         | _ ->
           let a_or_b = or_ a b in
           mk_clause "or_neg" [a_or_b; not_ b] [1] :: clauses, ax
        )

      | _ ->
        let clauses, ax = lem ax mpred clauses r in
        (match clauses with
         | [id] when not ax -> mk_clause "and" [b] [id; 1] :: [], ax
         | _ ->
           let a_and_b = th_res r in
           mk_clause "and_pos" [not_ a_and_b; b] [1] :: clauses, ax
        )
    end

  (* Ignore symmetry of equlity rules *)
  | Some (("symm"|"negsymm"), [_; _; _; r]) -> lem ax mpred clauses r

  (* Should not be traversed anyway *)
  | Some (("pred_eq_t"|"pred_eq_f"), [_; r]) -> lem ax mpred clauses r

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
    
    lem ax mpred clauses r

  | Some ("trans", [ty; x; y; z; p1; p2]) ->
    
    let neqs, clauses = trans [] ax mpred clauses p in
    let x_z = eq ty x z in
    mk_clause "eq_transitive" (neqs @ [x_z]) [] :: clauses, true

  (* | Some ("trans", [ty; x; y; z; p1; p2]) ->
    
    (* let clauses1 = lem mpred clauses p1 in *)
    (* let clauses2 = lem mpred clauses p2 in *)
    
    (* TODO: intermediate resolution step *)
    let clauses = lem mpred (lem mpred clauses p1) p2 in
    
    let x_y = th_res p1 in
    let y_z = th_res p2 in
    let x_z = eq ty x z in
    let clauses = mk_clause "eq_transitive" [not_ x_y; not_ y_z; x_z] [] :: clauses in

    (* let cl1 = [th_res p1] in *)
    (* let cl2 = [th_res p2] in *)
    (* let clauses = [ *)
    (*   mk_inter_resolution cl1 clauses1; *)
    (*   mk_inter_resolution cl2 clauses2] *)
    (* in *)
    clauses
  *)
    
  (* Congruence with predicates *)
  | Some ("cong", [_; rty; pp; _; x; y; _; _]) when is_ty_Bool rty ->
    let neqs, clauses = cong [] ax mpred clauses p in
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
    mk_clause "eq_congruent_pred" cl [] :: clauses, true

  (* Congruence *)
  | Some ("cong", [_; _; _; _; _; _; _; _]) ->
    let neqs, clauses = cong [] ax mpred clauses p in
    let fx_fy = th_res p in
    let cl = neqs @ [fx_fy] in
    mk_clause "eq_congruent" cl [] :: clauses, true
    
  | Some ("refl", [_; _]) ->
    let x_x = th_res p in
    mk_clause "eq_reflexive" [x_x] [] :: clauses, ax


  | Some (rule, _) ->
    (* TODO *)
    failwith (sprintf "Rule %s not implemented" rule)

  | None ->

    match name p with
    | Some h ->
      (* should be an input clause *)
      (try HS.find inputs h :: clauses, ax
       with Not_found -> clauses, true)

    | None -> clauses, true



type resores = RStep of string * term * term | Stop


let result_satlem p = match value p with
  | Lambda ({sname=Name n} as s, r) ->

    begin match app_name s.stype with
      | Some ("holds", [cl]) -> n, to_clause cl, r
      | _ -> assert false
    end
    
  | _ -> assert false

let continuation_satlem p = match value p with
  | Lambda (_, r) -> r
  | _ -> assert false



let rec satlem p = match app_name p with
  
  | Some ("satlem", [c; _; l; p]) ->
    let cl = to_clause c in
    let clauses =
      trim_junk_satlem l
      |> List.map (fun p -> fst (lem false MTerm.empty [] p))
      |> List.flatten in
    (* eprintf "SATLEM ---@."; *)
    let satlem_id = mk_inter_resolution cl clauses in
    register_clause_id cl satlem_id;
    (* eprintf "--- SATLEM@."; *)
    satlem (continuation_satlem p)
    
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

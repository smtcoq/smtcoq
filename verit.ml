open Format
open Ast
open Builtin


type step = {
  id: string;
  rule: string;
  result: term;
  args: string list;
  pos: int list;
}


let fmt = std_formatter

let abbrev = Hashtbl.create 201

(* let types = Hashtbl.create 201 *)

let propvars = Hashtbl.create 201

let cl_cpt = ref 0

let rec deref t = match t.value with
  | Ptr t -> deref t
  | _ -> t


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


let sharp_tbl = Hashtbl.create 13

let cpt = ref 0


let rec print_apply fmt t = match app_name t with
  | Some ("apply", [_; _; f; a]) ->
    fprintf fmt "%a %a" print_apply f print_term a
  | _ -> print_term fmt t
  

and print_term fmt t =
  try Hashtbl.find sharp_tbl t |> fprintf fmt "#%d"
  with Not_found ->
    match name t with
    | Some n -> pp_print_string fmt (smt2_of_lfsc n)
    | None -> match app_name t with

      | Some ("=", [_; a; b]) ->
        incr cpt;
        Hashtbl.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(= %a %a)" !cpt print_term a print_term b


      | Some ("not", [a]) -> fprintf fmt "(not %a)" print_term a
                               
      | Some ("apply", _) ->
        incr cpt;
        Hashtbl.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(%a)" !cpt print_apply t

      | Some ("p_app", [a]) -> print_term fmt a

      | Some (n, l) ->
        let n = smt2_of_lfsc n in
        incr cpt;
        Hashtbl.add sharp_tbl t !cpt;
        fprintf fmt "#%d:(%s%a)" !cpt n
          (fun fmt -> List.iter (fprintf fmt " %a" print_term)) l

      | _ -> assert false
        


let rec print_clause elim_or fmt t = match name t with
  | Some "cln" | Some "false" -> ()
  | Some n -> pp_print_string fmt (smt2_of_lfsc n)
  | None ->
    match app_name t with
    | Some ("pos", [v]) ->
      let t = Hashtbl.find propvars (deref v) in
      fprintf fmt "%a" print_term t
    | Some ("neg", [v]) ->
      let t = Hashtbl.find propvars (deref v) in
      fprintf fmt "(not %a)" print_term t
    | Some ("clc", [a; cl]) ->
      fprintf fmt "%a %a" (print_clause elim_or) a (print_clause elim_or) cl
    | Some ("or", [a; b]) when elim_or ->
      fprintf fmt "%a %a" (print_clause elim_or) a (print_clause elim_or) b
    | _ -> fprintf fmt "%a" print_term t


let print_clause_elim_or fmt t = fprintf fmt "(%a)" (print_clause true) t

let print_clause fmt t = fprintf fmt "(%a)" (print_clause false) t
  


let th_res p = match app_name (deref p).ttype with
  | Some ("th_holds", [r]) -> r
  | _ -> assert false


let rec ignore_decls p = match value p with
  | Lambda (s, p) ->
    (* eprintf "Ignored %a@." print_symbol s; *)
    ignore_decls p
  | _ -> p


let rec produce_inputs p = match app_name p with
  | Some ("th_let_pf", [_; _; p]) ->
    begin match value p with
      | Lambda ({sname = Name h; stype}, p) ->
        begin match app_name stype with
          | Some ("th_holds", [formula]) ->
            incr cl_cpt;
            let nb = !cl_cpt in
            Hashtbl.add abbrev formula nb;
            fprintf fmt "%d:(input (%a))@." nb print_term formula;
            produce_inputs p
          | _ -> assert false
        end
      | _ -> assert false
    end
  | _ -> p

    

let rec register_prop_vars p = match app_name p with
  | Some ("decl_atom", [formula; p]) ->
    begin match value p with
      | Lambda (v, p) ->
        Hashtbl.add propvars (symbol_to_const v) formula;
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

  | Some ("clausify_false", [p])
  | Some ("contra", [_; p]) -> trim_junk_satlem p

  | _ -> p



let rec or_elim result_id p = match app_name p with
  | Some (("or_elim_1"|"or_elim_2"), [_; _; _; p]) -> or_elim result_id p

  | _ ->
    let cl = th_res p in
    incr cl_cpt;
    let id = !cl_cpt in
    Hashtbl.add abbrev cl id;
    fprintf fmt "%d:(or %a %d)@." id print_clause_elim_or cl result_id;
    id


(* let or_impl_elim p = match app_name p with *)
(*   | Some (("or_elim_1"|"or_elim_2"), [_; _; _; p]) -> or_elim result_id p *)

  

let rec cnf_convertion result p = match app_name p with
  
  | Some ("and_elim_1", [_; _; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [_; _; w]) ->
        let res, acc = cnf_convertion result w in
        let result = th_res p in
        let id = "00" in
        let st =
          { id; rule = "not_implies1"; result; args = [res]; pos = [] } in
         id, st :: acc
      | _ ->
        let res, acc = cnf_convertion result r in
        let result = th_res p in
        let id = "00" in
        let st = { id; rule = "and"; result; args = [res]; pos = [0] } in
        id, st :: acc
    end

  | Some ("and_elim_2", [_; _; r]) ->
    begin match app_name r with
      | Some ("not_impl_elim", [_; _; w]) ->
        let res, acc = cnf_convertion result w in
        let result = th_res p in
        let id = "00" in
        let st =
          { id; rule = "not_implies2"; result; args = [res]; pos = [] } in
         id, st :: acc
      | _ ->
        let res, acc = cnf_convertion result r in
        let result = th_res p in
        let id = "00" in
        let st = { id; rule = "and"; result; args = [res]; pos = [1] } in
        id, st :: acc
    end
    
  | _ -> assert false (* TODO *) 


type resores = RStep of string * term * term | Stop


let result_satlem p = match value p with
  | Lambda ({sname=Name n} as s, r) ->

    begin match app_name s.stype with
      | Some ("holds", [cl]) -> n, cl, r
      | _ -> assert false
    end
    
  | _ -> assert false

let rec satlem acc p = match app_name p with
  
  | Some ("satlem", [_; _; lem; p]) ->

    let id, result, p = result_satlem p in
    
    satlem acc p
    
    
  | None -> p

  | _ -> assert false




let rec reso_of_QR acc qr = match app_name qr with
  | Some (("Q"|"R"), [_; _; u1; u2; _]) ->
    
    begin match name u1, name u2 with
      | Some cl1, Some cl2 -> cl1 :: cl2 :: acc
      | Some cl1, None -> reso_of_QR (cl1 :: acc) u2
      | None, Some cl2 -> reso_of_QR (cl2 :: acc) u1
      | _ -> assert false
    end

  | _ -> assert false



let rec reso_of_satlem_simplify acc p = match app_name p with

  | Some ("satlem_simplify", [_; _; _; qr; p]) ->

    let clauses = reso_of_QR [] qr in
    let id, result, p = result_satlem p in
    let st = { id; rule = "resolution"; result; args = clauses; pos = [] } in
    reso_of_satlem_simplify (st :: acc) p
    
  | None when name p <> None -> acc

  | _ -> assert false


let convert p =
  p
  |> ignore_decls
  |> produce_inputs
  |> register_prop_vars
  |> ignore

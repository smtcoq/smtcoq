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
open Builtin
open Format
open Translator_sig


module Make (T : Translator_sig.S) = struct

  open T

  module MTerm = Map.Make (Term)


  (** Environment for {!lem} *)
  type env = {
    clauses : int list;   (** Accumulated clauses *)
    ax : bool;            (** Force use of axiomatic rules? *)
    mpred : bool MTerm.t; (** map for positivity of predicates in cong *)
    assum : string list;  (** Assumptions that were not used *)
  }


  (** Empty environment *)
  let empty = {
    clauses = [];
    ax = false;
    mpred = MTerm.empty;
    assum = [];
  }


  (** Returns the formula of which p is a proof of *)
  let th_res p = match app_name (deref p).ttype with
    | Some ("th_holds", [r]) -> r
    | _ -> assert false

  
  (** Ignore declarations at begining of proof *)
  let rec ignore_all_decls p = match value p with
    | Lambda (s, p) -> ignore_all_decls p
    | _ -> p

  
  (** Ignore declarations but keep assumptions *)
  let rec ignore_decls p = match value p with
    | Lambda (s, p) ->
      (match s.sname with
       | Name n when n.[0] = 'A' -> p
       | _ -> ignore_decls p
      )
    | _ -> p

  
  (** Ignore result of preprocessing *)
  let rec ignore_preproc p = match app_name p with
    | Some ("th_let_pf", [_; _; p]) ->
      begin match value p with
        | Lambda (_, p) -> ignore_preproc p
        | _ -> assert false
      end
    | _ -> p

  
  (** Produce input clauses from the result of CVC4's pre-processing. This may
      not match the actual inputs in the original SMT2 file but they correspond
      to what the proof uses. *)
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


  (** Produce inputs from the assumptions *)
  let rec produce_inputs p = match value p with
    | Lambda ({sname = Name h; stype}, p) ->
      begin match app_name stype with
        | Some ("th_holds", [formula])
          when (match name formula with Some "true" -> false | _ -> true)
          ->
          mk_input h formula;
          produce_inputs p
        | _ -> produce_inputs p
      end
    | _ -> p


  let rec admit_preproc p = match app_name p with
    | Some ("th_let_pf", [_; tr; p]) ->
      begin match app_name tr with
        | Some ("trust_f", [formula]) ->
          begin match value p with
            | Lambda ({sname = Name h}, p) ->
              mk_admit_preproc h formula;
              admit_preproc p
            | _ -> assert false
          end
        | _ -> assert false
      end
    | _ -> p


  
  (** Registers a propositional variable as an abstraction for a
      formula. Proofs in SMTCoq have to be given in terms of formulas. *)
  let rec register_prop_vars p = match app_name p with
    | Some ("decl_atom", [formula; p]) ->
      begin match value p with
        | Lambda (v, p) ->
          let vt = (symbol_to_const v) in
          (* eprintf "register prop var: %a@." print_term_type vt; *)
          register_prop_abstr vt formula;
          begin match value p with
            | Lambda (_, p) -> register_prop_vars p
            | _ -> assert false
          end
        | _ -> assert false
      end
    | _ -> p


  (** Returns the name of the local assumptions made in [satlem] *)
  let rec get_assumptions acc p = match app_name p with
    | Some (("asf"|"ast"), [_; _; _; _; p]) ->
      begin match value p with
        | Lambda ({sname = Name n}, p) -> get_assumptions (n :: acc) p
        | _ -> assert false
      end
    | _ -> acc, p



  let rec rm_used' assumptions t = match name t with
    | Some x -> List.filter (fun y -> y <> x) assumptions
    | None -> match app_name t with
      | Some (_, l) -> List.fold_left rm_used' assumptions l
      | None -> assumptions

  (** Remove used assumptions from the environment *)
  let rm_used env t = { env with assum = rm_used' env.assum t }

  
  (** Create an intermediate resolution step in [satlem] with the accumulated
      clauses. {!Reso} ignores the resulting clause so we can just give the
      empty clause here. *)
  let mk_inter_resolution clauses = match clauses with
    | [id] -> id
    | _ -> mk_clause ~reuse:false Reso [] clauses



  let is_ty_Bool ty = match name ty with
    | Some "Bool" -> true
    | _ -> false


  (** Accumulates equalities for congruence. This is useful for when [f] takes
      multiples arguments. *)
  let rec cong neqs env p = match app_name p with
    | Some ("cong", [ty; rty; f; f'; x; y; p_f_eq_f'; r]) ->

      let neqs = not_ (eq ty x y) :: neqs in
      let env = lem env r in

      begin match name f, name f' with
        | Some n, Some n' when n = n' -> neqs, env
        | None, None -> cong neqs env p_f_eq_f'
        | _ -> assert false
      end

    | Some (("symm"|"negsymm"), [_; _; _; r])
    | Some ("trans", [_; _; _; _; r; _])
    | Some ("refl", [_; r]) -> cong neqs (rm_used env r) r

    | _ ->
      eprintf "something went wrong in congruence@.";
      neqs, env


  (** Accumulates equalities for transitivity to chain them together. *)
  and trans neqs env p = match app_name p with
    | Some ("trans", [ty; x; y; z; p1; p2]) ->

      (* let clauses = lem mpred assum (lem mpred assum clauses p1) p2 in *)

      let neqs1, env = trans neqs env p1 in
      let neqs2, env = trans neqs env p2 in

      let x_y = th_res p1 in
      let y_z = th_res p2 in

      let neqs = match neqs1, neqs2 with
        | [], [] -> [not_ x_y; not_ y_z]
        | [], _ -> not_ x_y :: neqs2
        | _, [] -> neqs1 @ [not_ y_z]
        | _, _ -> neqs1 @ neqs2
      in

      neqs, env

    | Some (("symm"|"negsymm"), [_; _; _; r]) -> trans neqs (rm_used env r) r

    | _ -> neqs, lem env p



  (** Convert the local proof of a [satlem]. We use decductive style rules when
      possible but revert to axiomatic ones when the context forces us to. *)
  and lem env p = match app_name p with
    | Some ("or_elim_1", [el; rem; x; r])
    | Some ("or_elim_2", [rem; el; x; r])
      when (match app_name r with
            Some (("iff_elim_1" |"iff_elim_2"), _) -> true | _ -> false)
      ->
      
      let env = lem env r in
      let env = lem env x in
      (match env.clauses with
       | ci1 :: ci2 :: cls ->
         { env with clauses = mk_clause_cl Reso [rem] [ci1; ci2] :: cls }
       | _ -> env
      )

    | Some (("or_elim_1"|"or_elim_2"), [_; _; x; r])
      when (match app_name r with
            Some (("impl_elim"
                  |"not_and_elim"
                  |"iff_elim_1"
                  |"iff_elim_2"), _) -> true | _ -> false)
      ->
      let env = rm_used env x in
      let env = lem env r in
      { env with ax = true }

    | Some (("or_elim_1"|"or_elim_2"), [a; b; x; r]) ->
      let env = rm_used env x in
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax -> mk_clause_cl Or [a; b] env.clauses :: []
        | _ ->
          let a_or_b = th_res r in
          mk_clause_cl Orp [not_ a_or_b; a; b] [] :: env.clauses
      in
      { env with clauses; ax = true }

    | Some ("impl_elim", [a; b; r]) ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax -> mk_clause_cl Imp [not_ a; b] env.clauses :: []
        | _ ->
          let a_impl_b = th_res r in
          mk_clause_cl Impp [not_ a_impl_b; not_ a; b] [] :: env.clauses
      in
      { env with clauses }

    | Some ("iff_elim_1", [a; b; r]) ->
      begin match app_name r with
        | Some ("not_iff_elim", [a; b; r]) ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nequ2 [not_ a; not_ b] env.clauses :: []
            | _ ->
              let a_iff_b = iff_ a b in
              mk_clause_cl Equn1 [a_iff_b; not_ a; not_ b] [] :: env.clauses
          in
          { env with clauses }
        | _ ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Equ1 [not_ a; b] env.clauses :: []
            | _ ->
              let a_iff_b = th_res r in
              mk_clause_cl Equp2 [not_ a_iff_b; not_ a; b] [] :: env.clauses
          in
          { env with clauses }
      end

      | Some ("iff_elim_2", [a; b; r]) ->
      begin match app_name r with
        | Some ("not_iff_elim", [a; b; r]) ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nequ1 [a; b] env.clauses :: []
            | _ ->
              let a_iff_b = iff_ a b in
              mk_clause_cl Equn2 [a_iff_b; a; b] [] :: env.clauses
          in
          { env with clauses }
        | _ ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Equ2 [a; not_ b] env.clauses :: []
            | _ ->
              let a_iff_b = th_res r in
              mk_clause_cl Equp1 [not_ a_iff_b; a; not_ b] [] :: env.clauses
          in
          { env with clauses }
      end

    | Some ("not_and_elim", [a; b; r]) ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Nand [not_ a; not_ b] env.clauses :: []
        | _ ->
          let a_and_b = and_ a b in
          mk_clause_cl Andn [a_and_b; not_ a; not_ b] [] :: env.clauses
      in
      { env with clauses }

    | Some ("and_elim_1", [a; _; r]) ->
      begin match app_name r with
        | Some ("not_impl_elim", [a; b; r]) ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax -> mk_clause_cl Nimp1 [a] env.clauses :: []
            | _ ->
              let a_impl_b = impl_ a b in
              mk_clause_cl Impn1 [a_impl_b; a] [] :: env.clauses
          in
          { env with clauses }

        | Some ("not_or_elim", [a; b; r]) ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [id] when not env.ax -> mk_clause_cl Nor [not_ a] [id; 0] :: []
            | _ ->
              let a_or_b = or_ a b in
              mk_clause_cl Orn [a_or_b; not_ a] [0] :: env.clauses
          in
          { env with clauses }

        | _ ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [id] when not env.ax -> mk_clause_cl And [a] [id; 0] :: []
            | _ ->
              let a_and_b = th_res r in
              mk_clause_cl Andp [not_ a_and_b; a] [0] :: env.clauses
          in
          { env with clauses }
      end

    | Some ("and_elim_2", [a; b; r]) ->
      begin match app_name r with
        | Some ("not_impl_elim", [a; b; r]) ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nimp2 [not_ b] env.clauses :: []
            | _ ->
              let a_impl_b = impl_ a b in
              mk_clause_cl Impn2 [a_impl_b; not_ b] [] :: env.clauses
          in
          { env with clauses }

        | Some ("not_or_elim", [a; b; r]) ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [id] when not env.ax -> mk_clause_cl Nor [not_ b] [id; 1] :: []
            | _ ->
              let a_or_b = or_ a b in
              mk_clause_cl Orn [a_or_b; not_ b] [1] :: env.clauses
          in
          { env with clauses }

        | _ ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [id] when not env.ax -> mk_clause_cl And [b] [id; 1] :: []
            | _ ->
              let a_and_b = th_res r in
              mk_clause_cl Andp [not_ a_and_b; b] [1] :: env.clauses
          in
          { env with clauses }
      end

    (* Ignore symmetry of equlity rules *)
    | Some (("symm"|"negsymm"), [_; _; _; r]) -> lem (rm_used env r) r

    (* Ignore double negation *)
    | Some (("not_not_elim"|"not_not_intro"), [_; r]) -> lem env r

    (* Should not be traversed anyway *)
    | Some (("pred_eq_t"|"pred_eq_f"), [_; r]) -> lem env r


    | Some ("trans", [_; _; _; _; r; w])
      when (match app_name w with
            Some (("pred_eq_t"|"pred_eq_f"), _) -> true | _ -> false)
      ->
      (* Remember which direction of the implication we want for congruence over
         predicates *)
      let env = match app_name w with
        | Some ("pred_eq_t", [pt; x]) ->
          let env = rm_used env x in
          { env with mpred = MTerm.add pt false env.mpred }
        | Some ("pred_eq_f", [pt; x]) ->
          let env = rm_used env x in
          { env with mpred = MTerm.add pt true env.mpred }
        | _ -> assert false
      in

      lem env r

    | Some ("trans", [ty; x; y; z; p1; p2]) ->

      let neqs, env = trans [] env p in
      let x_z = eq ty x z in
      { env with
        clauses = mk_clause_cl Eqtr (neqs @ [x_z]) [] :: env.clauses;
        ax = true }

    (* | Some ("trans", [ty; x; y; z; p1; p2]) ->

       (* let clauses1 = lem mpred assum clauses p1 in *)
       (* let clauses2 = lem mpred assum clauses p2 in *)

       (* TODO: intermediate resolution step *)
       let clauses = lem mpred assum (lem mpred assum clauses p1) p2 in

       let x_y = th_res p1 in
       let y_z = th_res p2 in
       let x_z = eq ty x z in
       let clauses = mk_clause_cl "eq_transitive" [not_ x_y; not_ y_z; x_z] [] :: clauses in

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
      let neqs, env = cong [] env p in
      let cptr, cpfa = match app_name (th_res p) with
        | Some ("=", [_; apx; apy]) ->
          (match MTerm.find apx env.mpred, MTerm.find apy env.mpred with
           | true, false -> p_app apx, not_ (p_app apy)
           | false, true -> p_app apy, not_ (p_app apx)
           | true, true -> p_app apx, p_app apy
           | false, false -> not_ (p_app apx), not_ (p_app apy)
          )
        | _ -> assert false
      in
      let cl = neqs @ [cpfa; cptr] in
      { env with
        clauses = mk_clause_cl Eqcp cl [] :: env.clauses;
        ax = true }

    (* Congruence *)
    | Some ("cong", [_; _; _; _; _; _; _; _]) ->
      let neqs, env = cong [] env p in
      let fx_fy = th_res p in
      let cl = neqs @ [fx_fy] in
      { env with
        clauses = mk_clause_cl Eqco cl [] :: env.clauses;
        ax = true }

    | Some ("refl", [_; _]) ->
      let x_x = th_res p in
      { env with clauses = mk_clause_cl Eqre [x_x] [] :: env.clauses }


    | Some (rule, _) ->
      (* TODO *)
      failwith (sprintf "Rule %s not implemented" rule)

    | None ->

      match name p with

      | Some ("A0"|"truth") ->
        { env with clauses = mk_clause_cl True [ttrue] [] :: env.clauses }
      
      | Some h ->
        (* should be an input clause *)
        (try { env with clauses = get_input_id h :: env.clauses }
         with Not_found ->
           { env with
             ax = true;
             assum = List.filter (fun a -> a <> h) env.assum }
        )

      | None -> { env with ax = true }


  
  (** Returns the name given to this lemma, its type and the continuation. *)
  let result_satlem p = match value p with
    | Lambda ({sname=Name n} as s, r) ->

      begin match app_name s.stype with
        | Some ("holds", [cl]) -> n, cl, r
        | _ -> assert false
      end

    | _ -> assert false


  (** Returns the clause used in a resolution step *)
  let clause_qr p =
    try match name p with
      | Some n -> get_input_id n
      | _ -> raise Not_found
    with Not_found -> match app_name (deref p).ttype with
      | Some ("holds", [cl]) ->
        (* eprintf "get_clause id : %a@." print_term cl; *)
        get_clause_id (to_clause cl)
      | _ -> raise Not_found
             

  let rec reso_of_QR acc qr = match app_name qr with
    | Some (("Q"|"R"), [_; _; u1; u2; _]) -> reso_of_QR (reso_of_QR acc u1) u2
    | _ -> clause_qr qr :: acc

  (** Returns clauses used in a linear resolution chain *)
  let reso_of_QR qr = reso_of_QR [] qr |> List.rev


  
  (** convert resolution proofs of [satlem_simplify] *)
  let satlem_simplify p = match app_name p with
    | Some ("satlem_simplify", [_; _; _; qr; p]) ->
      let clauses = reso_of_QR qr in
      let lem_name, res, p = result_satlem p in
      let cl_res = to_clause res in
      let id = mk_clause ~reuse:false Reso cl_res clauses in
      register_clause_id cl_res id;
      register_decl_id lem_name id;
      Some id, p
    | _ -> raise Exit

  
  let rec many_satlem_simplify lastid p =
    try
      let lastid, p = satlem_simplify p in
      many_satlem_simplify lastid p
    with Exit -> lastid, p


  (* can be empty, returns continuation *)
  let satlem_simplifies_c p = many_satlem_simplify None p |> snd


  (* There must be at least one, returns id of last deduced clause *)
  let reso_of_satlem_simplify p =
    match many_satlem_simplify None p with
    | Some id, _ -> id
    | _ -> assert false


  let rec bb_trim_intro_unit env p = match app_name p with
    | Some (("intro_assump_f"|"intro_assump_t"), [_; _; _; ullit; _; l]) ->
      let env = rm_used env ullit in
      (match value l with
       | Lambda (_, p) -> bb_trim_intro_unit env p
       | _ -> assert false)
    | _ -> env, p

  
  let is_last_bbres p = match app_name p with
    | Some ("satlem_simplify", [_; _; _; _; l]) ->
      (match value l with
       | Lambda ({sname=Name e}, pe) ->
         (match name pe with Some ne -> ne = e | None -> false)
       | _ -> false)
    | _ -> false


  let rec bb_lem_res lastid p =
    try
      if is_last_bbres p then raise Exit;
      let lastid, p = satlem_simplify p in
      bb_lem_res lastid p
    with Exit -> match lastid with
      | Some id -> id
      | None -> assert false


  let rec bb_lem env p =
    let env, p = bb_trim_intro_unit env p in
    let id = bb_lem_res None p in
    { env with clauses = id :: env.clauses }
  


  exception ArithLemma

  (** Remove superfluous applications at the top of [satlem] and returns a list
      of proofs whose resulting clauses need to be resolved.

      @raises {!ArithLemma} if the proof is a trust statement (we assume it is
      the case for now).  *)
  let rec trim_junk_satlem p = match app_name p with
    | Some ("clausify_false", [p]) ->
      (match name p with
       | Some "trust" -> raise ArithLemma
       | _ -> trim_junk_satlem p
      )
    | Some ("contra", [_; p1; p2]) ->
      trim_junk_satlem p1 @ trim_junk_satlem p2
    | _ -> [p]

  
  (** Returns the continuation of a [satlem]. *)
  let continuation_satlem p = match value p with
    | Lambda ({sname=Name n}, r) -> n, r
    | _ -> assert false


  let is_bbr_satlem_lam p = match value p with
    | Lambda ({sname = Name h}, _) ->
      (try String.sub h 0 5 = "bb.cl"
       with Invalid_argument _ -> false)
    | _ -> false 
  
  let has_intro_bv p = match app_name p with
    | Some (("intro_assump_f"|"intro_assump_t"), _) -> true
    | _ -> false

  
  (** Convert [satlem]. Clauses are chained together with an intermediate
      resolution step when needed, and when CVC4 uses superfluous local
      assumption, the clause is weakened. *)
  let rec satlem p = match app_name p with

    | Some ("satlem", [c; _; l; p]) ->
      (* eprintf "SATLEM ---@."; *)
      let cl = to_clause c in
      let lem_name, lem_cont = continuation_satlem p in
      (try
        let assumptions, l = get_assumptions [] l in
        let l = trim_junk_satlem l in
        let env = { empty with assum = assumptions } in
        let lem =
          if is_bbr_satlem_lam p || List.exists has_intro_bv l then bb_lem
          else lem in
        let env =
          List.fold_left (fun env p ->
              let local_env =
                { env with
                  clauses = [];
                  ax = false;
                  mpred = MTerm.empty;
                } in
              let local_env = lem local_env p in
              { env with
                clauses = List.rev_append local_env.clauses env.clauses;
                assum = local_env.assum
              }
            ) env l
        in
        let clauses = List.rev env.clauses in
        let id = mk_inter_resolution clauses in
        (* eprintf "remaining assumptions:"; *)
        (* List.iter (eprintf "%s, ") env.assu; *)
        (* eprintf "@."; *)
        let satlem_id =
          if env.assum = [] then id else mk_clause Weak cl [id]
        in
        register_clause_id cl satlem_id;
        register_decl_id lem_name satlem_id;
        (* eprintf "--- SATLEM@."; *)
        
       with ArithLemma ->
         let satlem_id = mk_clause Lage cl [] in
         register_clause_id cl satlem_id

      );
      
      satlem lem_cont

    | _ -> p


  let rec bbt p = match app_name p with
    | Some ("bv_bbl_var", [n; v; bb]) ->
      let res = bblast_term n (a_var_bv n v) bb in
      Some (mk_clause_cl Bbva [res] [])
    | Some ("bv_bbl_bvand", [n; x; y; _; _; rb; xbb; ybb]) ->
      let res = bblast_term n (bvand x y) rb in
      (match bbt xbb, bbt ybb with
       | Some idx, Some idy ->
         Some (mk_clause_cl Bband [res] [idx; idy])
       | _ -> assert false
      )
    | None ->
      begin match name p with
      | Some h -> (* should be an declared clause *)
        Some (try get_input_id h with Not_found -> assert false)
      | None -> assert false
      end
      
    | Some (r, _) -> failwith ("BV: Not implemented rule " ^ r)

  

  let rec bblast_decls p = match app_name p with
    | Some ("decl_bblast", [n; b; t; bb; l]) ->
      let res = bblast_term n t b in
      let id = match bbt bb with Some id -> id | None -> assert false in
      begin match value l with
        | Lambda ({sname = Name h}, p) ->
          register_decl_id h id;
          bblast_decls p
        | _ -> assert false
      end
    | _ -> p


  let rec bblast_eqs p = match app_name p with
    | Some ("th_let_pf", [f; pf; l]) ->
      begin match app_name pf with
        | Some ("bv_bbl_=", [_; _; _; _; _; _; a; b]) ->
          begin match name a, name b with
          | Some na, Some nb ->
            let id1, id2 =
              try get_input_id na, get_input_id nb
              with Not_found -> assert false in
            let clid = mk_clause_cl Bbeq [f] [id1; id2] in
            begin match value l with
              | Lambda ({sname = Name h}, p) ->
                register_decl_id h clid;
                bblast_eqs p
              | _ -> assert false
            end
          | _ -> assert false
          end
        | _ -> assert false
      end
    | _ -> p

  
  (** Bit-blasting and bitvector proof conversion (returns rest of the sat
      proof) *)
  let bb_proof p = match app_name p with
    | Some ("decl_bblast", _) ->
      p
      |> bblast_decls
      |> bblast_eqs
      |> register_prop_vars
      |> satlem
      |> satlem_simplifies_c
      |> satlem
      
    | _ -> p
  

  (** Convert an LFSC proof (this is the entry point) *)
  let convert p =
    p
      
    (* |> ignore_all_decls *)
    (* |> produce_inputs_preproc *)

    |> ignore_decls
    |> produce_inputs
    |> admit_preproc
    
    |> register_prop_vars
    |> satlem

    |> bb_proof
    
    |> reso_of_satlem_simplify


  (** Clean global environments *)
  let clear () = T.clear ()


end

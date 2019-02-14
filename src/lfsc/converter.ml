(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
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
    clauses : int list;     (** Accumulated clauses *)
    ax : bool;              (** Force use of axiomatic rules? *)
    mpred : bool MTerm.t;   (** map for positivity of predicates in cong *)
    assum : Hstring.t list; (** Assumptions that were not used *)
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
    | Some (n, [r]) when n == H.th_holds -> r
    | _ -> assert false

  
  (** Ignore declarations at begining of proof *)
  let rec ignore_all_decls p = match value p with
    | Lambda (s, p) -> ignore_all_decls p
    | _ -> p

  
  (** Ignore declarations but keep assumptions *)
  let rec ignore_decls p = match value p with
    | Lambda (s, pr) ->
      (match s.sname with
       | Name n when (Hstring.view n).[0] = 'A' -> p
       | _ -> ignore_decls pr
      )
    | _ -> p

  
  (** Ignore result of preprocessing *)
  let rec ignore_preproc p = match app_name p with
    | Some (n, [_; _; p]) when n == H.th_let_pf ->
      begin match value p with
        | Lambda (_, p) -> ignore_preproc p
        | _ -> assert false
      end
    | _ -> p

  
  (** Produce input clauses from the result of CVC4's pre-processing. This may
      not match the actual inputs in the original SMT2 file but they correspond
      to what the proof uses. *)
  let rec produce_inputs_preproc p = match app_name p with
    | Some (n, [_; _; p]) when n == H.th_let_pf ->
      begin match value p with
        | Lambda ({sname = Name h; stype}, p) ->
          begin match app_name stype with
            | Some (n, [formula]) when n == H.th_holds ->
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
        | Some (n, [formula])
          when n == H.th_holds &&
               (match name formula with
                | Some f when f == H.ttrue -> false | _ -> true)
          ->
          mk_input h formula;
          produce_inputs p
        | _ -> produce_inputs p
      end
    | _ -> p


  let dvar_of_v t = match app_name t with
    | Some (n, [_; v]) when n == H.a_var_bv -> v
    | _ -> t

  
  let trust_vareq_as_alias formula = match app_name formula with
    | Some (n, [ty; alias; t]) when n == H.eq ->
      (match name (dvar_of_v alias) with
      | Some n -> register_alias n t; true
      | None -> false)
    | _ -> false

  
  let rec admit_preproc p = match app_name p with
    | Some (n, [_; tr; p]) when n == H.th_let_pf ->
      begin match app_name tr with
        | Some (n, _) when n == H.trust_f ->
          eprintf "Warning: hole for trust_f.@."
        | Some (rule, _) ->
          eprintf "Warning: hole for unsupported rule %a.@." Hstring.print rule
        | None -> eprintf "Warning: hole@."
      end;
      let formula = th_res tr in
      begin match value p with
        | Lambda ({sname = Name h}, p) ->
          if not (trust_vareq_as_alias formula) then
            mk_admit_preproc h formula;
          admit_preproc p
        | _ -> assert false
      end
    | _ -> p



  (** Handle deferred declarations in LFSC (for extensionality rule atm.) *)
  let rec deferred p = match app_name p with
    | Some (n, [ty_i; ty_e; a; b; p]) when n == H.ext ->
      begin match value p with
        | Lambda ({sname = Name index_diff}, p) ->
          begin match value p with
            | Lambda ({sname = Name h}, p) ->
              let diff_a_b = (apply_diff ty_i ty_e a b) in
              register_alias index_diff diff_a_b;
              let f =
                or_ (eq (array ty_i ty_e) a b)
                  (not_ (eq ty_e
                           (apply_read ty_i ty_e a diff_a_b)
                           (apply_read ty_i ty_e b diff_a_b))) in
              let cid = mk_clause_cl Exte [f] [] in
              register_decl_id h cid;
              deferred p
            | _ -> assert false
          end
        | _ -> assert false
      end
    | _ -> p


   
  (** Registers a propositional variable as an abstraction for a
      formula. Proofs in SMTCoq have to be given in terms of formulas. *)
  let rec register_prop_vars p = match app_name p with
    | Some (n, [formula; p]) when n == H.decl_atom ->
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
    | Some (n, [_; _; _; _; p]) when n == H.ast || n == H.asf ->
      begin match value p with
        | Lambda ({sname = Name n}, p) -> get_assumptions (n :: acc) p
        | _ -> assert false
      end
    | _ -> acc, p



  let rec rm_used' assumptions t = match name t with
    | Some x -> List.filter (fun y -> y != x) assumptions
    | None -> match app_name t with
      | Some (_, l) -> List.fold_left rm_used' assumptions l
      | None -> assumptions

  (** Remove used assumptions from the environment *)
  let rm_used env t = { env with assum = rm_used' env.assum t }


  let rm_duplicates eq l =
    let rec aux acc = function
      | x :: r -> if List.exists (eq x) acc then aux acc r else aux (x :: acc) r
      | [] -> acc in
    aux [] (List.rev l)
  
  (** Create an intermediate resolution step in [satlem] with the accumulated
      clauses. {!Reso} ignores the resulting clause so we can just give the
      empty clause here. *)
  let mk_inter_resolution clauses = match clauses with
    | [] -> (* not false *)
      mk_clause_cl Fals [not_ tfalse] []
      (* assert false *)
    | [id] -> id
    | _ -> mk_clause ~reuse:false Reso [] clauses



  let is_ty_Bool ty = match name ty with
    | Some n -> n == H.tBool
    | _ -> false


  (** Accumulates equalities for congruence. This is useful for when [f] takes
      multiples arguments. *)
  let rec cong neqs env p = match app_name p with
    | Some (n, [ty; rty; f; f'; x; y; p_f_eq_f'; r]) when n == H.cong ->

      let ne = not_ (eq ty x y) in
      let neqs, env =
        if List.exists (Term.equal ne) neqs then neqs, env
        else ne :: neqs, lem env r in

      begin match name f, name f' with
        | Some n, Some n' when n == n' -> neqs, env
        | None, None -> cong neqs env p_f_eq_f'
        | _ -> assert false
      end

    | Some (n, [_; _; _; r])
      when n == H.symm || n == H.negsymm ->
      cong neqs (rm_used env r) r

    (* | Some (n, [t; x; y; z; r1; r2]) when n == H.trans *)
    (* | Some (n, [t; x; z; y; r1; r2]) when n == H.negtrans || n == H.negtrans1 *)
    (* | Some (n, [t; y; x; z; r1; r2]) when n == H.negtrans2 *)

    | Some (n, [t; x1; x2; x3; r1; r2])
      when n == H.trans || n == H.negtrans ||
           n == H.negtrans1 || n == H.negtrans2 ->

      let x, y, z =
        if n == H.trans then x1, x2, x3
        else if n == H.negtrans || n == H.negtrans1 then x1, x3, x2
        else if n == H.negtrans2 then x2, x1, x3
        else assert false
      in

      (* ignore useless transitivity *)
      if term_equal x z then
        match app_name x with
        | Some (n, [t; _; _; x]) when n == H.apply ->
          let x_x = eq t x x in
          not_ x_x :: neqs,
          { env with clauses = mk_clause_cl Eqre [x_x] [] :: env.clauses }
        | _ ->
          let x_x = eq t x x in
          not_ x_x :: neqs,
          { env with clauses = mk_clause_cl Eqre [x_x] [] :: env.clauses }
      else if term_equal x y then cong neqs (rm_used env r2) r2
      else if term_equal y z then cong neqs (rm_used env r1) r1
      else
        let neqs1, env1 = cong neqs (rm_used env r1) r1 in
        cong neqs1 (rm_used env1 r2) r2

    (* | Some ("refl", [_; r]) -> neqs, rm_used env r *)

    | _ -> neqs, env
      (* eprintf "something went wrong in congruence@."; *)
      (* neqs, lem env p (\* env *\) *)


  (** Accumulates equalities for transitivity to chain them together. *)
  and trans neqs env p = match app_name p with

    | Some (n, [ty; x; y; z; p1; p2]) when n == H.trans ->
    (* | Some (("negtrans"|"negtrans1") as r, [ty; x; z; y; p1; p2]) *)
    (* | Some ("negtrans2" as r, [ty; y; x; z; p1; p2]) *)

      let merge = true in
      
      (* let clauses = lem mpred assum (lem mpred assum clauses p1) p2 in *)

      (* let x_y = th_res p1 in *)
      (* let y_z = th_res p2 in *)
      (* let x_y = match r with "negtrans2" -> eq ty y x | _ -> eq ty x y in *)
      (* let y_z = match r with "negtrans"|"negtrans1" -> eq ty z y | _ -> eq ty y z in *)
      let n_x_y = not_ (eq ty x y) in
      let n_y_z = not_ (eq ty y z) in

      let neqs2, env = if merge then trans neqs env p2 else [], lem env p2 in
      let neqs1, env = if merge then trans neqs env p1 else [], lem env p1 in

      let neqs = match neqs1, neqs2 with
        | [], [] -> [n_x_y; n_y_z]
        | [], _ -> n_x_y :: neqs2
        | _, [] -> neqs1 @ [n_y_z]
        | _, _ -> neqs1 @ neqs2
      in

      (* rm_duplicates Term.equal neqs *)
      neqs, env

    | Some (n, [_; _; _; r]) when n == H.symm || n == H.negsymm ->
      let neqs, env = trans neqs (rm_used env r) r in
      List.rev neqs, env
      
    | Some (n, [_; r]) when n == H.refl -> neqs, rm_used env r
  
    | _ -> neqs, lem env p


  

  (** Convert the local proof of a [satlem]. We use decductive style rules when
      possible but revert to axiomatic ones when the context forces us to. *)
  and lem ?(toplevel=false) env p = match app_name p with
    | Some (n, [l1; l2; x; r])
      when (n == H.or_elim_1 || n == H.or_elim_2) &&
        (match app_name r with
          | Some (n, _) -> n == H.iff_elim_1 || n == H.iff_elim_2
          | _ -> false)
      ->

      let el, rem = if n == H.or_elim_1 then l1, l2 else l2, l1 in
      
      let env = lem env r in
      let env = lem env x in
      (match env.clauses with
       | ci1 :: ci2 :: cls ->
         { env with clauses = mk_clause_cl Reso [rem] [ci1; ci2] :: cls }
       | _ -> env
      )

    | Some (n, [_; _; x; r])
      when (n == H.or_elim_1 || n == H.or_elim_2) &&
        (match app_name r with
          | Some (n, _) -> n == H.impl_elim ||
                           n == H.not_and_elim ||
                           n == H.iff_elim_1 ||
                           n == H.iff_elim_2 ||
                           n == H.xor_elim_1 ||
                           n == H.xor_elim_2 ||
                           n == H.ite_elim_1 ||
                           n == H.ite_elim_2 ||
                           n == H.ite_elim_3 ||
                           n == H.not_ite_elim_1 ||
                           n == H.not_ite_elim_2 ||
                           n == H.not_ite_elim_3
          | _ -> false)
      ->
      let env = rm_used env x in
      let env = lem env r in
      { env with ax = true }

    | Some (n, [a; b; x; r]) when n == H.or_elim_1 || n == H.or_elim_2 ->
      let env = rm_used env x in
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax -> mk_clause_cl Or [a; b] env.clauses :: []
        | _ ->
          let a_or_b = th_res r in
          mk_clause_cl Orp [not_ a_or_b; a; b] [] :: env.clauses
      in
      { env with clauses; ax = true }

    | Some (n, [a; b; r]) when n == H.impl_elim ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax -> mk_clause_cl Imp [not_ a; b] env.clauses :: []
        | _ ->
          let a_impl_b = th_res r in
          mk_clause_cl Impp [not_ a_impl_b; not_ a; b] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; r]) when n == H.xor_elim_1 ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Xor2 [not_ a; not_ b] env.clauses :: []
        | _ ->
          let a_xor_b = xor_ a b in
          mk_clause_cl Xorp2 [not_ a_xor_b; not_ a; not_ b] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; r]) when n == H.xor_elim_2 ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Xor1 [a; b] env.clauses :: []
        | _ ->
          let a_xor_b = xor_ a b in
          mk_clause_cl Xorp1 [not_ a_xor_b; a; b] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; c; r]) when n == H.ite_elim_1 ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Ite2 [not_ a; b] env.clauses :: []
        | _ ->
          let ite_a_b_c = ifte_ a b c in
          mk_clause_cl Itep2 [not_ ite_a_b_c; not_ a; b] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; c; r]) when n == H.ite_elim_2 ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Ite1 [a; c] env.clauses :: []
        | _ ->
          let ite_a_b_c = ifte_ a b c in
          mk_clause_cl Itep1 [not_ ite_a_b_c; a; c] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; c; r]) when n == H.not_ite_elim_1 ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Nite2 [not_ a; not_ b] env.clauses :: []
        | _ ->
          let ite_a_b_c = ifte_ a b c in
          mk_clause_cl Iten2 [ite_a_b_c; not_ a; not_ b] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; c; r]) when n == H.not_ite_elim_2 ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Nite1 [a; not_ c] env.clauses :: []
        | _ ->
          let ite_a_b_c = ifte_ a b c in
          mk_clause_cl Iten1 [ite_a_b_c; a; not_ c] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; b; c; r]) when n == H.ite_elim_3 ->
      let env = lem env r in
      let ite_a_b_c = ifte_ a b c in
      { env with
        clauses =
          mk_clause_cl Itep1 [not_ ite_a_b_c; a; c] [] ::
          mk_clause_cl Itep2 [not_ ite_a_b_c; not_ a; b] [] ::
          env.clauses;
        ax = true }

    | Some (n, [a; b; c; r]) when n == H.not_ite_elim_3 ->
      let env = lem env r in
      let ite_a_b_c = ifte_ a b c in
      { env with
        clauses =
          mk_clause_cl Iten1 [ite_a_b_c; a; not_ c] [] ::
          mk_clause_cl Iten2 [ite_a_b_c; not_ a; not_ b] [] ::
          env.clauses;
        ax = true }

    | Some (n, [a; b; r]) when n == H.iff_elim_1 ->
      begin match app_name r with
        | Some (n, [a; b; r]) when n == H.not_iff_elim ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nequ2 [not_ a; not_ b] env.clauses :: []
            | _ ->
              let a_iff_b = iff_ a b in
              mk_clause_cl Equn1 [a_iff_b; not_ a; not_ b] [] :: env.clauses
          in
          { env with clauses }
        | Some (n, [a; b; r]) when n == H.not_xor_elim ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nxor2 [not_ a; b] env.clauses :: []
            | _ ->
              let a_xor_b = xor_ a b in
              mk_clause_cl Xorn2 [a_xor_b; not_ a; b] [] :: env.clauses
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

      | Some (n, [a; b; r]) when n == H.iff_elim_2 ->
      begin match app_name r with
        | Some (n, [a; b; r]) when n == H.not_iff_elim ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nequ1 [a; b] env.clauses :: []
            | _ ->
              let a_iff_b = iff_ a b in
              mk_clause_cl Equn2 [a_iff_b; a; b] [] :: env.clauses
          in
          { env with clauses }
        | Some (n, [a; b; r]) when n == H.not_xor_elim ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nxor1 [a; not_ b] env.clauses :: []
            | _ ->
              let a_xor_b = xor_ a b in
              mk_clause_cl Xorn1 [a_xor_b; a; not_ b] [] :: env.clauses
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

    | Some (n, [a; b; r]) when n == H.not_and_elim ->
      let env = lem env r in
      let clauses = match env.clauses with
        | [_] when not env.ax ->
          mk_clause_cl Nand [not_ a; not_ b] env.clauses :: []
        | _ ->
          let a_and_b = and_ a b in
          mk_clause_cl Andn [a_and_b; not_ a; not_ b] [] :: env.clauses
      in
      { env with clauses }

    | Some (n, [a; _; r]) when n == H.and_elim_1 ->
      begin match app_name r with
        | Some (n, [a; b; r]) when n == H.not_impl_elim ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax -> mk_clause_cl Nimp1 [a] env.clauses :: []
            | _ ->
              let a_impl_b = impl_ a b in
              mk_clause_cl Impn1 [a_impl_b; a] [] :: env.clauses
          in
          { env with clauses }

        | Some (n, [a; b; r]) when n == H.not_or_elim ->
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

    | Some (n, [a; b; r]) when n == H.and_elim_2 ->
      begin match app_name r with
        | Some (n, [a; b; r]) when n == H.not_impl_elim ->
          let env = lem env r in
          let clauses = match env.clauses with
            | [_] when not env.ax ->
              mk_clause_cl Nimp2 [not_ b] env.clauses :: []
            | _ ->
              let a_impl_b = impl_ a b in
              mk_clause_cl Impn2 [a_impl_b; not_ b] [] :: env.clauses
          in
          { env with clauses }

        | Some (n, [a; b; r]) when n == H.not_or_elim ->
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

    (* Only handle symmetry rules when they are the only rule of the lemma *)
      
    | Some (n, [ty; a; b; r])
      when n == H.symm && toplevel && name r <> None ->
      let env = lem env r in
      let a_b = eq ty a b in
      let b_a = eq ty b a in

      { env with
        clauses = mk_clause_cl Eqtr [not_ a_b; b_a] [] :: env.clauses;
        ax = true }

    | Some (n, [ty; a; b; r])
      when n == H.negsymm && toplevel && name r <> None ->
      let env = lem env r in
      let a_b = eq ty a b in
      let b_a = eq ty b a in

      { env with
        clauses = mk_clause_cl Eqtr [a_b; not_ b_a] [] :: env.clauses;
        ax = true }

    (* Ignore other symmetry of equlity rules *)
    | Some (n, [_; _; _; r]) when n == H.symm || n == H.negsymm ->
      lem (rm_used env r) r

    (* Ignore double negation *)
    | Some (n, [_; r]) when n == H.not_not_elim || n == H.not_not_intro ->
      lem env r

    (* Should not be traversed anyway *)
    | Some (n, [_; r]) when n == H.pred_eq_t || n == H.pred_eq_f ->
      lem env r


    | Some (n, [f]) when n == H.trust_f ->
      begin match app_name f with
        | Some (n, ty :: _)
          when n == H.eq &&
               (match name ty with Some i -> i == H.tInt | None -> false) ->
          (* trust are for lia lemma if equality between integers *)
          { env with clauses = mk_clause_cl Lage [f] [] :: env.clauses }
        | Some (n, [x]) when n == H.not_ ->
          begin match app_name x with
            | Some (n, ty :: _)
              when n == H.eq &&
                   (match name ty with Some i -> i == H.tInt | None -> false) ->
              (* trust are for lia lemma if disequality between integers *)
              { env with clauses = mk_clause_cl Lage [f] [] :: env.clauses }
            | _ -> { env with clauses = mk_clause_cl Hole [f] [] :: env.clauses }
          end
        | _ -> { env with clauses = mk_clause_cl Hole [f] [] :: env.clauses }
      end
      
    | Some (n, [_; _; _; _; r; w])
      when n == H.trans &&
           (match app_name w with
            | Some (n, _) -> n == H.pred_eq_t || n == H.pred_eq_f
            | _ -> false)
      ->
      (* Remember which direction of the implication we want for congruence over
         predicates *)
      let env = match app_name w with
        | Some (n, [pt; x]) when n == H.pred_eq_t ->
          let env = rm_used env x in
          { env with mpred = MTerm.add pt false env.mpred }
        | Some (n, [pt; x]) when n == H.pred_eq_f ->
          let env = rm_used env x in
          { env with mpred = MTerm.add pt true env.mpred }
        | _ -> assert false
      in

      lem env r


    | Some (n, [ty; x; y; z; p1; p2])
      when n == H.negtrans || n == H.negtrans1 ->

      if term_equal x y || term_equal x z || term_equal y z then env
      else 
        let env = lem env p2 in
        let env = lem env p1 in

        let x_y = eq ty x y in
        let y_z = eq ty y z in
        let x_z = eq ty x z in

        { env with
          clauses = mk_clause_cl Eqtr [x_y; not_ y_z; not_ x_z] [] :: env.clauses;
          ax = true }

    | Some (n, [ty; x; y; z; p1; p2]) when n == H.negtrans2 ->

      if term_equal x y || term_equal x z || term_equal y z then env
      else 
        let env = lem env p2 in
        let env = lem env p1 in

        let x_y = eq ty x y in
        let y_z = eq ty y z in
        let x_z = eq ty x z in

        { env with
          clauses = mk_clause_cl Eqtr [not_ x_y; y_z; not_ x_z] [] :: env.clauses;
          ax = true }

    | Some (n, [ty; x; y; z; p1; p2]) when n == H.trans ->
    (* | Some (("negtrans"|"negtrans1"), [ty; x; z; y; p1; p2]) *)
    (* | Some ("negtrans2", [ty; y; x; z; p1; p2]) *)

      (* if Term.equal x y || Term.equal x z || Term.equal y z then env *)
      (* else  *)
      
      let neqs, env = trans [] env p in
      let x_z = eq ty x z in
      let cl = (neqs @ [x_z]) in
      let id = mk_clause_cl Eqtr cl [] in
      let id = mk_clause_cl ~reuse:false Weak cl [id] in
      { env with 
        clauses = id :: env.clauses;
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
    | Some (n, [_; rty; pp; _; x; y; _; _])
      when n == H.cong && is_ty_Bool rty ->
      
      let neqs, env = cong [] env p in
      let cptr, cpfa = match app_name (th_res p) with
        | Some (n, [_; apx; apy]) when n == H.eq ->
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
    | Some (n, [_; _; _; _; _; _; _; _]) when n == H.cong ->
      let neqs, env = cong [] env p in
      let fx_fy = th_res p in
      let cl = neqs @ [fx_fy] in
      { env with
        clauses = mk_clause_cl Eqco cl [] :: env.clauses;
        ax = true }

    | Some (n, [_; _]) when n == H.refl ->
      let x_x = th_res p in
      { env with clauses = mk_clause_cl Eqre [x_x] [] :: env.clauses }

    | Some (n, [_; _; a; i; v]) when n == H.row1 ->
      let raiwaiv = th_res p in
      { env with clauses = mk_clause_cl Row1 [raiwaiv] [] :: env.clauses }

    | Some (n, [ti; _; i; j; a; v; r]) when n == H.row ->
      let env = lem env r in
      let i_eq_j = eq ti i j in
      let pr1 = th_res p in
      { env with
        clauses = mk_clause_cl Row2 [i_eq_j; pr1] [] :: env.clauses;
        ax = true}

    | Some (n, [ti; _; i; j; a; v; npr1]) when n == H.negativerow ->
      let env = lem env npr1 in
      let i_eq_j = eq ti i j in
      let pr1 = match app_name (th_res p) with
        | Some (n, [pr1]) when n == H.not_ -> pr1
        | _ -> assert false
      in
      { env with clauses = mk_clause_cl Row2 [i_eq_j; pr1] [] :: env.clauses }

    | Some (n, [_; x; y]) when n == H.bv_disequal_constants ->
      { env with clauses = mk_clause_cl Bbdis [th_res p] [] :: env.clauses }
  
    | Some (rule, args) ->
      eprintf "Warning: Introducing hole for unsupported rule %a@."
        Hstring.print rule;
      { env with clauses = mk_clause_cl Hole [th_res p] [] :: env.clauses }

    | None ->

      match name p with

      | Some n when n == H.truth ->
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
        | Some (n, [cl]) when n == H.holds -> n, cl, r
        | _ -> assert false
      end

    | _ -> assert false


  (** Returns the clause used in a resolution step *)
  let clause_qr p =
    try match name p with
      | Some n -> get_input_id n
      | _ -> raise Not_found
    with Not_found -> match app_name (deref p).ttype with
      | Some (n, [cl]) when n == H.holds ->
        (* eprintf "get_clause id : %a@." print_term cl; *)
        get_clause_id (to_clause cl)
      | _ -> raise Not_found
             

  (* let rec reso_of_QR acc qr = match app_name qr with
   *   | Some (n, [_; _; u1; u2; _]) when n == H.q || n == H.r ->
   *     reso_of_QR (reso_of_QR acc u1) u2
   *   | _ -> clause_qr qr :: acc *)

  (** Returns clauses used in a linear resolution chain *)
  (* let reso_of_QR qr = reso_of_QR [] qr |> List.rev *)


  (* let rec reso_of_QR qr = match app_name qr with
   *   | Some (n, [_; _; u1; u2; _]) when n == H.q || n == H.r ->
   *     reso_of_QR u1 @ reso_of_QR u2
   *   | _ -> [clause_qr qr] *)

  let rec reso_of_QR depth acc qr = match app_name qr with
    | Some (n, [_; _; u1; u2; _]) when n == H.q || n == H.r ->
      let depth = depth + 1 in
      reso_of_QR depth (reso_of_QR depth acc u1) u2
    | _ -> (depth, clause_qr qr) :: acc

  (** Returns clauses used in a linear resolution chain *)
  let reso_of_QR qr =
    reso_of_QR 0 [] qr
    |> List.rev
    |> List.stable_sort (fun (d1, _) (d2, _) -> d2 - d1)
    |> List.map snd
  
  
  (** convert resolution proofs of [satlem_simplify] *)
  let satlem_simplify p = match app_name p with
    | Some (n, [_; _; _; qr; p]) when n == H.satlem_simplify ->
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
  let satlem_simplifies_c p =
    many_satlem_simplify None p |> snd


  (* There must be at least one, returns id of last deduced clause *)
  let reso_of_satlem_simplify p =
    match many_satlem_simplify None p with
    | Some id, _ -> id
    | _ -> assert false


  let rec bb_trim_intro_unit env p = match app_name p with
    | Some (n, [_; _; _; ullit; _; l])
      when n == H.intro_assump_f || n == H.intro_assump_t ->
      let env = rm_used env ullit in
      (match value l with
       | Lambda (_, p) -> bb_trim_intro_unit env p
       | _ -> assert false)
    | _ -> env, p

  
  let is_last_bbres p = match app_name p with
    | Some (n, [_; _; _; _; l]) when n == H.satlem_simplify ->
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


  let bb_lem env p =
    let env, p = bb_trim_intro_unit env p in
    let id = bb_lem_res None p in
    { env with clauses = id :: env.clauses }
  


  exception ArithLemma

  (** Remove superfluous applications at the top of [satlem] and returns a list
      of proofs whose resulting clauses need to be resolved.

      @raises {!ArithLemma} if the proof is a trust statement (we assume it is
      the case for now).  *)
  let rec trim_junk_satlem p = match app_name p with
    | Some (n, [p]) when n == H.clausify_false ->
      (match name p with
       | Some n when n == H.trust -> raise ArithLemma
       | _ -> trim_junk_satlem p
      )
    | Some (n, [_; p1; p2]) when n == H.contra ->
      trim_junk_satlem p1 @ trim_junk_satlem p2
    | _ -> [p]

  
  (** Returns the continuation of a [satlem]. *)
  let continuation_satlem p = match value p with
    | Lambda ({sname=Name n}, r) -> n, r
    | _ -> assert false


  let is_bbr_satlem_lam p = match value p with
    | Lambda ({sname = Name h}, _) ->
      (try String.sub (Hstring.view h) 0 5 = "bb.cl"
       with Invalid_argument _ -> false)
    | _ -> false 
  
  let has_intro_bv p = match app_name p with
    | Some (n, _) when n == H.intro_assump_f || n == H.intro_assump_t -> true
    | _ -> false


  let has_prefix p s =
    try
      for i = 0 to String.length p - 1 do
        if p.[i] <> s.[i] then raise Exit
      done;
      true
    with Exit | Invalid_argument _ -> false
      
  
  (** Convert [satlem]. Clauses are chained together with an intermediate
      resolution step when needed, and when CVC4 uses superfluous local
      assumption, the clause is weakened. *)
  let rec satlem ?(prefix_cont) p =
    let old_p = p in
    match app_name p with

    | Some (n, [c; _; l; p]) when n == H.satlem ->
      (* eprintf "SATLEM ---@."; *)
      let lem_name, lem_cont = continuation_satlem p in
      begin match prefix_cont with
        | Some pref when not (has_prefix pref (Hstring.view lem_name)) -> old_p
        | _ ->
          let cl = to_clause c in
          (try
             let assumptions, l = get_assumptions [] l in
             let l = trim_junk_satlem l in
             let env = { empty with assum = assumptions } in
             let lem =
               if is_bbr_satlem_lam p || List.exists has_intro_bv l then bb_lem
               else lem ~toplevel:true in
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
             (* if env.assum = [] then id else *) 
             let satlem_id = mk_clause Weak cl [id] in
             register_clause_id cl satlem_id;
             register_decl_id lem_name satlem_id;
             (* eprintf "--- SATLEM@."; *)

           with ArithLemma ->
             let satlem_id = mk_clause Lage cl [] in
             register_clause_id cl satlem_id

          );

          satlem ?prefix_cont lem_cont
      end

    | Some (n, [_; _; _; _; l]) when n == H.satlem_simplify ->
      (match value l with
       | Lambda ({sname=Name _}, r) ->
         (match name r with
          | Some _ -> p
          | None -> match app_name r with
            | Some (n, _) when n == H.satlem_simplify -> p
            | _ ->
              (* Intermediate satlem_simplify *)
              (* eprintf ">>>>>> intermediate satlemsimplify@."; *)
              snd (satlem_simplify p) |> satlem ?prefix_cont
         )
       | _ -> p)

    | _ -> p


  let rec bbt p = match app_name p with
    | Some (b, [n; v; bb]) when b == H.bv_bbl_var ->
      let res = bblast_term n (a_var_bv n v) bb in
      Some (mk_clause_cl Bbva [res] [])
    | Some (b, [n; bb; bv]) when b == H.bv_bbl_const ->
      let res = bblast_term n (a_bv n bv) bb in
      Some (mk_clause_cl Bbconst [res] [])
    | Some (rop, [n; x; y; _; _; rb; xbb; ybb])
      when rop == H.bv_bbl_bvand ||
           rop == H.bv_bbl_bvor ||
           rop == H.bv_bbl_bvxor ||
           rop == H.bv_bbl_bvadd ||
           rop == H.bv_bbl_bvmul ||
           rop == H.bv_bbl_bvult ||
           rop == H.bv_bbl_bvslt
      ->
      let bvop, rule =
        if rop == H.bv_bbl_bvand then bvand, Bbop
        else if rop == H.bv_bbl_bvor then bvor, Bbop
        else if rop == H.bv_bbl_bvxor then bvxor, Bbop
        else if rop == H.bv_bbl_bvadd then bvadd, Bbadd
        else if rop == H.bv_bbl_bvmul then bvmul, Bbmul
        else if rop == H.bv_bbl_bvult then bvult, Bbult
        else if rop == H.bv_bbl_bvslt then bvslt, Bbslt
        else assert false
      in
      let res = bblast_term n (bvop n x y) rb in
      (match bbt xbb, bbt ybb with
       | Some idx, Some idy ->
         Some (mk_clause_cl rule [res] [idx; idy])
       | _ -> assert false
      )
      
    | Some (c, [n; x; _; rb; xbb]) when c == H.bv_bbl_bvnot ->
      let res = bblast_term n (bvnot n x) rb in
      (match bbt xbb with
       | Some idx ->
         Some (mk_clause_cl Bbnot [res] [idx])
       | _ -> assert false
      )
    | Some (c, [n; x; _; rb; xbb]) when c == H.bv_bbl_bvneg ->
      let res = bblast_term n (bvneg n x) rb in
      (match bbt xbb with
       | Some idx ->
         Some (mk_clause_cl Bbneg [res] [idx])
       | _ -> assert false
      )
        
    | Some (c, [n; m; m'; x; y; _; _; rb; xbb; ybb])
      when c == H.bv_bbl_concat ->
      let res = bblast_term n (concat n m m' x y) rb in
      (match bbt xbb, bbt ybb with
       | Some idx, Some idy ->
         Some (mk_clause_cl Bbconc [res] [idx; idy])
       | _ -> assert false
      )
        
    | Some (c, [n; i; j; m; x; _; rb; xbb])
      when c == H.bv_bbl_extract ->
      let res = bblast_term n (extract n i j m x) rb in
      (match bbt xbb with
       | Some idx ->
         Some (mk_clause_cl Bbextr [res] [idx])
       | _ -> assert false
      )

    | Some (c, [n; k; m; x; _; rb; xbb])
      when c == H.bv_bbl_zero_extend ->
      let res = bblast_term n (zero_extend n k m x) rb in
      (match bbt xbb with
       | Some idx ->
         Some (mk_clause_cl Bbzext [res] [idx])
       | _ -> assert false
      )

    | Some (c, [n; k; m; x; _; rb; xbb])
      when c == H.bv_bbl_sign_extend ->
      let res = bblast_term n (sign_extend n k m x) rb in
      (match bbt xbb with
       | Some idx ->
         Some (mk_clause_cl Bbsext [res] [idx])
       | _ -> assert false
      )
        
    | None ->
      begin match name p with
      | Some h -> (* should be an declared clause *)
        Some (try get_input_id h with Not_found -> assert false)
      | None -> assert false
      end
      
    | Some (rule, args) ->
      eprintf "Warning: Introducing hole for unsupported rule %a@."
        Hstring.print rule;
      Some (mk_clause_cl Hole [ttype p] [])

  

  let rec bblast_decls p = match app_name p with
    | Some (d, [n; b; t; bb; l]) when d == H.decl_bblast ->
      (* let res = bblast_term n t b in *)
      let id = match bbt bb with Some id -> id | None -> assert false in
      begin match value l with
        | Lambda ({sname = Name h}, p) ->
          register_decl_id h id;
          bblast_decls p
        | _ -> assert false
      end
      
    | Some (d, [n; b; t; a; bb; _; l]) when d == H.decl_bblast_with_alias ->
      (* register_termalias a t; *)
      (* begin match name a with *)
      (*   | Some n -> register_alias n t *)
      (*   | None -> () *)
      (* end; *)
      let id = match bbt bb with Some id -> id | None -> assert false in
      begin match value l with
        | Lambda ({sname = Name h}, p) ->
          register_decl_id h id;
          bblast_decls p
        | _ -> assert false
      end

    | _ -> p


  let bv_pred n =
    if n == H.bv_bbl_eq then Bbeq
    else if n == H.bv_bbl_eq_swap then Bbeq
    else if n == H.bv_bbl_bvult then Bbult
    else if n == H.bv_bbl_bvslt then Bbslt
    else assert false

  
  let rec bblast_eqs p = match app_name p with
    | Some (n, [f; pf; l]) when n == H.th_let_pf ->
      begin match app_name pf with
        | Some (rule_name, [_; _; _; _; _; _; a; b]) ->
          begin match name a, name b with
          | Some na, Some nb ->
            let id1, id2 =
              try get_input_id na, get_input_id nb
              with Not_found -> assert false in
            let clid = mk_clause_cl (bv_pred rule_name) [f] [id1; id2] in
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
    | Some (n, _) when n == H.decl_bblast || n == H.decl_bblast_with_alias ->
      p
      |> bblast_decls
      |> bblast_eqs
      |> register_prop_vars
      |> satlem ~prefix_cont:"bb."
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

    |> deferred
  
    |> admit_preproc

    |> register_prop_vars
    |> satlem

    |> bb_proof
    
    |> reso_of_satlem_simplify

  

  let convert_pt p =
    eprintf "Converting LFSC proof to SMTCoq...@?";
    let t0 = Sys.time () in
    let r = convert p in
    let t1 = Sys.time () in
    eprintf " Done [%.3f s]@." (t1 -. t0);
    r

  

  (** Clean global environments *)
  let clear () =
    Ast.clear_sc ();
    T.clear ()


end

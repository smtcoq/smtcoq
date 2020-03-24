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


open SmtForm
open SmtCertif
open SmtTrace

module MakeCnf (Form:FORM) =
  struct 

    type form_info = 
      | Immediate of bool (* true if the positive literal is set *) 
      | Done (* means that the equivalence clauses have been generated *)
      | Todo (* nothing has been done, process the cnf transformation *)

    type cnf_state =
      { stt : trace_state;
        mutable last : Form.t SmtCertif.clause;
        info : (int, form_info) Hashtbl.t;
        mutable cnf_todo : Form.t array list
      }
    let create_cnf_state (st:trace_state) : cnf_state =
      let last = SmtTrace.mk_scertif st Root None in
      { stt = st;
        last = last;
        info = Hashtbl.create 17;
        cnf_todo = []
      }

    let get_trace_state (st:cnf_state) = st.stt

    let get_last (st:cnf_state) = st.last
    let set_last (st:cnf_state) (cl:Form.t SmtCertif.clause) = st.last <- cl

    let push_cnf (st:cnf_state) args = st.cnf_todo <- args :: st.cnf_todo

    let get_info st l =
      try Hashtbl.find st.info (Form.index l)
      with Not_found -> Todo 

    let set_done st l =
      Hashtbl.add st.info (Form.index l) Done

    let set_immediate st l = 
      Hashtbl.add st.info (Form.index l) (Immediate (Form.is_pos l))

    let test_immediate st l = 
      match get_info st l with
      | Immediate b -> b = Form.is_pos l 
      | _ -> false

    let check_trivial st cl =
      List.exists (test_immediate st) cl 

    let link_Other st other cl =
      if not (check_trivial st cl) then 
        let c = mkOther (get_trace_state st) other (Some cl) in
        link (get_last st) c;
        set_last st c

    let both_lit l = if Form.is_pos l then Form.neg l,l else l, Form.neg l 

    let or_of_imp args =  
      Array.mapi (fun i l -> 
	if i = Array.length args - 1 then l else Form.neg l) args 

    let rec cnf st l =
      match get_info st l with
      | Immediate _ | Done -> ()
      | Todo -> 
	  match Form.pform l with
	  | Fatom _ | FbbT _ -> ()

	  | Fapp (op,args) ->
	      match op with
	      | Ftrue | Ffalse -> () 

	      | Fand ->
		  let nl,pl = both_lit l in
		  let nargs = Array.map Form.neg args in
                  link_Other st (BuildDef pl) (pl::Array.to_list nargs);
		  Array.iteri (fun i l' -> 
		    link_Other st (BuildProj (nl,i)) [nl;l']) args;
		  set_done st l;
		  Array.iter (cnf st) args

	      | For ->
		  let nl,pl = both_lit l in
		  link_Other st (BuildDef nl) (nl::Array.to_list args);
		  Array.iteri (fun i l' -> 
		    link_Other st (BuildProj(pl,i)) [pl;Form.neg l']) args;
		  set_done st l;
		  Array.iter (cnf st) args

	      | Fimp ->
		  let args = or_of_imp args in
		  let nl,pl = both_lit l in
		  link_Other st (BuildDef nl) (nl::Array.to_list args);
		  Array.iteri (fun i l' -> 
		    link_Other st (BuildProj(pl,i)) [pl;Form.neg l']) args;
		  set_done st l;
		  Array.iter (cnf st) args
	
	      | Fxor -> 
		  let nl,pl = both_lit l in
		  let a, b = args.(0), args.(1) in
		  let na, nb = Form.neg a, Form.neg b in
		  link_Other st (BuildDef nl) [nl;a;b];
		  link_Other st (BuildDef pl) [pl;a;nb];
		  link_Other st (BuildDef2 nl) [nl;na;nb];
		  link_Other st (BuildDef2 pl) [pl;na;b];
		  set_done st l;
		  cnf st a;
		  cnf st b
		
	      | Fiff ->
		  let nl,pl = both_lit l in
		  let a, b = args.(0), args.(1) in
		  let na, nb = Form.neg a, Form.neg b in
		  link_Other st (BuildDef nl) [nl;a;nb];
		  link_Other st (BuildDef pl) [pl;na;nb];
		  link_Other st (BuildDef2 nl) [nl;na;b];
		  link_Other st (BuildDef2 pl) [pl;a;b];
		  set_done st l;
		  cnf st a;
		  cnf st b

	      | Fite ->
		  let nl,pl = both_lit l in
		  let a, b, c = args.(0), args.(1), args.(2) in
		  let na, nb, nc = Form.neg a, Form.neg b, Form.neg c in
		  link_Other st (BuildDef nl) [nl;a;c];
		  link_Other st (BuildDef pl) [pl;a;nc];
		  link_Other st (BuildDef2 nl) [nl;na;b];
		  link_Other st (BuildDef2 pl) [pl;na;nb];
		  set_done st l;
		  cnf st a;
		  cnf st b;
		  cnf st c

	      | Fnot2 _ -> cnf st args.(0)
              | Fforall _ -> assert false

    exception Cnf_done

    let rec imm_link_Other st other l =
      if not (test_immediate st l) then
	let c = mkOther (get_trace_state st) other (Some [l]) in
	link (get_last st) c;
	set_last st c;
	imm_cnf st c

    and imm_cnf st c =
      let l = 
	match c.value with
	| Some [l] -> 
	    begin match Form.pform l with
	    | Fapp (Fnot2 _, args) -> 
		let l' = args.(0) in
		if Form.is_pos l then l'
		else Form.neg l'
	    | _ -> l
	    end
	| _ -> assert false in
      match get_info st l with
      | Immediate b -> if b = Form.is_neg l then raise Cnf_done
      | Done -> assert false
      | Todo ->
	  set_immediate st l;

	  match Form.pform l with
	  | Fatom _ | FbbT _ -> ()

	  | Fapp (op,args) ->
	      match op with
	      | Ftrue | Ffalse -> ()

	      | Fand ->
		  if Form.is_pos l then 
		    Array.iteri (fun i l' -> 
                        imm_link_Other st (ImmBuildProj(c,i)) l') args
		  else begin
		    let nargs = Array.map Form.neg args in
		    link_Other st (ImmBuildDef c) (Array.to_list nargs);
		    push_cnf st args
		  end

	      | For ->
		  if Form.is_pos l then begin
		    link_Other st (ImmBuildDef c) (Array.to_list args);
		    push_cnf st args
		  end else 
		    Array.iteri (fun i l' ->
		      imm_link_Other st (ImmBuildProj(c,i)) (Form.neg l')) args

	      | Fimp ->
		  let args = or_of_imp args in
		  if Form.is_pos l then begin
		    link_Other st (ImmBuildDef c) (Array.to_list args);
		    push_cnf st args
		  end else 
		    Array.iteri (fun i l' ->
		      imm_link_Other st (ImmBuildProj(c,i)) (Form.neg l')) args

	      | Fxor -> 
		  let args1 = 
		    if Form.is_pos l then [args.(0);args.(1)]
		    else [args.(0);Form.neg args.(1)] in
		  let args2 =
		    if Form.is_pos l then [Form.neg args.(0);Form.neg args.(1)] 
		    else  [Form.neg args.(0); args.(1)] in
		  link_Other st (ImmBuildDef c) args1;
		  link_Other st (ImmBuildDef2 c) args2;
		  push_cnf st args
		
	      | Fiff ->
		  let args1 = 
		    if Form.is_pos l then [args.(0);Form.neg args.(1)]
		    else [Form.neg args.(0);Form.neg args.(1)] in
		  let args2 =
		    if Form.is_pos l then [Form.neg args.(0);args.(1)] 
		    else  [args.(0); args.(1)] in
		  link_Other st (ImmBuildDef c) args1;
		  link_Other st (ImmBuildDef2 c) args2;
		  push_cnf st args

	      | Fite ->
		  let args1 = 
		    if Form.is_pos l then [args.(0);Form.neg args.(2)]
		    else [args.(0);Form.neg args.(2)] in
		  let args2 =
		    if Form.is_pos l then [Form.neg args.(0);args.(1)] 
		    else  [Form.neg args.(0); Form.neg args.(1)] in
		  link_Other st (ImmBuildDef c) args1;
		  link_Other st (ImmBuildDef2 c) args2;
		  push_cnf st args

              | Fnot2 _ -> assert false
              | Fforall _ -> assert false

    let make_cnf (stt:trace_state) reify c =
      let ftrue = Form.get reify (Fapp(Ftrue, [||])) in
      let ffalse = Form.get reify (Fapp(Ffalse, [||])) in
      let st = create_cnf_state stt in
      set_last st c;
      link_Other st True [ftrue];
      link_Other st False [Form.neg ffalse];
      (try 
	imm_cnf st c;
        List.iter (Array.iter (cnf st)) st.cnf_todo
      with Cnf_done -> ());
      let res = get_last st in
      res

  end


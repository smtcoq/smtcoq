(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
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

    let info = Hashtbl.create 17 

    let init_last = 
      let last = SmtTrace.mk_scertif Root None in
      SmtTrace.clear ();
      last

    let last = ref init_last

    let cnf_todo = ref [] 

    let clear () = 
      Hashtbl.clear info;
      last := init_last;
      cnf_todo := []

    let push_cnf args = cnf_todo := args :: !cnf_todo

    let get_info l =
      try Hashtbl.find info (Form.index l)
      with Not_found -> Todo 

    let set_done l =
      Hashtbl.add info (Form.index l) Done

    let set_immediate l = 
      Hashtbl.add info (Form.index l) (Immediate (Form.is_pos l))

    let test_immediate l = 
      match get_info l with
      | Immediate b -> b = Form.is_pos l 
      | _ -> false

    let check_trivial cl =
      List.exists test_immediate cl 

    let link_Other other cl =
      if not (check_trivial cl) then 
	let c = mkOther other (Some cl) in
	link !last c;
	last := c

    let both_lit l = if Form.is_pos l then Form.neg l,l else l, Form.neg l 

    let or_of_imp args =  
      Array.mapi (fun i l -> 
	if i = Array.length args - 1 then l else Form.neg l) args 

    let rec cnf l =
      match get_info l with
      | Immediate _ | Done -> ()
      | Todo -> 
	  match Form.pform l with
	  | Fatom _ -> ()

	  | Fapp (op,args) ->
	      match op with
	      | Ftrue | Ffalse -> () 

	      | Fand ->
		  let nl,pl = both_lit l in
		  let nargs = Array.map Form.neg args in
		  link_Other (BuildDef pl) (pl::Array.to_list nargs);
		  Array.iteri (fun i l' -> 
		    link_Other (BuildProj (nl,i)) [nl;l']) args;
		  set_done l;
		  Array.iter cnf args

	      | For ->
		  let nl,pl = both_lit l in
		  link_Other (BuildDef nl) (nl::Array.to_list args);
		  Array.iteri (fun i l' -> 
		    link_Other (BuildProj(pl,i)) [pl;Form.neg l']) args;
		  set_done l;
		  Array.iter cnf args

	      | Fimp ->
		  let args = or_of_imp args in
		  let nl,pl = both_lit l in
		  link_Other (BuildDef nl) (nl::Array.to_list args);
		  Array.iteri (fun i l' -> 
		    link_Other (BuildProj(pl,i)) [pl;Form.neg l']) args;
		  set_done l;
		  Array.iter cnf args
	
	      | Fxor -> 
		  let nl,pl = both_lit l in
		  let a, b = args.(0), args.(1) in
		  let na, nb = Form.neg a, Form.neg b in
		  link_Other (BuildDef nl) [nl;a;b];
		  link_Other (BuildDef pl) [pl;a;nb];
		  link_Other (BuildDef2 nl) [nl;na;nb];
		  link_Other (BuildDef2 pl) [pl;na;b];
		  set_done l;
		  cnf a;
		  cnf b
		
	      | Fiff ->
		  let nl,pl = both_lit l in
		  let a, b = args.(0), args.(1) in
		  let na, nb = Form.neg a, Form.neg b in
		  link_Other (BuildDef nl) [nl;a;nb];
		  link_Other (BuildDef pl) [pl;na;nb];
		  link_Other (BuildDef2 nl) [pl;na;b];
		  link_Other (BuildDef2 pl) [pl;a;b];
		  set_done l;
		  cnf a;
		  cnf b

	      | Fite ->
		  let nl,pl = both_lit l in
		  let a, b, c = args.(0), args.(1), args.(2) in
		  let na, nb, nc = Form.neg a, Form.neg b, Form.neg c in
		  link_Other (BuildDef nl) [nl;a;c];
		  link_Other (BuildDef pl) [pl;a;nc];
		  link_Other (BuildDef2 nl) [nl;na;b];
		  link_Other (BuildDef2 pl) [pl;na;nb];
		  set_done l;
		  cnf a;
		  cnf b;
		  cnf c

	      | Fnot2 _ -> cnf args.(0)
 
    exception Cnf_done

    let rec imm_link_Other other l =
      if not (test_immediate l) then
	let c = mkOther other (Some [l]) in
	link !last c;
	last := c;
	imm_cnf c

    and imm_cnf c =
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
      match get_info l with
      | Immediate b -> if b = Form.is_neg l then raise Cnf_done
      | Done -> assert false
      | Todo ->
	  set_immediate l;

	  match Form.pform l with
	  | Fatom _ -> ()

	  | Fapp (op,args) ->
	      match op with
	      | Ftrue | Ffalse -> ()

	      | Fand ->
		  if Form.is_pos l then 
		    Array.iteri (fun i l' -> 
		      imm_link_Other (ImmBuildProj(c,i)) l') args
		  else begin
		    let nargs = Array.map Form.neg args in
		    link_Other (ImmBuildDef c) (Array.to_list nargs);
		    push_cnf args
		  end

	      | For ->
		  if Form.is_pos l then begin
		    link_Other (ImmBuildDef c) (Array.to_list args);
		    push_cnf args
		  end else 
		    Array.iteri (fun i l' ->
		      imm_link_Other (ImmBuildProj(c,i)) (Form.neg l')) args

	      | Fimp ->
		  let args = or_of_imp args in
		  if Form.is_pos l then begin
		    link_Other (ImmBuildDef c) (Array.to_list args);
		    push_cnf args
		  end else 
		    Array.iteri (fun i l' ->
		      imm_link_Other (ImmBuildProj(c,i)) (Form.neg l')) args

	      | Fxor -> 
		  let args1 = 
		    if Form.is_pos l then [args.(0);args.(1)]
		    else [args.(0);Form.neg args.(1)] in
		  let args2 =
		    if Form.is_pos l then [Form.neg args.(0);Form.neg args.(1)] 
		    else  [Form.neg args.(0); args.(1)] in
		  link_Other (ImmBuildDef c) args1;
		  link_Other (ImmBuildDef2 c) args2;
		  push_cnf args
		
	      | Fiff ->
		  let args1 = 
		    if Form.is_pos l then [args.(0);Form.neg args.(1)]
		    else [Form.neg args.(0);Form.neg args.(1)] in
		  let args2 =
		    if Form.is_pos l then [Form.neg args.(0);args.(1)] 
		    else  [args.(0); args.(1)] in
		  link_Other (ImmBuildDef c) args1;
		  link_Other (ImmBuildDef2 c) args2;
		  push_cnf args

	      | Fite ->
		  let args1 = 
		    if Form.is_pos l then [args.(0);Form.neg args.(2)]
		    else [args.(0);Form.neg args.(2)] in
		  let args2 =
		    if Form.is_pos l then [Form.neg args.(0);args.(1)] 
		    else  [Form.neg args.(0); Form.neg args.(1)] in
		  link_Other (ImmBuildDef c) args1;
		  link_Other (ImmBuildDef2 c) args2;
		  push_cnf args

              | Fnot2 _ -> assert false

    let make_cnf reify c =
      let ftrue = Form.get reify (Fapp(Ftrue, [||])) in
      let ffalse = Form.get reify (Fapp(Ffalse, [||])) in
      last := c;
      link_Other True [ftrue];
      link_Other False [Form.neg ffalse];
      (try 
	imm_cnf c;
	List.iter (Array.iter cnf) !cnf_todo
      with Cnf_done -> ());
      let res = !last in
      clear ();
      res

  end


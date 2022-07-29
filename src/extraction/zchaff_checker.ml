(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


let mkInt = Uint63.of_int

(* From trace/coqTerms.ml *)
let mkArray a =
  let l = (Array.length a) - 1 in
  snd (Array.fold_left (fun (i,acc) c ->
                        let acc' =
                          if i = l then
                            acc
                          else
                            Sat_checker.set acc (mkInt i) c in
                        (i+1,acc')
                       ) (0, Sat_checker.make (mkInt l) a.(l)) a)


(* From zchaff/zchaff.ml *)
let make_roots first last =
  let roots = Array.make (last.SmtCertif.id + 2) (mkArray (Array.make 1 (mkInt 0))) in
  let mk_elem l =
    let x = match SatAtom.Form.pform l with
      | Fatom x -> x + 2
      | _ -> assert false  in
    mkInt (if SatAtom.Form.is_pos l then x lsl 1 else (x lsl 1) lxor 1) in
  let r = ref first in
  while !r.SmtCertif.id < last.SmtCertif.id do
    let root = Array.of_list (SmtTrace.get_val !r) in
    let croot = Array.make (Array.length root + 1) (mkInt 0) in
    Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
    roots.(!r.id) <- mkArray croot;
    r := SmtTrace.next !r
  done;
  let root = Array.of_list (SmtTrace.get_val !r) in
  let croot = Array.make (Array.length root + 1) (mkInt 0) in
  Array.iteri (fun i l -> croot.(i) <- mk_elem l) root;
  roots.(!r.id) <- mkArray croot;

  mkArray roots


(* From trace/coqInterface.ml *)
(* WARNING: side effect on r! *)
let mkTrace step_to_coq next size def_step r =
  let rec mkTrace s =
    if s = size then
      Sat_checker.Nil
    else (
      r := next !r;
      let st = step_to_coq !r in
      Sat_checker.Cons (st, mkTrace (s+1))
    ) in
  (mkTrace 0, def_step)


(* From trace/smtTrace.ml *)
let to_coq cRes confl =

  let step_to_coq c =
    match c.SmtCertif.kind with
    | Res res ->
	let size = List.length res.rtail + 3 in
	let args = Array.make size (mkInt 0) in
	args.(0) <- mkInt (SmtTrace.get_pos res.rc1);
	args.(1) <- mkInt (SmtTrace.get_pos res.rc2);
	let l = ref res.rtail in
	for i = 2 to size - 2 do
	  match !l with
	  | c::tl ->
	      args.(i) <- mkInt (SmtTrace.get_pos c);
	      l := tl
	  | _ -> assert false
	done;
        cRes (mkInt (SmtTrace.get_pos c), mkArray args)
    | Other other -> assert false
    | _ -> assert false
  in

  let def_step = cRes (mkInt 0, mkArray [|mkInt 0|]) in
  let r = ref confl in
  let nc = ref 0 in
  while not (SmtTrace.isRoot !r.SmtCertif.kind) do r := SmtTrace.prev !r; incr nc done;
  let last_root = !r in
  let res =
    mkTrace step_to_coq SmtTrace.next !nc def_step r
  in
  (res, last_root)


let checker fdimacs ftrace =
  SmtTrace.clear ();
  let _,first,last,reloc = Zchaff.import_cnf fdimacs in
  let d = make_roots first last in

  let max_id, confl = Zchaff.import_cnf_trace reloc ftrace first last in
  let (tres,_) =
    to_coq (fun (pos, args) -> Sat_checker.Sat_Checker.Res (pos, args)) confl in
  let certif =
    Sat_checker.Sat_Checker.Certif (mkInt (max_id + 1), tres, mkInt (SmtTrace.get_pos confl)) in

  Sat_checker.Sat_Checker.checker d certif

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


open Smtcoq_plugin


let mkInt = Uint63.of_int


(* From trace/coqTerms.ml *)
let mkArray : type b. (Uint63.t -> 'a -> b) -> (b -> Uint63.t -> 'a -> b) -> 'a array -> b =
  fun make set a ->
  let l = (Array.length a) - 1 in
  snd (Array.fold_left (fun (i,acc) c ->
                        let acc' =
                          if i = l then
                            acc
                          else
                            set acc (mkInt i) c in
                        (i+1,acc')
                       ) (0, make (mkInt l) a.(l)) a)


(* From trace/coqInterface.ml *)
(* WARNING: side effect on r! *)
let mkTrace nil cons step_to_coq next size def_step r =
  let rec mkTrace s =
    if s = size then
      nil
    else (
      r := next !r;
      let st = step_to_coq !r in
      cons (st, mkTrace (s+1))
    ) in
  (mkTrace 0, def_step)

(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2020                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* The global state contains the theorems that will be sent to the
   provers, added using the [Add_lemma] vernacular command *)

let lemmas_list = Summary.ref ~name:"Selected lemmas" []

let cache_lemmas (_, lems) =
  lemmas_list := lems

let declare_lemmas : Structures.constr_expr list -> Libobject.obj =
  let open Libobject in
  declare_object
    {
      (default_object "LEMMAS") with
      cache_function = cache_lemmas;
      load_function = (fun _ -> cache_lemmas);
    }

let add_lemmas lems =
  Lib.add_anonymous_leaf (declare_lemmas (lems @ !lemmas_list))

let clear_lemmas () =
  Lib.add_anonymous_leaf (declare_lemmas [])

let get_lemmas () = !lemmas_list

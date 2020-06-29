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


(* Since ZChaff does not allow to choose where the trace is outputted,
   we use a global mutex to prevent two parallel calls to ZChaff *)

let zchaff_mutex = Mutex.create ()

let cache_zchaff_mutex (_, acquire) =
  if acquire then Mutex.lock zchaff_mutex else Mutex.unlock zchaff_mutex

let declare_zchaff_mutex : bool -> Libobject.obj =
  let open Libobject in
  declare_object
    {
      (default_object "ZCHAFF_MUTEX") with
      cache_function = cache_zchaff_mutex;
      load_function = (fun _ -> cache_zchaff_mutex);
      open_function = (fun _ -> cache_zchaff_mutex)
    }

let lock_zchaff_mutex () =
  Lib.add_anonymous_leaf (declare_zchaff_mutex true)

let unlock_zchaff_mutex () =
  Lib.add_anonymous_leaf (declare_zchaff_mutex false)


(* TODO: when native-coq is not supported anymore, put here the list of
   lemmas from g_smtcoq *)

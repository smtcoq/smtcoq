(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

let msg_file filename =
  if CoqInterface.print_solver_status () then
    try
      let ic = open_in filename in
      (try
         while true do
           CoqInterface.msg_solver_status (input_line ic)
         done
       with End_of_file -> close_in ic)
    with Sys_error _ -> ()

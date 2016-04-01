(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*     Université Paris-Sud                                               *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open Entries
open Declare
open Decl_kinds

open SmtMisc
open CoqTerms
open SmtForm
open SmtCertif
open SmtTrace
open SmtAtom


(******************************************************************************)
(* Given a lfsc trace build the corresponding certif and theorem             *)
(******************************************************************************)

(* TODO: replace these dummy functions with complete ones *)

  (** Type of S-expressions *)
type t = Atom of string | List of t list


let rec print fmt = function
  | Atom s -> Format.pp_print_string fmt s
  | List l ->
    Format.fprintf fmt "(";
    List.iter (Format.fprintf fmt "%a " print) l;
    Format.fprintf fmt ")"

let rec print_list fmt = function
  | [] -> ()
  | s :: r ->
    Format.fprintf fmt "%a@." print s;
    print_list fmt r

let rec size = function
  | Atom _ -> 1
  | List l -> List.fold_left (fun acc s -> size s + acc) 0 l

let rec size_list = function
  | [] -> 0
  | s :: r -> size s + size_list r


let import_trace filename =
  (* What you have to do: parse the certificate, and produce the
     corresponding veriT steps linearly, as you are currently doing: the
     difference is that instead of pretty-printing, you should produce
     something in the format of SmtCertif, and return the (last)
     conflicting step *)
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let confl = LfscParser.certif LfscLexer.token lexbuf in
  (* Afterwards, the SMTCoq libraries will produce the remaining, you do
     not have to care *)
  SmtTrace.select confl;
  occur confl;
  (alloc first, confl)


let clear_all () =
  SmtTrace.clear ();
  LfscSyntax.clear ()


let import_all fsmt fproof =
  clear_all ();
  let rt = Btype.create () in
  let ro = Op.create () in
  let ra = LfscSyntax.ra in
  let rf = LfscSyntax.rf in
  let roots = Smtlib2_genConstr.import_smtlib2 rt ro ra rf fsmt in
  let (max_id, confl) = import_trace fproof in
  (rt, ro, ra, rf, roots, max_id, confl)


let parse_certif t_i t_func t_atom t_form root used_root trace fsmt fproof =
  SmtCommands.parse_certif t_i t_func t_atom t_form root used_root trace (import_all fsmt fproof)
let theorem name fsmt fproof = SmtCommands.theorem name (import_all fsmt fproof)
let checker fsmt fproof = SmtCommands.checker (import_all fsmt fproof)



(******************************************************************************)
(** Given a Coq formula build the proof                                       *)
(******************************************************************************)

(* TODO *)

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


(** Construction and internal representation of LFSC proofs and rules with type
    checking.
*)



(** {2 Structures for LFSC proofs, terms and types } *)


(** Implementation of the LFSC type [mpz] for integers. *)
type mpz = Big_int.big_int

(** Implementation of the LFSC type [mpq] for rationnals. *)
type mpq = Num.num


type name = Name of string | S_Hole of int

(** Type of symbols used in lambda/pi abstractions. *)
type symbol = { sname : name; stype : term }

(** Types of terms *)
and dterm =
  | Type                     (** The type [type] *)
  | Kind                     (** The type [kind] *)
  | Mpz                      (** The type [mpz] *)
  | Mpq                      (** The type [mpq] *)
  | Const of symbol          (** Constants *)
  | App of term * term list  (** Functions *)
  | Int of mpz               (** Integers *)
  | Rat of mpq               (** Rationals *)
  | Pi of symbol * term      (** Pi-abstractions *)
  | Lambda of symbol * term  (** Lambda-abstractions *)
  | Hole of int              (** Hole/Variable (to be filled) *)
  | Ptr of term              (** Pointer to another term (used to fill holes
                                 and keep physical equality). Pointers can be
                                 removed with {!flatten}. *)
  | SideCond of string * term list * term * term
  (** Side conditions. The last argument is the term
      to which the side-condition expression
      evaluates. *)

(** LFSC terms and types (same thing). Terms are annotated with their types. *)
and term = { mutable value: dterm; ttype: term }

(** Equality over terms (performs unification). To compare terms for equality
    use [compare_tem t1 t2 = 0] instead. *)
val term_equal : term -> term -> bool

(** Comparision between terms *)
val compare_term : term -> term -> int
val compare_term_list : term list -> term list -> int

val hash_term : term -> int

(** The type of LFSC top-level commands *)
type command =
  | Check of term
  | Define of string * term
  | Declare of string * term

(** The type of LFSC proofs *)
type proof = command list


(** Term module to build structures over terms. *)
module Term : sig
  type t = term
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end


(** {2 Pretty printing } *)

val print_term : Format.formatter -> term -> unit

val print_term_type : Format.formatter -> term -> unit

val print_symbol : Format.formatter -> symbol -> unit
  
val print_command : Format.formatter -> command -> unit

val print_proof : Format.formatter -> proof -> unit


(** {2 Predefined LFSC types } *)

(** The LFSC type [type]. *)
val lfsc_type : term

(** The LFSC type [kind] (of type [type]). *)
val kind : term

(** The LFSC type [mpz]. *)
val mpz : term

(** The LFSC type [mpq]. *)
val mpq : term

(** Constructor for LFSC integers. *)
val mk_mpz : mpz -> term

(** Constructor for LFSC rationals. *)
val mk_mpq : mpq -> term



(** {2 Utilities functions } *)

(* val unify : term -> term -> unit *)

(** @deprecated *)
val  get_real : term -> term

(** Remove pointers in term and type *)
val flatten_term : term -> unit

(** Returs [true] if the term contains pointers.*)
val has_ptr : term -> bool


(** follow pointers *)
val deref : term -> term

(** derefenced value *)
val value : term -> dterm

(** get dereferenced constant name (None if it's not a constant or it has no
    name) *)
val name : term -> string option

(** get dereferenced application name and its arguments (None if it's not a
    function application or the function symbol has no name) *)
val app_name : term -> (string * term list) option



(** {2 Smart constructors with type checking and unification } *)


(** Exception raised when the proof does not type check. *)
exception TypingError of term * term

(** Constructor for symbols, given their name and their type. *)
val mk_symbol : string -> term -> symbol

(** Create a hole symbol to be filled later on. *)
val mk_symbol_hole : term -> symbol

(** Create a constant term of a predeclared name. *)
val mk_const : string -> term

(** Create a constant term from a symbol. *)
val symbol_to_const : symbol -> term

(** Constructor for function application. This performs type inference and
    destructive unfification of type variables (holes), as well as
    beta-reduction. *)
val mk_app : term -> term list -> term

(** Constructor for a (fresh) unspecified hole term (i.e. a variable) given its
    type. *)
val mk_hole : term -> term

(** Create and unspecified term of unspecified type. *)
val mk_hole_hole : unit -> term

(** Create a pi-abstraction. [mk_pi s t] returns Π s : s.stype. t. *)
val mk_pi : symbol -> term -> term

(** Create a lambda-abstraction. [mk_lambda s t] returns λ s : s.stype. t. *)
val mk_lambda : symbol -> term -> term

(** Ascription, or type check. [mk_ascr ty t] checks that t has type ty, while
    performing all type checking operations decribed in {!mk_app}. *)
val mk_ascr : term -> term -> term


(** [mk_declare s ty] registers declaration of symbol [s] as having type
    [ty]. *)
val mk_declare : string -> term -> unit


(** [mk_define s t] registers [s] to be a definition for the term [t]. It is
    inlined in the subsequent terms. *)
val mk_define : string -> term -> unit

(** Create a check command. *)
val mk_check : term -> unit


(** {2 Auxiliary functions} *)

val register_symbol : symbol -> unit

val remove_symbol : symbol -> unit

val add_definition : symbol -> term -> unit

val remove_definition : symbol -> unit


(** {2 Side-conditions} *)

(** Table for callback functions of side conditions. *)
val callbacks_table : (string, term list -> term) Hashtbl.t

(** Add a side-condition to the callback table, and returns the continuation of
    the side condition in LFSC terms. See {!Builtin}. *)
val add_sc : string -> term list -> term -> term -> term

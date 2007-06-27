(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC TERMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature TermNet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of term sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool}

type 'a termNet

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> 'a termNet

val null : 'a termNet -> bool

val size : 'a termNet -> int

val insert : 'a termNet -> Term.term * 'a -> 'a termNet

val fromList : parameters -> (Term.term * 'a) list -> 'a termNet

val filter : ('a -> bool) -> 'a termNet -> 'a termNet

val toString : 'a termNet -> string

val pp : 'a Parser.pp -> 'a termNet Parser.pp

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

val match : 'a termNet -> Term.term -> 'a list

val matched : 'a termNet -> Term.term -> 'a list

val unify : 'a termNet -> Term.term -> 'a list

end

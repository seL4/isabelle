(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature LiteralNet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool}

type 'a literalNet

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> 'a literalNet

val size : 'a literalNet -> int

val profile : 'a literalNet -> {positive : int, negative : int}

val insert : 'a literalNet -> Literal.literal * 'a -> 'a literalNet

val fromList : parameters -> (Literal.literal * 'a) list -> 'a literalNet

val filter : ('a -> bool) -> 'a literalNet -> 'a literalNet

val toString : 'a literalNet -> string

val pp : 'a Parser.pp -> 'a literalNet Parser.pp

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

val match : 'a literalNet -> Literal.literal -> 'a list

val matched : 'a literalNet -> Literal.literal -> 'a list

val unify : 'a literalNet -> Literal.literal -> 'a list

end

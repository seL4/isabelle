(* ========================================================================= *)
(* THE KNUTH-BENDIX TERM ORDERING                                            *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature KnuthBendixOrder =
sig

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

type kbo =
     {weight : Term.function -> int,
      precedence : Term.function * Term.function -> order}

val default : kbo

val compare : kbo -> Term.term * Term.term -> order option

end

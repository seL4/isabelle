(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS              *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature AtomNet =
sig

(* ------------------------------------------------------------------------- *)
(* A type of atom sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = {fifo : bool}

type 'a atomNet

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

val new : parameters -> 'a atomNet

val size : 'a atomNet -> int

val insert : 'a atomNet -> Atom.atom * 'a -> 'a atomNet

val fromList : parameters -> (Atom.atom * 'a) list -> 'a atomNet

val filter : ('a -> bool) -> 'a atomNet -> 'a atomNet

val toString : 'a atomNet -> string

val pp : 'a Parser.pp -> 'a atomNet Parser.pp

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

val match : 'a atomNet -> Atom.atom -> 'a list

val matched : 'a atomNet -> Atom.atom -> 'a list

val unify : 'a atomNet -> Atom.atom -> 'a list

end

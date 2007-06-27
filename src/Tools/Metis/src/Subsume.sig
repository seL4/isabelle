(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* Copyright (c) 2002-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Subsume =
sig

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

type 'a subsume

val new : unit -> 'a subsume

val size : 'a subsume -> int

val insert : 'a subsume -> Thm.clause * 'a -> 'a subsume

val filter : ('a -> bool) -> 'a subsume -> 'a subsume

val pp : 'a subsume Parser.pp

val toString : 'a subsume -> string

(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

val subsumes :
    (Thm.clause * Subst.subst * 'a -> bool) -> 'a subsume -> Thm.clause ->
    (Thm.clause * Subst.subst * 'a) option

val isSubsumed : 'a subsume -> Thm.clause -> bool

val strictlySubsumes :  (* exclude subsuming clauses with more literals *)
    (Thm.clause * Subst.subst * 'a -> bool) -> 'a subsume -> Thm.clause ->
    (Thm.clause * Subst.subst * 'a) option

val isStrictlySubsumed : 'a subsume -> Thm.clause -> bool

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

val clauseSubsumes : Thm.clause -> Thm.clause -> Subst.subst option

val clauseStrictlySubsumes : Thm.clause -> Thm.clause -> Subst.subst option

end

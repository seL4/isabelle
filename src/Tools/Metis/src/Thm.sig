(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSES                                  *)
(* Copyright (c) 2001-2004 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Thm =
sig

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = LiteralSet.set

datatype inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality

type thm

type inference = inferenceType * thm list

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

val clause : thm -> clause

val inference : thm -> inference

(* Tautologies *)

val isTautology : thm -> bool

(* Contradictions *)

val isContradiction : thm -> bool

(* Unit theorems *)

val destUnit : thm -> Literal.literal

val isUnit : thm -> bool

(* Unit equality theorems *)

val destUnitEq : thm -> Term.term * Term.term

val isUnitEq : thm -> bool

(* Literals *)

val member : Literal.literal -> thm -> bool

val negateMember : Literal.literal -> thm -> bool

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

val compare : thm * thm -> order

val equal : thm -> thm -> bool

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

val freeIn : Term.var -> thm -> bool

val freeVars : thm -> NameSet.set

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val ppInferenceType : inferenceType Parser.pp

val inferenceTypeToString : inferenceType -> string

val pp : thm Parser.pp

val toString : thm -> string

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

val axiom : clause -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

val assume : Literal.literal -> thm

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

val subst : Subst.subst -> thm -> thm

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

val resolve : Literal.literal -> thm -> thm -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

val refl : Term.term -> thm

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

val equality : Literal.literal -> Term.path -> Term.term -> thm

end

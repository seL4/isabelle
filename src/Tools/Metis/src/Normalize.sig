(* ========================================================================= *)
(* NORMALIZING FORMULAS                                                      *)
(* Copyright (c) 2001-2009 Joe Hurd, distributed under the GNU GPL version 2 *)
(* ========================================================================= *)

signature Normalize =
sig

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

val nnf : Formula.formula -> Formula.formula

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form derivations.                                      *)
(* ------------------------------------------------------------------------- *)

type thm

datatype inference =
    Axiom of Formula.formula
  | Definition of string * Formula.formula
  | Simplify of thm * thm list
  | Conjunct of thm
  | Specialize of thm
  | Skolemize of thm
  | Clausify of thm

val mkAxiom : Formula.formula -> thm

val destThm : thm -> Formula.formula * inference

val proveThms :
    thm list -> (Formula.formula * inference * Formula.formula list) list

val toStringInference : inference -> string

val ppInference : inference Print.pp

(* ------------------------------------------------------------------------- *)
(* Conjunctive normal form.                                                  *)
(* ------------------------------------------------------------------------- *)

type cnf

val initialCnf : cnf

val addCnf : thm -> cnf -> (Thm.clause * thm) list * cnf

val proveCnf : thm list -> (Thm.clause * thm) list

val cnf : Formula.formula -> Thm.clause list

end

(* ========================================================================= *)
(* PROOFS IN FIRST ORDER LOGIC                                               *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

signature Proof =
sig

(* ------------------------------------------------------------------------- *)
(* A type of first order logic proofs.                                       *)
(* ------------------------------------------------------------------------- *)

datatype inference =
    Axiom of LiteralSet.set
  | Assume of Atom.atom
  | Subst of Subst.subst * Thm.thm
  | Resolve of Atom.atom * Thm.thm * Thm.thm
  | Refl of Term.term
  | Equality of Literal.literal * Term.path * Term.term

type proof = (Thm.thm * inference) list

(* ------------------------------------------------------------------------- *)
(* Reconstructing single inferences.                                         *)
(* ------------------------------------------------------------------------- *)

val inferenceToThm : inference -> Thm.thm

val thmToInference : Thm.thm -> inference

(* ------------------------------------------------------------------------- *)
(* Reconstructing whole proofs.                                              *)
(* ------------------------------------------------------------------------- *)

val proof : Thm.thm -> proof

(* ------------------------------------------------------------------------- *)
(* Printing.                                                                 *)
(* ------------------------------------------------------------------------- *)

val ppInference : inference Parser.pp

val inferenceToString : inference -> string

val pp : proof Parser.pp

val toString : proof -> string

end

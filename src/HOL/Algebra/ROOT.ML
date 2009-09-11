(*
    The Isabelle Algebraic Library
    $Id$
    Author: Clemens Ballarin, started 24 September 1999
*)

(* Preliminaries from set and number theory *)
no_document use_thys ["FuncSet", "~~/src/HOL/Old_Number_Theory/Primes", "Binomial", "Permutation"];


(*** New development, based on explicit structures ***)

use_thys [
  (* Groups *)
  "FiniteProduct",      (* Product operator for commutative groups *)
  "Sylow",              (* Sylow's theorem *)
  "Bij",                (* Automorphism Groups *)

  (* Rings *)
  "Divisibility",       (* Rings *)
  "IntRing",            (* Ideals and residue classes *)
  "UnivPoly"            (* Polynomials *)
];


(*** Old development, based on axiomatic type classes.
     Will be withdrawn in future. ***)

no_document use_thys [
  "abstract/Abstract",  (*The ring theory*)
  "poly/Polynomial"     (*The full theory*)
];

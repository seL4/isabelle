(*
    The Isabelle Algebraic Library
    $Id$
    Author: Clemens Ballarin, started 24 September 1999
*)

(*** New development, based on explicit structures ***)

(* Preliminaries from set and number theory *)

no_document use_thy "FuncSet";
no_document use_thy "Primes";

(* Groups *)

use_thy "FiniteProduct";	(* Product operator for commutative groups *)
use_thy "Sylow";		(* Sylow's theorem *)
use_thy "Bij";			(* Automorphism Groups *)

(* Rings *)

use_thy "UnivPoly";		(* Rings and polynomials *)

(*** Old development, based on axiomatic type classes.
     Will be withdrawn in future. ***)

with_path "abstract" (no_document time_use_thy) "Abstract";   (*The ring theory*)
with_path "poly"     (no_document time_use_thy) "Polynomial"; (*The full theory*)

(*
    The Isabelle Algebraic Library
    $Id$
    Author: Clemens Ballarin, started 24 September 1999
*)

(* New development, based on explicit structures *)

use_thy "Sylow";		(* Groups *)
(* use_thy "UnivPoly"; *)	(* Rings and polynomials *)

(* Old development, based on axiomatic type classes.
   Will be withdrawn in future. *)

with_path "abstract" time_use_thy "Abstract";        (*The ring theory*)
with_path "poly"     time_use_thy "Polynomial";      (*The full theory*)

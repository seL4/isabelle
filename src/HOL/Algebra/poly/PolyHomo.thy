(*
    Universal property and evaluation homomorphism of univariate polynomials
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

PolyHomo = Degree +

(* Instantiate result from Degree.ML *)

instance
  up :: (domain) domain (up_integral)

consts
  EVAL2	:: ('a::ringS => 'b) => 'b => 'a up => 'b::ringS
  EVAL	:: 'a => 'a up => 'a

defs
  EVAL2_def	"EVAL2 phi a p == SUM (deg p) (%i. phi (coeff i p) * a ^ i)"
  EVAL_def	"EVAL == EVAL2 (%x. x)"

end

(*
    Universal property and evaluation homomorphism of univariate polynomials
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

PolyHomo = UnivPoly +

consts
  EVAL2	:: "['a::ring => 'b, 'b, 'a up] => 'b::ring"
  EVAL	:: "['a::ring, 'a up] => 'a"

defs
  EVAL2_def	"EVAL2 phi a p ==
                 setsum (%i. phi (coeff p i) * a ^ i) {..deg p}"
  EVAL_def	"EVAL == EVAL2 (%x. x)"

end

(*
    Experimental theory: long division of polynomials
    $Id$
    Author: Clemens Ballarin, started 23 June 1999
*)

LongDiv = PolyHomo +

consts
  lcoeff :: "'a::ringS up => 'a"
  eucl_size :: 'a::ringS => nat

defs
  lcoeff_def	"lcoeff p == coeff (deg p) p"
  eucl_size_def "eucl_size p == if p = <0> then 0 else deg p+1"

end


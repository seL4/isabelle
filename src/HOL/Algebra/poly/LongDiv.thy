(*
    Experimental theory: long division of polynomials
    $Id$
    Author: Clemens Ballarin, started 23 June 1999
*)

LongDiv = PolyHomo +

consts
  lcoeff :: "'a::ring up => 'a"
  eucl_size :: 'a::ring => nat

defs
  lcoeff_def	"lcoeff p == coeff p (deg p)"
  eucl_size_def "eucl_size p == if p = 0 then 0 else deg p+1"

end


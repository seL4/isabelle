(*
    Experimental theory: long division of polynomials
    $Id$
    Author: Clemens Ballarin, started 23 June 1999
*)

theory LongDiv = PolyHomo:

consts
  lcoeff :: "'a::ring up => 'a"
  eucl_size :: "'a::ring => nat"

defs
  lcoeff_def: "lcoeff p == coeff p (deg p)"
  eucl_size_def: "eucl_size p == (if p = 0 then 0 else deg p+1)"

lemma SUM_shrink_below_lemma:
  "!! f::(nat=>'a::ring). (ALL i. i < m --> f i = 0) --> 
  setsum (%i. f (i+m)) {..d} = setsum f {..m+d}"
  apply (induct_tac d)
  apply (induct_tac m)
  apply (simp)
  apply (force)
  apply (simp)
  apply (subst ab_semigroup_add.add_commute[of m])
  apply (simp)
  done

end


(*  Title: 	HOLCF/cprod1.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


Partial ordering for cartesian product of HOL theory prod.thy

*)

Cprod1 = Cfun3 +


consts
  less_cprod	:: "[('a::pcpo * 'b::pcpo),('a * 'b)] => bool"	

rules

  less_cprod_def "less_cprod(p1,p2) == ( fst(p1) << fst(p2) &\
\					snd(p1) << snd(p2))"

end


(*  Title: 	HOLCF/sprod1.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Partial ordering for the strict product
*)

Sprod1 = Sprod0 +

consts
  less_sprod	:: "[('a ** 'b),('a ** 'b)] => bool"	

rules

  less_sprod_def "less_sprod(p1,p2) == @z.\
\	 ( p1=Ispair(UU,UU) --> z = True)\
\	&(~p1=Ispair(UU,UU) --> z = (   Isfst(p1) << Isfst(p2) &\
\					Issnd(p1) << Issnd(p2)))"

end


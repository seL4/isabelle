(*  Title:      HOLCF/Cprod1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen


Partial ordering for cartesian product of HOL theory prod.thy

*)

Cprod1 = Cfun3 +

default cpo

instance "*"::(sq_ord,sq_ord)sq_ord 

defs

  less_cprod_def "p1 << p2 == (fst p1<<fst p2 & snd p1 << snd p2)"

end

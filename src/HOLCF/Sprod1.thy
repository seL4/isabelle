(*  Title:      HOLCF/sprod1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Partial ordering for the strict product
*)

Sprod1 = Sprod0 +

instance "**"::(sq_ord,sq_ord)sq_ord 

defs
  less_sprod_def "p1 << p2 == Isfst p1 << Isfst p2 & Issnd p1 << Issnd p2"

end

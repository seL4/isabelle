(*  Title:      HOLCF/Ssum1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Partial ordering for the strict sum ++
*)

Ssum1 = Ssum0 +

defs
  less_ssum_def "less == (%s1 s2.@z.
         (! u x.s1=Isinl u & s2=Isinl x --> z = u << x)
        &(! v y.s1=Isinr v & s2=Isinr y --> z = v << y)
        &(! u y.s1=Isinl u & s2=Isinr y --> z = (u = UU))
        &(! v x.s1=Isinr v & s2=Isinl x --> z = (v = UU)))"

end



(*  Title:      HOLCF/ccc1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Merge Theories Cprof, Sprod, Ssum, Lift, Fix and
define constants for categorical reasoning
*)

ccc1 = Cprod3 + Sprod3 + Ssum3 + Lift3 + Fix +

consts
        ID      :: "'a -> 'a"
        cfcomp  :: "('b->'c)->('a->'b)->'a->'c"

syntax  "@oo"   :: "('b->'c)=>('a->'b)=>'a->'c" ("_ oo _" [101,100] 100)
     
translations    "f1 oo f2" == "cfcomp`f1`f2"

defs

  ID_def        "ID ==(LAM x.x)"
  oo_def        "cfcomp == (LAM f g x.f`(g`x))" 

end





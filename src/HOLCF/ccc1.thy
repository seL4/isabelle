(*  Title:      HOLCF/ccc1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Merge Theories Cprof, Sprod, Ssum, Up, Fix and
define constants for categorical reasoning
*)

ccc1 = Cprod3 + Sprod3 + Ssum3 + Up3 + Fix + 

instance flat<chfin (flat_imp_chain_finite)

consts
        ID      :: "('a::cpo) -> 'a"
        cfcomp  :: "('b->'c)->(('a::cpo)->('b::cpo))->'a->('c::cpo)"

syntax  "@oo"   :: "('b->'c)=>('a->'b)=>'a->'c" ("_ oo _" [101,100] 100)
     
translations    "f1 oo f2" == "cfcomp`f1`f2"

defs

  ID_def        "ID ==(LAM x.x)"
  oo_def        "cfcomp == (LAM f g x.f`(g`x))" 

end





(*  Title:      HOLCF/ssum3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ++ for class pcpo
*)

Ssum3 = Ssum2 +

instance "++" :: (pcpo,pcpo)pcpo (least_ssum,cpo_ssum)

consts  
        sinl    :: "'a -> ('a++'b)" 
        sinr    :: "'b -> ('a++'b)" 
        sswhen  :: "('a->'c)->('b->'c)->('a ++ 'b)-> 'c"

defs

sinl_def        "sinl   == (LAM x.Isinl(x))"
sinr_def        "sinr   == (LAM x.Isinr(x))"
sswhen_def      "sswhen   == (LAM f g s.Iwhen(f)(g)(s))"

translations
"case s of sinl`x => t1 | sinr`y => t2" == "sswhen`(LAM x.t1)`(LAM y.t2)`s"

end

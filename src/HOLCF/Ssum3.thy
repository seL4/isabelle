(*  Title:      HOLCF/ssum3.thy
    ID:         $Id$
    Author:     Franz Regensburger

Class instance of  ++ for class pcpo
*)

Ssum3 = Ssum2 +

instance "++" :: (pcpo,pcpo)pcpo (least_ssum,cpo_ssum)

consts  
        sinl    :: "'a -> ('a++'b)" 
        sinr    :: "'b -> ('a++'b)" 
        sscase  :: "('a->'c)->('b->'c)->('a ++ 'b)-> 'c"

defs

sinl_def        "sinl   == (LAM x. Isinl(x))"
sinr_def        "sinr   == (LAM x. Isinr(x))"
sscase_def      "sscase   == (LAM f g s. Iwhen(f)(g)(s))"

translations
"case s of sinl$x => t1 | sinr$y => t2" == "sscase$(LAM x. t1)$(LAM y. t2)$s"

end

(*  Title:      HOLCF/ssum3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ++ for class pcpo
*)

Ssum3 = Ssum2 +

arities "++" :: (pcpo,pcpo)pcpo                 (* Witness ssum2.ML *)

consts  
        sinl    :: "'a -> ('a++'b)" 
        sinr    :: "'b -> ('a++'b)" 
        sswhen  :: "('a->'c)->('b->'c)->('a ++ 'b)-> 'c"

rules 

inst_ssum_pcpo  "(UU::'a++'b) = Isinl(UU)"


defs

sinl_def        "sinl   == (LAM x.Isinl(x))"
sinr_def        "sinr   == (LAM x.Isinr(x))"
sswhen_def      "sswhen   == (LAM f g s.Iwhen(f)(g)(s))"

translations
"case s of sinl`x => t1 | sinr`y => t2" == "sswhen`(LAM x.t1)`(LAM y.t2)`s"

(* start 8bit 1 *)
translations
"case s of sinl`x => t1 | sinr`y => t2" == "sswhen`(¤x.t1)`(¤y.t2)`s"

(* end 8bit 1 *)

end

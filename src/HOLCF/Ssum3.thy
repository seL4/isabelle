(*  Title: 	HOLCF/ssum3.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  ++ for class pcpo
*)

Ssum3 = Ssum2 +

arities "++" :: (pcpo,pcpo)pcpo			(* Witness ssum2.ML *)

consts  
	sinl	     :: "'a -> ('a++'b)" 
	sinr	     :: "'b -> ('a++'b)" 
	when         :: "('a->'c)->('b->'c)->('a ++ 'b)-> 'c"

rules 

inst_ssum_pcpo	"UU::'a++'b = Isinl(UU)"

sinl_def	"sinl   == (LAM x.Isinl(x))"
sinr_def	"sinr   == (LAM x.Isinr(x))"
when_def	"when   == (LAM f g s.Iwhen(f)(g)(s))"

end




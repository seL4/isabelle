(*  Title: 	HOLCF/lift3.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen


Class instance of  ('a)u for class pcpo

*)

Lift3 = Lift2 +

arities "u" :: (pcpo)pcpo			(* Witness lift2.ML *)

consts  
	up	     :: "'a -> ('a)u" 
	lift         :: "('a->'c)-> ('a)u -> 'c"

rules 

	inst_lift_pcpo	"(UU::('a)u) = UU_lift"

defs
	up_def		"up     == (LAM x.Iup(x))"
	lift_def	"lift   == (LAM f p.Ilift(f)(p))"

translations
"case l of up`x => t1" == "lift`(LAM x.t1)`l"

(* start 8bit 1 *)
(* end 8bit 1 *)

end




(*  Title:      HOLCF/Up3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen


Class instance of  ('a)u for class pcpo

*)

Up3 = Up2 +

arities "u" :: (pcpo)pcpo                       (* Witness up2.ML *)

consts  
        up  :: "'a -> ('a)u" 
        fup :: "('a->'c)-> ('a)u -> 'c"

rules 

        inst_up_pcpo  "(UU::('a)u) = UU_up"

defs
        up_def   "up  == (LAM x.Iup(x))"
        fup_def  "fup == (LAM f p.Ifup(f)(p))"

translations

"case l of up`x => t1" == "fup`(LAM x.t1)`l"

end




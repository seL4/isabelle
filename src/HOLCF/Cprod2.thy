(*  Title:      HOLCF/Cprod2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance *::(pcpo,pcpo)po

*)

Cprod2 = Cprod1 + 

default pcpo

instance "*"::(cpo,cpo)po 
	(refl_less_cprod,antisym_less_cprod,trans_less_cprod)
end




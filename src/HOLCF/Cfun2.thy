(*  Title:      HOLCF/Cfun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance ->::(pcpo,pcpo)po

*)

Cfun2 = Cfun1 + 

instance "->"::(pcpo,pcpo)po (refl_less_cfun,antisym_less_cfun,trans_less_cfun)

end

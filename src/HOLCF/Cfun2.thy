(*  Title:      HOLCF/Cfun2.thy
    ID:         $Id$
    Author:     Franz Regensburger

Class Instance ->::(cpo,cpo)po

*)

Cfun2 = Cfun1 + 

instance "->"::(cpo,cpo)po (refl_less_cfun,antisym_less_cfun,trans_less_cfun)

end

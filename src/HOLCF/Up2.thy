(*  Title:      HOLCF/Up2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance u::(pcpo)po
*)

Up2 = Up1 + 

instance u :: (pcpo)po (refl_less_up,antisym_less_up,trans_less_up)

end




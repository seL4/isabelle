(*  Title:      HOLCF/ssum2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance ++::(pcpo,pcpo)po
*)

Ssum2 = Ssum1 + 

instance "++"::(pcpo,pcpo)po (refl_less_ssum,antisym_less_ssum,trans_less_ssum)

end




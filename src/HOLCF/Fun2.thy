(*  Title:      HOLCF/Fun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

Fun2 = Fun1 + 

(* default class is still type!*)

instance fun  :: (type, po) po (refl_less_fun,antisym_less_fun,trans_less_fun)

end









(*  Title:      HOLCF/Fun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance =>::(term,po)po
*)

Fun2 = Fun1 + 

(* default class is still term !*)

instance fun  :: (term,po)po (refl_less_fun,antisym_less_fun,trans_less_fun)

end









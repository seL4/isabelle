(*  Title:      HOLCF/Fun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance =>::(term,po)po
*)

Fun2 = Fun1 + 

(* default class is still term !*)

instance fun  :: (term,po)po (refl_less_fun,antisym_less_fun,trans_less_fun)

end









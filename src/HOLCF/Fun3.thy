(*  Title:      HOLCF/Fun3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class instance of  => (fun) for class pcpo

*)

Fun3 = Fun2 +

(* default class is still term *)

instance fun  :: (term,cpo)cpo         (cpo_fun)
instance fun  :: (term,pcpo)pcpo       (least_fun)

end


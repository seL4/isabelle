(*  Title:      HOLCF/Fun3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  => (fun) for class pcpo
*)

Fun3 = Fun2 +

(* default class is still type *)

instance fun  :: (type, cpo) cpo         (cpo_fun)
instance fun  :: (type, pcpo)pcpo       (least_fun)

end


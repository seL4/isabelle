(*  Title:      HOLCF/Fun3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  => (fun) for class pcpo
*)

theory Fun3 = Fun2:

(* default class is still type *)

instance fun  :: (type, cpo) cpo
apply (intro_classes)
apply (erule cpo_fun)
done

instance fun  :: (type, pcpo)pcpo
apply (intro_classes)
apply (rule least_fun)
done

(*  Title:      HOLCF/Fun3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_fun_pcpo: "UU = (%x. UU)"
apply (simp add: UU_def UU_fun_def)
done

end


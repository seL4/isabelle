(*  Title:      HOLCF/sprod1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Partial ordering for the strict product.
*)

theory Sprod1 = Sprod0:

instance "**"::(sq_ord,sq_ord)sq_ord ..

defs (overloaded)
  less_sprod_def: "p1 << p2 == Isfst p1 << Isfst p2 & Issnd p1 << Issnd p2"

(*  Title:      HOLCF/Sprod1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(* ------------------------------------------------------------------------ *)
(* less_sprod is a partial order on Sprod                                   *)
(* ------------------------------------------------------------------------ *)

lemma refl_less_sprod: "(p::'a ** 'b) << p"

apply (unfold less_sprod_def)
apply (fast intro: refl_less)
done

lemma antisym_less_sprod: 
        "[|(p1::'a ** 'b) << p2;p2 << p1|] ==> p1=p2"
apply (unfold less_sprod_def)
apply (rule Sel_injective_Sprod)
apply (fast intro: antisym_less)
apply (fast intro: antisym_less)
done

lemma trans_less_sprod: 
        "[|(p1::'a**'b) << p2;p2 << p3|] ==> p1 << p3"
apply (unfold less_sprod_def)
apply (blast intro: trans_less)
done

end

(*  Title:      HOLCF/Cprod1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Partial ordering for cartesian product of HOL theory Product_Type.thy
*)


(* ------------------------------------------------------------------------ *)
(* less_cprod is a partial order on 'a * 'b                                 *)
(* ------------------------------------------------------------------------ *)

Goalw [less_cprod_def] "(p::'a*'b) << p";
by (Simp_tac 1);
qed "refl_less_cprod";

Goalw [less_cprod_def] "[|(p1::'a * 'b) << p2;p2 << p1|] ==> p1=p2";
by (rtac injective_fst_snd 1);
by (fast_tac (HOL_cs addIs [antisym_less]) 1);
by (fast_tac (HOL_cs addIs [antisym_less]) 1);
qed "antisym_less_cprod";

Goalw [less_cprod_def]
        "[|(p1::'a*'b) << p2;p2 << p3|] ==> p1 << p3";
by (rtac conjI 1);
by (fast_tac (HOL_cs addIs [trans_less]) 1);
by (fast_tac (HOL_cs addIs [trans_less]) 1);
qed "trans_less_cprod";

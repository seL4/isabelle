(*  Title:      HOLCF/Sprod1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

*)

(* ------------------------------------------------------------------------ *)
(* less_sprod is a partial order on Sprod                                   *)
(* ------------------------------------------------------------------------ *)

val prems = goalw thy [less_sprod_def]"(p::'a ** 'b) << p";
by (fast_tac (HOL_cs addIs [refl_less]) 1);
qed "refl_less_sprod";

val prems = goalw thy [less_sprod_def]
        "[|(p1::'a ** 'b) << p2;p2 << p1|] ==> p1=p2";
by (cut_facts_tac prems 1);
by (rtac Sel_injective_Sprod 1);
by (fast_tac (HOL_cs addIs [antisym_less]) 1);
by (fast_tac (HOL_cs addIs [antisym_less]) 1);
qed "antisym_less_sprod";

val prems = goalw thy [less_sprod_def]
        "[|(p1::'a**'b) << p2;p2 << p3|] ==> p1 << p3";
by (cut_facts_tac prems 1);
by (rtac conjI 1);
by (fast_tac (HOL_cs addIs [trans_less]) 1);
by (fast_tac (HOL_cs addIs [trans_less]) 1);
qed "trans_less_sprod";

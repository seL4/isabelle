(*  Title:      HOLCF/Cprod1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Partial ordering for cartesian product of HOL theory Prod.thy
*)


(* ------------------------------------------------------------------------ *)
(* less_cprod is a partial order on 'a * 'b                                 *)
(* ------------------------------------------------------------------------ *)

val prems = goal Prod.thy
        "[|fst x = fst y; snd x = snd y|] ==> x = y";
by (cut_facts_tac prems 1);
by (subgoal_tac "(fst x,snd x)=(fst y,snd y)" 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac(HOL_ss addsimps[surjective_pairing RS sym])1);
by (asm_simp_tac (simpset_of Prod.thy) 1);
qed "Sel_injective_cprod";

val prems = goalw Cprod1.thy [less_cprod_def] "(p::'a*'b) << p";
by (Simp_tac 1);
qed "refl_less_cprod";

Goalw [less_cprod_def] "[|(p1::'a * 'b) << p2;p2 << p1|] ==> p1=p2";
by (rtac Sel_injective_cprod 1);
by (fast_tac (HOL_cs addIs [antisym_less]) 1);
by (fast_tac (HOL_cs addIs [antisym_less]) 1);
qed "antisym_less_cprod";

val prems = goalw thy [less_cprod_def]
        "[|(p1::'a*'b) << p2;p2 << p3|] ==> p1 << p3";
by (cut_facts_tac prems 1);
by (rtac conjI 1);
by (fast_tac (HOL_cs addIs [trans_less]) 1);
by (fast_tac (HOL_cs addIs [trans_less]) 1);
qed "trans_less_cprod";

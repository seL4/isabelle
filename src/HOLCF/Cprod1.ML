(*  Title:      HOLCF/Cprod1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory Cprod1.thy 
*)

open Cprod1;


(* ------------------------------------------------------------------------ *)
(* less_cprod is a partial order on 'a * 'b                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "Sel_injective_cprod" Prod.thy 
        "[|fst x = fst y; snd x = snd y|] ==> x = y"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (subgoal_tac "(fst x,snd x)=(fst y,snd y)" 1),
        (rotate_tac ~1 1),
        (asm_full_simp_tac(HOL_ss addsimps[surjective_pairing RS sym])1),
        (Asm_simp_tac 1)
        ]);

qed_goalw "refl_less_cprod" Cprod1.thy [less_cprod_def] "(p::'a*'b) << p"
 (fn prems => [Simp_tac 1]);

qed_goalw "antisym_less_cprod" thy [less_cprod_def]
        "[|(p1::'a * 'b) << p2;p2 << p1|] ==> p1=p2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac Sel_injective_cprod 1),
        (fast_tac (HOL_cs addIs [antisym_less]) 1),
        (fast_tac (HOL_cs addIs [antisym_less]) 1)
        ]);

qed_goalw "trans_less_cprod" thy [less_cprod_def]
        "[|(p1::'a*'b) << p2;p2 << p3|] ==> p1 << p3"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac conjI 1),
        (fast_tac (HOL_cs addIs [trans_less]) 1),
        (fast_tac (HOL_cs addIs [trans_less]) 1)
        ]);

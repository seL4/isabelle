(*  Title:      HOLCF/Sprod1.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for theory Sprod1.thy
*)

open Sprod1;

(* ------------------------------------------------------------------------ *)
(* less_sprod is a partial order on Sprod                                   *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_sprod" thy [less_sprod_def]"(p::'a ** 'b) << p"
(fn prems => [(fast_tac (HOL_cs addIs [refl_less]) 1)]);

qed_goalw "antisym_less_sprod" thy [less_sprod_def]
        "[|(p1::'a ** 'b) << p2;p2 << p1|] ==> p1=p2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac Sel_injective_Sprod 1),
        (fast_tac (HOL_cs addIs [antisym_less]) 1),
        (fast_tac (HOL_cs addIs [antisym_less]) 1)
        ]);

qed_goalw "trans_less_sprod" thy [less_sprod_def]
        "[|(p1::'a**'b) << p2;p2 << p3|] ==> p1 << p3"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac conjI 1),
        (fast_tac (HOL_cs addIs [trans_less]) 1),
        (fast_tac (HOL_cs addIs [trans_less]) 1)
        ]);

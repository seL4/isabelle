(*  Title:      ZF/AC/recfunAC16.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Properties of the recursive definition used in the proof of WO2 ==> AC16
*)

(* ********************************************************************** *)
(* Basic properties of recfunAC16                                         *)
(* ********************************************************************** *)

Goalw [recfunAC16_def] "recfunAC16(f,fa,0,a) = 0";
by (rtac transrec2_0 1);
qed "recfunAC16_0";

Goalw [recfunAC16_def]
     "recfunAC16(f,fa,succ(i),a) =  \
\     (if (\\<exists>y \\<in> recfunAC16(f,fa,i,a). fa ` i \\<subseteq> y) then recfunAC16(f,fa,i,a) \
\      else recfunAC16(f,fa,i,a) Un \
\           {f ` (LEAST j. fa ` i \\<subseteq> f ` j &  \
\            (\\<forall>b<a. (fa`b \\<subseteq> f`j  \
\             --> (\\<forall>t \\<in> recfunAC16(f,fa,i,a). ~ fa`b \\<subseteq> t))))})";
by (rtac transrec2_succ 1);
qed "recfunAC16_succ";

Goalw [recfunAC16_def] "Limit(i)  \
\       ==> recfunAC16(f,fa,i,a) = (\\<Union>j<i. recfunAC16(f,fa,j,a))";
by (etac transrec2_Limit 1);
qed "recfunAC16_Limit";

(* ********************************************************************** *)
(* Monotonicity of transrec2                                              *)
(* ********************************************************************** *)

val [prem1, prem2] = goal thy 
    "[| !!g r. r \\<subseteq> B(g,r);  Ord(i) |]  \
\       ==> j<i --> transrec2(j, 0, B) \\<subseteq> transrec2(i, 0, B)";
by (resolve_tac [prem2 RS trans_induct] 1);
by (rtac Ord_cases 1 THEN (REPEAT (assume_tac 1)));
by (Fast_tac 1);
by (Asm_simp_tac 1);
by (fast_tac (FOL_cs addSIs [succI1, prem1]
        addSEs [ballE, leE, prem1 RSN (2, subset_trans)]) 1);
by (fast_tac (claset() addIs [OUN_I, ltI]
        addSEs [Limit_has_succ RS ltE, succI1 RSN (2, Ord_in_Ord) RS le_refl,
                transrec2_Limit RS ssubst]) 1);
qed "transrec2_mono_lemma";

val [prem1, prem2] = goal thy "[| !!g r. r \\<subseteq> B(g,r); j le i |]  \
\       ==> transrec2(j, 0, B) \\<subseteq> transrec2(i, 0, B)";
by (resolve_tac [prem2 RS leE] 1);
by (resolve_tac [transrec2_mono_lemma RS impE] 1);
by (TRYALL (fast_tac (claset() addSIs [prem1, prem2, lt_Ord2])));
qed "transrec2_mono";

(* ********************************************************************** *)
(* Monotonicity of recfunAC16                                             *)
(* ********************************************************************** *)

Goalw [recfunAC16_def]
        "!!i. i le j ==> recfunAC16(f, g, i, a) \\<subseteq> recfunAC16(f, g, j, a)";
by (rtac transrec2_mono 1);
by (REPEAT (fast_tac (claset() addIs [split_if RS iffD2]) 1));
qed "recfunAC16_mono";


(*  Title: 	ZF/AC/recfunAC16.ML
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Properties of the recursive definition used in the proof of WO2 ==> AC16
*)

open recfunAC16;

(* ********************************************************************** *)
(* Basic properties of recfunAC16					  *)
(* ********************************************************************** *)

goalw thy [recfunAC16_def] "recfunAC16(f,fa,0,a) = 0";
by (rtac transrec2_0 1);
val recfunAC16_0 = result();

goalw thy [recfunAC16_def] "recfunAC16(f,fa,succ(i),a) =  \
\       if (EX y:recfunAC16(f,fa,i,a). fa ` i <= y, recfunAC16(f,fa,i,a), \
\       recfunAC16(f,fa,i,a) Un {f ` (LEAST j. fa ` i <= f ` j &  \
\	(ALL b<a. (fa`b <= f`j  \
\	--> (ALL t:recfunAC16(f,fa,i,a). ~ fa`b <= t))))})";
by (rtac transrec2_succ 1);
val recfunAC16_succ = result();

goalw thy [recfunAC16_def] "!!i. Limit(i)  \
\	==> recfunAC16(f,fa,i,a) = (UN j<i. recfunAC16(f,fa,j,a))";
by (etac transrec2_Limit 1);
val recfunAC16_Limit = result();

(* ********************************************************************** *)
(* Monotonicity of transrec2						  *)
(* ********************************************************************** *)

val [prem1, prem2] = goal thy 
    "[| !!g r. r <= B(g,r); Ord(i) |]  \
\	==> j<i --> transrec2(j, 0, B) <= transrec2(i, 0, B)";
by (resolve_tac [prem2 RS trans_induct] 1);
by (rtac Ord_cases 1 THEN (REPEAT (assume_tac 1)));
by (fast_tac lt_cs 1);
by (asm_simp_tac (AC_ss addsimps [transrec2_succ]) 1);
by (fast_tac (FOL_cs addSIs [succI1, prem1]
	addSEs [ballE, leE, prem1 RSN (2, subset_trans)]) 1);
by (fast_tac (AC_cs addIs [OUN_I, ltI]
	addSEs [Limit_has_succ RS ltE, succI1 RSN (2, Ord_in_Ord) RS le_refl,
		transrec2_Limit RS ssubst]) 1);
val transrec2_mono_lemma = result();

val [prem1, prem2] = goal thy "[| !!g r. r <= B(g,r); j le i |]  \
\	==> transrec2(j, 0, B) <= transrec2(i, 0, B)";
by (resolve_tac [prem2 RS leE] 1);
by (resolve_tac [transrec2_mono_lemma RS impE] 1);
by (TRYALL (fast_tac (AC_cs addSIs [prem1, prem2, lt_Ord2])));
val transrec2_mono = result();

(* ********************************************************************** *)
(* Monotonicity of recfunAC16						  *)
(* ********************************************************************** *)

goalw thy [recfunAC16_def]
	"!!i. i le j ==> recfunAC16(f, g, i, a) <= recfunAC16(f, g, j, a)";
by (rtac transrec2_mono 1);
by (REPEAT (fast_tac (AC_cs addIs [expand_if RS iffD2]) 1));
val recfunAC16_mono = result();


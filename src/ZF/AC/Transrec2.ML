(*  Title: 	ZF/AC/Transrec2.ML
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Transfinite recursion introduced to handle definitions based on the three
cases of ordinals.
*)

open Transrec2;

goal thy "transrec2(0,a,b) = a";
by (rtac (transrec2_def RS def_transrec RS trans) 1);
by (simp_tac ZF_ss 1);
val transrec2_0 = result();

goal thy "(THE j. succ(i)=succ(j)) = i";
by (fast_tac (AC_cs addSIs [the_equality]) 1);
val THE_succ_eq = result();

goal thy "transrec2(succ(i),a,b) = b(i, transrec2(i,a,b))";
by (rtac (transrec2_def RS def_transrec RS trans) 1);
by (simp_tac (ZF_ss addsimps [succ_not_0, THE_succ_eq, if_P]
	            setsolver K (fast_tac FOL_cs)) 1);
val transrec2_succ = result();

goal thy "!!i. Limit(i) ==> transrec2(i,a,b) = (UN j<i. transrec2(j,a,b))";
by (rtac (transrec2_def RS def_transrec RS trans) 1);
by (resolve_tac [if_not_P RS trans] 1 THEN
    fast_tac (AC_cs addSDs [Limit_has_0] addSEs [ltE]) 1);
by (resolve_tac [if_not_P RS trans] 1 THEN
    fast_tac (AC_cs addSEs [succ_LimitE]) 1);
by (simp_tac AC_ss 1);
val transrec2_Limit = result();

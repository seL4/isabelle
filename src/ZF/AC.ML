(*  Title: 	ZF/AC.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

For AC.thy.  The Axiom of Choice
*)

open AC;

(*The same as AC, but no premise a:A*)
val [nonempty] = goal AC.thy
     "[| !!x. x:A ==> (EX y. y:B(x)) |] ==> EX z. z : Pi(A,B)";
by (excluded_middle_tac "A=0" 1);
by (asm_simp_tac (ZF_ss addsimps [Pi_empty1]) 2 THEN fast_tac ZF_cs 2);
(*The non-trivial case*)
by (fast_tac (eq_cs addIs [AC, nonempty]) 1);
qed "AC_Pi";

(*Using dtac, this has the advantage of DELETING the universal quantifier*)
goal AC.thy "!!A B. ALL x:A. EX y. y:B(x) ==> EX y. y : Pi(A,B)";
by (resolve_tac [AC_Pi] 1);
by (eresolve_tac [bspec] 1);
by (assume_tac 1);
qed "AC_ball_Pi";

goal AC.thy "EX f. f: (PROD X: Pow(C)-{0}. X)";
by (res_inst_tac [("B1", "%x.x")] (AC_Pi RS exE) 1);
by (etac exI 2);
by (fast_tac eq_cs 1);
qed "AC_Pi_Pow";

val [nonempty] = goal AC.thy
     "[| !!x. x:A ==> (EX y. y:x)	\
\     |] ==> EX f: A->Union(A). ALL x:A. f`x : x";
by (res_inst_tac [("B1", "%x.x")] (AC_Pi RS exE) 1);
by (etac nonempty 1);
by (fast_tac (ZF_cs addDs [apply_type] addIs [Pi_type]) 1);
qed "AC_func";

goal ZF.thy "!!x A. [| 0 ~: A;  x: A |] ==> EX y. y:x";
by (subgoal_tac "x ~= 0" 1);
by (ALLGOALS (fast_tac eq_cs));
qed "non_empty_family";

goal AC.thy "!!A. 0 ~: A ==> EX f: A->Union(A). ALL x:A. f`x : x";
by (rtac AC_func 1);
by (REPEAT (ares_tac [non_empty_family] 1));
qed "AC_func0";

goal AC.thy "EX f: (Pow(C)-{0}) -> C. ALL x:(Pow(C)-{0}). f`x : x";
by (resolve_tac [AC_func0 RS bexE] 1);
by (rtac bexI 2);
by (assume_tac 2);
by (eresolve_tac [fun_weaken_type] 2);
by (ALLGOALS (fast_tac ZF_cs));
qed "AC_func_Pow";

goal AC.thy "!!A. 0 ~: A ==> EX f. f: (PROD x:A. x)";
by (rtac AC_Pi 1);
by (REPEAT (ares_tac [non_empty_family] 1));
qed "AC_Pi0";


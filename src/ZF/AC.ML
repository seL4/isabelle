(*  Title:      ZF/AC.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The Axiom of Choice
*)

(*The same as AC, but no premise a:A*)
val [nonempty] = goal (the_context ())
     "[| !!x. x:A ==> (EX y. y:B(x)) |] ==> EX z. z : Pi(A,B)";
by (excluded_middle_tac "A=0" 1);
by (asm_simp_tac (simpset() addsimps [Pi_empty1]) 2 THEN Blast_tac 2);
(*The non-trivial case*)
by (blast_tac (claset() addIs [AC, nonempty]) 1);
qed "AC_Pi";

(*Using dtac, this has the advantage of DELETING the universal quantifier*)
Goal "ALL x:A. EX y. y:B(x) ==> EX y. y : Pi(A,B)";
by (rtac AC_Pi 1);
by (etac bspec 1);
by (assume_tac 1);
qed "AC_ball_Pi";

Goal "EX f. f: (PROD X: Pow(C)-{0}. X)";
by (res_inst_tac [("B1", "%x. x")] (AC_Pi RS exE) 1);
by (etac exI 2);
by (Blast_tac 1);
qed "AC_Pi_Pow";

val [nonempty] = goal (the_context ())
     "[| !!x. x:A ==> (EX y. y:x)       \
\     |] ==> EX f: A->Union(A). ALL x:A. f`x : x";
by (res_inst_tac [("B1", "%x. x")] (AC_Pi RS exE) 1);
by (etac nonempty 1);
by (blast_tac (claset() addDs [apply_type] addIs [Pi_type]) 1);
qed "AC_func";

goal ZF.thy "!!x A. [| 0 ~: A;  x: A |] ==> EX y. y:x";
by (subgoal_tac "x ~= 0" 1);
by (ALLGOALS Blast_tac);
qed "non_empty_family";

Goal "0 ~: A ==> EX f: A->Union(A). ALL x:A. f`x : x";
by (rtac AC_func 1);
by (REPEAT (ares_tac [non_empty_family] 1));
qed "AC_func0";

Goal "EX f: (Pow(C)-{0}) -> C. ALL x:(Pow(C)-{0}). f`x : x";
by (resolve_tac [AC_func0 RS bexE] 1);
by (rtac bexI 2);
by (assume_tac 2);
by (etac fun_weaken_type 2);
by (ALLGOALS Blast_tac);
qed "AC_func_Pow";

Goal "0 ~: A ==> EX f. f: (PROD x:A. x)";
by (rtac AC_Pi 1);
by (REPEAT (ares_tac [non_empty_family] 1));
qed "AC_Pi0";

(*Used in Zorn.ML*)
Goal "[| ch : (PROD X:Pow(S) - {0}. X);  X<=S;  X~=S |] ==> ch ` (S-X) : S-X";
by (etac apply_type 1);
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "choice_Diff";


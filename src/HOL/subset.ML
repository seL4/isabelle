(*  Title:      HOL/subset
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Derived rules involving subsets
Union and Intersection as lattice operations
*)

(*** insert ***)

qed_goal "subset_insertI" Set.thy "B <= insert a B"
 (fn _=> [ (rtac subsetI 1), (etac insertI2 1) ]);

goal Set.thy "!!x. x ~: A ==> (A <= insert x B) = (A <= B)";
by(fast_tac set_cs 1);
qed "subset_insert";

(*** Big Union -- least upper bound of a set  ***)

val prems = goal Set.thy
    "B:A ==> B <= Union(A)";
by (REPEAT (ares_tac (prems@[subsetI,UnionI]) 1));
qed "Union_upper";

val [prem] = goal Set.thy
    "[| !!X. X:A ==> X<=C |] ==> Union(A) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UnionE, prem RS subsetD] 1));
qed "Union_least";

(** General union **)

val prems = goal Set.thy
    "a:A ==> B(a) <= (UN x:A. B(x))";
by (REPEAT (ares_tac (prems@[UN_I RS subsetI]) 1));
qed "UN_upper";

val [prem] = goal Set.thy
    "[| !!x. x:A ==> B(x)<=C |] ==> (UN x:A. B(x)) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UN_E, prem RS subsetD] 1));
qed "UN_least";

goal Set.thy "B(a) <= (UN x. B(x))";
by (REPEAT (ares_tac [UN1_I RS subsetI] 1));
qed "UN1_upper";

val [prem] = goal Set.thy "[| !!x. B(x)<=C |] ==> (UN x. B(x)) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UN1_E, prem RS subsetD] 1));
qed "UN1_least";


(*** Big Intersection -- greatest lower bound of a set ***)

val prems = goal Set.thy "B:A ==> Inter(A) <= B";
by (rtac subsetI 1);
by (REPEAT (resolve_tac prems 1 ORELSE etac InterD 1));
qed "Inter_lower";

val [prem] = goal Set.thy
    "[| !!X. X:A ==> C<=X |] ==> C <= Inter(A)";
by (rtac (InterI RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "Inter_greatest";

val prems = goal Set.thy "a:A ==> (INT x:A. B(x)) <= B(a)";
by (rtac subsetI 1);
by (REPEAT (resolve_tac prems 1 ORELSE etac INT_D 1));
qed "INT_lower";

val [prem] = goal Set.thy
    "[| !!x. x:A ==> C<=B(x) |] ==> C <= (INT x:A. B(x))";
by (rtac (INT_I RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "INT_greatest";

goal Set.thy "(INT x. B(x)) <= B(a)";
by (rtac subsetI 1);
by (REPEAT (resolve_tac prems 1 ORELSE etac INT1_D 1));
qed "INT1_lower";

val [prem] = goal Set.thy
    "[| !!x. C<=B(x) |] ==> C <= (INT x. B(x))";
by (rtac (INT1_I RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "INT1_greatest";

(*** Finite Union -- the least upper bound of 2 sets ***)

goal Set.thy "A <= A Un B";
by (REPEAT (ares_tac [subsetI,UnI1] 1));
qed "Un_upper1";

goal Set.thy "B <= A Un B";
by (REPEAT (ares_tac [subsetI,UnI2] 1));
qed "Un_upper2";

val prems = goal Set.thy "[| A<=C;  B<=C |] ==> A Un B <= C";
by (cut_facts_tac prems 1);
by (DEPTH_SOLVE (ares_tac [subsetI] 1 
          ORELSE eresolve_tac [UnE,subsetD] 1));
qed "Un_least";

(*** Finite Intersection -- the greatest lower bound of 2 sets *)

goal Set.thy "A Int B <= A";
by (REPEAT (ares_tac [subsetI] 1 ORELSE etac IntE 1));
qed "Int_lower1";

goal Set.thy "A Int B <= B";
by (REPEAT (ares_tac [subsetI] 1 ORELSE etac IntE 1));
qed "Int_lower2";

val prems = goal Set.thy "[| C<=A;  C<=B |] ==> C <= A Int B";
by (cut_facts_tac prems 1);
by (REPEAT (ares_tac [subsetI,IntI] 1
     ORELSE etac subsetD 1));
qed "Int_greatest";

(*** Set difference ***)

qed_goal "Diff_subset" Set.thy "A-B <= (A::'a set)"
 (fn _ => [ (REPEAT (ares_tac [subsetI] 1 ORELSE etac DiffE 1)) ]);

(*** Monotonicity ***)

val [prem] = goal Set.thy "mono(f) ==> f(A) Un f(B) <= f(A Un B)";
by (rtac Un_least 1);
by (rtac (Un_upper1 RS (prem RS monoD)) 1);
by (rtac (Un_upper2 RS (prem RS monoD)) 1);
qed "mono_Un";

val [prem] = goal Set.thy "mono(f) ==> f(A Int B) <= f(A) Int f(B)";
by (rtac Int_greatest 1);
by (rtac (Int_lower1 RS (prem RS monoD)) 1);
by (rtac (Int_lower2 RS (prem RS monoD)) 1);
qed "mono_Int";

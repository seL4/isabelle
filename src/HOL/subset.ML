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

Goal "x ~: A ==> (A <= insert x B) = (A <= B)";
by (Blast_tac 1);
qed "subset_insert";

(*** Big Union -- least upper bound of a set  ***)

Goal "B:A ==> B <= Union(A)";
by (REPEAT (ares_tac [subsetI,UnionI] 1));
qed "Union_upper";

val [prem] = Goal "[| !!X. X:A ==> X<=C |] ==> Union(A) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UnionE, prem RS subsetD] 1));
qed "Union_least";

(** General union **)

Goal "a:A ==> B(a) <= (UN x:A. B(x))";
by (Blast_tac 1);
qed "UN_upper";

val [prem] = Goal "[| !!x. x:A ==> B(x)<=C |] ==> (UN x:A. B(x)) <= C";
by (rtac subsetI 1);
by (REPEAT (eresolve_tac [asm_rl, UN_E, prem RS subsetD] 1));
qed "UN_least";


(*** Big Intersection -- greatest lower bound of a set ***)

Goal "B:A ==> Inter(A) <= B";
by (Blast_tac 1);
qed "Inter_lower";

val [prem] = Goal "[| !!X. X:A ==> C<=X |] ==> C <= Inter(A)";
by (rtac (InterI RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "Inter_greatest";

Goal "a:A ==> (INT x:A. B(x)) <= B(a)";
by (Blast_tac 1);
qed "INT_lower";

val [prem] = Goal "[| !!x. x:A ==> C<=B(x) |] ==> C <= (INT x:A. B(x))";
by (rtac (INT_I RS subsetI) 1);
by (REPEAT (eresolve_tac [asm_rl, prem RS subsetD] 1));
qed "INT_greatest";

(*** Finite Union -- the least upper bound of 2 sets ***)

Goal "A <= A Un B";
by (Blast_tac 1);
qed "Un_upper1";

Goal "B <= A Un B";
by (Blast_tac 1);
qed "Un_upper2";

Goal "[| A<=C;  B<=C |] ==> A Un B <= C";
by (Blast_tac 1);
qed "Un_least";

(*** Finite Intersection -- the greatest lower bound of 2 sets *)

Goal "A Int B <= A";
by (Blast_tac 1);
qed "Int_lower1";

Goal "A Int B <= B";
by (Blast_tac 1);
qed "Int_lower2";

Goal "[| C<=A;  C<=B |] ==> C <= A Int B";
by (Blast_tac 1);
qed "Int_greatest";

(*** Set difference ***)

qed_goal "Diff_subset" Set.thy "A-B <= (A::'a set)"
 (fn _ => [ (Blast_tac 1) ]);

(*** Monotonicity ***)

Goal "mono(f) ==> f(A) Un f(B) <= f(A Un B)";
by (rtac Un_least 1);
by (etac (Un_upper1 RSN (2,monoD)) 1);
by (etac (Un_upper2 RSN (2,monoD)) 1);
qed "mono_Un";

Goal "mono(f) ==> f(A Int B) <= f(A) Int f(B)";
by (rtac Int_greatest 1);
by (etac (Int_lower1 RSN (2,monoD)) 1);
by (etac (Int_lower2 RSN (2,monoD)) 1);
qed "mono_Int";

(*  Title:      CCL/subset
    ID:         $Id$

Modified version of
    Title:      HOL/subset
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Derived rules involving subsets
Union and Intersection as lattice operations
*)

(*** Big Union -- least upper bound of a set  ***)

val prems = goal Set.thy
    "B:A ==> B <= Union(A)";
by (REPEAT (ares_tac (prems@[subsetI,UnionI]) 1));
qed "Union_upper";

val prems = goal Set.thy
    "[| !!X. X:A ==> X<=C |] ==> Union(A) <= C";
by (REPEAT (ares_tac [subsetI] 1
     ORELSE eresolve_tac ([UnionE] @ (prems RL [subsetD])) 1));
qed "Union_least";


(*** Big Intersection -- greatest lower bound of a set ***)

val prems = goal Set.thy
    "B:A ==> Inter(A) <= B";
by (REPEAT (resolve_tac (prems@[subsetI]) 1
     ORELSE etac InterD 1));
qed "Inter_lower";

val prems = goal Set.thy
    "[| !!X. X:A ==> C<=X |] ==> C <= Inter(A)";
by (REPEAT (ares_tac [subsetI,InterI] 1
     ORELSE eresolve_tac (prems RL [subsetD]) 1));
qed "Inter_greatest";

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

(*** Monotonicity ***)

val [prem] = goalw Set.thy [mono_def]
    "[| !!A B. A <= B ==> f(A) <= f(B) |] ==> mono(f)";
by (REPEAT (ares_tac [allI, impI, prem] 1));
qed "monoI";

val [major,minor] = goalw Set.thy [mono_def]
    "[| mono(f);  A <= B |] ==> f(A) <= f(B)";
by (rtac (major RS spec RS spec RS mp) 1);
by (rtac minor 1);
qed "monoD";

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

(****)

val set_cs = FOL_cs 
    addSIs [ballI, subsetI, InterI, INT_I, CollectI, 
            ComplI, IntI, UnCI, singletonI] 
    addIs  [bexI, UnionI, UN_I] 
    addSEs [bexE, UnionE, UN_E,
            CollectE, ComplE, IntE, UnE, emptyE, singletonE] 
    addEs  [ballE, InterD, InterE, INT_D, INT_E, subsetD, subsetCE];

fun cfast_tac prems = cut_facts_tac prems THEN' fast_tac set_cs;

fun prover s = prove_goal Set.thy s (fn _=>[fast_tac set_cs 1]);

val mem_rews = [trivial_set,empty_eq] @ (map prover
 [ "(a : A Un B)   <->  (a:A | a:B)",
   "(a : A Int B)  <->  (a:A & a:B)",
   "(a : Compl(B)) <->  (~a:B)",
   "(a : {b})      <->  (a=b)",
   "(a : {})       <->   False",
   "(a : {x.P(x)}) <->  P(a)" ]);

val set_congs = [ball_cong, bex_cong, INT_cong, UN_cong];

val set_ss = FOL_ss addcongs set_congs
                    delsimps (ex_simps @ all_simps)  (*NO miniscoping*)
		    addsimps mem_rews;

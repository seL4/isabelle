(*  Title: 	Substitutions/setplus.ML
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For setplus.thy.
Properties of subsets and empty sets.
*)

open Setplus;

(*********)

(*** Rules for subsets ***)

goal Set.thy "A <= B =  (! t.t:A --> t:B)";
by (fast_tac set_cs 1);
qed "subset_iff";

goalw Setplus.thy [ssubset_def] "A < B = ((A <= B) & ~(A=B))";
by (rtac refl 1);
qed "ssubset_iff";

goal Setplus.thy "((A::'a set) <= B) = ((A < B) | (A=B))";
by (simp_tac (set_ss addsimps [ssubset_iff]) 1);
by (fast_tac set_cs 1);
qed "subseteq_iff_subset_eq";

(*Rule in Modus Ponens style*)
goal Setplus.thy "A < B --> c:A --> c:B";
by (simp_tac (set_ss addsimps [ssubset_iff]) 1);
by (fast_tac set_cs 1);
qed "ssubsetD";

(*********)

goalw Setplus.thy [empty_def] "~ a : {}";
by (fast_tac set_cs 1);
qed "not_in_empty";

goalw Setplus.thy [empty_def] "(A = {}) = (ALL a.~ a:A)";
by (fast_tac (set_cs addIs [set_ext]) 1);
qed "empty_iff";


(*********)

goal Set.thy "(~A=B)  = ((? x.x:A & ~x:B) | (? x.~x:A & x:B))";
by (fast_tac (set_cs addIs [set_ext]) 1);
qed "not_equal_iff";

(*********)

val setplus_rews = [ssubset_iff,not_in_empty,empty_iff];

(*********)

(*Case analysis for rewriting; P also gets rewritten*)
val [prem1,prem2] = goal HOL.thy "[| P-->Q;  ~P-->Q |] ==> Q";
by (rtac (excluded_middle RS disjE) 1);
by (etac (prem2 RS mp) 1);
by (etac (prem1 RS mp) 1);
qed "imp_excluded_middle";

fun imp_excluded_middle_tac s = res_inst_tac [("P",s)] imp_excluded_middle;

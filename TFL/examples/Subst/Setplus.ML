(*  Title:      Substitutions/setplus.ML
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For setplus.thy.
Properties of subsets and empty sets.
*)

open Setplus;
val eq_cs = claset_of "equalities";

(*********)

(*** Rules for subsets ***)

goal Set.thy "A <= B =  (! t.t:A --> t:B)";
by (fast_tac set_cs 1);
qed "subset_iff";

goalw Setplus.thy [ssubset_def] "A < B = ((A <= B) & ~(A=B))";
by (rtac refl 1);
qed "ssubset_iff";

goal Setplus.thy "((A::'a set) <= B) = ((A < B) | (A=B))";
by (simp_tac (simpset_of "Fun" addsimps [ssubset_iff]) 1);
by (fast_tac set_cs 1);
qed "subseteq_iff_subset_eq";

(*Rule in Modus Ponens style*)
goal Setplus.thy "A < B --> c:A --> c:B";
by (simp_tac (simpset_of "Fun" addsimps [ssubset_iff]) 1);
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


goal Set.thy "(insert a A ~= insert a B) --> A ~= B";
by (fast_tac set_cs 1);
val insert_lim = result() RS mp;

goal Set.thy "x~:A --> (A-{x} = A)";
by (fast_tac eq_cs 1);
val lem = result() RS mp;

goal Nat.thy "B<=A --> B = Suc A --> P";
by (strip_tac 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
val leq_lem = standard(result() RS mp RS mp);

goal Nat.thy "A<=B --> (A ~= Suc B)";
by (strip_tac 1);
by (rtac notI 1);
by (rtac leq_lem 1);
by (REPEAT (atac 1));
val leq_lem1 = standard(result() RS mp);

(* The following is an adaptation of the proof for the "<=" version 
 * in Finite. *) 

goalw Setplus.thy [ssubset_def]
"!!B. finite B ==> !A. A < B --> card(A) < card(B)";
by (etac finite_induct 1);
by (Simp_tac 1);
by (fast_tac set_cs 1);
by (strip_tac 1);
by (etac conjE 1);
by (case_tac "x:A" 1);
(*1*)
by (dtac mk_disjoint_insert 1);
by (etac exE 1);
by (etac conjE 1);
by (hyp_subst_tac 1);
by (rotate_tac ~1 1);
by (asm_full_simp_tac (!simpset addsimps 
                        [subset_insert_iff,finite_subset,lem]) 1);
by (dtac insert_lim 1);
by (Asm_full_simp_tac 1);
(*2*)
by (rotate_tac ~1 1);
by (asm_full_simp_tac (!simpset addsimps 
                       [subset_insert_iff,finite_subset,lem]) 1);
by (case_tac "A=F" 1);
by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (rtac leq_lem1 1);
by (Asm_simp_tac 1);
val ssubset_card = result() ;


goal Set.thy "(A = B) = ((A <= (B::'a set)) & (B<=A))";
by (rtac iffI 1);
by (simp_tac (HOL_ss addsimps [subset_iff]) 1);
by (fast_tac set_cs 1);
by (rtac subset_antisym 1);
by (ALLGOALS Asm_simp_tac);
val set_eq_subset = result();



(*  Title:      ZF/AC/AC15_WO6.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> WO2
*)

open AC15_WO6;

goal thy "!!x. Ord(x) ==> (UN a<x. F(a)) = (UN a:x. F(a))";
by (fast_tac (claset() addSIs [ltI] addSDs [ltD]) 1);
qed "OUN_eq_UN";

val [prem] = goal thy "ALL x:Pow(A)-{0}. f`x~=0 & f`x<=x & f`x lepoll m ==>  \
\       (UN i<LEAST x. HH(f,A,x)={A}. HH(f,A,i)) = A";
by (simp_tac (simpset() addsimps [Ord_Least RS OUN_eq_UN]) 1);
by (rtac equalityI 1);
by (fast_tac (claset() addSDs [less_Least_subset_x]) 1);
by (fast_tac (claset() addSDs [prem RS bspec]
                addSIs [f_subsets_imp_UN_HH_eq_x RS (Diff_eq_0_iff RS iffD1)]) 1);
val lemma1 = result();

val [prem] = goal thy "ALL x:Pow(A)-{0}. f`x~=0 & f`x<=x & f`x lepoll m ==>  \
\       ALL x<LEAST x. HH(f,A,x)={A}. HH(f,A,x) lepoll m";
by (rtac oallI 1);
by (dresolve_tac [ltD RS less_Least_subset_x] 1);
by (forward_tac [HH_subset_imp_eq] 1);
by (etac ssubst 1);
by (fast_tac (claset() addIs [prem RS ballE]
                addSDs [HH_subset_x_imp_subset_Diff_UN RS not_emptyI2]) 1);
val lemma2 = result();

goalw thy [AC15_def, WO6_def] "!!Z. AC15 ==> WO6";
by (rtac allI 1);
by (eres_inst_tac [("x","Pow(A)-{0}")] allE 1);
by (etac impE 1);
by (Fast_tac 1);
by (REPEAT (eresolve_tac [bexE,conjE,exE] 1));
by (rtac bexI 1 THEN (assume_tac 2));
by (rtac conjI 1 THEN (assume_tac 1));
by (res_inst_tac [("x","LEAST i. HH(f,A,i)={A}")] exI 1);
by (res_inst_tac [("x","lam j: (LEAST i. HH(f,A,i)={A}). HH(f,A,j)")] exI 1);
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addSIs [Ord_Least, lam_type RS domain_of_fun]
                addSEs [less_Least_subset_x, lemma1, lemma2]) 1);
qed "AC15_WO6";

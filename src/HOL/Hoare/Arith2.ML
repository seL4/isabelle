(*  Title:      HOL/Hoare/Arith2.ML
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic lemmas.
*)

open Arith2;


(*** HOL lemmas ***)


val [prem1,prem2]=goal HOL.thy "[|~P ==> ~Q; Q|] ==> P";
by (cut_facts_tac [prem1 COMP impI,prem2] 1);
by (Fast_tac 1);
val not_imp_swap=result();



(*** cd ***)


val prems=goalw thy [cd_def] "0<n ==> cd n n n";
by (cut_facts_tac prems 1);
by (Asm_simp_tac 1);
qed "cd_nnn";

val prems=goalw thy [cd_def] "[| cd x m n; 0<m; 0<n |] ==> x<=m & x<=n";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addIs [dvd_imp_le]) 1);
qed "cd_le";

val prems=goalw thy [cd_def] "cd x m n = cd x n m";
by (Fast_tac 1);
qed "cd_swap";

val prems=goalw thy [cd_def] "n<=m ==> cd x m n = cd x (m-n) n";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addIs [dvd_diff] addDs [dvd_diffD]) 1);
qed "cd_diff_l";

val prems=goalw thy [cd_def] "m<=n ==> cd x m n = cd x m (n-m)";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addIs [dvd_diff] addDs [dvd_diffD]) 1);
qed "cd_diff_r";


(*** gcd ***)

goalw thy [gcd_def] "!!n. 0<n ==> n = gcd n n";
by (forward_tac [cd_nnn] 1);
by (rtac (select_equality RS sym) 1);
by (blast_tac (claset() addDs [cd_le]) 1);
by (blast_tac (claset() addIs [le_anti_sym] addDs [cd_le]) 1);
qed "gcd_nnn";

val prems = goalw thy [gcd_def] "gcd m n = gcd n m";
by (simp_tac (simpset() addsimps [cd_swap]) 1);
qed "gcd_swap";

val prems=goalw thy [gcd_def] "n<=m ==> gcd m n = gcd (m-n) n";
by (cut_facts_tac prems 1);
by (subgoal_tac "n<=m ==> !x. cd x m n = cd x (m-n) n" 1);
by (Asm_simp_tac 1);
by (rtac allI 1);
by (etac cd_diff_l 1);
qed "gcd_diff_l";

val prems=goalw thy [gcd_def] "m<=n ==> gcd m n = gcd m (n-m)";
by (cut_facts_tac prems 1);
by (subgoal_tac "m<=n ==> !x. cd x m n = cd x m (n-m)" 1);
by (Asm_simp_tac 1);
by (rtac allI 1);
by (etac cd_diff_r 1);
qed "gcd_diff_r";


(*** pow ***)

val [pow_0,pow_Suc] = nat_recs pow_def;
store_thm("pow_0",pow_0);
store_thm("pow_Suc",pow_Suc);

goalw thy [pow_def] "m pow (n+k) = m pow n * m pow k";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [mult_left_commute])));
qed "pow_add_reduce";

goalw thy [pow_def] "m pow n pow k = m pow (n*k)";
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
by (fold_goals_tac [pow_def]);
by (rtac (pow_add_reduce RS sym) 1);
qed "pow_pow_reduce";

(*** fac ***)

Addsimps(nat_recs fac_def);

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


(*** analogue of diff_induct, for simultaneous induction over 3 vars ***)

val prems = goal Nat.thy
    "[| !!x. P x 0 0;  \
\       !!y. P 0 (Suc y) 0;  \
\       !!z. P 0 0 (Suc z);  \
\       !!x y. [| P x y 0 |] ==> P (Suc x) (Suc y) 0;  \
\       !!x z. [| P x 0 z |] ==> P (Suc x) 0 (Suc z);  \
\       !!y z. [| P 0 y z |] ==> P 0 (Suc y) (Suc z);  \
\       !!x y z. [| P x y z |] ==> P (Suc x) (Suc y) (Suc z)  \
\    |] ==> P m n k";
by (res_inst_tac [("x","m")] spec 1);
by (rtac diff_induct 1);
by (rtac allI 1);
by (rtac allI 2);
by (res_inst_tac [("m","xa"),("n","x")] diff_induct 1);
by (res_inst_tac [("m","x"),("n","Suc y")] diff_induct 4);
by (rtac allI 7);
by (nat_ind_tac "xa" 7);
by (ALLGOALS (resolve_tac prems));
by (assume_tac 1);
by (assume_tac 1);
by (Fast_tac 1);
by (Fast_tac 1);
qed "diff_induct3";

(*** interaction of + and - ***)

val prems=goal Arith.thy "~m<n+k ==> (m - n) - k = m - ((n + k)::nat)";
by (cut_facts_tac prems 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_not_assoc";

val prems=goal Arith.thy "[|~m<n; ~n<k|] ==> (m - n) + k = m - ((n - k)::nat)";
by (cut_facts_tac prems 1);
by (dtac conjI 1);
by (assume_tac 1);
by (res_inst_tac [("P","~m<n & ~n<k")] mp 1);
by (assume_tac 2);
by (res_inst_tac [("m","m"),("n","n"),("k","k")] diff_induct3 1);
by (ALLGOALS Asm_simp_tac);
by (rtac impI 1);
by (dres_inst_tac [("P","~x<y")] conjE 1);
by (assume_tac 2);
by (rtac (Suc_diff_n RS sym) 1);
by (rtac le_less_trans 1);
by (etac (not_less_eq RS subst) 2);
by (rtac (hd ([diff_less_Suc RS lessD] RL [Suc_le_mono RS subst])) 1);
qed "diff_add_not_assoc";

val prems=goal Arith.thy "~n<k ==> (m + n) - k = m + ((n - k)::nat)";
by (cut_facts_tac prems 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("m","n"),("n","k")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "add_diff_assoc";

(*** more ***)

val prems = goal Arith.thy "m~=(n::nat) = (m<n | n<m)";
by (rtac iffI 1);
by (cut_inst_tac [("m","m"),("n","n")] less_linear 1);
by (Asm_full_simp_tac 1);
by (etac disjE 1);
by (etac (less_not_refl2 RS not_sym) 1);
by (etac less_not_refl2 1);
qed "not_eq_eq_less_or_gr";

val [prem] = goal Arith.thy "m<n ==> n-m~=0";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "less_imp_diff_not_0";

(*******************************************************************)

val prems = goal Arith.thy "(i::nat)<j ==> k+i<k+j";
by (cut_facts_tac prems 1);
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_less_mono_l";

val prems = goal Arith.thy "~(i::nat)<j ==> ~k+i<k+j";
by (cut_facts_tac prems 1);
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "add_not_less_mono_l";

(******************************************************************)

(*** mod ***)

val prems=goal thy "[|0<x; m mod x = 0; n mod x = 0|] ==> (m+n) mod x = 0";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","m div x * x + m mod x"),("t","m")] subst 1);
by (etac mod_div_equality 1);
by (res_inst_tac [("s","n div x * x + n mod x"),("t","n")] subst 1);
by (etac mod_div_equality 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("s","(m div x + n div x) * x"),("t","m div x * x + n div x * x")] subst 1);
by (rtac add_mult_distrib 1);
by (etac mod_prod_nn_is_0 1);
qed "mod0_sum";

val prems=goal thy "[|0<x; m mod x = 0; n mod x = 0; n<=m|] ==> (m-n) mod x = 0";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","m div x * x + m mod x"),("t","m")] subst 1);
by (etac mod_div_equality 1);
by (res_inst_tac [("s","n div x * x + n mod x"),("t","n")] subst 1);
by (etac mod_div_equality 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("s","(m div x - n div x) * x"),("t","m div x * x - n div x * x")] subst 1);
by (rtac diff_mult_distrib 1);
by (etac mod_prod_nn_is_0 1);
qed "mod0_diff";


(*** divides ***)

val prems=goalw thy [divides_def] "0<n ==> n divides n";
by (cut_facts_tac prems 1);
by (forward_tac [mod_nn_is_0] 1);
by (Asm_simp_tac 1);
qed "divides_nn";

val prems=goalw thy [divides_def] "x divides n ==> x<=n";
by (cut_facts_tac prems 1);
by (rtac ((mod_less COMP rev_contrapos) RS (le_def RS meta_eq_to_obj_eq RS iffD2)) 1);
by (Asm_simp_tac 1);
by (rtac (less_not_refl2 RS not_sym) 1);
by (Asm_simp_tac 1);
qed "divides_le";

val prems=goalw thy [divides_def] "[|x divides m; x divides n|] ==> x divides (m+n)";
by (cut_facts_tac prems 1);
by (REPEAT ((dtac conjE 1) THEN (atac 2)));
by (rtac conjI 1);
by (dres_inst_tac [("m","0"),("n","m")] less_imp_add_less 1);
by (assume_tac 1);
by (etac conjI 1);
by (rtac mod0_sum 1);
by (ALLGOALS atac);
qed "divides_sum";

val prems=goalw thy [divides_def] "[|x divides m; x divides n; n<m|] ==> x divides (m-n)";
by (cut_facts_tac prems 1);
by (REPEAT ((dtac conjE 1) THEN (atac 2)));
by (rtac conjI 1);
by (etac less_imp_diff_positive 1);
by (etac conjI 1);
by (rtac mod0_diff 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [le_def])));
by (etac less_not_sym 1);
qed "divides_diff";


(*** cd ***)


val prems=goalw thy [cd_def] "0<n ==> cd n n n";
by (cut_facts_tac prems 1);
by (dtac divides_nn 1);
by (Asm_simp_tac 1);
qed "cd_nnn";

val prems=goalw thy [cd_def] "cd x m n ==> x<=m & x<=n";
by (cut_facts_tac prems 1);
by (dtac conjE 1);
by (assume_tac 2);
by (dtac divides_le 1);
by (dtac divides_le 1);
by (Asm_simp_tac 1);
qed "cd_le";

val prems=goalw thy [cd_def] "cd x m n = cd x n m";
by (Fast_tac 1);
qed "cd_swap";

val prems=goalw thy [cd_def] "n<m ==> cd x m n = cd x (m-n) n";
by (cut_facts_tac prems 1);
by (rtac iffI 1);
by (dtac conjE 1);
by (assume_tac 2);
by (rtac conjI 1);
by (rtac divides_diff 1);
by (dtac conjE 5);
by (assume_tac 6);
by (rtac conjI 5);
by (dtac less_not_sym 5);
by (dtac add_diff_inverse 5);
by (dres_inst_tac [("m","n"),("n","m-n")] divides_sum 5);
by (ALLGOALS Asm_full_simp_tac);
qed "cd_diff_l";

val prems=goalw thy [cd_def] "m<n ==> cd x m n = cd x m (n-m)";
by (cut_facts_tac prems 1);
by (rtac iffI 1);
by (dtac conjE 1);
by (assume_tac 2);
by (rtac conjI 1);
by (rtac divides_diff 2);
by (dtac conjE 5);
by (assume_tac 6);
by (rtac conjI 5);
by (dtac less_not_sym 6);
by (dtac add_diff_inverse 6);
by (dres_inst_tac [("n","n-m")] divides_sum 6);
by (ALLGOALS Asm_full_simp_tac);
qed "cd_diff_r";


(*** gcd ***)

val prems = goalw thy [gcd_def] "0<n ==> n = gcd n n";
by (cut_facts_tac prems 1);
by (dtac cd_nnn 1);
by (rtac (select_equality RS sym) 1);
by (etac conjI 1);
by (rtac allI 1);
by (rtac impI 1);
by (dtac cd_le 1);
by (dtac conjE 2);
by (assume_tac 3);
by (rtac le_anti_sym 2);
by (dres_inst_tac [("x","x")] cd_le 2);
by (dres_inst_tac [("x","n")] spec 3);
by (ALLGOALS Asm_full_simp_tac);
qed "gcd_nnn";

val prems = goalw thy [gcd_def] "gcd m n = gcd n m";
by (simp_tac (!simpset addsimps [cd_swap]) 1);
qed "gcd_swap";

val prems=goalw thy [gcd_def] "n<m ==> gcd m n = gcd (m-n) n";
by (cut_facts_tac prems 1);
by (subgoal_tac "n<m ==> !x.cd x m n = cd x (m-n) n" 1);
by (Asm_simp_tac 1);
by (rtac allI 1);
by (etac cd_diff_l 1);
qed "gcd_diff_l";

val prems=goalw thy [gcd_def] "m<n ==> gcd m n = gcd m (n-m)";
by (cut_facts_tac prems 1);
by (subgoal_tac "m<n ==> !x.cd x m n = cd x m (n-m)" 1);
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
by (ALLGOALS (asm_simp_tac (!simpset addsimps [mult_left_commute])));
qed "pow_add_reduce";

goalw thy [pow_def] "m pow n pow k = m pow (n*k)";
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
by (fold_goals_tac [pow_def]);
by (rtac (pow_add_reduce RS sym) 1);
qed "pow_pow_reduce";

(*** fac ***)

Addsimps(nat_recs fac_def);

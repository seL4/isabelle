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
by (fast_tac HOL_cs 1);
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
br diff_induct 1;
br allI 1;
br allI 2;
by (res_inst_tac [("m","xa"),("n","x")] diff_induct 1);
by (res_inst_tac [("m","x"),("n","Suc y")] diff_induct 4);
br allI 7;
by (nat_ind_tac "xa" 7);
by (ALLGOALS (resolve_tac prems));
ba 1;
ba 1;
by (fast_tac HOL_cs 1);
by (fast_tac HOL_cs 1);
qed "diff_induct3";

(*** interaction of + and - ***)

val prems=goal Arith.thy "~m<n+k ==> (m - n) - k = m - ((n + k)::nat)";
by (cut_facts_tac prems 1);
br mp 1;
ba 2;
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "diff_not_assoc";

val prems=goal Arith.thy "[|~m<n; ~n<k|] ==> (m - n) + k = m - ((n - k)::nat)";
by (cut_facts_tac prems 1);
bd conjI 1;
ba 1;
by (res_inst_tac [("P","~m<n & ~n<k")] mp 1);
ba 2;
by (res_inst_tac [("m","m"),("n","n"),("k","k")] diff_induct3 1);
by (ALLGOALS Asm_simp_tac);
br impI 1;
by (dres_inst_tac [("P","~x<y")] conjE 1);
ba 2;
br (Suc_diff_n RS sym) 1;
br le_less_trans 1;
be (not_less_eq RS subst) 2;
br (hd ([diff_less_Suc RS lessD] RL [Suc_le_mono RS subst])) 1;
qed "diff_add_not_assoc";

val prems=goal Arith.thy "~n<k ==> (m + n) - k = m + ((n - k)::nat)";
by (cut_facts_tac prems 1);
br mp 1;
ba 2;
by (res_inst_tac [("m","n"),("n","k")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "add_diff_assoc";

(*** more ***)

val prems = goal Arith.thy "m~=(n::nat) = (m<n | n<m)";
br iffI 1;
by (cut_inst_tac [("m","m"),("n","n")] less_linear 1);
by (Asm_full_simp_tac 1);
be disjE 1;
be (less_not_refl2 RS not_sym) 1;
be less_not_refl2 1;
qed "not_eq_eq_less_or_gr";

val [prem] = goal Arith.thy "m<n ==> n-m~=0";
by (rtac (prem RS rev_mp) 1);
by (res_inst_tac [("m","m"),("n","n")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed "less_imp_diff_not_0";

(*******************************************************************)

(** Some of these are now proved, with different names, in HOL/Arith.ML **)

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

val prems = goal Arith.thy "[|0<k; m<(n::nat)|] ==> m*k<n*k";
by (cut_facts_tac prems 1);
by (res_inst_tac [("n","k")] natE 1);
by (ALLGOALS Asm_full_simp_tac);
by (nat_ind_tac "x" 1);
be add_less_mono 2;
by (ALLGOALS Asm_full_simp_tac);
qed "mult_less_mono_r";

val prems = goal Arith.thy "~m<(n::nat) ==> ~m*k<n*k";
by (cut_facts_tac prems 1);
by (nat_ind_tac "k" 1);
by (ALLGOALS Simp_tac);
by (fold_goals_tac [le_def]);
be add_le_mono 1;
ba 1;
qed "mult_not_less_mono_r";

val prems = goal Arith.thy "m=(n::nat) ==> m*k=n*k";
by (cut_facts_tac prems 1);
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
qed "mult_eq_mono_r";

val prems = goal Arith.thy "[|0<k; m~=(n::nat)|] ==> m*k~=n*k";
by (cut_facts_tac prems 1);
by (res_inst_tac [("P","m<n"),("Q","n<m")] disjE 1);
br (less_not_refl2 RS not_sym) 2;
be mult_less_mono_r 2;
br less_not_refl2 3;
be mult_less_mono_r 3;
by (ALLGOALS (asm_full_simp_tac ((simpset_of "Arith") addsimps [not_eq_eq_less_or_gr])));
qed "mult_not_eq_mono_r";

(******************************************************************)

(*** mod ***)

goal Arith.thy "(%m. m mod n) = wfrec (trancl pred_nat) \
             \                      (%f j. if j<n then j else f (j-n))";
by (simp_tac (HOL_ss addsimps [mod_def]) 1);
val mod_def = result() RS eq_reflection;

(* Alternativ-Beweis zu mod_nn_is_0: Spezialfall zu mod_prod_nn_is_0 *)
(*
val prems = goal thy "0<n ==> n mod n = 0";
by (cut_inst_tac [("m","Suc(0)")] (mod_prod_nn_is_0 COMP impI) 1);
by (cut_facts_tac prems 1);
by (Asm_full_simp_tac 1);
by (fast_tac HOL_cs 1);
*)

val prems=goal thy "0<n ==> n mod n = 0";
by (cut_facts_tac prems 1);
br (mod_def RS wf_less_trans) 1;
by (asm_full_simp_tac ((simpset_of "Arith") addsimps [diff_self_eq_0,cut_def,less_eq]) 1);
be mod_less 1;
qed "mod_nn_is_0";

val prems=goal thy "0<n ==> m mod n = (m+n) mod n";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","n+m"),("t","m+n")] subst 1);
br add_commute 1;
by (res_inst_tac [("s","n+m-n"),("P","%x.x mod n = (n + m) mod n")] subst 1);
br diff_add_inverse 1;
br sym 1;
be mod_geq 1;
by (res_inst_tac [("s","n<=n+m"),("t","~n+m<n")] subst 1);
by (simp_tac ((simpset_of "Arith") addsimps [le_def]) 1);
br le_add1 1;
qed "mod_eq_add";

val prems=goal thy "0<n ==> m*n mod n = 0";
by (cut_facts_tac prems 1);
by (nat_ind_tac "m" 1);
by (Simp_tac 1);
be mod_less 1;
by (dres_inst_tac [("n","n"),("m","m1*n")] mod_eq_add 1);
by (asm_full_simp_tac ((simpset_of "Arith") addsimps [add_commute]) 1);
qed "mod_prod_nn_is_0";

val prems=goal thy "[|0<x; m mod x = 0; n mod x = 0|] ==> (m+n) mod x = 0";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","m div x * x + m mod x"),("t","m")] subst 1);
be mod_div_equality 1;
by (res_inst_tac [("s","n div x * x + n mod x"),("t","n")] subst 1);
be mod_div_equality 1;
by (Asm_simp_tac 1);
by (res_inst_tac [("s","(m div x + n div x) * x"),("t","m div x * x + n div x * x")] subst 1);
br add_mult_distrib 1;
be mod_prod_nn_is_0 1;
qed "mod0_sum";

val prems=goal thy "[|0<x; m mod x = 0; n mod x = 0; n<=m|] ==> (m-n) mod x = 0";
by (cut_facts_tac prems 1);
by (res_inst_tac [("s","m div x * x + m mod x"),("t","m")] subst 1);
be mod_div_equality 1;
by (res_inst_tac [("s","n div x * x + n mod x"),("t","n")] subst 1);
be mod_div_equality 1;
by (Asm_simp_tac 1);
by (res_inst_tac [("s","(m div x - n div x) * x"),("t","m div x * x - n div x * x")] subst 1);
br diff_mult_distrib 1;
be mod_prod_nn_is_0 1;
qed "mod0_diff";


(*** div ***)


val prems = goal thy "0<n ==> m*n div n = m";
by (cut_facts_tac prems 1);
br (mult_not_eq_mono_r RS not_imp_swap) 1;
ba 1;
ba 1;
by (res_inst_tac [("P","%x.m*n div n * n = x")] (mod_div_equality RS subst) 1);
ba 1;
by (dres_inst_tac [("m","m")] mod_prod_nn_is_0 1);
by (Asm_simp_tac 1);
qed "div_prod_nn_is_m";


(*** divides ***)

val prems=goalw thy [divides_def] "0<n ==> n divides n";
by (cut_facts_tac prems 1);
by (forward_tac [mod_nn_is_0] 1);
by (Asm_simp_tac 1);
qed "divides_nn";

val prems=goalw thy [divides_def] "x divides n ==> x<=n";
by (cut_facts_tac prems 1);
br ((mod_less COMP rev_contrapos) RS (le_def RS meta_eq_to_obj_eq RS iffD2)) 1;
by (Asm_simp_tac 1);
br (less_not_refl2 RS not_sym) 1;
by (Asm_simp_tac 1);
qed "divides_le";

val prems=goalw thy [divides_def] "[|x divides m; x divides n|] ==> x divides (m+n)";
by (cut_facts_tac prems 1);
by (REPEAT ((dtac conjE 1) THEN (atac 2)));
br conjI 1;
by (dres_inst_tac [("m","0"),("n","m")] less_imp_add_less 1);
ba 1;
be conjI 1;
br mod0_sum 1;
by (ALLGOALS atac);
qed "divides_sum";

val prems=goalw thy [divides_def] "[|x divides m; x divides n; n<m|] ==> x divides (m-n)";
by (cut_facts_tac prems 1);
by (REPEAT ((dtac conjE 1) THEN (atac 2)));
br conjI 1;
be less_imp_diff_positive 1;
be conjI 1;
br mod0_diff 1;
by (ALLGOALS (asm_simp_tac ((simpset_of "Arith") addsimps [le_def])));
be less_not_sym 1;
qed "divides_diff";


(*** cd ***)


val prems=goalw thy [cd_def] "0<n ==> cd n n n";
by (cut_facts_tac prems 1);
bd divides_nn 1;
by (Asm_simp_tac 1);
qed "cd_nnn";

val prems=goalw thy [cd_def] "cd x m n ==> x<=m & x<=n";
by (cut_facts_tac prems 1);
bd conjE 1;
ba 2;
bd divides_le 1;
bd divides_le 1;
by (Asm_simp_tac 1);
qed "cd_le";

val prems=goalw thy [cd_def] "cd x m n = cd x n m";
by (fast_tac HOL_cs 1);
qed "cd_swap";

val prems=goalw thy [cd_def] "n<m ==> cd x m n = cd x (m-n) n";
by (cut_facts_tac prems 1);
br iffI 1;
bd conjE 1;
ba 2;
br conjI 1;
br divides_diff 1;
bd conjE 5;
ba 6;
br conjI 5;
bd less_not_sym 5;
bd add_diff_inverse 5;
by (dres_inst_tac [("m","n"),("n","m-n")] divides_sum 5);
by (ALLGOALS Asm_full_simp_tac);
qed "cd_diff_l";

val prems=goalw thy [cd_def] "m<n ==> cd x m n = cd x m (n-m)";
by (cut_facts_tac prems 1);
br iffI 1;
bd conjE 1;
ba 2;
br conjI 1;
br divides_diff 2;
bd conjE 5;
ba 6;
br conjI 5;
bd less_not_sym 6;
bd add_diff_inverse 6;
by (dres_inst_tac [("n","n-m")] divides_sum 6);
by (ALLGOALS Asm_full_simp_tac);
qed "cd_diff_r";


(*** gcd ***)

val prems = goalw thy [gcd_def] "0<n ==> n = gcd n n";
by (cut_facts_tac prems 1);
bd cd_nnn 1;
br (select_equality RS sym) 1;
be conjI 1;
br allI 1;
br impI 1;
bd cd_le 1;
bd conjE 2;
ba 3;
br le_anti_sym 2;
by (dres_inst_tac [("x","x")] cd_le 2);
by (dres_inst_tac [("x","n")] spec 3);
by (ALLGOALS Asm_full_simp_tac);
qed "gcd_nnn";

val prems = goalw thy [gcd_def] "gcd m n = gcd n m";
by (simp_tac ((simpset_of "Arith") addsimps [cd_swap]) 1);
qed "gcd_swap";

val prems=goalw thy [gcd_def] "n<m ==> gcd m n = gcd (m-n) n";
by (cut_facts_tac prems 1);
by (subgoal_tac "n<m ==> !x.cd x m n = cd x (m-n) n" 1);
by (Asm_simp_tac 1);
br allI 1;
be cd_diff_l 1;
qed "gcd_diff_l";

val prems=goalw thy [gcd_def] "m<n ==> gcd m n = gcd m (n-m)";
by (cut_facts_tac prems 1);
by (subgoal_tac "m<n ==> !x.cd x m n = cd x m (n-m)" 1);
by (Asm_simp_tac 1);
br allI 1;
be cd_diff_r 1;
qed "gcd_diff_r";


(*** pow ***)

val [pow_0,pow_Suc] = nat_recs pow_def;
store_thm("pow_0",pow_0);
store_thm("pow_Suc",pow_Suc);

goalw thy [pow_def] "m pow (n+k) = m pow n * m pow k";
by (nat_ind_tac "k" 1);
by (ALLGOALS (asm_simp_tac ((simpset_of "Arith") addsimps [mult_left_commute])));
qed "pow_add_reduce";

goalw thy [pow_def] "m pow n pow k = m pow (n*k)";
by (nat_ind_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
by (fold_goals_tac [pow_def]);
br (pow_add_reduce RS sym) 1;
qed "pow_pow_reduce";

(*** fac ***)

Addsimps(nat_recs fac_def);

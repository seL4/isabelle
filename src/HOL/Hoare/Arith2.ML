(*  Title:      HOL/Hoare/Arith2.ML
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

More arithmetic lemmas.
*)

open Arith2;


(*** cd ***)


Goalw [cd_def] "0<n ==> cd n n n";
by (Asm_simp_tac 1);
qed "cd_nnn";

Goalw [cd_def] "[| cd x m n; 0<m; 0<n |] ==> x<=m & x<=n";
by (blast_tac (claset() addIs [dvd_imp_le]) 1);
qed "cd_le";

Goalw [cd_def] "cd x m n = cd x n m";
by (Fast_tac 1);
qed "cd_swap";

Goalw [cd_def] "n<=m ==> cd x m n = cd x (m-n) n";
by (blast_tac (claset() addIs [dvd_diff] addDs [dvd_diffD]) 1);
qed "cd_diff_l";

Goalw [cd_def] "m<=n ==> cd x m n = cd x m (n-m)";
by (blast_tac (claset() addIs [dvd_diff] addDs [dvd_diffD]) 1);
qed "cd_diff_r";


(*** gcd ***)

Goalw [gcd_def] "0<n ==> n = gcd n n";
by (ftac cd_nnn 1);
by (rtac (some_equality RS sym) 1);
by (blast_tac (claset() addDs [cd_le]) 1);
by (blast_tac (claset() addIs [le_anti_sym] addDs [cd_le]) 1);
qed "gcd_nnn";

val prems = goalw thy [gcd_def] "gcd m n = gcd n m";
by (simp_tac (simpset() addsimps [cd_swap]) 1);
qed "gcd_swap";

Goalw [gcd_def] "n<=m ==> gcd m n = gcd (m-n) n";
by (subgoal_tac "n<=m ==> !x. cd x m n = cd x (m-n) n" 1);
by (Asm_simp_tac 1);
by (rtac allI 1);
by (etac cd_diff_l 1);
qed "gcd_diff_l";

Goalw [gcd_def] "m<=n ==> gcd m n = gcd m (n-m)";
by (subgoal_tac "m<=n ==> !x. cd x m n = cd x m (n-m)" 1);
by (Asm_simp_tac 1);
by (rtac allI 1);
by (etac cd_diff_r 1);
qed "gcd_diff_r";


(*** pow ***)

Goal "m mod 2 = 0 ==> ((n::nat)*n)^(m div 2) = n^m";
by (asm_simp_tac (simpset() addsimps [power_two RS sym, power_mult RS sym,
				      mult_div_cancel]) 1);
qed "sq_pow_div2";
Addsimps [sq_pow_div2];

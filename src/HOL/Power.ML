(*  Title:      HOL/Power.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The (overloaded) exponentiation operator, ^ :: [nat,nat]=>nat
Also binomial coefficents
*)


open Power;

(*** Simple laws about Power ***)

goal thy "!!i::nat. i ^ (j+k) = (i^j) * (i^k)";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps mult_ac)));
qed "power_add";

goal thy "!!i::nat. i ^ (j*k) = (i^j) ^ k";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [power_add])));
qed "power_mult";

goal thy "!! i. 0 < i ==> 0 < i^n";
by (induct_tac "n" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [zero_less_mult_iff])));
qed "zero_less_power";

goalw thy [dvd_def] "!!m::nat. m<=n ==> i^m dvd i^n";
by (etac (not_less_iff_le RS iffD2 RS add_diff_inverse RS subst) 1);
by (asm_simp_tac (!simpset addsimps [power_add]) 1);
by (Blast_tac 1);
qed "le_imp_power_dvd";

goal thy "!! i r. [| 0 < i; i^m < i^n |] ==> m<n";
by (rtac ccontr 1);
by (dtac (leI RS le_imp_power_dvd RS dvd_imp_le RS leD) 1);
by (etac zero_less_power 1);
by (contr_tac 1);
qed "power_less_imp_less";

goal thy "!!n. k^j dvd n --> i<j --> k^i dvd n";
by (induct_tac "j" 1);
by (ALLGOALS (simp_tac (!simpset addsimps [less_Suc_eq])));
by (stac mult_commute 1);
by (blast_tac (!claset addSDs [dvd_mult_left]) 1);
qed_spec_mp "power_less_dvd";


(*** Binomial Coefficients, following Andy Gordon and Florian Kammueller ***)

goal thy "(n choose 0) = 1";
by (exhaust_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "binomial_n_0";

goal thy "(0 choose Suc k) = 0";
by (Simp_tac 1);
qed "binomial_0_Suc";

goal thy "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)";
by (Simp_tac 1);
qed "binomial_Suc_Suc";

Addsimps [binomial_n_0, binomial_0_Suc, binomial_Suc_Suc];
Delsimps [binomial_0, binomial_Suc];


goal thy "!k. n<k --> (n choose k) = 0";
by (induct_tac "n" 1);
by (ALLGOALS (rtac allI THEN' exhaust_tac "k"));
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "less_imp_binomial_eq_0";

goal thy "(n choose n) = 1";
by (induct_tac "n" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [less_imp_binomial_eq_0])));
qed "binomial_n_n";
Addsimps [binomial_n_n];

goal thy "(Suc n choose n) = Suc n";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "binomial_Suc_n";
Addsimps [binomial_Suc_n];

goal thy "(n choose 1) = n";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "binomial_1";
Addsimps [binomial_1];

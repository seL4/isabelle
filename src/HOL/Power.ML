(*  Title:      HOL/Power.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

The (overloaded) exponentiation operator, ^ :: [nat,nat]=>nat
Also binomial coefficents
*)

(*** Simple laws about Power ***)

Goal "!!i::nat. i ^ (j+k) = (i^j) * (i^k)";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps mult_ac)));
qed "power_add";

Goal "!!i::nat. i ^ (j*k) = (i^j) ^ k";
by (induct_tac "k" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [power_add])));
qed "power_mult";

Goal "!!i::nat. 0 < i ==> 0 < i^n";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "zero_less_power";
Addsimps [zero_less_power];

Goal "i^n = 0 ==> i = (0::nat)";
by (etac contrapos_pp 1); 
by Auto_tac;  
qed "power_eq_0D";

Goal "!!i::nat. 1 <= i ==> Suc 0 <= i^n";
by (induct_tac "n" 1);
by Auto_tac;
qed "one_le_power";
Addsimps [one_le_power];

Goal "!!i::nat. 1 < i ==> !m. (i^n = i^m) = (n=m)";
by (induct_tac "n" 1);
by Auto_tac;
by (ALLGOALS (case_tac "m"));
by Auto_tac;
qed_spec_mp "power_inject";
Addsimps [power_inject];

Goalw [dvd_def] "!!i::nat. m<=n ==> i^m dvd i^n";
by (etac (not_less_iff_le RS iffD2 RS add_diff_inverse RS subst) 1);
by (asm_simp_tac (simpset() addsimps [power_add]) 1);
qed "le_imp_power_dvd";

Goal "(1::nat) < i ==> \\<forall>n. i ^ m <= i ^ n --> m <= n";
by (induct_tac "m" 1);
by Auto_tac;  
by (case_tac "na" 1); 
by Auto_tac;
by (subgoal_tac "Suc 1 * 1 <= i * i^n" 1);
by (Asm_full_simp_tac 1); 
by (rtac mult_le_mono 1);
by Auto_tac;   
qed_spec_mp "power_le_imp_le";

Goal "!!i::nat. [| 0 < i; i^m < i^n |] ==> m < n";
by (rtac ccontr 1);
by (dtac (leI RS le_imp_power_dvd RS dvd_imp_le RS leD) 1);
by (etac zero_less_power 1);
by (contr_tac 1);
qed "power_less_imp_less";

Goal "k^j dvd n --> i<=j --> k^i dvd (n::nat)";
by (induct_tac "j" 1);
by (ALLGOALS (simp_tac (simpset() addsimps [le_Suc_eq])));
by (blast_tac (claset() addSDs [dvd_mult_right]) 1);
qed_spec_mp "power_le_dvd";

Goal "[|i^m dvd i^n;  (1::nat) < i|] ==> m <= n";
by (rtac power_le_imp_le 1); 
by (assume_tac 1); 
by (etac dvd_imp_le 1); 
by (Asm_full_simp_tac 1); 
qed "power_dvd_imp_le";


(*** Logical equivalences for inequalities ***)

Goal "(x^n = 0) = (x = (0::nat) & 0<n)";
by (induct_tac "n" 1);
by Auto_tac; 
qed "power_eq_0_iff";
Addsimps [power_eq_0_iff];

Goal "(0 < x^n) = (x ~= (0::nat) | n=0)";
by (induct_tac "n" 1);
by Auto_tac; 
qed "zero_less_power_iff";
Addsimps [zero_less_power_iff];

Goal "(0::nat) <= x^n";
by (induct_tac "n" 1);
by Auto_tac; 
qed "zero_le_power";
Addsimps [zero_le_power];


(**** Binomial Coefficients, following Andy Gordon and Florian Kammueller ****)

Goal "(n choose 0) = 1";
by (case_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "binomial_n_0";

Goal "(0 choose Suc k) = 0";
by (Simp_tac 1);
qed "binomial_0_Suc";

Goal "(Suc n choose Suc k) = (n choose k) + (n choose Suc k)";
by (Simp_tac 1);
qed "binomial_Suc_Suc";

Goal "ALL k. n < k --> (n choose k) = 0";
by (induct_tac "n" 1);
by Auto_tac;
by (etac allE 1);
by (etac mp 1);
by (arith_tac 1);
qed_spec_mp "binomial_eq_0";

Addsimps [binomial_n_0, binomial_0_Suc, binomial_Suc_Suc];
Delsimps [binomial_0, binomial_Suc];

Goal "(n choose n) = 1";
by (induct_tac "n" 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [binomial_eq_0])));
qed "binomial_n_n";
Addsimps [binomial_n_n];

Goal "(Suc n choose n) = Suc n";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "binomial_Suc_n";
Addsimps [binomial_Suc_n];

Goal "(n choose Suc 0) = n";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "binomial_1";
Addsimps [binomial_1];

Goal "k <= n --> 0 < (n choose k)";
by (res_inst_tac [("m","n"),("n","k")] diff_induct 1);
by (ALLGOALS Asm_simp_tac);
qed_spec_mp "zero_less_binomial";

Goal "(n choose k = 0) = (n<k)";
by (safe_tac (claset() addSIs [binomial_eq_0]));
by (etac contrapos_pp 1);
by (asm_full_simp_tac (simpset() addsimps [zero_less_binomial]) 1); 
qed "binomial_eq_0_iff";

Goal "(0 < n choose k) = (k<=n)";
by (simp_tac (simpset() addsimps [linorder_not_less RS sym, 
                                  binomial_eq_0_iff RS sym]) 1); 
qed "zero_less_binomial_iff";

(*Might be more useful if re-oriented*)
Goal "ALL k. k <= n --> Suc n * (n choose k) = (Suc n choose Suc k) * Suc k";
by (induct_tac "n" 1);
by (simp_tac (simpset() addsimps [binomial_0]) 1);
by (Clarify_tac 1);
by (case_tac "k" 1);
by (auto_tac (claset(),
	      simpset() addsimps [add_mult_distrib, add_mult_distrib2,
				  le_Suc_eq, binomial_eq_0]));
qed_spec_mp "Suc_times_binomial_eq";

(*This is the well-known version, but it's harder to use because of the
  need to reason about division.*)
Goal "k <= n ==> (Suc n choose Suc k) = (Suc n * (n choose k)) div Suc k";
by (asm_simp_tac (simpset()
  addsimps [Suc_times_binomial_eq, div_mult_self_is_m, zero_less_Suc]
  delsimps [mult_Suc, mult_Suc_right]) 1);
qed "binomial_Suc_Suc_eq_times";

(*Another version, with -1 instead of Suc.*)
Goal "[|k <= n;  0<k|] ==> (n choose k) * k = n * ((n - 1) choose (k - 1))";
by (cut_inst_tac [("n","n - 1"),("k","k - 1")] Suc_times_binomial_eq 1);
by (asm_full_simp_tac (simpset() addsplits [nat_diff_split]) 1); 
by Auto_tac;  
qed "times_binomial_minus1_eq";


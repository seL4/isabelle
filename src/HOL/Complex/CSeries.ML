(*  Title       : CSeries.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2002  University of Edinburgh
    Description : Finite summation and infinite series for complex numbers
*)


Goal "sumc (Suc n) n f = 0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumc_Suc_zero";
Addsimps [sumc_Suc_zero];

Goal "sumc m m f = 0";
by (induct_tac "m" 1);
by (Auto_tac);
qed "sumc_eq_bounds";
Addsimps [sumc_eq_bounds];

Goal "sumc m (Suc m) f = f(m)";
by (Auto_tac);
qed "sumc_Suc_eq";
Addsimps [sumc_Suc_eq];

Goal "sumc (m+k) k f = 0";
by (induct_tac "k" 1);
by (Auto_tac);
qed "sumc_add_lbound_zero";
Addsimps [sumc_add_lbound_zero];

Goal "sumc m n f + sumc m n g = sumc m n (%n. f n + g n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps add_ac));
qed "sumc_add";

Goal "r * sumc m n f = sumc m n (%n. r * f n)";
by (induct_tac "n" 1);
by (Auto_tac);
by (auto_tac (claset(),simpset() addsimps 
    [right_distrib]));
qed "sumc_mult";

Goal "n < p --> sumc 0 n f + sumc n p f = sumc 0 p f";
by (induct_tac "p" 1);
by (auto_tac (claset() addSDs [CLAIM "n < Suc na ==> n <= na",
    leI] addDs [le_anti_sym], simpset()));
qed_spec_mp "sumc_split_add";

Goal "n < p ==> sumc 0 p f + \
\                - sumc 0 n f = sumc n p f";
by (dres_inst_tac [("f1","f")] (sumc_split_add RS sym) 1);
by (asm_simp_tac (simpset() addsimps add_ac) 1);
qed "sumc_split_add_minus";

Goal "cmod(sumc m n f) <= sumr m n (%i. cmod(f i))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [complex_mod_triangle_ineq RS order_trans], 
              simpset()));
qed "sumc_cmod";

Goal "!!f g. (ALL r. m <= r & r < n --> f r = g r) \
\                --> sumc m n f = sumc m n g";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "sumc_fun_eq";

Goal "sumc 0 n (%i. r) = complex_of_real (real n) * r";
by (induct_tac "n" 1);
by (auto_tac (claset(),
              simpset() addsimps [left_distrib,
                                  complex_of_real_add RS sym,
                                  real_of_nat_Suc]));
qed "sumc_const";
Addsimps [sumc_const];

Goal "sumc 0 n f + -(complex_of_real(real n) * r) = sumc 0 n (%i. f i + -r)";
by (full_simp_tac (simpset() addsimps [sumc_add RS sym]) 1);
qed "sumc_add_mult_const";

Goalw [complex_diff_def] 
     "sumc 0 n f - (complex_of_real(real n)*r) = sumc 0 n (%i. f i - r)";
by (full_simp_tac (simpset() addsimps [sumc_add_mult_const]) 1);
qed "sumc_diff_mult_const";

Goal "n < m --> sumc m n f = 0";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "sumc_less_bounds_zero";
Addsimps [sumc_less_bounds_zero];

Goal "sumc m n (%i. - f i) = - sumc m n f";
by (induct_tac "n" 1);
by Auto_tac;
qed "sumc_minus";

Goal "sumc (m+k) (n+k) f = sumc m n (%i. f(i + k))";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumc_shift_bounds";

Goal "sumc 0 (2*n) (%i. (-1) ^ Suc i) = 0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumc_minus_one_complexpow_zero";
Addsimps [sumc_minus_one_complexpow_zero];

Goal "(ALL n. m <= Suc n --> f n = r) & m <= na \
\                --> sumc m na f = (complex_of_real(real (na - m)) * r)";
by (induct_tac "na" 1);
by (auto_tac (claset(),simpset() addsimps [left_distrib, Suc_diff_n,
                                      real_of_nat_Suc,complex_of_real_add RS sym,
                                      left_distrib]));
qed_spec_mp "sumc_interval_const";

Goal "(ALL n. m <= n --> f n = r) & m <= na \
\     --> sumc m na f = (complex_of_real(real (na - m)) * r)";
by (induct_tac "na" 1);
by (auto_tac (claset(),simpset() addsimps [left_distrib, Suc_diff_n,
                                      real_of_nat_Suc,complex_of_real_add RS sym,
                                      left_distrib]));
qed_spec_mp "sumc_interval_const2";

(*** 
Goal "(ALL n. m <= n --> 0 <= cmod(f n)) & m < k --> cmod(sumc 0 m f) <= cmod(sumc 0 k f)";
by (induct_tac "k" 1);
by (Step_tac 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [less_Suc_eq_le])));
by (ALLGOALS(dres_inst_tac [("x","n")] spec));
by (Step_tac 1);
by (dtac le_imp_less_or_eq 1 THEN Step_tac 1);
by (dtac add_mono 2);
by (dres_inst_tac [("i","sumr 0 m f")] (order_refl RS add_mono) 1);
by (Auto_tac);
qed_spec_mp "sumc_le";

Goal "!!f g. (ALL r. m <= r & r < n --> f r <= g r) \
\                --> sumc m n f <= sumc m n g";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [add_mono],
    simpset() addsimps [le_def]));
qed_spec_mp "sumc_le2";

Goal "(ALL n. 0 <= f n) --> 0 <= sumc m n f";
by (induct_tac "n" 1);
by Auto_tac;
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
qed_spec_mp "sumc_ge_zero";

Goal "(ALL n. m <= n --> 0 <= f n) --> 0 <= sumc m n f";
by (induct_tac "n" 1);
by Auto_tac;
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
qed_spec_mp "sumc_ge_zero2";
***)

Goal "0 <= sumr m n (%n. cmod (f n))";
by (induct_tac "n" 1);
by Auto_tac;
by (res_inst_tac [("j","0")] real_le_trans 1);
by Auto_tac;
qed "sumr_cmod_ge_zero";
Addsimps [sumr_cmod_ge_zero];
AddSIs [sumr_cmod_ge_zero]; 

Goal "abs (sumr m n (%n. cmod (f n))) = (sumr m n (%n. cmod (f n)))";
by (rtac (abs_eqI1 RS ssubst) 1 THEN Auto_tac);
qed "rabs_sumc_cmod_cancel";
Addsimps [rabs_sumc_cmod_cancel];

Goal "ALL n. N <= n --> f n = 0 \
\     ==> ALL m n. N <= m --> sumc m n f = 0";   
by (Step_tac 1);
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumc_zero";

Goal "ALL n. N <= n --> f (Suc n) = 0 \
\     ==> ALL m n. Suc N <= m --> sumc m n f = 0";   
by (rtac sumc_zero 1 THEN Step_tac 1);
by (dres_inst_tac [("x","n - 1")] spec 1);
by Auto_tac;
by (arith_tac 1);
qed "fun_zero_sumc_zero";

Goal "sumc 1 n (%n. f(n) * 0 ^ n) = 0";
by (induct_tac "n" 1);
by (case_tac "n" 2);
by Auto_tac;
qed "sumc_one_lb_complexpow_zero";
Addsimps [sumc_one_lb_complexpow_zero];

Goalw [complex_diff_def] "sumc m n f - sumc m n g = sumc m n (%n. f n - g n)";
by (simp_tac (simpset() addsimps [sumc_add RS sym,sumc_minus]) 1);
qed "sumc_diff";

Goal "(ALL p. (m <= p & p < m + n --> (f p = g p))) --> sumc m n f = sumc m n g";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "sumc_subst";

Goal "sumc 0 n (%m. sumc (m * k) (m*k + k) f) = sumc 0 (n * k) f";
by (subgoal_tac "k = 0 | 0 < k" 1);
by (Auto_tac);
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [sumc_split_add,add_commute]));
qed "sumc_group";
Addsimps [sumc_group];


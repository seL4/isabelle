(*  Title       : Series.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
                : 1999  University of Edinburgh
    Description : Finite summation and infinite series
*) 

Goal "sumr (Suc n) n f = 0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_Suc_zero";
Addsimps [sumr_Suc_zero];

Goal "sumr m m f = 0";
by (induct_tac "m" 1);
by (Auto_tac);
qed "sumr_eq_bounds";
Addsimps [sumr_eq_bounds];

Goal "sumr m (Suc m) f = f(m)";
by (Auto_tac);
qed "sumr_Suc_eq";
Addsimps [sumr_Suc_eq];

Goal "sumr (m+k) k f = 0";
by (induct_tac "k" 1);
by (Auto_tac);
qed "sumr_add_lbound_zero";
Addsimps [sumr_add_lbound_zero];

Goal "sumr m n f + sumr m n g = sumr m n (%n. f n + g n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps add_ac));
qed "sumr_add";

Goal "r * sumr m n f = sumr m n (%n. r * f n)";
by (induct_tac "n" 1);
by (Auto_tac);
by (auto_tac (claset(),simpset() addsimps 
    [right_distrib]));
qed "sumr_mult";

Goal "n < p --> sumr 0 n f + sumr n p f = sumr 0 p f";
by (induct_tac "p" 1);
by (auto_tac (claset() addSDs [CLAIM "n < Suc na ==> n <= na",
    leI] addDs [le_anti_sym], simpset()));
qed_spec_mp "sumr_split_add";

Goal "n < p ==> sumr 0 p f + \
\                - sumr 0 n f = sumr n p f";
by (dres_inst_tac [("f1","f")] (sumr_split_add RS sym) 1);
by (asm_simp_tac (simpset() addsimps add_ac) 1);
qed "sumr_split_add_minus";

Goal "0 < n --> n < p --> sumr (Suc 0) n f + sumr n p f = sumr (Suc 0) p f";
by (induct_tac "p" 1);
by (auto_tac (claset() addSDs [CLAIM "[| m < Suc n; n <= m |] ==> m = n"],
    simpset()));
qed_spec_mp "sumr_split_add2";

Goal "[| 0<n; n <= p |] ==> sumr (Suc 0) n f + sumr n p f = sumr (Suc 0) p f";
by (dtac le_imp_less_or_eq 1 THEN Auto_tac);
by (blast_tac (claset() addIs [sumr_split_add2]) 1);
qed "sumr_split_add3";

Goal "abs(sumr m n f) <= sumr m n (%i. abs(f i))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [abs_triangle_ineq RS order_trans,
                              add_right_mono], 
              simpset()));
qed "sumr_rabs";

Goal "!!f g. (ALL r. m <= r & r < n --> f r = g r) \
\                --> sumr m n f = sumr m n g";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "sumr_fun_eq";

Goal "sumr 0 n (%i. r) = real n * r";
by (induct_tac "n" 1);
by (auto_tac (claset(),
              simpset() addsimps [left_distrib,real_of_nat_zero,
                                  real_of_nat_Suc]));
qed "sumr_const";
Addsimps [sumr_const];

Goal "sumr 0 n f + -(real n * r) = sumr 0 n (%i. f i + -r)";
by (full_simp_tac (HOL_ss addsimps [sumr_add RS sym, minus_mult_right]) 1);
by (Simp_tac 1);
qed "sumr_add_mult_const";

Goalw [real_diff_def] 
     "sumr 0 n f - (real n*r) = sumr 0 n (%i. f i - r)";
by (full_simp_tac (simpset() addsimps [sumr_add_mult_const]) 1);
qed "sumr_diff_mult_const";

Goal "n < m --> sumr m n f = 0";
by (induct_tac "n" 1);
by (auto_tac (claset() addDs [less_imp_le], simpset()));
qed_spec_mp "sumr_less_bounds_zero";
Addsimps [sumr_less_bounds_zero];

Goal "sumr m n (%i. - f i) = - sumr m n f";
by (induct_tac "n" 1);
by (case_tac "Suc n <= m" 2);
by (auto_tac (claset(),simpset() addsimps [minus_add_distrib]));
qed "sumr_minus";

Goal "sumr (m+k) (n+k) f = sumr m n (%i. f(i + k))";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_shift_bounds";

Goal "sumr 0 (2*n) (%i. (-1) ^ Suc i) = 0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_minus_one_realpow_zero";
Addsimps [sumr_minus_one_realpow_zero];

Goal "m < Suc n ==> Suc n - m = Suc (n - m)";
by (dtac less_imp_Suc_add 1);
by (Auto_tac);
val Suc_diff_n = result();

Goal "(ALL n. m <= Suc n --> f n = r) & m <= na \
\                --> sumr m na f = (real (na - m) * r)";
by (induct_tac "na" 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [le_Suc_eq])  2);
by (Step_tac 1);
by (dres_inst_tac [("x","n")] spec 3);
by (auto_tac (claset() addSDs [le_imp_less_or_eq], simpset()));
by (asm_simp_tac (simpset() addsimps [left_distrib, Suc_diff_n,
                                      real_of_nat_Suc]) 1);
qed_spec_mp "sumr_interval_const";

Goal "(ALL n. m <= n --> f n = r) & m <= na \
\     --> sumr m na f = (real (na - m) * r)";
by (induct_tac "na" 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [le_Suc_eq])  2);
by (Step_tac 1);
by (dres_inst_tac [("x","n")] spec 3);
by (auto_tac (claset() addSDs [le_imp_less_or_eq],
    simpset()));
by (asm_simp_tac (simpset() addsimps [Suc_diff_n, left_distrib,
                                      real_of_nat_Suc]) 1);
qed_spec_mp "sumr_interval_const2";

Goal "(ALL n. m <= n --> 0 <= f n) & m < k --> sumr 0 m f <= sumr 0 k f";
by (induct_tac "k" 1);
by (Step_tac 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps [less_Suc_eq_le])));
by (ALLGOALS(dres_inst_tac [("x","n")] spec));
by (Step_tac 1);
by (dtac le_imp_less_or_eq 1 THEN Step_tac 1);
by (dres_inst_tac [("a","sumr 0 m f")] add_mono 2);
by (dres_inst_tac [("a","sumr 0 m f")] (order_refl RS add_mono) 1);
by (Auto_tac);
qed_spec_mp "sumr_le";

Goal "!!f g. (ALL r. m <= r & r < n --> f r <= g r) \
\                --> sumr m n f <= sumr m n g";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [add_mono],
    simpset() addsimps [le_def]));
qed_spec_mp "sumr_le2";

Goal "(ALL n. 0 <= f n) --> 0 <= sumr m n f";
by (induct_tac "n" 1);
by Auto_tac;
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
qed_spec_mp "sumr_ge_zero";

Goal "(ALL n. m <= n --> 0 <= f n) --> 0 <= sumr m n f";
by (induct_tac "n" 1);
by Auto_tac;
by (dres_inst_tac [("x","n")] spec 1);
by (arith_tac 1);
qed_spec_mp "sumr_ge_zero2";

Goal "0 <= sumr m n (%n. abs (f n))";
by (induct_tac "n" 1);
by Auto_tac;
by (arith_tac 1);
qed "sumr_rabs_ge_zero";
Addsimps [sumr_rabs_ge_zero];
AddSIs [sumr_rabs_ge_zero]; 

Goal "abs (sumr m n (%n. abs (f n))) = (sumr m n (%n. abs (f n)))";
by (induct_tac "n" 1);
by (Auto_tac THEN arith_tac 1);
qed "rabs_sumr_rabs_cancel";
Addsimps [rabs_sumr_rabs_cancel];

Goal "ALL n. N <= n --> f n = 0 \
\     ==> ALL m n. N <= m --> sumr m n f = 0";   
by (Step_tac 1);
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_zero";

Goal "ALL n. N <= n --> f (Suc n) = 0 \
\     ==> ALL m n. Suc N <= m --> sumr m n f = 0";   
by (rtac sumr_zero 1 THEN Step_tac 1);
by (case_tac "n" 1);
by Auto_tac; 
qed "Suc_le_imp_diff_ge2";

Goal "sumr (Suc 0) n (%n. f(n) * 0 ^ n) = 0";
by (induct_tac "n" 1);
by (case_tac "n" 2);
by Auto_tac; 
qed "sumr_one_lb_realpow_zero";
Addsimps [sumr_one_lb_realpow_zero];

Goalw [real_diff_def] "sumr m n f - sumr m n g = sumr m n (%n. f n - g n)";
by (simp_tac (simpset() addsimps [sumr_add RS sym,sumr_minus]) 1);
qed "sumr_diff";

Goal "(ALL p. m <= p & p < m+n --> (f p = g p)) --> sumr m n f = sumr m n g";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "sumr_subst";

Goal "(ALL p. m <= p & p < m + n --> (f(p) <= K)) \
\     --> (sumr m (m + n) f <= (real n * K))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [add_mono],
              simpset() addsimps [left_distrib, real_of_nat_Suc]));
qed_spec_mp "sumr_bound";

Goal "(ALL p. 0 <= p & p < n --> (f(p) <= K)) \
\     --> (sumr 0 n f <= (real n * K))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [add_mono],
        simpset() addsimps [left_distrib, real_of_nat_Suc]));
qed_spec_mp "sumr_bound2";

Goal "sumr 0 n (%m. sumr (m * k) (m*k + k) f) = sumr 0 (n * k) f";
by (subgoal_tac "k = 0 | 0 < k" 1);
by (Auto_tac);
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [sumr_split_add,add_commute]));
qed "sumr_group";
Addsimps [sumr_group];

(*-------------------------------------------------------------------
                        Infinite sums
    Theorems follow from properties of limits and sums
 -------------------------------------------------------------------*)
(*----------------------
   suminf is the sum   
 ---------------------*)
Goalw [sums_def,summable_def] 
      "f sums l ==> summable f";
by (Blast_tac 1);
qed "sums_summable";

Goalw [summable_def,suminf_def]
     "summable f ==> f sums (suminf f)";
by (blast_tac (claset() addIs [someI2]) 1);
qed "summable_sums";

Goalw [summable_def,suminf_def,sums_def]
     "summable f ==> (%n. sumr 0 n f) ----> (suminf f)";
by (blast_tac (claset() addIs [someI2]) 1);
qed "summable_sumr_LIMSEQ_suminf";

(*-------------------
    sum is unique                    
 ------------------*)
Goal "f sums s ==> (s = suminf f)";
by (forward_tac [sums_summable RS summable_sums] 1);
by (auto_tac (claset() addSIs [LIMSEQ_unique],
    simpset() addsimps [sums_def]));
qed "sums_unique";

(*
Goalw [sums_def,LIMSEQ_def] 
     "(ALL m. n <= Suc m --> f(m) = 0) ==> f sums (sumr 0 n f)";
by (Step_tac 1);
by (res_inst_tac [("x","n")] exI 1);
by (Step_tac 1 THEN ftac le_imp_less_or_eq 1);
by (Step_tac 1);
by (dres_inst_tac [("f","f")] sumr_split_add_minus 1);
by (ALLGOALS (Asm_simp_tac));
by (dtac (conjI RS sumr_interval_const) 1);
by (Auto_tac);
qed "series_zero";
next one was called series_zero2
**********************)

Goalw [sums_def,LIMSEQ_def] 
     "(ALL m. n <= m --> f(m) = 0) ==> f sums (sumr 0 n f)";
by (Step_tac 1);
by (res_inst_tac [("x","n")] exI 1);
by (Step_tac 1 THEN ftac le_imp_less_or_eq 1);
by (Step_tac 1);
by (dres_inst_tac [("f","f")] sumr_split_add_minus 1);
by (ALLGOALS (Asm_simp_tac));
by (dtac (conjI RS sumr_interval_const2) 1);
by (Auto_tac);
qed "series_zero";

Goalw [sums_def] "x sums x0 ==> (%n. c * x(n)) sums (c * x0)";
by (auto_tac (claset() addSIs [LIMSEQ_mult] addIs [LIMSEQ_const], 
              simpset() addsimps [sumr_mult RS sym]));
qed "sums_mult";

Goal "x sums x' ==> (%n. x(n)/c) sums (x'/c)";
by (asm_simp_tac (simpset() addsimps [real_divide_def, sums_mult,
                              inst "w" "inverse c" real_mult_commute]) 1); 
qed "sums_divide";

Goalw [sums_def] "[| x sums x0; y sums y0 |] ==> (%n. x n - y n) sums (x0-y0)";
by (auto_tac (claset() addIs [LIMSEQ_diff],
              simpset() addsimps [sumr_diff RS sym]));
qed "sums_diff";

Goal "summable f ==> suminf f * c = suminf(%n. f n * c)";
by (auto_tac (claset() addSIs [sums_unique,sums_mult,summable_sums],
    simpset() addsimps [real_mult_commute]));
qed "suminf_mult";

Goal "summable f ==> c * suminf f  = suminf(%n. c * f n)";
by (auto_tac (claset() addSIs [sums_unique,sums_mult,summable_sums],
    simpset()));
qed "suminf_mult2";

Goal "[| summable f; summable g |]  \
\     ==> suminf f - suminf g  = suminf(%n. f n - g n)";
by (auto_tac (claset() addSIs [sums_diff,sums_unique,summable_sums], simpset()));
qed "suminf_diff";

Goalw [sums_def] 
       "x sums x0 ==> (%n. - x n) sums - x0";
by (auto_tac (claset() addSIs [LIMSEQ_minus], simpset() addsimps [sumr_minus]));
qed "sums_minus";

Goal "[|summable f; 0 < k |] \
\     ==> (%n. sumr (n*k) (n*k + k) f) sums (suminf f)";
by (dtac summable_sums 1);
by (auto_tac (claset(),simpset() addsimps [sums_def,LIMSEQ_def]));
by (dres_inst_tac [("x","r")] spec 1 THEN Step_tac 1); 
by (res_inst_tac [("x","no")] exI 1 THEN Step_tac 1); 
by (dres_inst_tac [("x","n*k")] spec 1); 
by (auto_tac (claset() addSDs [not_leE], simpset()));
by (dres_inst_tac [("j","no")] less_le_trans 1);
by (Auto_tac);
qed "sums_group";

Goal "[|summable f; ALL d. 0 < (f(n + (Suc (Suc 0) * d))) + f(n + ((Suc (Suc 0) * d) + 1))|] \
\     ==> sumr 0 n f < suminf f";
by (dtac summable_sums 1);
by (auto_tac (claset(),simpset() addsimps [sums_def,LIMSEQ_def]));
by (dres_inst_tac [("x","f(n) + f(n + 1)")] spec 1);
by (Auto_tac);
by (rtac ccontr 2 THEN dtac (linorder_not_less RS iffD1) 2);
by (subgoal_tac "sumr 0 (n + Suc (Suc 0)) f <= sumr 0 (Suc (Suc 0) * (Suc no) + n) f" 2);
by (induct_tac "no" 3 THEN Simp_tac 3);
by (res_inst_tac [("y","sumr 0 (Suc (Suc 0)*(Suc na)+n) f")] order_trans 3);
by (assume_tac 3);
by (dres_inst_tac [("x","Suc na")] spec 3);
by (dres_inst_tac [("x","0")] spec 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps add_ac) 2);
by (rotate_tac 1 1 THEN dres_inst_tac [("x","Suc (Suc 0) * (Suc no) + n")] spec 1);
by (Step_tac 1 THEN Asm_full_simp_tac 1);
by (subgoal_tac "suminf f + (f(n) + f(n + 1)) <= \
\                 sumr 0 (Suc (Suc 0) * (Suc no) + n) f" 1);
by (res_inst_tac [("y","sumr 0 (n+ Suc (Suc 0)) f")] order_trans 2);
by (assume_tac 3);
by (res_inst_tac [("y","sumr 0 n f + (f(n) + f(n + 1))")] order_trans 2);
by (REPEAT(Asm_simp_tac 2));
by (subgoal_tac "suminf f <= sumr 0 (Suc (Suc 0) * (Suc no) + n) f" 1);
by (res_inst_tac [("y","suminf f + (f(n) + f(n + 1))")] order_trans 2);
by (assume_tac 3);
by (dres_inst_tac [("x","0")] spec 2);
by (Asm_full_simp_tac 2);
by (subgoal_tac "0 <= sumr 0 (Suc (Suc 0) * Suc no + n) f + - suminf f" 1);
by (dtac (abs_eqI1) 1 );
by (Asm_full_simp_tac 1);
by (auto_tac (claset(),simpset() addsimps [real_le_def]));
qed "sumr_pos_lt_pair";

(*-----------------------------------------------------------------
   Summable series of positive terms has limit >= any partial sum 
 ----------------------------------------------------------------*)
Goal 
     "[| summable f; ALL m. n <= m --> 0 <= f(m) |] \
\          ==> sumr 0 n f <= suminf f";
by (dtac summable_sums 1);
by (rewtac sums_def);
by (cut_inst_tac [("k","sumr 0 n f")] LIMSEQ_const 1);
by (etac LIMSEQ_le 1 THEN Step_tac 1);
by (res_inst_tac [("x","n")] exI 1 THEN Step_tac 1);
by (dtac le_imp_less_or_eq 1 THEN Step_tac 1);
by (auto_tac (claset() addIs [sumr_le], simpset()));
qed "series_pos_le";

Goal "[| summable f; ALL m. n <= m --> 0 < f(m) |] \
\          ==> sumr 0 n f < suminf f";
by (res_inst_tac [("y","sumr 0 (Suc n) f")] order_less_le_trans 1);
by (rtac series_pos_le 2);
by (Auto_tac);
by (dres_inst_tac [("x","m")] spec 1);
by (Auto_tac);
qed "series_pos_less";

(*-------------------------------------------------------------------
                    sum of geometric progression                 
 -------------------------------------------------------------------*)

Goal "x ~= 1 ==> sumr 0 n (%n. x ^ n) = (x ^ n - 1) / (x - 1)";
by (induct_tac "n" 1);
by (Auto_tac);
by (res_inst_tac [("c1","x - 1")] (real_mult_right_cancel RS iffD1) 1);
by (auto_tac (claset(),
       simpset() addsimps [real_mult_assoc, left_distrib]));
by (auto_tac (claset(),
       simpset() addsimps [right_distrib,
                           real_diff_def, real_mult_commute]));
qed "sumr_geometric";

Goal "abs(x) < 1 ==> (%n. x ^ n) sums (1/(1 - x))";
by (case_tac "x = 1" 1);
by (auto_tac (claset() addSDs [LIMSEQ_rabs_realpow_zero2],
             simpset() addsimps [sumr_geometric ,sums_def,
                                 real_diff_def, add_divide_distrib]));
by (subgoal_tac "1 / (1 + -x) = 0/(x - 1) + - 1/(x - 1)" 1); 
by (asm_full_simp_tac (simpset() addsimps [thm"minus_divide_right"]) 2); 
by (etac ssubst 1); 
by (rtac LIMSEQ_add 1 THEN rtac LIMSEQ_divide 1);
by (auto_tac (claset() addIs [LIMSEQ_const], 
              simpset() addsimps [real_diff_def, LIMSEQ_rabs_realpow_zero2]));
qed "geometric_sums";

(*-------------------------------------------------------------------
    Cauchy-type criterion for convergence of series (c.f. Harrison)
 -------------------------------------------------------------------*)
Goalw [summable_def,sums_def,convergent_def]
      "summable f = convergent (%n. sumr 0 n f)";
by (Auto_tac);
qed "summable_convergent_sumr_iff";

Goal "summable f = \
\     (ALL e. 0 < e --> (EX N. ALL m n. N <= m --> abs(sumr m n f) < e))";
by (auto_tac (claset(),simpset() addsimps [summable_convergent_sumr_iff,
    Cauchy_convergent_iff RS sym,Cauchy_def]));
by (ALLGOALS(dtac spec) THEN Auto_tac);
by (res_inst_tac [("x","M")] exI 1);
by (res_inst_tac [("x","N")] exI 2);
by (Auto_tac);
by (ALLGOALS(cut_inst_tac [("m","m"),("n","n")] less_linear));
by (Auto_tac);
by (ftac (le_less_trans RS less_imp_le) 1 THEN assume_tac 1);
by (dres_inst_tac [("x","n")] spec 1);
by (dres_inst_tac [("x","m")] spec 1);
by (auto_tac (claset() addIs [(abs_minus_add_cancel RS subst)],
    simpset() addsimps [sumr_split_add_minus,abs_minus_add_cancel]));
qed "summable_Cauchy";

(*-------------------------------------------------------------------
     Terms of a convergent series tend to zero
     > Goalw [LIMSEQ_def] "summable f ==> f ----> 0";
     Proved easily in HSeries after proving nonstandard case.
 -------------------------------------------------------------------*)
(*-------------------------------------------------------------------
                    Comparison test
 -------------------------------------------------------------------*)
Goal "[| EX N. ALL n. N <= n --> abs(f n) <= g n; \
\        summable g \
\     |] ==> summable f";
by (auto_tac (claset(),simpset() addsimps [summable_Cauchy]));
by (dtac spec 1 THEN Auto_tac);
by (res_inst_tac [("x","N + Na")] exI 1 THEN Auto_tac);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","m")] spec 1);
by (Auto_tac THEN rotate_tac 2 1 THEN dres_inst_tac [("x","n")] spec 1);
by (res_inst_tac [("y","sumr m n (%k. abs(f k))")] order_le_less_trans 1);
by (rtac sumr_rabs 1);
by (res_inst_tac [("y","sumr m n g")] order_le_less_trans 1);
by (auto_tac (claset() addIs [sumr_le2],
    simpset() addsimps [abs_interval_iff]));
qed "summable_comparison_test";

Goal "[| EX N. ALL n. N <= n --> abs(f n) <= g n; \
\        summable g \
\     |] ==> summable (%k. abs (f k))";
by (rtac summable_comparison_test 1);
by (auto_tac (claset(),simpset() addsimps [abs_idempotent]));
qed "summable_rabs_comparison_test";

(*------------------------------------------------------------------*)
(*       Limit comparison property for series (c.f. jrh)            *)
(*------------------------------------------------------------------*)
Goal "[|ALL n. f n <= g n; summable f; summable g |] \
\     ==> suminf f <= suminf g";
by (REPEAT(dtac summable_sums 1));
by (auto_tac (claset() addSIs [LIMSEQ_le], simpset() addsimps [sums_def]));
by (rtac exI 1);
by (auto_tac (claset() addSIs [sumr_le2], simpset()));
qed "summable_le";

Goal "[|ALL n. abs(f n) <= g n; summable g |] \
\     ==> summable f & suminf f <= suminf g";
by (auto_tac (claset() addIs [summable_comparison_test]
    addSIs [summable_le], simpset()));
by (auto_tac (claset(),simpset() addsimps [abs_le_interval_iff]));
qed "summable_le2";

(*-------------------------------------------------------------------
         Absolute convergence imples normal convergence
 -------------------------------------------------------------------*)
Goal "summable (%n. abs (f n)) ==> summable f";
by (auto_tac (claset(),simpset() addsimps [sumr_rabs,summable_Cauchy]));
by (dtac spec 1 THEN Auto_tac);
by (res_inst_tac [("x","N")] exI 1 THEN Auto_tac);
by (dtac spec 1 THEN Auto_tac);
by (res_inst_tac [("y","sumr m n (%n. abs(f n))")] order_le_less_trans 1);
by (auto_tac (claset() addIs [sumr_rabs], simpset()));
qed "summable_rabs_cancel";

(*-------------------------------------------------------------------
         Absolute convergence of series
 -------------------------------------------------------------------*)
Goal "summable (%n. abs (f n)) ==> abs(suminf f) <= suminf (%n. abs(f n))";
by (auto_tac (claset() addIs [LIMSEQ_le,LIMSEQ_imp_rabs,summable_rabs_cancel,
                              summable_sumr_LIMSEQ_suminf,sumr_rabs], 
              simpset()));
qed "summable_rabs";

(*-------------------------------------------------------------------
                        The ratio test
 -------------------------------------------------------------------*)

Goal "[| c <= 0; abs x <= c * abs y |] ==> x = (0::real)";
by (dtac order_le_imp_less_or_eq 1);
by Auto_tac;  
by (subgoal_tac "0 <= c * abs y" 1);
by (arith_tac 2);
by (asm_full_simp_tac (simpset() addsimps [zero_le_mult_iff]) 1); 
qed "rabs_ratiotest_lemma";

(* lemmas *)

Goal "(k::nat) <= l ==> (EX n. l = k + n)";
by (dtac le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [less_imp_Suc_add], simpset()));
qed "le_Suc_ex";

Goal "((k::nat) <= l) = (EX n. l = k + n)";
by (auto_tac (claset(),simpset() addsimps [le_Suc_ex]));
qed "le_Suc_ex_iff";

(*All this trouble just to get 0<c *)
Goal "[| ALL n. N <= n --> abs(f(Suc n)) <= c*abs(f n) |] \
\     ==> 0 < c | summable f";
by (simp_tac (simpset() addsimps [linorder_not_le RS sym]) 1); 
by (asm_full_simp_tac (simpset() addsimps [summable_Cauchy]) 1);
by (Step_tac 1 THEN subgoal_tac "ALL n. N <= n --> f (Suc n) = 0" 1);
by (blast_tac (claset() addIs [rabs_ratiotest_lemma]) 2);
by (res_inst_tac [("x","Suc N")] exI 1);
by (Clarify_tac 1); 
by (dtac Suc_le_imp_diff_ge2 1 THEN Auto_tac);
qed "ratio_test_lemma2";

Goal "[| c < 1; ALL n. N <= n --> abs(f(Suc n)) <= c*abs(f n) |] \
\     ==> summable f";
by (ftac ratio_test_lemma2 1);
by Auto_tac;  
by (res_inst_tac [("g","%n. (abs (f N)/(c ^ N))*c ^ n")] 
    summable_comparison_test 1);
by (res_inst_tac [("x","N")] exI 1 THEN Step_tac 1);
by (dtac (le_Suc_ex_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [realpow_add, realpow_not_zero]));
by (induct_tac "na" 1 THEN Auto_tac);
by (res_inst_tac [("y","c*abs(f(N + n))")] order_trans 1);
by (auto_tac (claset() addIs [mult_right_mono],
              simpset() addsimps [summable_def]));
by (asm_full_simp_tac (simpset() addsimps mult_ac) 1);
by (res_inst_tac [("x","abs(f N) * (1/(1 - c)) / (c ^ N)")] exI 1);
by (rtac sums_divide 1); 
by (rtac sums_mult 1); 
by (auto_tac (claset() addSIs [sums_mult,geometric_sums], 
              simpset() addsimps [real_abs_def]));
qed "ratio_test";


(*--------------------------------------------------------------------------*)
(* Differentiation of finite sum                                            *)
(*--------------------------------------------------------------------------*)

Goal "(ALL r. m <= r & r < (m + n) --> DERIV (%x. f r x) x :> (f' r x)) \
\     --> DERIV (%x. sumr m n (%n. f n x)) x :> sumr m n (%r. f' r x)";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [DERIV_add], simpset()));
qed_spec_mp "DERIV_sumr";

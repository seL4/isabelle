(*  Title       : Series.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
                : 1999  University of Edinburgh
    Description : Finite summation and infinite series
*) 

Goal "sumr (Suc n) n f = #0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_Suc_zero";
Addsimps [sumr_Suc_zero];

Goal "sumr m m f = #0";
by (induct_tac "m" 1);
by (Auto_tac);
qed "sumr_eq_bounds";
Addsimps [sumr_eq_bounds];

Goal "sumr m (Suc m) f = f(m)";
by (Auto_tac);
qed "sumr_Suc_eq";
Addsimps [sumr_Suc_eq];

Goal "sumr (m+k) k f = #0";
by (induct_tac "k" 1);
by (Auto_tac);
qed "sumr_add_lbound_zero";
Addsimps [sumr_add_lbound_zero];

Goal "sumr m n f + sumr m n g = sumr m n (%n. f n + g n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps real_add_ac));
qed "sumr_add";

Goal "r * sumr m n f = sumr m n (%n. r * f n)";
by (induct_tac "n" 1);
by (Auto_tac);
by (auto_tac (claset(),simpset() addsimps 
    [real_add_mult_distrib2]));
qed "sumr_mult";

Goal "n < p --> sumr 0 n f + sumr n p f = sumr 0 p f";
by (induct_tac "p" 1);
by (auto_tac (claset() addSDs [CLAIM "n < Suc na ==> n <= na",
    leI] addDs [le_anti_sym], simpset()));
qed_spec_mp "sumr_split_add";

Goal "!!n. n < p ==> sumr 0 p f + \
\                - sumr 0 n f = sumr n p f";
by (dres_inst_tac [("f1","f")] (sumr_split_add RS sym) 1);
by (asm_simp_tac (simpset() addsimps real_add_ac) 1);
qed "sumr_split_add_minus";

Goal "abs(sumr m n f) <= sumr m n (%i. abs(f i))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [(abs_triangle_ineq 
    RS real_le_trans),real_add_le_mono1], simpset()));
qed "sumr_rabs";

Goal "!!f g. (ALL r. m <= r & r < n --> f r = g r) \
\                --> sumr m n f = sumr m n g";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "sumr_fun_eq";

Goal "sumr 0 n (%i. r) = real_of_nat n*r";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [real_add_mult_distrib,real_of_nat_zero]));
qed "sumr_const";
Addsimps [sumr_const];

Goal "sumr 0 n f + -(real_of_nat n*r) = sumr 0 n (%i. f i + -r)";
by (full_simp_tac (simpset() addsimps [sumr_add RS sym,
    real_minus_mult_eq2] delsimps [real_minus_mult_eq2 RS sym]) 1);
qed "sumr_add_mult_const";

goalw Series.thy [real_diff_def] 
     "sumr 0 n f - (real_of_nat n*r) = sumr 0 n (%i. f i - r)";
by (full_simp_tac (simpset() addsimps [sumr_add_mult_const]) 1);
qed "sumr_diff_mult_const";

Goal "n < m --> sumr m n f = #0";
by (induct_tac "n" 1);
by (auto_tac (claset() addDs [less_imp_le], simpset()));
qed_spec_mp "sumr_less_bounds_zero";
Addsimps [sumr_less_bounds_zero];

Goal "sumr m n (%i. - f i) = - sumr m n f";
by (induct_tac "n" 1);
by (case_tac "Suc n <= m" 2);
by (auto_tac (claset(),simpset() addsimps 
    [real_minus_add_distrib]));
qed "sumr_minus";

context NatArith.thy;

Goal "!!n. ~ Suc n <= m + k ==> ~ Suc n <= m";
by (auto_tac (claset() addSDs [not_leE], simpset()));
qed "lemma_not_Suc_add";

context thy;

Goal "sumr (m+k) (n+k) f = sumr m n (%i. f(i + k))";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_shift_bounds";

Goal "sumr 0 (n + n) (%i. (- #1) ^ Suc i) = #0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_minus_one_realpow_zero";
Addsimps [sumr_minus_one_realpow_zero];

Goal "sumr 0 (n + n) (%i. (#-1) ^ Suc i) = #0";
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_minus_one_realpow_zero2";
Addsimps [sumr_minus_one_realpow_zero2];

Goal "m < Suc n ==> Suc n - m = Suc (n - m)";
by (dtac less_imp_Suc_add 1);
by (Auto_tac);
val Suc_diff_n = result();

Goal "(ALL n. m <= Suc n --> f n = r) & m <= na \
\                --> sumr m na f = (real_of_nat (na - m) * r)";
by (induct_tac "na" 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [le_Suc_eq])  2);
by (Step_tac 1);
by (dres_inst_tac [("x","n")] spec 3);
by (auto_tac (claset() addSDs [le_imp_less_or_eq],
    simpset()));
by (asm_simp_tac (simpset() addsimps [real_add_mult_distrib,
    Suc_diff_n]) 1);
qed_spec_mp "sumr_interval_const";

Goal "(ALL n. m <= n --> f n = r) & m <= na \
\     --> sumr m na f = (real_of_nat (na - m) * r)";
by (induct_tac "na" 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [le_Suc_eq])  2);
by (Step_tac 1);
by (dres_inst_tac [("x","n")] spec 3);
by (auto_tac (claset() addSDs [le_imp_less_or_eq],
    simpset()));
by (asm_simp_tac (simpset() addsimps [Suc_diff_n,
    real_add_mult_distrib]) 1);
qed_spec_mp "sumr_interval_const2";

Goal "(m <= n)= (m < Suc n)";
by (Auto_tac);
qed "le_eq_less_Suc";

Goal "(ALL n. m <= n --> #0 <= f n) & m < na \
\                --> sumr 0 m f <= sumr 0 na f";
by (induct_tac "na" 1);
by (Step_tac 1);
by (ALLGOALS(asm_full_simp_tac (simpset() addsimps 
    [le_eq_less_Suc RS sym])));
by (ALLGOALS(dres_inst_tac [("x","n")] spec));
by (Step_tac 1);
by (dtac le_imp_less_or_eq 1 THEN Step_tac 1);
by (dtac real_add_le_mono 2);
by (dres_inst_tac [("i","sumr 0 m f")] 
    (real_le_refl RS real_add_le_mono) 1);
by (Auto_tac);
qed_spec_mp "sumr_le";

Goal "!!f g. (ALL r. m <= r & r < n --> f r <= g r) \
\                --> sumr m n f <= sumr m n g";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_add_le_mono],
    simpset() addsimps [le_def]));
qed_spec_mp "sumr_le2";

Goal "(ALL n. #0 <= f n) --> #0 <= sumr m n f";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [rename_numerals real_le_add_order]));
qed_spec_mp "sumr_ge_zero";

Goal "(ALL n. m <= n --> #0 <= f n) --> #0 <= sumr m n f";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [rename_numerals real_le_add_order] 
    addDs [leI], simpset()));
qed_spec_mp "sumr_ge_zero2";

Goal "#0 <= sumr m n (%n. abs (f n))";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [rename_numerals real_le_add_order,
    abs_ge_zero], simpset()));
qed "sumr_rabs_ge_zero";
Addsimps [sumr_rabs_ge_zero];
AddSIs [sumr_rabs_ge_zero]; 

Goal "abs (sumr m n (%n. abs (f n))) = (sumr m n (%n. abs (f n)))";
by (induct_tac "n" 1);
by (Auto_tac THEN arith_tac 1);
qed "rabs_sumr_rabs_cancel";
Addsimps [rabs_sumr_rabs_cancel];

Goal "ALL n. N <= n --> f n = #0 \
\     ==> ALL m n. N <= m --> sumr m n f = #0";   
by (Step_tac 1);
by (induct_tac "n" 1);
by (Auto_tac);
qed "sumr_zero";

Goal "Suc N <= n --> N <= n - 1";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "Suc_le_imp_diff_ge";

Goal "ALL n. N <= n --> f (Suc n) = #0 \
\     ==> ALL m n. Suc N <= m --> sumr m n f = #0";   
by (rtac sumr_zero 1 THEN Step_tac 1);
by (subgoal_tac "0 < n" 1);
by (dtac Suc_le_imp_diff_ge 1);
by (Auto_tac);
qed "Suc_le_imp_diff_ge2";

(* proved elsewhere? *)
Goal "(0 < n) = (EX m. n = Suc m)";
by (induct_tac "n" 1);
by (Auto_tac);
qed "gt_zero_eq_Ex";

Goal "sumr 1 n (%n. f(n) * #0 ^ n) = #0";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [gt_zero_eq_Ex]));
qed "sumr_one_lb_realpow_zero";
Addsimps [sumr_one_lb_realpow_zero];

Goalw [real_diff_def] "sumr m n f - sumr m n g = sumr m n (%n. f n - g n)";
by (simp_tac (simpset() addsimps [sumr_add RS sym,sumr_minus]) 1);
qed "sumr_diff";

Goal "(ALL p. (m <= p & p < m + n --> (f p = g p))) --> sumr m n f = sumr m n g";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "sumr_subst";

Goal "(ALL p. m <= p & p < m + n --> (f(p) <= K)) \
\     --> (sumr m (m + n) f <= (real_of_nat n * K))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_add_le_mono],
    simpset() addsimps [real_add_mult_distrib]));
qed_spec_mp "sumr_bound";

Goal "(ALL p. 0 <= p & p < n --> (f(p) <= K)) \
\     --> (sumr 0 n f <= (real_of_nat n * K))";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_add_le_mono],
    simpset() addsimps [real_add_mult_distrib]));
qed_spec_mp "sumr_bound2";

Goal "sumr 0 n (%m. sumr (m * k) (m*k + k) f) = sumr 0 (n * k) f";
by (subgoal_tac "k = 0 | 0 < k" 1);
by (Auto_tac);
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [sumr_split_add,add_commute]));
qed "sumr_group";
Addsimps [sumr_group];

Goal "0 < (k::nat) --> ~(n*k < n)";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "lemma_summable_group";
Addsimps [lemma_summable_group];

(*-------------------------------------------------------------------
                        Infinite sums
    Theorems follow from properties of limits and sums
 -------------------------------------------------------------------*)
(*----------------------
   suminf is the sum   
 ---------------------*)
Goalw [sums_def,summable_def] 
      "!!f. f sums l ==> summable f";
by (Blast_tac 1);
qed "sums_summable";

Goalw [summable_def,suminf_def]
     "!!f. summable f ==> f sums (suminf f)";
by (blast_tac (claset() addIs [someI2]) 1);
qed "summable_sums";

Goalw [summable_def,suminf_def,sums_def]
     "!!f. summable f ==> (%n. sumr 0 n f) ----> (suminf f)";
by (blast_tac (claset() addIs [someI2]) 1);
qed "summable_sumr_LIMSEQ_suminf";

(*-------------------
    sum is unique                    
 ------------------*)
Goal "!!f. f sums s ==> (s = suminf f)";
by (forward_tac [sums_summable RS summable_sums] 1);
by (auto_tac (claset() addSIs [LIMSEQ_unique],
    simpset() addsimps [sums_def]));
qed "sums_unique";

Goalw [sums_def,LIMSEQ_def] 
     "!!f. ALL m. n <= Suc m --> f(m) = #0 \
\                ==> f sums (sumr 0 n f)";
by (Step_tac 1);
by (res_inst_tac [("x","n")] exI 1);
by (Step_tac 1 THEN forward_tac [le_imp_less_or_eq] 1);
by (Step_tac 1);
by (dres_inst_tac [("f","f")] sumr_split_add_minus 1);
by (ALLGOALS (Asm_simp_tac));
by (dtac (conjI RS sumr_interval_const) 1);
by (Auto_tac);
qed "series_zero";

goalw Series.thy [sums_def,LIMSEQ_def] 
     "!!f. ALL m. n <= m --> f(m) = #0 \
\                ==> f sums (sumr 0 n f)";
by (Step_tac 1);
by (res_inst_tac [("x","n")] exI 1);
by (Step_tac 1 THEN forward_tac [le_imp_less_or_eq] 1);
by (Step_tac 1);
by (dres_inst_tac [("f","f")] sumr_split_add_minus 1);
by (ALLGOALS (Asm_simp_tac));
by (dtac (conjI RS sumr_interval_const2) 1);
by (Auto_tac);
qed "series_zero2";

Goalw [sums_def] "x sums x0 ==> (%n. c * x(n)) sums (c * x0)";
by (auto_tac (claset() addSIs [LIMSEQ_mult] addIs [LIMSEQ_const], 
    simpset() addsimps [sumr_mult RS sym]));
qed "sums_mult";

Goalw [sums_def] "[| x sums x0; y sums y0 |] ==> (%n. x n - y n) sums (x0 - y0)";
by (auto_tac (claset() addIs [LIMSEQ_diff],
    simpset() addsimps [sumr_diff RS sym]));
qed "sums_diff";

goal Series.thy "!!f. summable f ==> suminf f * c = suminf(%n. f n * c)";
by (auto_tac (claset() addSIs [sums_unique,sums_mult,summable_sums],
    simpset() addsimps [real_mult_commute]));
qed "suminf_mult";

goal Series.thy "!!f. summable f ==> c * suminf f  = suminf(%n. c * f n)";
by (auto_tac (claset() addSIs [sums_unique,sums_mult,summable_sums],
    simpset()));
qed "suminf_mult2";

Goal "[| summable f; summable g |]  \
\     ==> suminf f - suminf g  = suminf(%n. f n - g n)";
by (auto_tac (claset() addSIs [sums_diff,sums_unique,summable_sums], simpset()));
qed "suminf_diff";

goalw Series.thy [sums_def] 
       "!!x. x sums x0 ==> (%n. - x n) sums - x0";
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

Goal "[|summable f; ALL d. #0 < (f(n + (2 * d))) + f(n + ((2 * d) + 1))|] \
\     ==> sumr 0 n f < suminf f";
by (dtac summable_sums 1);
by (auto_tac (claset(),simpset() addsimps [sums_def,LIMSEQ_def]));
by (dres_inst_tac [("x","f(n) + f(n + 1)")] spec 1);
by (Auto_tac);
by (rtac ccontr 2 THEN dtac real_leI 2);
by (subgoal_tac "sumr 0 (n + 2) f <= sumr 0 (2 * (Suc no) + n) f" 2);
by (induct_tac "no" 3 THEN Simp_tac 3);
by (res_inst_tac [("j","sumr 0 (2*(Suc na)+n) f")] real_le_trans 3);
by (assume_tac 3);
by (dres_inst_tac [("x","Suc na")] spec 3);
by (dres_inst_tac [("x","0")] spec 1);
by (Asm_full_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps add_ac) 2);
by (rotate_tac 1 1 THEN dres_inst_tac [("x","2 * (Suc no) + n")] spec 1);
by (Step_tac 1 THEN Asm_full_simp_tac 1);
by (subgoal_tac "suminf f + (f(n) + f(n + 1)) <= \
\                 sumr 0 (2 * (Suc no) + n) f" 1);
by (res_inst_tac [("j","sumr 0 (n+2) f")] real_le_trans 2);
by (assume_tac 3);
by (res_inst_tac [("j","sumr 0 n f + (f(n) + f(n + 1))")] real_le_trans 2);
by (REPEAT(Asm_simp_tac 2));
by (subgoal_tac "suminf f <= sumr 0 (2 * (Suc no) + n) f" 1);
by (res_inst_tac [("j","suminf f + (f(n) + f(n + 1))")] real_le_trans 2);
by (assume_tac 3);
by (dres_inst_tac [("x","0")] spec 2);
by (Asm_full_simp_tac 2);
by (subgoal_tac "#0 <= sumr 0 (2 * Suc no + n) f + - suminf f" 1);
by (dtac (rename_numerals abs_eqI1) 1 );
by (Asm_full_simp_tac 1);
by (auto_tac (claset(),simpset() addsimps [real_le_def]));
qed "sumr_pos_lt_pair";

(*-----------------------------------------------------------------
   Summable series of positive terms has limit >= any partial sum 
 ----------------------------------------------------------------*)
Goal 
     "!!f. [| summable f; ALL m. n <= m --> #0 <= f(m) |] \
\          ==> sumr 0 n f <= suminf f";
by (dtac summable_sums 1);
by (rewtac sums_def);
by (cut_inst_tac [("k","sumr 0 n f")] LIMSEQ_const 1);
by (etac LIMSEQ_le 1 THEN Step_tac 1);
by (res_inst_tac [("x","n")] exI 1 THEN Step_tac 1);
by (dtac le_imp_less_or_eq 1 THEN Step_tac 1);
by (auto_tac (claset() addIs [sumr_le], simpset()));
qed "series_pos_le";

Goal "!!f. [| summable f; ALL m. n <= m --> #0 < f(m) |] \
\          ==> sumr 0 n f < suminf f";
by (res_inst_tac [("j","sumr 0 (Suc n) f")] real_less_le_trans 1);
by (rtac series_pos_le 2);
by (Auto_tac);
by (dres_inst_tac [("x","m")] spec 1);
by (Auto_tac);
qed "series_pos_less";

(*-------------------------------------------------------------------
                    sum of geometric progression                 
 -------------------------------------------------------------------*)
(* lemma *)

Goalw [real_diff_def] "x ~= y ==> x - y ~= (#0::real)";
by (asm_full_simp_tac (simpset() addsimps 
   [rename_numerals (real_eq_minus_iff2 RS sym)]) 1);
qed "real_not_eq_diff";

Goal "x ~= #1 ==> sumr 0 n (%n. x ^ n) = (x ^ n - #1) * rinv(x - #1)";
by (induct_tac "n" 1);
by (Auto_tac);
by (res_inst_tac [("c1","x - #1")] (real_mult_right_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_not_eq_diff,
    real_eq_minus_iff2 RS sym,real_mult_assoc,real_add_mult_distrib]));
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
    real_diff_def,real_mult_commute]) 1);
qed "sumr_geometric";

Goal "abs(x) < #1 ==> (%n. x ^ n) sums rinv(#1 - x)";
by (case_tac "x = #1" 1);
by (auto_tac (claset() addSDs [LIMSEQ_rabs_realpow_zero2],
    simpset() addsimps [sumr_geometric,abs_one,sums_def,
    real_diff_def,real_add_mult_distrib]));
by (rtac (real_add_zero_left RS subst) 1);
by (rtac (real_mult_0 RS subst) 1);
by (rtac LIMSEQ_add 1 THEN rtac LIMSEQ_mult 1);
by (dtac real_not_eq_diff 3);
by (auto_tac (claset() addIs [LIMSEQ_const], simpset() addsimps 
    [real_minus_rinv RS sym,real_diff_def,real_add_commute,
     rename_numerals LIMSEQ_rabs_realpow_zero2]));
qed "geometric_sums";

(*-------------------------------------------------------------------
    Cauchy-type criterion for convergence of series (c.f. Harrison)
 -------------------------------------------------------------------*)
Goalw [summable_def,sums_def,convergent_def]
      "summable f = convergent (%n. sumr 0 n f)";
by (Auto_tac);
qed "summable_convergent_sumr_iff";

Goal "summable f = \
\     (ALL e. #0 < e --> (EX N. ALL m n. N <= m --> abs(sumr m n f) < e))";
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
     > Goalw [LIMSEQ_def] "summable f ==> f ----> #0";
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
by (res_inst_tac [("j","sumr m n (%k. abs(f k))")] real_le_less_trans 1);
by (rtac sumr_rabs 1);
by (res_inst_tac [("j","sumr m n g")] real_le_less_trans 1);
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
by (res_inst_tac [("j","sumr m n (%n. abs(f n))")] real_le_less_trans 1);
by (auto_tac (claset() addIs [sumr_rabs], simpset()));
qed "summable_rabs_cancel";

(*-------------------------------------------------------------------
         Absolute convergence of series
 -------------------------------------------------------------------*)
Goal "summable (%n. abs (f n)) ==> abs(suminf f) <= suminf (%n. abs(f n))";
by (auto_tac (claset() addIs [LIMSEQ_le,LIMSEQ_imp_rabs,summable_rabs_cancel,
    summable_sumr_LIMSEQ_suminf,sumr_rabs], simpset()));
qed "summable_rabs";

(*-------------------------------------------------------------------
                        The ratio test
 -------------------------------------------------------------------*)
Goal "[| c <= #0; abs x <= c * abs y |] ==> x = (#0::real)";
by (dtac real_le_imp_less_or_eq 1);
by (Auto_tac);
by (dres_inst_tac [("x1","y")] (abs_ge_zero RS 
    rename_numerals real_mult_le_zero) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_commute]) 1);
by (dtac real_le_trans 1 THEN assume_tac 1);
by (TRYALL(arith_tac));
qed "rabs_ratiotest_lemma";

(* lemmas *)
Goal "#0 < r ==> (x * r ^ n) * rinv (r ^ n) = x";
by (auto_tac (claset(),simpset() addsimps 
    [real_mult_assoc,rename_numerals realpow_not_zero]));
val lemma_rinv_realpow = result();

Goal "[| c ~= #0; ALL n. N <= n --> abs(f(Suc n)) <= c*abs(f n) |] \
\  ==> ALL n. N <= n --> abs(f(Suc n)) <= (c * c ^ n)* (rinv(c ^ n)*abs(f n))";
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
by (res_inst_tac [("z2.1","c ^ n")] (real_mult_left_commute RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [rename_numerals  
    realpow_not_zero]));
val lemma_rinv_realpow2 = result();

Goal "(k::nat) <= l ==> (EX n. l = k + n)";
by (dtac le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [less_imp_Suc_add], simpset()));
qed "le_Suc_ex";

Goal "((k::nat) <= l) = (EX n. l = k + n)";
by (auto_tac (claset(),simpset() addsimps [le_Suc_ex]));
qed "le_Suc_ex_iff";

Goal "!!c. [| c < #1; ALL n. N <= n --> abs(f(Suc n)) <= c*abs(f n) |] \
\     ==> summable f";
by (subgoal_tac "c <= #0 | #0 < c" 1 THEN Auto_tac);
by (asm_full_simp_tac (simpset() addsimps [summable_Cauchy]) 1);
by (Step_tac 1 THEN subgoal_tac "ALL n. N <= n --> f (Suc n) = #0" 1);
by (blast_tac (claset() addIs [rabs_ratiotest_lemma]) 2);
by (res_inst_tac [("x","Suc N")] exI 1 THEN Step_tac 1);
by (dtac Suc_le_imp_diff_ge2 1 THEN Auto_tac);
by (res_inst_tac [("g","%n. (abs (f N)* rinv(c ^ N))*c ^ n")] 
    summable_comparison_test 1);
by (res_inst_tac [("x","N")] exI 1 THEN Step_tac 1);
by (dtac (le_Suc_ex_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [realpow_add,
    CLAIM_SIMP "(a * b) * (c * d) = (a * d) * (b * (c::real))" real_mult_ac,
    rename_numerals realpow_not_zero]));
by (induct_tac "na" 1 THEN Auto_tac);
by (res_inst_tac [("j","c*abs(f(N + n))")] real_le_trans 1);
by (auto_tac (claset() addIs [real_mult_le_le_mono1],
    simpset() addsimps [summable_def, CLAIM_SIMP 
    "a * (b * c) = b * (a * (c::real))" real_mult_ac]));
by (res_inst_tac [("x","(abs(f N)*rinv(c ^ N))*rinv(#1 - c)")] exI 1);
by (auto_tac (claset() addSIs [sums_mult,geometric_sums], simpset() addsimps 
    [abs_eqI2]));
qed "ratio_test";


(*----------------------------------------------------------------------------*)
(* Differentiation of finite sum                                              *)
(*----------------------------------------------------------------------------*)

Goal "(ALL r. m <= r & r < (m + n) --> DERIV (%x. f r x) x :> (f' r x)) \
\     --> DERIV (%x. sumr m n (%n. f n x)) x :> sumr m n (%r. f' r x)";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [DERIV_add], simpset()));
qed "DERIV_sumr";







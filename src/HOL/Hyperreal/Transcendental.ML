(*  Title       : Transcendental.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998,1999  University of Cambridge
                  1999 University of Edinburgh
    Description : Power Series
*)

fun multr_by_tac x i = 
       let val cancel_thm = 
           CLAIM "[| (0::real)<z; x*z<y*z |] ==> x<y" 
       in
           res_inst_tac [("z",x)] cancel_thm i 
       end;

val mult_less_cancel_left = thm"mult_less_cancel_left";

Goalw [root_def] "root (Suc n) 0 = 0";
by (safe_tac (claset() addSIs [some_equality,power_0_Suc] 
    addSEs [realpow_zero_zero]));
qed "real_root_zero";
Addsimps [real_root_zero];

Goalw [root_def]
     "0 < x ==> (root(Suc n) x) ^ (Suc n) = x";
by (dres_inst_tac [("n","n")] realpow_pos_nth2 1);
by (auto_tac (claset() addIs [someI2],simpset()));
qed "real_root_pow_pos";

Goal "0 <= x ==> (root(Suc n) x) ^ (Suc n) = x";
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq]
              addDs [real_root_pow_pos],simpset()));
qed "real_root_pow_pos2";

Goalw [root_def] 
     "0 < x ==> root(Suc n) (x ^ (Suc n)) = x";
by (rtac some_equality 1);
by (forw_inst_tac [("n","n")] zero_less_power 2);
by (auto_tac (claset(),simpset() addsimps [zero_less_mult_iff]));
by (res_inst_tac [("R1.0","u"),("R2.0","x")] real_linear_less2 1);
by (dres_inst_tac [("n1","n"),("x","u")] (zero_less_Suc RSN  (3, realpow_less)) 1);
by (dres_inst_tac [("n1","n"),("x","x")] (zero_less_Suc RSN (3, realpow_less)) 4);
by (auto_tac (claset(),simpset() addsimps [real_less_not_refl])); 
qed "real_root_pos";

Goal "0 <= x ==> root(Suc n) (x ^ (Suc n)) = x";
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq,
              real_root_pos],simpset()));
qed "real_root_pos2";

Goalw [root_def]
     "0 < x ==> 0 <= root(Suc n) x";
by (dres_inst_tac [("n","n")] realpow_pos_nth2 1);
by (Safe_tac THEN rtac someI2 1);
by (auto_tac (claset() addSIs [order_less_imp_le] 
    addDs [zero_less_power],simpset() addsimps [zero_less_mult_iff]));
qed "real_root_pos_pos";

Goal "0 <= x ==> 0 <= root(Suc n) x";
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq]
              addDs [real_root_pos_pos],simpset()));
qed "real_root_pos_pos_le";  

Goalw [root_def] "root (Suc n) 1 = 1";
by (rtac some_equality 1);
by Auto_tac;
by (rtac ccontr 1);
by (res_inst_tac [("R1.0","u"),("R2.0","1")] real_linear_less2 1);
by (dres_inst_tac [("n","n")] realpow_Suc_less_one 1);
by (dres_inst_tac [("n","n")] power_gt1_lemma 4);
by (auto_tac (claset(),simpset() addsimps [real_less_not_refl]));
qed "real_root_one";
Addsimps [real_root_one];

(*----------------------------------------------------------------------*)
(* Square root                                                          *)
(*----------------------------------------------------------------------*)

(*lcp: needed now because 2 is a binary numeral!*)
Goal "root 2 = root (Suc (Suc 0))";
by (simp_tac (simpset() delsimps [numeral_0_eq_0, numeral_1_eq_1]
	                addsimps [numeral_0_eq_0 RS sym]) 1);  
qed "root_2_eq";
Addsimps [root_2_eq];

Goalw [sqrt_def] "sqrt 0 = 0";
by (Auto_tac);
qed "real_sqrt_zero";
Addsimps [real_sqrt_zero];

Goalw [sqrt_def] "sqrt 1 = 1";
by (Auto_tac);
qed "real_sqrt_one";
Addsimps [real_sqrt_one];

Goalw [sqrt_def] "(sqrt(x) ^ 2 = x) = (0 <= x)";
by (Step_tac 1);
by (cut_inst_tac [("r","root 2 x")] realpow_two_le 1);
by (stac numeral_2_eq_2 2); 
by (rtac real_root_pow_pos2 2);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "real_sqrt_pow2_iff";
Addsimps [real_sqrt_pow2_iff];


Addsimps [realpow_two_le_add_order RS (real_sqrt_pow2_iff RS iffD2)];
Addsimps [simplify (simpset()) (realpow_two_le_add_order RS 
           (real_sqrt_pow2_iff RS iffD2))];

Goalw [sqrt_def] "0 < x ==> sqrt(x) ^ 2 = x";
by (stac numeral_2_eq_2 1); 
by (etac real_root_pow_pos 1);
qed "real_sqrt_gt_zero_pow2";

Goal "(sqrt(abs(x)) ^ 2 = abs x)";
by (rtac (real_sqrt_pow2_iff RS iffD2) 1);
by (arith_tac 1);
qed "real_sqrt_abs_abs";
Addsimps [real_sqrt_abs_abs];

Goalw [sqrt_def] 
      "0 <= x ==> sqrt(x) ^ 2 = sqrt(x ^ 2)";
by (stac numeral_2_eq_2 1); 
by (auto_tac (claset() addIs [real_root_pow_pos2 
    RS ssubst, real_root_pos2 RS ssubst],
     simpset() delsimps [realpow_Suc]));
qed "real_pow_sqrt_eq_sqrt_pow";

Goal "0 <= x ==> sqrt(x) ^ 2 = sqrt(abs(x ^ 2))";
by (asm_full_simp_tac (simpset() addsimps [real_pow_sqrt_eq_sqrt_pow]) 1);
by (stac numeral_2_eq_2 1); 
by (asm_full_simp_tac (simpset()delsimps [realpow_Suc]) 1); 
qed "real_pow_sqrt_eq_sqrt_abs_pow";

Goal "0 <= x ==> sqrt(x) ^ 2 = sqrt(abs(x) ^ 2)";
by (asm_full_simp_tac (simpset() addsimps [real_pow_sqrt_eq_sqrt_abs_pow]) 1); 
by (stac numeral_2_eq_2 1); 
by (asm_full_simp_tac (simpset()delsimps [realpow_Suc]) 1); 
qed "real_pow_sqrt_eq_sqrt_abs_pow2";

Goal "0 <= x ==> sqrt(x) ^ 2 = abs(x)";
by (rtac (real_sqrt_abs_abs RS subst) 1);
by (res_inst_tac [("x1","x")] 
     (real_pow_sqrt_eq_sqrt_abs_pow2 RS ssubst) 1);
by (rtac (real_pow_sqrt_eq_sqrt_pow RS sym) 2);
by (assume_tac 1 THEN arith_tac 1);
qed "real_sqrt_pow_abs";

Goal "(~ (0::real) < x*x) = (x = 0)";
by Auto_tac;
by (rtac ccontr 1);
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by Auto_tac;
by (ftac (real_mult_order) 2);
by (asm_full_simp_tac (simpset() addsimps [zero_less_mult_iff]) 1); 
by Auto_tac;
qed "not_real_square_gt_zero";
Addsimps [not_real_square_gt_zero];


(* proof used to be simpler *)
Goalw [sqrt_def,root_def] 
      "[| 0 < x; 0 < y |] ==>sqrt(x*y) =  sqrt(x) * sqrt(y)";
by (dres_inst_tac [("n","1")] realpow_pos_nth2 1);
by (dres_inst_tac [("n","1")] realpow_pos_nth2 1);
by (asm_full_simp_tac (simpset() delsimps [realpow_Suc]
                                 addsimps [numeral_2_eq_2]) 1); 
by (Step_tac 1);
by (rtac someI2 1 THEN Step_tac 1 THEN Blast_tac 2);
by (Asm_full_simp_tac 1 THEN Asm_full_simp_tac 1);
by (rtac someI2 1 THEN Step_tac 1 THEN Blast_tac 2);
by (Asm_full_simp_tac 1 THEN Asm_full_simp_tac 1);
by (res_inst_tac [("a","xa * x")] someI2 1);
by (auto_tac (claset() addEs [real_less_asym],
    simpset() addsimps mult_ac@[power_mult_distrib RS sym,realpow_two_disj,
    zero_less_power, real_mult_order] delsimps [realpow_Suc]));
qed "real_sqrt_mult_distrib";

Goal "[|0<=x; 0<=y |] ==> sqrt(x*y) =  sqrt(x) * sqrt(y)";
by (auto_tac (claset() addIs [ real_sqrt_mult_distrib],
    simpset() addsimps [real_le_less]));
qed "real_sqrt_mult_distrib2";

Goal "(r * r = 0) = (r = (0::real))";
by Auto_tac;
qed "real_mult_self_eq_zero_iff";
Addsimps [real_mult_self_eq_zero_iff];

Goalw [sqrt_def,root_def] "0 < x ==> 0 < sqrt(x)";
by (stac numeral_2_eq_2 1); 
by (dtac realpow_pos_nth2 1 THEN Step_tac 1);
by (rtac someI2 1 THEN Step_tac 1 THEN Blast_tac 2);
by Auto_tac;
qed "real_sqrt_gt_zero";

Goal "0 <= x ==> 0 <= sqrt(x)";
by (auto_tac (claset() addIs [real_sqrt_gt_zero],
    simpset() addsimps [real_le_less]));
qed "real_sqrt_ge_zero";

Goal "0 <= sqrt (x ^ 2 + y ^ 2)";
by (auto_tac (claset() addSIs [real_sqrt_ge_zero],simpset()));
qed "real_sqrt_sum_squares_ge_zero";
Addsimps [real_sqrt_sum_squares_ge_zero];

Goal "0 <= sqrt ((x ^ 2 + y ^ 2)*(xa ^ 2 + ya ^ 2))";
by (auto_tac (claset() addSIs [real_sqrt_ge_zero],simpset() 
    addsimps [zero_le_mult_iff]));
qed "real_sqrt_sum_squares_mult_ge_zero";
Addsimps [real_sqrt_sum_squares_mult_ge_zero];

Goal "sqrt ((x ^ 2 + y ^ 2) * (xa ^ 2 + ya ^ 2)) ^ 2 = \
\     (x ^ 2 + y ^ 2) * (xa ^ 2 + ya ^ 2)";
by (auto_tac (claset(),simpset() addsimps [real_sqrt_pow2_iff,
    zero_le_mult_iff] delsimps [realpow_Suc]));
qed "real_sqrt_sum_squares_mult_squared_eq";
Addsimps [real_sqrt_sum_squares_mult_squared_eq];

Goal "sqrt(x ^ 2) = abs(x)";
by (rtac (abs_realpow_two RS subst) 1);
by (rtac (real_sqrt_abs_abs RS subst) 1);
by (stac real_pow_sqrt_eq_sqrt_pow 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2, abs_mult]));
qed "real_sqrt_abs";
Addsimps [real_sqrt_abs];

Goal "sqrt(x*x) = abs(x)";
by (rtac (realpow_two RS subst) 1);
by (stac (numeral_2_eq_2 RS sym) 1); 
by (rtac real_sqrt_abs 1);
qed "real_sqrt_abs2";
Addsimps [real_sqrt_abs2];

Goal "0 < x ==> 0 < sqrt(x) ^ 2";
by (asm_full_simp_tac (simpset() addsimps [real_sqrt_gt_zero_pow2]) 1); 
qed "real_sqrt_pow2_gt_zero";

Goal "0 < x ==> sqrt x ~= 0";
by (ftac real_sqrt_pow2_gt_zero 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2, real_less_not_refl]));
qed "real_sqrt_not_eq_zero";

Goal "0 < x ==> inverse (sqrt(x)) ^ 2 = inverse x";
by (cut_inst_tac [("n1","2"),("a1","sqrt x")] (power_inverse RS sym) 1);
by (auto_tac (claset() addDs [real_sqrt_gt_zero_pow2],simpset()));
qed "real_inv_sqrt_pow2";

Goal "[| 0 <= x; sqrt(x) = 0|] ==> x = 0";
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [real_sqrt_not_eq_zero],simpset()));
qed "real_sqrt_eq_zero_cancel";

Goal "0 <= x ==> ((sqrt x = 0) = (x = 0))";
by (auto_tac (claset(),simpset() addsimps [real_sqrt_eq_zero_cancel]));
qed "real_sqrt_eq_zero_cancel_iff";
Addsimps [real_sqrt_eq_zero_cancel_iff];

Goal "x <= sqrt(x ^ 2 + y ^ 2)";
by (subgoal_tac "x <= 0 | 0 <= x" 1);
by (Step_tac 1);
by (rtac real_le_trans 1);
by (auto_tac (claset(),simpset() delsimps [realpow_Suc]));
by (res_inst_tac [("n","1")] realpow_increasing 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2 RS sym]
				 delsimps [realpow_Suc]));
qed "real_sqrt_sum_squares_ge1";
Addsimps [real_sqrt_sum_squares_ge1];

Goal "y <= sqrt(z ^ 2 + y ^ 2)";
by (simp_tac (simpset() addsimps [real_add_commute] 
    delsimps [realpow_Suc]) 1);
qed "real_sqrt_sum_squares_ge2";
Addsimps [real_sqrt_sum_squares_ge2];

Goal "1 <= x ==> 1 <= sqrt x";
by (res_inst_tac [("n","1")] realpow_increasing 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2 RS sym, real_sqrt_gt_zero_pow2,
    real_sqrt_ge_zero] delsimps [realpow_Suc]));
qed "real_sqrt_ge_one";

(*-------------------------------------------------------------------------*)
(* Exponential function                                                    *)
(*-------------------------------------------------------------------------*)

Goal "summable (%n. inverse (real (fact n)) * x ^ n)";
by (cut_facts_tac [zero_less_one RS real_dense] 1);
by (Step_tac 1);
by (cut_inst_tac [("x","r")] reals_Archimedean3 1);
by Auto_tac;
by (dres_inst_tac [("x","abs x")] spec 1 THEN Safe_tac);
by (res_inst_tac [("N","n"),("c","r")] ratio_test 1);
by (auto_tac (claset(),
     simpset() addsimps [abs_mult,mult_assoc RS sym] delsimps [fact_Suc]));
by (rtac mult_right_mono 1);
by (res_inst_tac [("b1","abs x")] (mult_commute RS ssubst) 1);
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (auto_tac (claset(),simpset() addsimps [abs_mult,inverse_mult_distrib]));
by (auto_tac (claset(), simpset() addsimps 
     [mult_assoc RS sym, abs_eqI2, positive_imp_inverse_positive]));
by (rtac order_less_imp_le 1);
by (res_inst_tac [("z1","real (Suc na)")] (real_mult_less_iff1
    RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_not_refl2 RS not_sym,
    mult_assoc,abs_inverse]));
by (etac order_less_trans 1);
by (auto_tac (claset(),simpset() addsimps [mult_less_cancel_left]@mult_ac));
qed "summable_exp";

Addsimps [real_of_nat_fact_gt_zero,
    real_of_nat_fact_ge_zero,inv_real_of_nat_fact_gt_zero,
    inv_real_of_nat_fact_ge_zero];

Goalw [real_divide_def] 
     "summable (%n. \
\          (if even n then 0 \
\          else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * \
\               x ^ n)";
by (res_inst_tac [("g","(%n. inverse (real (fact n)) * abs(x) ^ n)")] 
    summable_comparison_test 1);
by (rtac summable_exp 2);
by (res_inst_tac [("x","0")] exI 1);
by (auto_tac (claset(), simpset() addsimps [power_abs RS sym,
    abs_mult,zero_le_mult_iff]));
by (auto_tac (claset() addIs [mult_right_mono],
    simpset() addsimps [positive_imp_inverse_positive,abs_eqI2]));
qed "summable_sin";

Goalw [real_divide_def] 
      "summable (%n. \
\          (if even n then \
\          (- 1) ^ (n div 2)/(real (fact n)) else 0) * x ^ n)";
by (res_inst_tac [("g","(%n. inverse (real (fact n)) * abs(x) ^ n)")] 
    summable_comparison_test 1);
by (rtac summable_exp 2);
by (res_inst_tac [("x","0")] exI 1);
by (auto_tac (claset(), simpset() addsimps [power_abs RS sym,abs_mult,
    zero_le_mult_iff]));
by (auto_tac (claset() addSIs [mult_right_mono],
    simpset() addsimps [positive_imp_inverse_positive,abs_eqI2]));
qed "summable_cos";

Goal "(if even n then 0 \
\      else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * 0 ^ n = 0";
by (induct_tac "n" 1);
by (Auto_tac);
val lemma_STAR_sin = result();
Addsimps [lemma_STAR_sin];

Goal "0 < n --> \
\     (- 1) ^ (n div 2)/(real (fact n)) * 0 ^ n = 0";
by (induct_tac "n" 1);
by (Auto_tac);
val lemma_STAR_cos = result();
Addsimps [lemma_STAR_cos];

Goal "0 < n --> \
\     (-1) ^ (n div 2)/(real (fact n)) * 0 ^ n = 0";
by (induct_tac "n" 1);
by (Auto_tac);
val lemma_STAR_cos1 = result();
Addsimps [lemma_STAR_cos1];

Goal "sumr 1 n (%n. if even n \
\                   then (- 1) ^ (n div 2)/(real (fact n)) * \
\                         0 ^ n \
\                   else 0) = 0";
by (induct_tac "n" 1);
by (case_tac "n" 2);
by (Auto_tac);
val lemma_STAR_cos2 = result();
Addsimps [lemma_STAR_cos2];

Goalw [exp_def] "(%n. inverse (real (fact n)) * x ^ n) sums exp(x)";
by (rtac (summable_exp RS summable_sums) 1);
qed "exp_converges";

Goalw [sin_def] 
      "(%n. (if even n then 0 \
\           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * \
\                x ^ n) sums sin(x)";
by (rtac (summable_sin RS summable_sums) 1);
qed "sin_converges";

Goalw [cos_def]
      "(%n. (if even n then \
\          (- 1) ^ (n div 2)/(real (fact n)) \
\          else 0) * x ^ n) sums cos(x)";
by (rtac (summable_cos RS summable_sums) 1);
qed "cos_converges";

Goal "p <= n --> y ^ (Suc n - p) = ((y::real) ^ (n - p)) * y";
by (induct_tac "n" 1 THEN Auto_tac);
by (subgoal_tac "p = Suc n" 1);
by (Asm_simp_tac 1 THEN Auto_tac);
by (dtac sym 1 THEN asm_full_simp_tac (simpset() addsimps 
    [Suc_diff_le,real_mult_commute,realpow_Suc RS sym] 
    delsimps [realpow_Suc]) 1);
qed_spec_mp "lemma_realpow_diff";

(*--------------------------------------------------------------------------*)
(* Properties of power series                                               *)
(*--------------------------------------------------------------------------*)

Goal "sumr 0 (Suc n) (%p. (x ^ p) * y ^ ((Suc n) - p)) = \
\     y * sumr 0 (Suc n) (%p. (x ^ p) * (y ^ (n - p)))";
by (auto_tac (claset(),simpset() addsimps [sumr_mult] delsimps [sumr_Suc]));
by (rtac sumr_subst 1);
by (strip_tac 1);
by (stac lemma_realpow_diff 1);
by (auto_tac (claset(),simpset() addsimps mult_ac));
qed "lemma_realpow_diff_sumr";

Goal "x ^ (Suc n) - y ^ (Suc n) = \
\     (x - y) * sumr 0 (Suc n) (%p. (x ^ p) * (y ^(n - p)))";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() delsimps [sumr_Suc]));
by (stac sumr_Suc 1);
by (dtac sym 1);
by (auto_tac (claset(),simpset() addsimps [lemma_realpow_diff_sumr,
    right_distrib,real_diff_def] @ 
    mult_ac delsimps [sumr_Suc]));
qed "lemma_realpow_diff_sumr2";

Goal "sumr 0 (Suc n) (%p. (x ^ p) * (y ^ (n - p))) = \
\     sumr 0 (Suc n) (%p. (x ^ (n - p)) * (y ^ p))";
by (case_tac "x = y" 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_commute,
    power_add RS sym] delsimps [sumr_Suc]));
by (res_inst_tac [("c1","x - y")] (real_mult_left_cancel RS iffD1) 1);
by (rtac (minus_minus RS subst) 2);
by (stac minus_mult_left 2);
by (auto_tac (claset(),simpset() addsimps [lemma_realpow_diff_sumr2 
    RS sym] delsimps [sumr_Suc]));
qed "lemma_realpow_rev_sumr";

(* ------------------------------------------------------------------------ *)
(* Power series has a `circle` of convergence,                              *)
(* i.e. if it sums for x, then it sums absolutely for z with |z| < |x|.     *)
(* ------------------------------------------------------------------------ *)

Goal "[| summable (%n. f(n) * (x ^ n)); abs(z) < abs(x) |] \
\     ==> summable (%n. abs(f(n)) * (z ^ n))";
by (dtac summable_LIMSEQ_zero 1);
by (dtac convergentI 1);
by (asm_full_simp_tac (simpset() addsimps [Cauchy_convergent_iff RS sym]) 1);
by (dtac Cauchy_Bseq 1);
by (asm_full_simp_tac (simpset() addsimps [Bseq_def]) 1);
by (Step_tac 1);
by (res_inst_tac [("g","%n. K * abs(z ^ n) * inverse (abs(x ^ n))")] 
    summable_comparison_test 1);
by (res_inst_tac [("x","0")] exI 1 THEN Step_tac 1);
by (subgoal_tac "0 < abs (x ^ n)" 1);
by (res_inst_tac [("z","abs (x ^ n)")] (CLAIM_SIMP 
    "[| (0::real) <z; x*z<=y*z |] ==> x<=y" [mult_le_cancel_left]) 1);
by (auto_tac (claset(),
    simpset() addsimps [mult_assoc,power_abs]));
by (dres_inst_tac [("x","0")] spec 2 THEN Force_tac 2); 
by (auto_tac (claset(),simpset() addsimps [abs_mult,power_abs] @ mult_ac));
by (res_inst_tac [("a2","z ^ n")] (abs_ge_zero RS real_le_imp_less_or_eq
    RS disjE) 1 THEN dtac sym 2);
by (auto_tac (claset() addSIs [mult_right_mono],
    simpset() addsimps [mult_assoc RS sym, power_abs,summable_def, power_0_left]));
by (res_inst_tac [("x","K * inverse(1 - (abs(z) * inverse(abs x)))")] exI 1);
by (auto_tac (claset() addSIs [sums_mult],simpset() addsimps [mult_assoc]));
by (subgoal_tac 
    "abs(z ^ n) * inverse(abs x ^ n) = (abs(z) * inverse(abs x)) ^ n" 1);
by (auto_tac (claset(),simpset() addsimps [power_abs RS sym]));
by (subgoal_tac "x ~= 0" 1);
by (subgoal_tac "x ~= 0" 3);
by (auto_tac (claset(),
     simpset() delsimps [abs_inverse, abs_mult]
      addsimps [abs_inverse RS sym, realpow_not_zero, abs_mult RS sym,
    power_inverse, power_mult_distrib RS sym]));
by (auto_tac (claset() addSIs [geometric_sums],
       simpset() addsimps [power_abs, inverse_eq_divide]));
by (res_inst_tac [("z","abs(x)")] (CLAIM_SIMP 
    "[|(0::real)<z; x*z<y*z |] ==> x<y" [mult_less_cancel_left]) 1);
by (auto_tac (claset(),simpset() addsimps [abs_mult RS sym,mult_assoc]));
qed "powser_insidea";

Goal "[| summable (%n. f(n) * (x ^ n)); abs(z) < abs(x) |] \
\     ==> summable (%n. f(n) * (z ^ n))";
by (dres_inst_tac [("z","abs z")] powser_insidea 1);
by (auto_tac (claset() addIs [summable_rabs_cancel],
    simpset() addsimps [power_abs RS sym]));
qed "powser_inside";

(* ------------------------------------------------------------------------ *)
(*               Differentiation of power series                            *)
(* ------------------------------------------------------------------------ *)

(* Lemma about distributing negation over it *)
Goalw [diffs_def] "diffs (%n. - c n) = (%n. - diffs c n)";
by Auto_tac;
qed "diffs_minus";

(* ------------------------------------------------------------------------ *)
(* Show that we can shift the terms down one                                *)
(* ------------------------------------------------------------------------ *)

Goal "sumr 0 n (%n. (diffs c)(n) * (x ^ n)) = \
\     sumr 0 n (%n. real n * c(n) * (x ^ (n - Suc 0))) + \
\     (real n * c(n) * x ^ (n - Suc 0))";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc, 
    real_add_assoc RS sym,diffs_def]));
qed "lemma_diffs";

Goal "sumr 0 n (%n. real n * c(n) * (x ^ (n - Suc 0))) = \
\     sumr 0 n (%n. (diffs c)(n) * (x ^ n)) - \
\     (real n * c(n) * x ^ (n - Suc 0))";
by (auto_tac (claset(),simpset() addsimps [lemma_diffs]));
qed "lemma_diffs2";

Goal "summable (%n. (diffs c)(n) * (x ^ n)) ==> \
\     (%n. real n * c(n) * (x ^ (n - Suc 0))) sums \
\        (suminf(%n. (diffs c)(n) * (x ^ n)))";
by (ftac summable_LIMSEQ_zero 1);
by (subgoal_tac "(%n. real n * c(n) * (x ^ (n - Suc 0))) ----> 0" 1);
by (rtac LIMSEQ_imp_Suc 2);
by (dtac summable_sums 1);
by (auto_tac (claset(),simpset() addsimps [sums_def]));
by (thin_tac "(%n. diffs c n * x ^ n) ----> 0" 1);
by (rotate_tac 1 1);
by (dtac LIMSEQ_diff 1);
by (auto_tac (claset(),simpset() addsimps [lemma_diffs2 RS sym,
    symmetric diffs_def]));
by (asm_full_simp_tac (simpset() addsimps [diffs_def]) 1);
qed "diffs_equiv";

(* -------------------------------------------------------------------------*)
(* Term-by-term differentiability of power series                           *)
(* -------------------------------------------------------------------------*)

Goal "sumr 0 m (%p. (((z + h) ^ (m - p)) * (z ^ p)) - (z ^ m)) = \
\       sumr 0 m (%p. (z ^ p) * \
\       (((z + h) ^ (m - p)) - (z ^ (m - p))))";
by (rtac sumr_subst 1);
by (auto_tac (claset(),simpset() addsimps [right_distrib,
    real_diff_def,power_add RS sym] 
    @ mult_ac));
qed "lemma_termdiff1";

(* proved elsewhere? *)
Goal "m < n --> (EX d. n = m + d + Suc 0)";
by (induct_tac "m" 1 THEN Auto_tac);
by (case_tac "n" 1);
by (case_tac "d" 3);
by (Auto_tac);
qed_spec_mp "less_add_one";

Goal " h ~= 0 ==> \
\       (((z + h) ^ n) - (z ^ n)) * inverse h - \
\           real n * (z ^ (n - Suc 0)) = \
\        h * sumr 0 (n - Suc 0) (%p. (z ^ p) * \
\              sumr 0 ((n - Suc 0) - p) \
\                (%q. ((z + h) ^ q) * (z ^ (((n - 2) - p) - q))))";
by (rtac (real_mult_left_cancel RS iffD1) 1 THEN Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [right_diff_distrib]
    @ mult_ac) 1);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
by (case_tac "n" 1 THEN auto_tac (claset(),simpset() 
    addsimps [lemma_realpow_diff_sumr2,
    right_diff_distrib RS sym,real_mult_assoc] 
    delsimps [realpow_Suc,sumr_Suc]));
by (auto_tac (claset(),simpset() addsimps [lemma_realpow_rev_sumr]
    delsimps [sumr_Suc]));
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc,sumr_diff_mult_const,
    left_distrib,CLAIM "(a + b) - (c + d) = a - c + b - (d::real)",
    lemma_termdiff1,sumr_mult]));
by (auto_tac (claset() addSIs [sumr_subst],simpset() addsimps 
    [real_diff_def,real_add_assoc]));
by (fold_tac [real_diff_def] THEN dtac less_add_one 1);
by (auto_tac (claset(),simpset() addsimps [sumr_mult,lemma_realpow_diff_sumr2] 
    @ mult_ac delsimps [sumr_Suc,realpow_Suc]));
qed "lemma_termdiff2";

Goal "[| h ~= 0; abs z <= K; abs (z + h) <= K |] \
\     ==> abs (((z + h) ^ n - z ^ n) * inverse h - real n * z ^ (n - Suc 0)) \
\         <= real n * real (n - Suc 0) * K ^ (n - 2) * abs h";
by (stac lemma_termdiff2 1);
by (asm_full_simp_tac (simpset() addsimps [abs_mult,real_mult_commute]) 2);
by (stac real_mult_commute 2); 
by (rtac (sumr_rabs RS real_le_trans) 2);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 2);
by (rtac (real_mult_commute RS subst) 2);
by (auto_tac (claset() addSIs [sumr_bound2],simpset() addsimps [abs_mult]));
by (case_tac "n" 1 THEN Auto_tac);
by (dtac less_add_one 1);
by (auto_tac (claset(),simpset() addsimps [power_add,real_add_assoc RS sym,
    CLAIM_SIMP "(a * b) * c = a * (c * (b::real))" mult_ac] 
    delsimps [sumr_Suc]));
by (auto_tac (claset() addSIs [mult_mono],simpset()delsimps [sumr_Suc])); 
by (auto_tac (claset() addSIs [power_mono],
            simpset() addsimps [power_abs] delsimps [sumr_Suc] ));
by (res_inst_tac [("j","real (Suc d) * (K ^ d)")] real_le_trans 1);
by (subgoal_tac "0 <= K" 2);
by (arith_tac 3);
by (dres_inst_tac [("n","d")] zero_le_power 2);
by (auto_tac (claset(),simpset() delsimps [sumr_Suc] ));
by (rtac (sumr_rabs RS real_le_trans) 1);
by (rtac sumr_bound2 1 THEN 
    auto_tac (claset() addSDs [less_add_one]
    addSIs [mult_mono], simpset() addsimps [abs_mult, power_add]));
by (auto_tac (claset() addSIs [power_mono,zero_le_power],
              simpset() addsimps [power_abs]));
by (ALLGOALS(arith_tac));
qed "lemma_termdiff3";

Goalw [LIM_def]
  "[| 0 < k; \
\     (ALL h. 0 < abs(h) & abs(h) < k --> abs(f h) <= K * abs(h)) |] \
\  ==> f -- 0 --> 0";
by (Auto_tac);
by (subgoal_tac "0 <= K" 1);
by (dres_inst_tac [("x","k*inverse 2")] spec 2);
by (ftac real_less_half_sum 2);
by (dtac real_gt_half_sum 2);
by (auto_tac (claset(),simpset() addsimps [abs_eqI2]));
by (res_inst_tac [("z","k/2")] (CLAIM_SIMP 
    "[| (0::real) <z; x*z<=y*z |] ==> x<=y" [mult_le_cancel_left]) 2);
by (auto_tac (claset() addIs [abs_ge_zero RS real_le_trans],simpset()));
by (dtac real_le_imp_less_or_eq 1);
by Auto_tac;
by (subgoal_tac "0 < (r * inverse K) * inverse 2" 1);
by (REPEAT(rtac (real_mult_order) 2));
by (dres_inst_tac [("d1.0","r * inverse K * inverse 2"),("d2.0","k")]
    real_lbound_gt_zero 1);
by (auto_tac (claset(),simpset() addsimps [positive_imp_inverse_positive,
    zero_less_mult_iff]));
by (rtac real_le_trans 2 THEN assume_tac 3 THEN Auto_tac);
by (res_inst_tac [("x","e")] exI 1 THEN Auto_tac);
by (res_inst_tac [("y","K * abs x")] order_le_less_trans 1);
by (res_inst_tac [("R2.0","K * e")] real_less_trans 2);
by (res_inst_tac [("z","inverse K")] (CLAIM_SIMP 
    "[|(0::real) <z; z*x<z*y |] ==> x<y" [mult_less_cancel_left]) 3);
by (asm_full_simp_tac (simpset() addsimps [mult_assoc RS sym]) 4);
by (Force_tac 1);
by (asm_full_simp_tac (simpset() addsimps [mult_less_cancel_left]) 1); 
by (auto_tac (claset(),simpset() addsimps mult_ac));
qed "lemma_termdiff4";

Goal "[| 0 < k; \
\           summable f; \
\           ALL h. 0 < abs(h) & abs(h) < k --> \
\                   (ALL n. abs(g(h) (n::nat)) <= (f(n) * abs(h))) |] \
\        ==> (%h. suminf(g h)) -- 0 --> 0";
by (dtac summable_sums 1);
by (subgoal_tac "ALL h. 0 < abs h & abs h < k --> \
\         abs(suminf (g h)) <= suminf f * abs h" 1);
by (Auto_tac);
by (subgoal_tac "summable (%n. f n * abs h)" 2);
by (simp_tac (simpset() addsimps [summable_def]) 3);
by (res_inst_tac [("x","suminf f * abs h")] exI 3);
by (dres_inst_tac [("c","abs h")] sums_mult 3);
by (asm_full_simp_tac (simpset() addsimps mult_ac) 3);
by (subgoal_tac "summable (%n. abs(g(h::real)(n::nat)))" 2);
by (res_inst_tac [("g","%n. f(n::nat) * abs(h)")] summable_comparison_test 3);
by (res_inst_tac [("x","0")] exI 3);
by Auto_tac;
by (res_inst_tac [("j","suminf(%n. abs(g h n))")] real_le_trans 2);
by (auto_tac (claset() addIs [summable_rabs,summable_le],simpset() addsimps 
    [sums_summable RS suminf_mult]));
by (auto_tac (claset() addSIs [lemma_termdiff4],simpset() addsimps 
    [(sums_summable RS suminf_mult) RS sym]));
qed "lemma_termdiff5";

(* FIXME: Long proof *)
Goalw [deriv_def] 
    "[| summable(%n. c(n) * (K ^ n)); \
\       summable(%n. (diffs c)(n) * (K ^ n)); \
\       summable(%n. (diffs(diffs c))(n) * (K ^ n)); \
\       abs(x) < abs(K) |] \
\    ==> DERIV (%x. suminf (%n. c(n) * (x ^ n)))  x :> \
\            suminf (%n. (diffs c)(n) * (x ^ n))";

by (res_inst_tac [("g","%h. suminf(%n. ((c(n) * ((x + h) ^ n)) - \
\                 (c(n) * (x ^ n))) * inverse h)")] LIM_trans 1);
by (asm_full_simp_tac (simpset() addsimps [LIM_def]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","abs K - abs x")] exI 1);
by (auto_tac (claset(),simpset() addsimps [less_diff_eq]));
by (dtac (abs_triangle_ineq RS order_le_less_trans) 1);
by (res_inst_tac [("y","0")] order_le_less_trans 1);
by Auto_tac;
by (subgoal_tac "(%n. (c n) * (x ^ n)) sums \
\           (suminf(%n. (c n) * (x ^ n))) & \
\       (%n. (c n) * ((x + xa) ^ n)) sums \
\           (suminf(%n. (c n) * ((x + xa) ^ n)))" 1);
by (auto_tac (claset() addSIs [summable_sums],simpset()));
by (rtac powser_inside 2 THEN rtac powser_inside 4);
by (auto_tac (claset(),simpset() addsimps [real_add_commute]));
by (EVERY1[rotate_tac 8, dtac sums_diff, assume_tac]);
by (dres_inst_tac [("x","(%n. c n * (xa + x) ^ n - c n * x ^ n)"),
    ("c","inverse xa")] sums_mult 1);
by (rtac (sums_unique RS sym) 1);
by (asm_full_simp_tac (simpset() addsimps [real_diff_def,
    real_divide_def] @ add_ac @ mult_ac) 1);
by (rtac LIM_zero_cancel 1);
by (res_inst_tac [("g","%h. suminf (%n. c(n) * (((((x + h) ^ n) - \
\   (x ^ n)) * inverse  h) - (real n * (x ^ (n - Suc 0)))))")] LIM_trans 1);
by (asm_full_simp_tac (simpset() addsimps [LIM_def]) 1);
by (Step_tac 1);
by (res_inst_tac [("x","abs K - abs x")] exI 1);
by (auto_tac (claset(),simpset() addsimps [less_diff_eq]));
by (dtac (abs_triangle_ineq RS order_le_less_trans) 1);
by (res_inst_tac [("y","0")] order_le_less_trans 1);
by Auto_tac;
by (subgoal_tac "summable(%n. (diffs c)(n) * (x ^ n))" 1);
by (rtac powser_inside 2);
by (Auto_tac);
by (dres_inst_tac [("c","c"),("x","x")] diffs_equiv 1);
by (ftac sums_unique 1 THEN Auto_tac);
by (subgoal_tac "(%n. (c n) * (x ^ n)) sums \
\           (suminf(%n. (c n) * (x ^ n))) & \
\       (%n. (c n) * ((x + xa) ^ n)) sums \
\           (suminf(%n. (c n) * ((x + xa) ^ n)))" 1);
by (Step_tac 1);
by (auto_tac (claset() addSIs [summable_sums],simpset()));
by (rtac powser_inside 2 THEN rtac powser_inside 4);
by (auto_tac (claset(),simpset() addsimps [real_add_commute]));
by (forw_inst_tac [("x","(%n. c n * (xa + x) ^ n)"),
    ("y","(%n. c n * x ^ n)")] sums_diff 1 THEN assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [[sums_summable,sums_summable] 
    MRS suminf_diff,right_diff_distrib RS sym]) 1);
by (forw_inst_tac [("x","(%n. c n * ((xa + x) ^ n - x ^ n))"),
    ("c","inverse xa")] sums_mult 1);
by (asm_full_simp_tac (simpset() addsimps [sums_summable RS suminf_mult2]) 1);
by (forw_inst_tac [("x","(%n. inverse xa * (c n * ((xa + x) ^ n - x ^ n)))"),
    ("y","(%n. real n * c n * x ^ (n - Suc 0))")] sums_diff 1);
by (assume_tac 1);
by (rtac (ARITH_PROVE "z - y = x ==> - x = (y::real) - z") 1);
by (asm_full_simp_tac (simpset() addsimps [[sums_summable,sums_summable] 
    MRS suminf_diff] @ add_ac @ mult_ac ) 1);
by (res_inst_tac [("f","suminf")] arg_cong 1);
by (rtac ext 1);
by (asm_full_simp_tac (simpset() addsimps [real_diff_def,
     right_distrib] @ add_ac @ mult_ac) 1);
(* 46 *)
by (dtac real_dense 1 THEN Step_tac 1);
by (ftac (real_less_sum_gt_zero) 1);
by (dres_inst_tac [("f","%n. abs(c n) * real n * \
\                    real (n - Suc 0) * (r ^ (n - 2))"),
                   ("g","%h n. c(n) * (((((x + h) ^ n) - (x ^ n)) * inverse  h) - \
\                    (real  n * (x ^ (n - Suc 0))))")] lemma_termdiff5 1);
by (auto_tac (claset(),simpset() addsimps [real_add_commute]));
by (subgoal_tac "summable(%n. abs(diffs(diffs c) n) * (r ^ n))" 1);
by (res_inst_tac [("x","K")] powser_insidea 2 THEN Auto_tac);
by (subgoal_tac "abs r = r" 2 THEN Auto_tac);
by (res_inst_tac [("j1","abs x")] (real_le_trans RS abs_eqI1) 2);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [diffs_def,abs_mult,
    real_mult_assoc RS sym]) 1);
by (subgoal_tac "ALL n. real (Suc n) * real (Suc(Suc n)) * \
\   abs(c(Suc(Suc n))) * (r ^ n) = diffs(diffs (%n. abs(c n))) n * (r ^ n)" 1);
by (dres_inst_tac [("P","summable")] 
    (CLAIM "[|ALL n. f(n) = g(n); P(%n. f n)|] ==> P(%n. g(n))") 1);
by (Auto_tac);
by (asm_full_simp_tac (simpset() addsimps [diffs_def]) 2
    THEN asm_full_simp_tac (simpset() addsimps [diffs_def]) 2);
by (dtac diffs_equiv 1);
by (dtac sums_summable 1);
by (asm_full_simp_tac (simpset() addsimps [diffs_def] @ mult_ac) 1);
by (subgoal_tac "(%n. real n * (real (Suc n) * (abs(c(Suc n)) * \
\                 (r ^ (n - Suc 0))))) = (%n. diffs(%m. real (m - Suc 0) * \
\                  abs(c m) * inverse r) n * (r ^ n))" 1);
by (Auto_tac);
by (rtac ext 2);
by (asm_full_simp_tac (simpset() addsimps [diffs_def]) 2);
by (case_tac "n" 2);
by Auto_tac;
(* 69 *)
by (dtac (abs_ge_zero RS order_le_less_trans) 2);
by (asm_full_simp_tac (simpset() addsimps mult_ac) 2);
by (dtac diffs_equiv 1);
by (dtac sums_summable 1);
by (res_inst_tac [("a","summable (%n. real n * \
\    (real (n - Suc 0) * abs (c n) * inverse r) * r ^ (n - Suc 0))")] 
    (CLAIM "(a = b) ==> a ==> b") 1  THEN assume_tac 2);
by (res_inst_tac [("f","summable")] arg_cong 1 THEN rtac ext 1);
by (dtac (abs_ge_zero RS order_le_less_trans) 2);
by (asm_full_simp_tac (simpset() addsimps mult_ac) 2);
(* 77 *)
by (case_tac "n" 1);
by Auto_tac;
by (case_tac "nat" 1);
by Auto_tac;
by (dtac (abs_ge_zero RS order_le_less_trans) 1);
by (auto_tac (claset(),simpset() addsimps [CLAIM_SIMP 
    "(a::real) * (b * (c * d)) = a * (b * c) * d"
     mult_ac]));
by (dtac (abs_ge_zero RS order_le_less_trans) 1);
by (asm_full_simp_tac (simpset() addsimps [abs_mult,real_mult_assoc]) 1);
by (rtac mult_left_mono 1);
by (rtac (add_commute RS subst) 1);
by (simp_tac (simpset() addsimps [mult_assoc RS sym]) 1);
by (rtac lemma_termdiff3 1);
by (auto_tac (claset() addIs [(abs_triangle_ineq RS real_le_trans)],
    simpset()));
by (arith_tac 1);
qed "termdiffs";

(* ------------------------------------------------------------------------ *)
(* Formal derivatives of exp, sin, and cos series                           *)
(* ------------------------------------------------------------------------ *)

Goalw [diffs_def]  
      "diffs (%n. inverse(real (fact n))) = (%n. inverse(real (fact n)))";
by (rtac ext 1);
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac inverse_mult_distrib 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym]));
qed "exp_fdiffs";

Goalw [diffs_def,real_divide_def]
      "diffs(%n. if even n then 0 \
\          else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) \
\      = (%n. if even n then \
\                (- 1) ^ (n div 2)/(real (fact n)) \
\             else 0)";
by (rtac ext 1);
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac even_Suc 1);
by (stac inverse_mult_distrib 1);
by Auto_tac;
qed "sin_fdiffs";

Goalw  [diffs_def,real_divide_def]
       "diffs(%n. if even n then 0 \
\          else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) n \
\      = (if even n then \
\                (- 1) ^ (n div 2)/(real (fact n)) \
\             else 0)";
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac even_Suc 1);
by (stac inverse_mult_distrib 1);
by Auto_tac;
qed "sin_fdiffs2";

(* thms in EvenOdd needed *)
Goalw [diffs_def,real_divide_def]
      "diffs(%n. if even n then \
\                (- 1) ^ (n div 2)/(real (fact n)) else 0) \
\      = (%n. - (if even n then 0 \
\          else (- 1) ^ ((n - Suc 0)div 2)/(real (fact n))))";
by (rtac ext 1);
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac even_Suc 1);
by (stac inverse_mult_distrib 1);
by (res_inst_tac [("z1","real (Suc n)")] (real_mult_commute RS ssubst) 1);
by (res_inst_tac [("z1","inverse(real (Suc n))")] 
     (real_mult_commute RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc,
    odd_not_even RS sym,odd_Suc_mult_two_ex]));
qed "cos_fdiffs";


Goalw [diffs_def,real_divide_def]
      "diffs(%n. if even n then \
\                (- 1) ^ (n div 2)/(real (fact n)) else 0) n\
\      = - (if even n then 0 \
\          else (- 1) ^ ((n - Suc 0)div 2)/(real (fact n)))";
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac even_Suc 1);
by (stac inverse_mult_distrib 1);
by (res_inst_tac [("z1","real (Suc n)")] (real_mult_commute RS ssubst) 1);
by (res_inst_tac [("z1","inverse (real (Suc n))")] 
     (real_mult_commute RS ssubst) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc,
    odd_not_even RS sym,odd_Suc_mult_two_ex]));
qed "cos_fdiffs2";

(* ------------------------------------------------------------------------ *)
(* Now at last we can get the derivatives of exp, sin and cos               *)
(* ------------------------------------------------------------------------ *)

Goal "- sin x = suminf(%n. - ((if even n then 0 \
\    else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * x ^ n))";
by (auto_tac (claset() addSIs [sums_unique,sums_minus,sin_converges],
    simpset()));
qed "lemma_sin_minus";

Goal "exp = (%x. suminf (%n. inverse (real (fact n)) * x ^ n))";
by (auto_tac (claset() addSIs [ext],simpset() addsimps [exp_def]));
val lemma_exp_ext = result();

Goalw [exp_def] "DERIV exp x :> exp(x)";
by (stac lemma_exp_ext 1);
by (subgoal_tac "DERIV (%u. suminf (%n. inverse (real (fact n)) * u ^ n)) x \
\    :> suminf (%n. diffs (%n. inverse (real (fact n))) n * x ^ n)" 1);
by (res_inst_tac [("K","1 + abs(x)")] termdiffs 2);
by (auto_tac (claset() addIs [exp_converges RS sums_summable],
    simpset() addsimps [exp_fdiffs]));
by (arith_tac 1);
qed "DERIV_exp";
Addsimps [DERIV_exp];

Goal "sin = (%x. suminf(%n. (if even n then 0 \
\           else (- 1) ^ ((n - Suc 0) div 2)/(real (fact n))) * \
\                x ^ n))";
by (auto_tac (claset() addSIs [ext],simpset() addsimps [sin_def]));
val lemma_sin_ext = result();

Goal "cos = (%x. suminf(%n. (if even n then \
\          (- 1) ^ (n div 2)/(real (fact n)) \
\          else 0) * x ^ n))";
by (auto_tac (claset() addSIs [ext],simpset() addsimps [cos_def]));
val lemma_cos_ext = result();

Goalw [cos_def] "DERIV sin x :> cos(x)";
by (stac lemma_sin_ext 1);
by (auto_tac (claset(),simpset() addsimps [sin_fdiffs2 RS sym]));
by (res_inst_tac [("K","1 + abs(x)")] termdiffs 1);
by (auto_tac (claset() addIs [sin_converges, cos_converges, sums_summable] 
    addSIs [sums_minus RS sums_summable],
    simpset() addsimps [cos_fdiffs,sin_fdiffs]));
by (arith_tac 1);
qed "DERIV_sin";
Addsimps [DERIV_sin];

Goal "DERIV cos x :> -sin(x)";
by (stac lemma_cos_ext 1);
by (auto_tac (claset(),simpset() addsimps [lemma_sin_minus,
    cos_fdiffs2 RS sym,minus_mult_left]));
by (res_inst_tac [("K","1 + abs(x)")] termdiffs 1);
by (auto_tac (claset() addIs [sin_converges,cos_converges, sums_summable] 
    addSIs [sums_minus RS sums_summable],
    simpset() addsimps [cos_fdiffs,sin_fdiffs,diffs_minus]));
by (arith_tac 1);
qed "DERIV_cos";
Addsimps [DERIV_cos];

(* ------------------------------------------------------------------------ *)
(* Properties of the exponential function                                   *)
(* ------------------------------------------------------------------------ *)

Goalw [exp_def] "exp 0 = 1";
by (rtac (CLAIM_SIMP "sumr 0 1 (%n. inverse (real (fact n)) * 0 ^ n) = 1" 
           [real_of_nat_one] RS subst) 1);
by (rtac ((series_zero RS sums_unique) RS sym) 1);
by (Step_tac 1);
by (case_tac "m" 1);
by (Auto_tac);
qed "exp_zero";
Addsimps [exp_zero];

Goal "0 <= x ==> (1 + x) <= exp(x)";
by (dtac real_le_imp_less_or_eq 1 THEN Auto_tac);
by (rewtac exp_def);
by (rtac real_le_trans 1);
by (res_inst_tac [("n","2"),("f","(%n. inverse (real (fact n)) * x ^ n)")]
    series_pos_le 2);
by (auto_tac (claset() addIs [summable_exp],simpset()
    addsimps [numeral_2_eq_2,zero_le_power,zero_le_mult_iff]));
qed "exp_ge_add_one_self";
Addsimps [exp_ge_add_one_self];

Goal "0 < x ==> 1 < exp x";
by (rtac order_less_le_trans 1);
by (rtac exp_ge_add_one_self 2);
by (Auto_tac);
qed "exp_gt_one";
Addsimps [exp_gt_one];

Goal "DERIV (%x. exp (x + y)) x :> exp(x + y)";
by (auto_tac (claset(),simpset() addsimps 
    [CLAIM_SIMP "(%x. exp (x + y)) = exp o (%x. x + y)" [ext]]));
by (rtac (real_mult_1_right RS subst) 1);
by (rtac DERIV_chain 1);
by (rtac (add_zero_right RS subst) 2);
by (rtac DERIV_add 2);
by Auto_tac;
qed "DERIV_exp_add_const";
Addsimps [DERIV_exp_add_const];

Goal "DERIV (%x. exp (-x)) x :> - exp(-x)";
by (auto_tac (claset(),simpset() addsimps
    [CLAIM_SIMP "(%x. exp(-x)) = exp o (%x. - x)" [ext]]));
by (rtac (real_mult_1_right RS subst) 1);
by (rtac (minus_mult_left RS subst) 1);
by (stac minus_mult_right 1);
by (rtac DERIV_chain 1);
by (rtac DERIV_minus 2);
by Auto_tac;
qed "DERIV_exp_minus";
Addsimps [DERIV_exp_minus];

Goal "DERIV (%x. exp (x + y) * exp (- x)) x :> 0";
by (cut_inst_tac [("x","x"),("y2","y")] ([DERIV_exp_add_const,
    DERIV_exp_minus] MRS DERIV_mult) 1);
by (auto_tac (claset(),simpset() addsimps mult_ac));
qed "DERIV_exp_exp_zero";
Addsimps [DERIV_exp_exp_zero];

Goal "exp(x + y)*exp(-x) = exp(y)";
by (cut_inst_tac [("x","x"),("y2","y"),("y","0")] 
    ((CLAIM "ALL x. DERIV (%x. exp (x + y) * exp (- x)) x :> 0") RS
      DERIV_isconst_all) 1);
by (Auto_tac);
qed "exp_add_mult_minus";
Addsimps [exp_add_mult_minus];

Goal "exp(x)*exp(-x) = 1";
by (cut_inst_tac [("x","x"),("y","0")] exp_add_mult_minus 1);
by (Asm_full_simp_tac 1);
qed "exp_mult_minus";
Addsimps [exp_mult_minus];

Goal "exp(-x)*exp(x) = 1";
by (simp_tac (simpset() addsimps [real_mult_commute]) 1);
qed "exp_mult_minus2";
Addsimps [exp_mult_minus2];

Goal "exp(-x) = inverse(exp(x))";
by (auto_tac (claset() addIs [real_inverse_unique],simpset()));
qed "exp_minus";

Goal "exp(x + y) = exp(x) * exp(y)";
by (cut_inst_tac [("x1","x"),("y1","y"),("z","exp x")] 
    (exp_add_mult_minus RS (CLAIM "x = y ==> z * y = z * (x::real)")) 1);
by (asm_full_simp_tac HOL_ss 1);
by (asm_full_simp_tac (simpset() delsimps [exp_add_mult_minus] 
    addsimps mult_ac) 1);
qed "exp_add";

Goal "0 <= exp x";
by (res_inst_tac [("t","x")] (real_sum_of_halves RS subst) 1);
by (stac exp_add 1 THEN Auto_tac);
qed "exp_ge_zero";
Addsimps [exp_ge_zero];

Goal "exp x ~= 0";
by (cut_inst_tac [("x","x")] exp_mult_minus2 1);
by (auto_tac (claset(),simpset() delsimps [exp_mult_minus2]));
qed "exp_not_eq_zero";
Addsimps [exp_not_eq_zero];

Goal "0 < exp x";
by (simp_tac (simpset() addsimps 
    [CLAIM_SIMP "(x < y) = (x <= y & y ~= (x::real))" [real_le_less]]) 1);
qed "exp_gt_zero";
Addsimps [exp_gt_zero];

Goal "0 < inverse(exp x)";
by (auto_tac (claset() addIs [positive_imp_inverse_positive],simpset()));
qed "inv_exp_gt_zero";
Addsimps [inv_exp_gt_zero];

Goal "abs(exp x) = exp x";
by (auto_tac (claset(),simpset() addsimps [abs_eqI2]));
qed "abs_exp_cancel";
Addsimps [abs_exp_cancel];

Goal "exp(real n * x) = exp(x) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc,
    right_distrib,exp_add,real_mult_commute]));
qed "exp_real_of_nat_mult";

Goalw [real_diff_def,real_divide_def] 
       "exp(x - y) = exp(x)/(exp y)";
by (simp_tac (simpset() addsimps [exp_add,exp_minus]) 1);
qed "exp_diff";

Goal "x < y ==> exp x < exp y";
by (dtac ((real_less_sum_gt_zero) RS exp_gt_one) 1);
by (multr_by_tac "inverse(exp x)" 1);
by (auto_tac (claset(),simpset() addsimps [exp_add,exp_minus]));
qed "exp_less_mono";

Goal "exp x < exp y ==> x < y";
by (EVERY1[rtac ccontr, dtac (linorder_not_less RS iffD1), dtac real_le_imp_less_or_eq]);
by (auto_tac (claset() addDs [exp_less_mono],simpset()));
qed "exp_less_cancel";

Goal "(exp(x) < exp(y)) = (x < y)";
by (auto_tac (claset() addIs [exp_less_mono,exp_less_cancel],simpset()));
qed "exp_less_cancel_iff";
AddIffs [exp_less_cancel_iff];

Goalw [real_le_def] "(exp(x) <= exp(y)) = (x <= y)";
by (Auto_tac);
qed "exp_le_cancel_iff";
AddIffs [exp_le_cancel_iff];

Goal "(exp x = exp y) = (x = y)";
by (auto_tac (claset(),simpset() addsimps 
    [CLAIM "(x = (y::real)) = (x <= y & y <= x)"]));
qed "exp_inj_iff";
AddIffs [exp_inj_iff];

Goal "1 <= y ==> EX x. 0 <= x & x <= y - 1 & exp(x) = y";
by (rtac IVT 1);
by (auto_tac (claset() addIs [DERIV_exp RS DERIV_isCont],
              simpset() addsimps [le_diff_eq]));
by (dtac (CLAIM_SIMP "x <= y ==> (0::real) <= y - x" [le_diff_eq]) 1);
by (dtac exp_ge_add_one_self 1);
by (Asm_full_simp_tac 1);
qed "lemma_exp_total";

Goal "0 < y ==> EX x. exp x = y";
by (res_inst_tac [("R1.0","1"),("R2.0","y")] real_linear_less2 1);
by (dtac (order_less_imp_le RS lemma_exp_total) 1);
by (res_inst_tac [("x","0")] exI 2);
by (ftac real_inverse_gt_one 3);
by (dtac (order_less_imp_le RS lemma_exp_total) 4);
by (Step_tac 3);
by (res_inst_tac [("x","-x")] exI 3);
by (auto_tac (claset(),simpset() addsimps [exp_minus]));
qed "exp_total";

(* ------------------------------------------------------------------------ *)
(* Properties of the logarithmic function                                   *)
(* ------------------------------------------------------------------------ *)

Goalw [ln_def] "ln(exp x) = x";
by (Simp_tac 1);
qed "ln_exp";
Addsimps [ln_exp];

Goal "(exp(ln x) = x) = (0 < x)";
by (auto_tac (claset() addDs [exp_total],simpset()));
by (dtac subst 1);
by (Auto_tac);
qed "exp_ln_iff";
Addsimps [exp_ln_iff];

Goal "[| 0 < x; 0 < y |] ==> ln(x * y) = ln(x) + ln(y)";
by (rtac (exp_inj_iff RS iffD1) 1);
by (ftac (real_mult_order) 1);
by (auto_tac (claset(),simpset() addsimps [exp_add,exp_ln_iff RS sym] 
    delsimps [exp_inj_iff,exp_ln_iff]));
qed "ln_mult";

Goal "[| 0 < x; 0 < y |] ==> (ln x = ln y) = (x = y)";
by (auto_tac (claset() addSDs [(exp_ln_iff RS iffD2 RS sym)],simpset()));
qed "ln_inj_iff";
Addsimps [ln_inj_iff];

Goal "ln 1 = 0";
by (rtac (exp_inj_iff RS iffD1) 1);
by Auto_tac;
qed "ln_one";
Addsimps [ln_one];

Goal "0 < x ==> ln(inverse x) = - ln x";
by (res_inst_tac [("a1","ln x")] (add_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [positive_imp_inverse_positive,ln_mult RS sym]));
qed "ln_inverse";

Goalw [real_divide_def]
    "[|0 < x; 0 < y|] ==> ln(x/y) = ln x - ln y";
by (auto_tac (claset(),simpset() addsimps [positive_imp_inverse_positive,
    ln_mult,ln_inverse]));
qed "ln_div";

Goal "[| 0 < x; 0 < y|] ==> (ln x < ln y) = (x < y)";
by (REPEAT(dtac (exp_ln_iff RS iffD2) 1));
by (REPEAT(dtac subst 1 THEN assume_tac 2));
by (Simp_tac 1);
qed "ln_less_cancel_iff";
Addsimps [ln_less_cancel_iff];

Goalw [real_le_def] "[| 0 < x; 0 < y|] ==> (ln x <= ln y) = (x <= y)";
by (Auto_tac);
qed "ln_le_cancel_iff";
Addsimps [ln_le_cancel_iff];

Goal "0 < x ==> ln(x ^ n) = real n * ln(x)";
by (auto_tac (claset() addSDs [exp_total],simpset() 
    addsimps [exp_real_of_nat_mult RS sym]));
qed "ln_realpow";

Goal "0 <= x ==> ln(1 + x) <= x";
by (rtac (ln_exp RS subst) 1);
by (rtac (ln_le_cancel_iff RS iffD2) 1);
by Auto_tac;
qed "ln_add_one_self_le_self";
Addsimps [ln_add_one_self_le_self];

Goal "0 < x ==> ln x < x";
by (rtac order_less_le_trans 1);
by (rtac ln_add_one_self_le_self 2);
by (rtac (ln_less_cancel_iff RS iffD2) 1);
by Auto_tac;
qed "ln_less_self";
Addsimps [ln_less_self];

Goal "1 <= x ==> 0 <= ln x";
by (subgoal_tac "0 < x" 1);
by (rtac order_less_le_trans 2 THEN assume_tac 3);
by (rtac (exp_le_cancel_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps 
    [exp_ln_iff RS sym] delsimps [exp_ln_iff]));
qed "ln_ge_zero";
Addsimps [ln_ge_zero];

Goal "1 < x ==> 0 < ln x";
by (rtac (exp_less_cancel_iff RS iffD1) 1);
by (rtac (exp_ln_iff RS iffD2 RS ssubst) 1);
by Auto_tac;
qed "ln_gt_zero";
Addsimps [ln_gt_zero];

Goal "[| 0 < x; x ~= 1 |] ==> ln x ~= 0";
by (Step_tac 1);
by (dtac (exp_inj_iff RS iffD2) 1);
by (dtac (exp_ln_iff RS iffD2) 1);
by Auto_tac;
qed "ln_not_eq_zero";
Addsimps [ln_not_eq_zero];

Goal "[| 0 < x; x < 1 |] ==> ln x < 0";
by (rtac (exp_less_cancel_iff RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [exp_ln_iff RS sym]
    delsimps [exp_ln_iff]));
qed "ln_less_zero";

Goal "exp u = x ==> ln x = u";
by Auto_tac;
qed "exp_ln_eq";

Addsimps [hypreal_less_not_refl];

(* ------------------------------------------------------------------------ *)
(* Basic properties of the trig functions                                   *)
(* ------------------------------------------------------------------------ *)

Goalw [sin_def] "sin 0 = 0";
by (auto_tac (claset() addSIs [sums_unique RS sym, LIMSEQ_const],
              simpset() addsimps [sums_def] delsimps [power_0_left]));
qed "sin_zero";
Addsimps [sin_zero];

Goal "(ALL m. n <= m --> f m = 0) --> f sums sumr 0 n f";
by (auto_tac (claset() addIs [series_zero],simpset()));
qed "lemma_series_zero2";

Goalw [cos_def] "cos 0 = 1";
by (rtac (sums_unique RS sym) 1);
by (cut_inst_tac [("n","1"),("f","(%n. (if even n then (- 1) ^ (n div 2)/ \
\   (real (fact n)) else 0) * 0 ^ n)")] lemma_series_zero2 1);
by Auto_tac;
qed "cos_zero";
Addsimps [cos_zero];

Goal "DERIV (%x. sin(x)*sin(x)) x :> cos(x) * sin(x) + cos(x) * sin(x)";
by (rtac DERIV_mult 1 THEN Auto_tac);
qed "DERIV_sin_sin_mult";
Addsimps [DERIV_sin_sin_mult];

Goal "DERIV (%x. sin(x)*sin(x)) x :> 2 * cos(x) * sin(x)";
by (cut_inst_tac [("x","x")] DERIV_sin_sin_mult 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc]));
qed "DERIV_sin_sin_mult2";
Addsimps [DERIV_sin_sin_mult2];

Goal "DERIV (%x. sin(x) ^ 2) x :> cos(x) * sin(x) + cos(x) * sin(x)";
by (auto_tac (claset(),
              simpset() addsimps [numeral_2_eq_2, real_mult_assoc RS sym]));
qed "DERIV_sin_realpow2";
Addsimps [DERIV_sin_realpow2];

Goal "DERIV (%x. sin(x) ^ 2) x :> 2 * cos(x) * sin(x)";
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "DERIV_sin_realpow2a";
Addsimps [ DERIV_sin_realpow2a];

Goal "DERIV (%x. cos(x)*cos(x)) x :> -sin(x) * cos(x) + -sin(x) * cos(x)";
by (rtac DERIV_mult 1 THEN Auto_tac);
qed "DERIV_cos_cos_mult";
Addsimps [DERIV_cos_cos_mult];

Goal "DERIV (%x. cos(x)*cos(x)) x :> -2 * cos(x) * sin(x)";
by (cut_inst_tac [("x","x")] DERIV_cos_cos_mult 1);
by (auto_tac (claset(),simpset() addsimps mult_ac));
qed "DERIV_cos_cos_mult2";
Addsimps [DERIV_cos_cos_mult2];

Goal "DERIV (%x. cos(x) ^ 2) x :> -sin(x) * cos(x) + -sin(x) * cos(x)";
by (auto_tac (claset(),
              simpset() addsimps [numeral_2_eq_2, real_mult_assoc RS sym]));
qed "DERIV_cos_realpow2";
Addsimps [DERIV_cos_realpow2];

Goal "DERIV (%x. cos(x) ^ 2) x :> -2 * cos(x) * sin(x)";
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "DERIV_cos_realpow2a";
Addsimps [DERIV_cos_realpow2a];

Goal "[| DERIV f x :> D; D = E |] ==> DERIV f x :> E";
by (Auto_tac);
val lemma_DERIV_subst = result();

Goal "DERIV (%x. cos(x) ^ 2) x :> -(2 * cos(x) * sin(x))";
by (rtac lemma_DERIV_subst 1);
by (rtac DERIV_cos_realpow2a 1);
by Auto_tac;
qed "DERIV_cos_realpow2b";

(* most useful *)
Goal "DERIV (%x. cos(x)*cos(x)) x :> -(2 * cos(x) * sin(x))";
by (rtac lemma_DERIV_subst 1);
by (rtac DERIV_cos_cos_mult2 1);
by Auto_tac;
qed "DERIV_cos_cos_mult3";
Addsimps [DERIV_cos_cos_mult3];

Goalw [real_diff_def] 
     "ALL x. DERIV (%x. sin(x) ^ 2 + cos(x) ^ 2) x :> \
\            (2*cos(x)*sin(x) - 2*cos(x)*sin(x))";
by (Step_tac 1);
by (rtac DERIV_add 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "DERIV_sin_circle_all";

Goal "ALL x. DERIV (%x. sin(x) ^ 2 + cos(x) ^ 2) x :> 0";
by (cut_facts_tac [DERIV_sin_circle_all] 1);
by Auto_tac;
qed "DERIV_sin_circle_all_zero";
Addsimps [DERIV_sin_circle_all_zero];

Goal "(sin(x) ^ 2) + (cos(x) ^ 2) = 1";
by (cut_inst_tac [("x","x"),("y","0")] 
    (DERIV_sin_circle_all_zero RS DERIV_isconst_all) 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "sin_cos_squared_add";
Addsimps [sin_cos_squared_add];

Goal "(cos(x) ^ 2) + (sin(x) ^ 2) = 1";
by (stac real_add_commute 1);
by (simp_tac (simpset() delsimps [realpow_Suc]) 1);
qed "sin_cos_squared_add2";
Addsimps [sin_cos_squared_add2];

Goal "cos x * cos x + sin x * sin x = 1";
by (cut_inst_tac [("x","x")] sin_cos_squared_add2 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "sin_cos_squared_add3";
Addsimps [sin_cos_squared_add3];

Goal "(sin(x) ^ 2) = 1 - (cos(x) ^ 2)";
by (res_inst_tac [("a1","(cos(x) ^ 2)")] (add_right_cancel RS iffD1) 1);
by (simp_tac (simpset() delsimps [realpow_Suc]) 1);
qed "sin_squared_eq";

Goal "(cos(x) ^ 2) = 1 - (sin(x) ^ 2)";
by (res_inst_tac [("a1","(sin(x) ^ 2)")] (add_right_cancel RS iffD1) 1);
by (simp_tac (simpset() delsimps [realpow_Suc]) 1);
qed "cos_squared_eq";

Goal "[| 1 < x; 0 <= y |] ==> 1 < x + (y::real)";
by (arith_tac 1);
qed "real_gt_one_ge_zero_add_less";

Goalw [real_le_def] "abs(sin x) <= 1";
by (rtac notI 1);
by (dres_inst_tac [("n","Suc 0")] power_gt1 1); 
by (auto_tac (claset(),simpset() delsimps [realpow_Suc]));
by (dres_inst_tac [("r1","cos x")] (realpow_two_le RSN 
    (2, real_gt_one_ge_zero_add_less)) 1);
by (asm_full_simp_tac (simpset() addsimps [numeral_2_eq_2 RS sym]
				 delsimps [realpow_Suc]) 1);
qed "abs_sin_le_one";
Addsimps [abs_sin_le_one];

Goal "- 1 <= sin x";
by (full_simp_tac (simpset() addsimps [simplify (simpset()) (abs_sin_le_one RS 
    (abs_le_interval_iff RS iffD1))]) 1);
qed "sin_ge_minus_one";
Addsimps [sin_ge_minus_one];

Goal "-1 <= sin x";
by (rtac (simplify (simpset()) sin_ge_minus_one) 1);
qed "sin_ge_minus_one2";
Addsimps [sin_ge_minus_one2];

Goal "sin x <= 1";
by (full_simp_tac (simpset() addsimps [abs_sin_le_one RS 
    (abs_le_interval_iff RS iffD1)]) 1);
qed "sin_le_one";
Addsimps [sin_le_one];

Goalw [real_le_def] "abs(cos x) <= 1";
by (rtac notI 1);
by (dres_inst_tac [("n","Suc 0")] power_gt1 1); 
by (auto_tac (claset(),simpset() delsimps [realpow_Suc]));
by (dres_inst_tac [("r1","sin x")] (realpow_two_le RSN 
    (2, real_gt_one_ge_zero_add_less)) 1);
by (asm_full_simp_tac (simpset() addsimps [numeral_2_eq_2 RS sym]
				 delsimps [realpow_Suc]) 1);
qed "abs_cos_le_one";
Addsimps [abs_cos_le_one];

Goal "- 1 <= cos x";
by (full_simp_tac (simpset() addsimps [simplify (simpset())(abs_cos_le_one RS 
    (abs_le_interval_iff RS iffD1))]) 1);
qed "cos_ge_minus_one";
Addsimps [cos_ge_minus_one];

Goal "-1 <= cos x";
by (rtac (simplify (simpset()) cos_ge_minus_one) 1);
qed "cos_ge_minus_one2";
Addsimps [cos_ge_minus_one2];

Goal "cos x <= 1";
by (full_simp_tac (simpset() addsimps [abs_cos_le_one RS 
    (abs_le_interval_iff RS iffD1)]) 1);
qed "cos_le_one";
Addsimps [cos_le_one];

Goal "DERIV g x :> m ==> \
\     DERIV (%x. (g x) ^ n) x :> real n * (g x) ^ (n - 1) * m";
by (rtac lemma_DERIV_subst 1);
by (res_inst_tac [("f","(%x. x ^ n)")] DERIV_chain2 1);
by (rtac DERIV_pow 1 THEN Auto_tac);
qed "DERIV_fun_pow";

Goal "DERIV g x :> m ==> DERIV (%x. exp(g x)) x :> exp(g x) * m";
by (rtac lemma_DERIV_subst 1);
by (res_inst_tac [("f","exp")] DERIV_chain2 1);
by (rtac DERIV_exp 1 THEN Auto_tac);
qed "DERIV_fun_exp";

Goal "DERIV g x :> m ==> DERIV (%x. sin(g x)) x :> cos(g x) * m";
by (rtac lemma_DERIV_subst 1);
by (res_inst_tac [("f","sin")] DERIV_chain2 1);
by (rtac DERIV_sin 1 THEN Auto_tac);
qed "DERIV_fun_sin";

Goal "DERIV g x :> m ==> DERIV (%x. cos(g x)) x :> -sin(g x) * m";
by (rtac lemma_DERIV_subst 1);
by (res_inst_tac [("f","cos")] DERIV_chain2 1);
by (rtac DERIV_cos 1 THEN Auto_tac);
qed "DERIV_fun_cos";

(* FIXME: remove this quick, crude tactic *)
exception DERIV_name;
fun get_fun_name (_ $ (Const ("Lim.deriv",_) $ Abs(_,_, Const (f,_) $ _) $ _ $ _)) = f
|   get_fun_name (_ $ (_ $ (Const ("Lim.deriv",_) $ Abs(_,_, Const (f,_) $ _) $ _ $ _))) = f
|   get_fun_name _ = raise DERIV_name;

val deriv_rulesI = [DERIV_Id,DERIV_const,DERIV_cos,DERIV_cmult,
                    DERIV_sin, DERIV_exp, DERIV_inverse,DERIV_pow,
                    DERIV_add, DERIV_diff, DERIV_mult, DERIV_minus,
                    DERIV_inverse_fun,DERIV_quotient,DERIV_fun_pow,
                    DERIV_fun_exp,DERIV_fun_sin,DERIV_fun_cos,
                    DERIV_Id,DERIV_const,DERIV_cos];


fun deriv_tac i = (resolve_tac deriv_rulesI i) ORELSE 
                   ((rtac (read_instantiate [("f",get_fun_name (getgoal i))] 
                     DERIV_chain2) i) handle DERIV_name => no_tac);

val DERIV_tac = ALLGOALS(fn i => REPEAT(deriv_tac i));

(* lemma *)
Goal "ALL x. \
\        DERIV (%x. (sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 + \
\              (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2) x :> 0";
by (Step_tac 1 THEN rtac lemma_DERIV_subst 1);
by DERIV_tac;
by (auto_tac (claset(),simpset() addsimps [real_diff_def,
    left_distrib,right_distrib] @ 
    mult_ac @ add_ac));
val lemma_DERIV_sin_cos_add = result();

Goal "(sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 + \
\     (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2 = 0";
by (cut_inst_tac [("y","0"),("x","x"),("y7","y")] 
    (lemma_DERIV_sin_cos_add RS DERIV_isconst_all) 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "sin_cos_add";
Addsimps [sin_cos_add];

Goal "sin (x + y) = sin x * cos y + cos x * sin y";
by (cut_inst_tac [("x","x"),("y","y")] sin_cos_add 1); 
by (auto_tac (claset() addSDs [real_sum_squares_cancel_a],
         simpset()  addsimps [numeral_2_eq_2] delsimps [sin_cos_add]));
qed "sin_add";

Goal "cos (x + y) = cos x * cos y - sin x * sin y";
by (cut_inst_tac [("x","x"),("y","y")] sin_cos_add 1);
by (auto_tac (claset() addSDs [real_sum_squares_cancel_a],simpset() addsimps [numeral_2_eq_2] delsimps [sin_cos_add]));
qed "cos_add";

Goal "ALL x. \
\         DERIV (%x. (sin(-x) + (sin x)) ^ 2 + (cos(-x) - (cos x)) ^ 2) x :> 0";
by (Step_tac 1 THEN rtac lemma_DERIV_subst 1);
by DERIV_tac;
by (auto_tac (claset(),simpset() addsimps [real_diff_def,
    left_distrib,right_distrib]
    @ mult_ac @ add_ac));
val lemma_DERIV_sin_cos_minus = result();

Goal "(sin(-x) + (sin x)) ^ 2 + (cos(-x) - (cos x)) ^ 2 = 0";
by (cut_inst_tac [("y","0"),("x","x")] 
    (lemma_DERIV_sin_cos_minus RS DERIV_isconst_all) 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "sin_cos_minus";
Addsimps [sin_cos_minus];

Goal "sin (-x) = -sin(x)";
by (cut_inst_tac [("x","x")] sin_cos_minus 1);
by (auto_tac (claset() addSDs [real_sum_squares_cancel_a],
              simpset() addsimps [numeral_2_eq_2] delsimps [sin_cos_minus]));
qed "sin_minus";
Addsimps [sin_minus];

Goal "cos (-x) = cos(x)";
by (cut_inst_tac [("x","x")] sin_cos_minus 1);
by (auto_tac (claset() addSDs [real_sum_squares_cancel_a],
              simpset() addsimps [numeral_2_eq_2] delsimps [sin_cos_minus]));
qed "cos_minus";
Addsimps [cos_minus];

Goalw [real_diff_def] "sin (x - y) = sin x * cos y - cos x * sin y";
by (simp_tac (simpset() addsimps [sin_add]) 1);
qed "sin_diff";

Goal "sin (x - y) = cos y * sin x - sin y * cos x";
by (simp_tac (simpset() addsimps [sin_diff,real_mult_commute]) 1);
qed "sin_diff2";

Goalw [real_diff_def] "cos (x - y) = cos x * cos y + sin x * sin y";
by (simp_tac (simpset() addsimps [cos_add]) 1);
qed "cos_diff";

Goal "cos (x - y) = cos y * cos x + sin y * sin x";
by (simp_tac (simpset() addsimps [cos_diff,real_mult_commute]) 1);
qed "cos_diff2";

Goal "sin(2 * x) = 2* sin x * cos x";
by (cut_inst_tac [("x","x"),("y","x")] sin_add 1);
by Auto_tac;
qed "sin_double";

Addsimps [sin_double];

Goal "cos(2* x) = (cos(x) ^ 2) - (sin(x) ^ 2)";
by (cut_inst_tac [("x","x"),("y","x")] cos_add 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "cos_double";

(* ------------------------------------------------------------------------ *)
(* Show that there's a least positive x with cos(x) = 0; hence define pi    *)
(* ------------------------------------------------------------------------ *)

Goal "(%n. (- 1) ^ n /(real (fact (2 * n + 1))) * \
\      x ^ (2 * n + 1)) sums  sin x";
by (cut_inst_tac [("x2","x")] (CLAIM "0 < (2::nat)" RS ((sin_converges 
    RS sums_summable) RS sums_group)) 1);
by (auto_tac (claset(),simpset() addsimps mult_ac@[sin_def]));
qed "sin_paired";

Goal "real (Suc (Suc (Suc (Suc 2)))) = \
\     real (2::nat) * real (Suc 2)";
by (simp_tac (simpset() addsimps [numeral_2_eq_2, real_of_nat_Suc]) 1);
val lemma_real_of_nat_six_mult = result();

Goal "[|0 < x; x < 2 |] ==> 0 < sin x";
by (cut_inst_tac [("x2","x")] (CLAIM "0 < (2::nat)" RS ((sin_paired
    RS sums_summable) RS sums_group)) 1);
by (rotate_tac 2 1);
by (dtac ((sin_paired RS sums_unique) RS ssubst) 1);
by (auto_tac (claset(),simpset() delsimps [fact_Suc,realpow_Suc]));
by (ftac sums_unique 1);
by (auto_tac (claset(),simpset() delsimps [fact_Suc,realpow_Suc]));
by (res_inst_tac [("n1","0")] (series_pos_less RSN (2,order_le_less_trans)) 1);
by (auto_tac (claset(),simpset() delsimps [fact_Suc,realpow_Suc]));
by (etac sums_summable 1);
by (case_tac "m=0" 1);
by (Asm_simp_tac 1);
by (subgoal_tac "6 * (x * (x * x) / real (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) < 6 * x" 1); 
by (asm_full_simp_tac (HOL_ss addsimps [mult_less_cancel_left]) 1); 
by (asm_full_simp_tac (simpset() addsimps []) 1); 
by (asm_simp_tac (simpset() addsimps [numeral_2_eq_2 RS sym, real_mult_assoc RS sym]) 1);
by (stac (CLAIM "6 = 2 * (3::real)") 1);
by (rtac real_mult_less_mono 1); (*mult_strict_mono would be stronger*)  
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc] delsimps [fact_Suc]));
by (stac fact_Suc 1);
by (stac fact_Suc 1);
by (stac fact_Suc 1);
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac real_of_nat_mult 1);
by (stac real_of_nat_mult 1);
by (stac real_of_nat_mult 1);
by (simp_tac (simpset() addsimps [real_divide_def,
    inverse_mult_distrib] delsimps [fact_Suc]) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym] 
    delsimps [fact_Suc]));
by (multr_by_tac "real (Suc (Suc (4*m)))" 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc] 
    delsimps [fact_Suc]));
by (multr_by_tac "real (Suc (Suc (Suc (4*m))))" 1);
by (auto_tac (claset(),simpset() addsimps [mult_assoc,mult_less_cancel_left] 
    delsimps [fact_Suc]));
by (auto_tac (claset(),simpset() addsimps [
        CLAIM "x * (x * x ^ (4*m)) = (x ^ (4*m)) * (x * (x::real))"] 
    delsimps [fact_Suc]));
by (subgoal_tac "0 < x ^ (4 * m)" 1);
by (asm_simp_tac (simpset() addsimps [zero_less_power]) 2); 
by (asm_simp_tac (simpset() addsimps [mult_less_cancel_left]) 1); 
by (rtac real_mult_less_mono 1); (*mult_strict_mono would be stronger*)
by (ALLGOALS(Asm_simp_tac));
by (TRYALL(rtac real_less_trans));
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc] delsimps [fact_Suc]));
by (res_inst_tac [("y","0")] order_less_le_trans 1);
by (ALLGOALS(Asm_simp_tac));
qed "sin_gt_zero";

Goal "[|0 < x; x < 2 |] ==> 0 < sin x";
by (auto_tac (claset() addIs [sin_gt_zero],simpset()));
qed "sin_gt_zero1";

Goal "[| 0 < x; x < 2 |] ==> cos (2 * x) < 1";
by (auto_tac (claset(),
    simpset() addsimps [cos_squared_eq,
    minus_add_distrib RS sym, neg_less_0_iff_less,sin_gt_zero1,
    real_add_order,zero_less_power,cos_double] 
    delsimps [realpow_Suc,minus_add_distrib]));
qed "cos_double_less_one";

Goal  "(%n. (- 1) ^ n /(real (fact (2 * n))) * x ^ (2 * n)) \
\      sums cos x";
by (cut_inst_tac [("x2","x")] (CLAIM "0 < (2::nat)" RS ((cos_converges 
    RS sums_summable) RS sums_group)) 1);
by (auto_tac (claset(),simpset() addsimps  mult_ac@[cos_def]));
qed "cos_paired";

Addsimps [zero_less_power];

Goal "cos (2) < 0";
by (cut_inst_tac [("x","2")] cos_paired 1);
by (dtac sums_minus 1);
by (rtac (CLAIM "- x < -y ==> (y::real) < x") 1);
by (ftac sums_unique 1 THEN Auto_tac);
by (res_inst_tac [("R2.0",
    "sumr 0 (Suc (Suc (Suc 0))) (%n. -((- 1) ^ n /(real (fact(2 * n))) \
\               * 2 ^ (2 * n)))")] real_less_trans 1);
by (simp_tac (simpset() addsimps [fact_num_eq_if,realpow_num_eq_if] 
    delsimps [fact_Suc,realpow_Suc]) 1);
by (simp_tac (simpset() addsimps [real_mult_assoc] 
    delsimps [sumr_Suc]) 1);
by (rtac sumr_pos_lt_pair 1);
by (etac sums_summable 1);
by (Step_tac 1);
by (simp_tac (simpset() addsimps [real_divide_def,real_mult_assoc RS sym] 
    delsimps [fact_Suc]) 1);
by (rtac real_mult_inverse_cancel2 1);
by (TRYALL(rtac (real_of_nat_fact_gt_zero)));
by (simp_tac (simpset() addsimps [real_mult_assoc RS sym] 
    delsimps [fact_Suc]) 1);
by (rtac ((CLAIM "real(n::nat) * 4 = real(4 * n)") RS ssubst) 1);
by (stac fact_Suc 1);
by (stac real_of_nat_mult 1);
by (stac real_of_nat_mult 1);
by (rtac real_mult_less_mono 1); (*mult_strict_mono would be stronger*)
by (Force_tac 1);
by (Force_tac 2);
by (rtac real_of_nat_fact_gt_zero 2);
by (rtac (real_of_nat_less_iff RS iffD2) 1);
by (rtac fact_less_mono 1);
by Auto_tac;
qed "cos_two_less_zero";
Addsimps [cos_two_less_zero];
Addsimps [cos_two_less_zero RS real_not_refl2];
Addsimps [cos_two_less_zero RS order_less_imp_le];

Goal "EX! x. 0 <= x & x <= 2 & cos x = 0";
by (subgoal_tac "EX x.  0 <= x & x <= 2 & cos x = 0" 1);
by (rtac IVT2  2);
by (auto_tac (claset() addIs [DERIV_isCont,DERIV_cos],simpset ()));
by (cut_inst_tac [("x","xa"),("y","y")] linorder_less_linear 1);
by (rtac ccontr 1);
by (subgoal_tac "(ALL x. cos differentiable x) & \
\   (ALL x. isCont cos x)" 1);
by (auto_tac (claset() addIs [DERIV_cos,DERIV_isCont],simpset() 
    addsimps [differentiable_def]));
by (dres_inst_tac [("f","cos")] Rolle 1);
by (dres_inst_tac [("f","cos")] Rolle 5);
by (auto_tac (claset() addSDs [DERIV_cos RS DERIV_unique],
    simpset() addsimps [differentiable_def]));
by (dres_inst_tac [("y1","xa")] (order_le_less_trans RS sin_gt_zero) 1);
by (assume_tac 1 THEN rtac order_less_le_trans 1);
by (dres_inst_tac [("y1","y")] (order_le_less_trans RS sin_gt_zero) 4);
by (assume_tac 4 THEN rtac order_less_le_trans 4);
by (assume_tac 1 THEN assume_tac 3);
by (ALLGOALS (Asm_full_simp_tac));
qed "cos_is_zero";
    
Goalw [pi_def] "pi/2 = (@x. 0 <= x & x <= 2 & cos x = 0)";
by Auto_tac;
qed "pi_half";

Goal "cos (pi / 2) = 0";
by (rtac (cos_is_zero RS ex1E) 1);
by (auto_tac (claset() addSIs [someI2],
    simpset() addsimps [pi_half]));
qed "cos_pi_half";
Addsimps [cos_pi_half];

Goal "0 < pi / 2";
by (rtac (cos_is_zero RS ex1E) 1);
by (auto_tac (claset(),simpset() addsimps [pi_half]));
by (rtac someI2 1);
by (Blast_tac 1);
by (Step_tac 1);
by (dres_inst_tac [("y","xa")] real_le_imp_less_or_eq 1);
by (Step_tac 1 THEN Asm_full_simp_tac 1);
qed "pi_half_gt_zero";
Addsimps [pi_half_gt_zero];
Addsimps [(pi_half_gt_zero RS real_not_refl2) RS not_sym];
Addsimps [pi_half_gt_zero RS order_less_imp_le];

Goal "pi / 2 < 2";
by (rtac (cos_is_zero RS ex1E) 1);
by (auto_tac (claset(),simpset() addsimps [pi_half]));
by (rtac someI2 1);
by (Blast_tac 1);
by (Step_tac 1);
by (dres_inst_tac [("x","xa")] order_le_imp_less_or_eq 1);
by (Step_tac 1 THEN Asm_full_simp_tac 1);
qed "pi_half_less_two";
Addsimps [pi_half_less_two];
Addsimps [pi_half_less_two RS real_not_refl2];
Addsimps [pi_half_less_two RS order_less_imp_le];

Goal "0 < pi";
by (multr_by_tac "inverse 2" 1);
by (Simp_tac 1);
by (cut_facts_tac [pi_half_gt_zero] 1);
by (full_simp_tac (HOL_ss addsimps [thm"mult_left_zero", real_divide_def]) 1);
qed "pi_gt_zero";
Addsimps [pi_gt_zero];
Addsimps [(pi_gt_zero RS real_not_refl2) RS not_sym];
Addsimps [pi_gt_zero RS CLAIM "(x::real) < y ==> ~ y < x"];

Goal "0 <= pi";
by (auto_tac (claset() addIs [order_less_imp_le],simpset()));
qed "pi_ge_zero";
Addsimps [pi_ge_zero];

Goal "-(pi/2) < 0";
by Auto_tac;
qed "minus_pi_half_less_zero";
Addsimps [minus_pi_half_less_zero];

Goal "sin(pi/2) = 1";
by (cut_inst_tac [("x","pi/2")] sin_cos_squared_add2 1);
by (cut_facts_tac [[pi_half_gt_zero,pi_half_less_two] MRS sin_gt_zero] 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "sin_pi_half";
Addsimps [sin_pi_half];

Goal "cos pi = - 1";
by (cut_inst_tac [("x","pi/2"),("y","pi/2")] cos_add 1);
by (Asm_full_simp_tac 1);
qed "cos_pi";
Addsimps [cos_pi];

Goal "sin pi = 0";
by (cut_inst_tac [("x","pi/2"),("y","pi/2")] sin_add 1);
by (Asm_full_simp_tac 1);
qed "sin_pi";
Addsimps [sin_pi];

Goalw [real_diff_def] "sin x = cos (pi/2 - x)";
by (simp_tac (simpset() addsimps [cos_add]) 1);
qed "sin_cos_eq";

Goal "-sin x = cos (x + pi/2)";
by (simp_tac (simpset() addsimps [cos_add]) 1);
qed "minus_sin_cos_eq";
Addsimps [minus_sin_cos_eq RS sym];

Goalw [real_diff_def] "cos x = sin (pi/2 - x)";
by (simp_tac (simpset() addsimps [sin_add]) 1);
qed "cos_sin_eq";
Addsimps [sin_cos_eq RS sym, cos_sin_eq RS sym];

Goal "sin (x + pi) = - sin x";
by (simp_tac (simpset() addsimps [sin_add]) 1);
qed "sin_periodic_pi";
Addsimps [sin_periodic_pi];

Goal "sin (pi + x) = - sin x";
by (simp_tac (simpset() addsimps [sin_add]) 1);
qed "sin_periodic_pi2";
Addsimps [sin_periodic_pi2];

Goal "cos (x + pi) = - cos x";
by (simp_tac (simpset() addsimps [cos_add]) 1);
qed "cos_periodic_pi";
Addsimps [cos_periodic_pi];

Goal "sin (x + 2*pi) = sin x";
by (simp_tac (simpset() addsimps [sin_add,cos_double,numeral_2_eq_2]) 1);
  (*FIXME: just needs x^n for literals!*)
qed "sin_periodic";
Addsimps [sin_periodic];

Goal "cos (x + 2*pi) = cos x";
by (simp_tac (simpset() addsimps [cos_add,cos_double,numeral_2_eq_2]) 1);
  (*FIXME: just needs x^n for literals!*)
qed "cos_periodic";
Addsimps [cos_periodic];

Goal "cos (real n * pi) = (-(1::real)) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [real_of_nat_Suc,left_distrib]));
qed "cos_npi";
Addsimps [cos_npi];

Goal "sin (real (n::nat) * pi) = 0";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [real_of_nat_Suc,left_distrib]));
qed "sin_npi";
Addsimps [sin_npi];

Goal "sin (pi * real (n::nat)) = 0";
by (cut_inst_tac [("n","n")] sin_npi 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_commute] 
    delsimps [sin_npi]));
qed "sin_npi2";
Addsimps [sin_npi2];

Goal "cos (2 * pi) = 1";
by (simp_tac (simpset() addsimps [cos_double,numeral_2_eq_2]) 1);
  (*FIXME: just needs x^n for literals!*)
qed "cos_two_pi";
Addsimps [cos_two_pi];

Goal "sin (2 * pi) = 0";
by (Simp_tac 1);
qed "sin_two_pi";
Addsimps [sin_two_pi];

Goal "[| 0 < x; x < pi/2 |] ==> 0 < sin x";
by (rtac sin_gt_zero 1);
by (assume_tac 1); 
by (rtac real_less_trans 1 THEN assume_tac 1);
by (rtac pi_half_less_two 1); 
qed "sin_gt_zero2";

Goal "[| - pi/2 < x; x < 0 |] ==> sin x < 0";
by (rtac (CLAIM "(0::real) < - x ==> x < 0") 1);
by (rtac (sin_minus RS subst) 1);
by (rtac sin_gt_zero2 1);
by (rtac (CLAIM "-y < x ==> -x < (y::real)") 2);
by Auto_tac;
qed "sin_less_zero";

Goal "pi < 4";
by (cut_facts_tac [pi_half_less_two] 1);
by Auto_tac; 
qed "pi_less_4";

Goal "[| 0 < x; x < pi/2 |] ==> 0 < cos x";
by (cut_facts_tac [pi_less_4] 1);
by (cut_inst_tac [("f","cos"),("a","0"),("b","x"),("y","0")] IVT2_objl 1);
by (Step_tac 1);
by (cut_facts_tac [cos_is_zero] 5);
by (Step_tac 5);
by (dres_inst_tac [("x","xa")] spec 5);
by (dres_inst_tac [("x","pi/2")] spec 5);
by (force_tac (claset(), simpset() addsimps []) 1); 
by (force_tac (claset(), simpset() addsimps []) 1); 
by (force_tac (claset(), simpset() addsimps []) 1); 
by (auto_tac (claset() addSDs [ pi_half_less_two RS order_less_trans, 
    CLAIM "~ m <= n ==> n < (m::real)"]
    addIs [DERIV_isCont,DERIV_cos],simpset()));
qed "cos_gt_zero";

Goal "[| -(pi/2) < x; x < pi/2 |] ==> 0 < cos x";
by (res_inst_tac [("R1.0","x"),("R2.0","0")] real_linear_less2 1);
by (rtac (cos_minus RS subst) 1);
by (rtac cos_gt_zero 1);
by (rtac (CLAIM "-y < x ==> -x < (y::real)") 2);
by (auto_tac (claset() addIs [cos_gt_zero],simpset()));
qed "cos_gt_zero_pi";
 
Goal "[| -(pi/2) <= x; x <= pi/2 |] ==> 0 <= cos x";
by (auto_tac (claset(),HOL_ss addsimps [real_le_less,
    cos_gt_zero_pi]));
by Auto_tac;
qed "cos_ge_zero";

Goal "[| 0 < x; x < pi  |] ==> 0 < sin x";
by (stac sin_cos_eq 1);
by (rotate_tac 1 1);
by (dtac (real_sum_of_halves RS ssubst) 1);
by (auto_tac (claset() addSIs [cos_gt_zero_pi],
    simpset() delsimps [sin_cos_eq RS sym]));
qed "sin_gt_zero_pi";

Goal "[| 0 <= x; x <= pi |] ==> 0 <= sin x";
by (auto_tac (claset(),simpset() addsimps [real_le_less,
    sin_gt_zero_pi]));
qed "sin_ge_zero";

Goal "[| - 1 <= y; y <= 1 |] ==> EX! x. 0 <= x & x <= pi & (cos x = y)";
by (subgoal_tac "EX x.  0 <= x & x <= pi & cos x = y" 1);
by (rtac IVT2  2);
by (auto_tac (claset() addIs [order_less_imp_le,DERIV_isCont,DERIV_cos],
    simpset ()));
by (cut_inst_tac [("x","xa"),("y","y")] linorder_less_linear 1);
by (rtac ccontr 1 THEN Auto_tac);
by (dres_inst_tac [("f","cos")] Rolle 1);
by (dres_inst_tac [("f","cos")] Rolle 5);
by (auto_tac (claset() addIs [order_less_imp_le,DERIV_isCont,DERIV_cos]
    addSDs [DERIV_cos RS DERIV_unique],simpset() addsimps [differentiable_def]));
by (auto_tac (claset() addDs [[order_le_less_trans,order_less_le_trans] MRS 
    sin_gt_zero_pi],simpset()));
qed "cos_total";

Goal "[| - 1 <= y; y <= 1 |] ==> \
\     EX! x. -(pi/2) <= x & x <= pi/2 & (sin x = y)";
by (rtac ccontr 1);
by (subgoal_tac "ALL x. (-(pi/2) <= x & x <= pi/2 & (sin x = y)) \
\   = (0 <= (x + pi/2) & (x + pi/2) <= pi & \
\     (cos(x + pi/2) = -y))" 1);
by (etac swap 1);
by (asm_full_simp_tac (simpset() delsimps [minus_sin_cos_eq RS sym]) 1);
by (dtac (CLAIM "(x::real) <= y ==> -y <= -x") 1);
by (dtac (CLAIM "(x::real) <= y ==> -y <= -x") 1);
by (dtac cos_total 1);
by (Asm_full_simp_tac 1);
by (etac ex1E 1);
by (res_inst_tac [("a","x - (pi/2)")] ex1I 1);
by (simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (rotate_tac 3 1);
by (dres_inst_tac [("x","xa + pi/2")] spec 1);
by (Step_tac 1);
by (TRYALL(Asm_full_simp_tac));
by (auto_tac (claset(),simpset() addsimps [CLAIM "(-x <= y) = (-y <= (x::real))"]));
qed "sin_total";

Goal "(EX n. P (n::nat)) = (EX n. P n & (ALL m. m < n --> ~ P m))";
by (rtac iffI 1);
by (rtac contrapos_pp 1 THEN assume_tac 1);
by (EVERY1[Simp_tac, rtac allI, rtac nat_less_induct]);
by (Auto_tac);
qed "less_induct_ex_iff";

Goal "[| 0 < y; 0 <= x |] ==> \
\     EX n. real n * y <= x & x < real (Suc n) * y";
by (auto_tac (claset() addSDs [reals_Archimedean3],simpset()));
by (dres_inst_tac [("x","x")] spec 1);
by (dtac (less_induct_ex_iff RS iffD1) 1 THEN Step_tac 1);
by (case_tac "n" 1);
by (res_inst_tac [("x","nat")] exI 2);
by Auto_tac;
qed "reals_Archimedean4";

(* Pre Isabelle99-2 proof was simpler- numerals arithmetic 
   now causes some unwanted re-arrangements of literals!   *)
Goal "[| 0 <= x; cos x = 0 |] ==> \
\     EX n. ~even n & x = real n * (pi/2)";
by (dtac (pi_gt_zero RS reals_Archimedean4) 1);
by (Step_tac 1);
by (subgoal_tac 
    "0 <= x - real n * pi & (x - real n * pi) <= pi & \
\    (cos(x - real n * pi) = 0)" 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [real_of_nat_Suc,
    left_distrib]) 2);
by (asm_full_simp_tac (simpset() addsimps [cos_diff]) 1);
by (asm_full_simp_tac (simpset() addsimps [cos_diff]) 2);
by (subgoal_tac "EX! x. 0 <= x & x <= pi & cos x = 0" 1);
by (rtac cos_total 2);
by (Step_tac 1);
by (dres_inst_tac [("x","x - real n * pi")] spec 1);
by (dres_inst_tac [("x","pi/2")] spec 1);
by (asm_full_simp_tac (simpset() addsimps [cos_diff]) 1);
by (res_inst_tac [("x","Suc (2 * n)")] exI 1);
by (asm_full_simp_tac (simpset() addsimps [real_of_nat_Suc,
    left_distrib]) 1);
by Auto_tac;
qed "cos_zero_lemma";

Goal "[| 0 <= x; sin x = 0 |] ==> \
\     EX n. even n & x = real n * (pi/2)";
by (subgoal_tac 
    "EX n. ~ even n & x + pi/2  = real n * (pi/2)" 1);
by (rtac cos_zero_lemma 2);
by (Step_tac 1);
by (res_inst_tac [("x","n - 1")] exI 1);
by (rtac (CLAIM "-y <= x ==> -x <= (y::real)") 2);
by (rtac real_le_trans 2 THEN assume_tac 3);
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym,
    odd_Suc_mult_two_ex,real_of_nat_Suc,
    left_distrib,real_mult_assoc RS sym]));
qed "sin_zero_lemma";

(* also spoilt by numeral arithmetic *)
Goal "(cos x = 0) = \
\     ((EX n. ~even n & (x = real n * (pi/2))) |   \
\      (EX n. ~even n & (x = -(real n * (pi/2)))))";
by (rtac iffI 1);
by (cut_inst_tac [("x","x")] (CLAIM "0 <= (x::real) | x <= 0") 1);
by (Step_tac 1);
by (dtac cos_zero_lemma 1);
by (dtac (CLAIM "(x::real) <= 0 ==> 0 <= -x") 3);
by (dtac cos_zero_lemma 3);
by (Step_tac 1);
by (dtac (CLAIM "-x = y ==> x = -(y::real)") 2);
by (auto_tac (claset(),HOL_ss addsimps [odd_not_even RS sym,
    odd_Suc_mult_two_ex,real_of_nat_Suc,left_distrib]));
by (auto_tac (claset(),simpset() addsimps [cos_add]));
qed "cos_zero_iff";

(* ditto: but to a lesser extent *)
Goal "(sin x = 0) = \
\     ((EX n. even n & (x = real n * (pi/2))) |   \
\      (EX n. even n & (x = -(real n * (pi/2)))))";
by (rtac iffI 1);
by (cut_inst_tac [("x","x")] (CLAIM "0 <= (x::real) | x <= 0") 1);
by (Step_tac 1);
by (dtac sin_zero_lemma 1);
by (dtac (CLAIM "(x::real) <= 0 ==> 0 <= -x") 3);
by (dtac sin_zero_lemma 3);
by (Step_tac 1);
by (dtac (CLAIM "-x = y ==> x = -(y::real)") 2);
by (auto_tac (claset(),simpset() addsimps [even_mult_two_ex]));
qed "sin_zero_iff";

(* ------------------------------------------------------------------------ *)
(* Tangent                                                                  *)
(* ------------------------------------------------------------------------ *)

Goalw [tan_def] "tan 0 = 0";
by (Simp_tac 1);
qed "tan_zero";
Addsimps [tan_zero];

Goalw [tan_def] "tan pi = 0";
by (Simp_tac 1);
qed "tan_pi";
Addsimps [tan_pi];

Goalw [tan_def] "tan (real (n::nat) * pi) = 0";
by (Simp_tac 1);
qed "tan_npi";
Addsimps [tan_npi];

Goalw [tan_def] "tan (-x) = - tan x";
by (simp_tac (simpset() addsimps [minus_mult_left]) 1);
qed "tan_minus";
Addsimps [tan_minus];

Goalw [tan_def] "tan (x + 2*pi) = tan x";
by (Simp_tac 1);
qed "tan_periodic";
Addsimps [tan_periodic];

Goalw [tan_def,real_divide_def] 
      "[| cos x ~= 0; cos y ~= 0 |] \
\       ==> 1 - tan(x)*tan(y) = cos (x + y)/(cos x * cos y)";
by (auto_tac (claset(),
   simpset() delsimps [thm"Ring_and_Field.inverse_mult_distrib"]
	     addsimps [inverse_mult_distrib RS sym] @ mult_ac));
by (res_inst_tac [("c1","cos x * cos y")] (real_mult_right_cancel RS subst) 1);
by (auto_tac (claset(), 
    simpset() delsimps [thm"Ring_and_Field.inverse_mult_distrib"]
	      addsimps [mult_assoc, left_diff_distrib,cos_add]));
val lemma_tan_add1 = result();
Addsimps [lemma_tan_add1];

Goalw [tan_def] 
      "[| cos x ~= 0; cos y ~= 0 |] \
\      ==> tan x + tan y = sin(x + y)/(cos x * cos y)";
by (res_inst_tac [("c1","cos x * cos y")] (real_mult_right_cancel RS subst) 1);
by (auto_tac (claset(), simpset() addsimps [mult_assoc, left_distrib]));
by (simp_tac (simpset() addsimps [sin_add]) 1);
qed "add_tan_eq";

Goal "[| cos x ~= 0; cos y ~= 0; cos (x + y) ~= 0 |] \
\     ==> tan(x + y) = (tan(x) + tan(y))/(1 - tan(x) * tan(y))";
by (asm_simp_tac (simpset() addsimps [add_tan_eq]) 1);
by (simp_tac (simpset() addsimps [tan_def]) 1);
qed "tan_add";

Goal "[| cos x ~= 0; cos (2 * x) ~= 0 |] \
\     ==> tan (2 * x) = (2 * tan x)/(1 - (tan(x) ^ 2))";
by (auto_tac (claset(),simpset() addsimps [asm_full_simplify 
    (simpset() addsimps [real_mult_2 RS sym] delsimps [lemma_tan_add1]) 
    (read_instantiate [("x","x"),("y","x")] tan_add),numeral_2_eq_2]
    delsimps [lemma_tan_add1]));
qed "tan_double";

Goalw [tan_def,real_divide_def] "[| 0 < x; x < pi/2 |] ==> 0 < tan x";
by (auto_tac (claset() addSIs [sin_gt_zero2,cos_gt_zero_pi]
    addSIs [real_mult_order, positive_imp_inverse_positive],simpset()));
qed "tan_gt_zero";

Goal "[| - pi/2 < x; x < 0 |] ==> tan x < 0";
by (rtac (CLAIM "(0::real) < - x ==> x < 0") 1);
by (rtac (tan_minus RS subst) 1);
by (rtac tan_gt_zero 1);
by (rtac (CLAIM "-x < y ==> -y < (x::real)") 2 THEN Auto_tac);
qed "tan_less_zero";

Goal "cos x ~= 0 ==> DERIV (%x. sin(x)/cos(x)) x :> inverse(cos x ^ 2)";
by (rtac lemma_DERIV_subst 1);
by DERIV_tac;
by (auto_tac (claset(),simpset() addsimps [real_divide_def,numeral_2_eq_2]));
qed "lemma_DERIV_tan";

Goal "cos x ~= 0 ==> DERIV tan x :> inverse(cos(x) ^ 2)";
by (auto_tac (claset() addDs [lemma_DERIV_tan],simpset()
    addsimps [(tan_def RS meta_eq_to_obj_eq) RS sym]));
qed "DERIV_tan";
Addsimps [DERIV_tan];

Goalw [real_divide_def] 
      "(%x. cos(x)/sin(x)) -- pi/2 --> 0";
by (res_inst_tac [("a1","1")] ((mult_left_zero) RS subst) 1);
by (rtac LIM_mult2 1); 
by (rtac (inverse_1 RS subst) 2);
by (rtac LIM_inverse 2);
by (fold_tac [real_divide_def]);
by (auto_tac (claset() addSIs [DERIV_isCont],simpset() 
    addsimps [(isCont_def RS meta_eq_to_obj_eq)
    RS sym, cos_pi_half RS sym, sin_pi_half RS sym] 
    delsimps [cos_pi_half,sin_pi_half]));
by (DERIV_tac THEN Auto_tac);
qed "LIM_cos_div_sin";
Addsimps [LIM_cos_div_sin];

Goal "0 < y ==> EX x. 0 < x & x < pi/2 & y < tan x";
by (cut_facts_tac [LIM_cos_div_sin] 1);
by (asm_full_simp_tac (HOL_ss addsimps [LIM_def]) 1);
by (dres_inst_tac [("x","inverse y")] spec 1);
by (Step_tac 1);
by (Force_tac 1);
by (dres_inst_tac [("d1.0","s")] 
    (pi_half_gt_zero RSN (2,real_lbound_gt_zero)) 1);
by (Step_tac 1);
by (res_inst_tac [("x","(pi/2) - e")] exI 1);
by (Asm_simp_tac 1);
by (dres_inst_tac [("x","(pi/2) - e")] spec 1);
by (auto_tac (claset(),simpset() addsimps [abs_eqI2,tan_def]));
by (rtac (inverse_less_iff_less RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [real_divide_def]));
by (rtac (real_mult_order) 1);
by (subgoal_tac "0 < sin e" 3);
by (subgoal_tac "0 < cos e" 3);
by (auto_tac (claset() addIs [cos_gt_zero,sin_gt_zero2],simpset()
    addsimps [inverse_mult_distrib,abs_mult]));
by (dres_inst_tac [("a","cos e")] (positive_imp_inverse_positive) 1);
by (dres_inst_tac [("x","inverse (cos e)")] abs_eqI2 1);
by (auto_tac (claset() addSDs [abs_eqI2],simpset() addsimps mult_ac));
qed "lemma_tan_total";


Goal "0 <= y ==> EX x. 0 <= x & x < pi/2 & tan x = y";
by (ftac real_le_imp_less_or_eq 1);
by (Step_tac 1 THEN Force_tac 2);
by (dtac lemma_tan_total 1 THEN Step_tac 1);
by (cut_inst_tac [("f","tan"),("a","0"),("b","x"),("y","y")] IVT_objl 1);
by (auto_tac (claset() addSIs [DERIV_tan RS DERIV_isCont],simpset()));
by (dres_inst_tac [("y","xa")] order_le_imp_less_or_eq 1);
by (auto_tac (claset() addDs [cos_gt_zero],simpset()));
qed "tan_total_pos";

Goal "EX x. -(pi/2) < x & x < (pi/2) & tan x = y";
by (cut_inst_tac [("y","y")] (CLAIM "0 <= (y::real) | 0 <= -y") 1);
by (Step_tac 1);
by (dtac tan_total_pos 1);
by (dtac tan_total_pos 2);
by (Step_tac 1);
by (res_inst_tac [("x","-x")] exI 2);
by (auto_tac (claset() addSIs [exI],simpset()));
qed "lemma_tan_total1";

Goal "EX! x. -(pi/2) < x & x < (pi/2) & tan x = y";
by (cut_inst_tac [("y","y")] lemma_tan_total1 1);
by (Auto_tac);
by (cut_inst_tac [("x","xa"),("y","y")] linorder_less_linear 1);
by (Auto_tac);
by (subgoal_tac "EX z. xa < z & z < y & DERIV tan z :> 0" 1);
by (subgoal_tac "EX z. y < z & z < xa & DERIV tan z :> 0" 3);
by (rtac Rolle 2);
by (rtac Rolle 7);
by (auto_tac (claset() addSIs [DERIV_tan,DERIV_isCont,exI],simpset()
    addsimps [differentiable_def]));
by (TRYALL(rtac DERIV_tan));
by (TRYALL(dtac (DERIV_tan RSN (2,DERIV_unique))));
by (TRYALL(rtac (real_not_refl2 RS not_sym)));
by (auto_tac (claset() addSIs [cos_gt_zero_pi],simpset()));
by (ALLGOALS(subgoal_tac "0 < cos z")); 
by (Force_tac 1 THEN Force_tac 2);
by (ALLGOALS(thin_tac "cos z = 0"));
by (auto_tac (claset() addSIs [cos_gt_zero_pi],simpset()));
qed "tan_total";

Goal "[| - 1 <= y; y <= 1 |] \
\     ==> -(pi/2) <= arcsin y & arcsin y <= pi & sin(arcsin y) = y";
by (dtac sin_total 1);
by (etac ex1E 2);
by (rewtac arcsin_def);
by (rtac someI2 2);
by (EVERY1[assume_tac, Blast_tac, Step_tac]);
by (rtac real_le_trans 1 THEN assume_tac 1);
by (Force_tac 1);
qed "arcsin_pi";

Goal "[| - 1 <= y; y <= 1 |] \
\     ==> -(pi/2) <= arcsin y & \
\          arcsin y <= pi/2 & sin(arcsin y) = y";
by (dtac sin_total 1 THEN assume_tac 1);
by (etac ex1E 1);
by (rewtac arcsin_def);
by (rtac someI2 1);
by (ALLGOALS(Blast_tac));
qed "arcsin";

Goal "[| - 1 <= y; y <= 1 |] ==> sin(arcsin y) = y";
by (blast_tac (claset() addDs [arcsin]) 1);
qed "sin_arcsin";
Addsimps [sin_arcsin];
      
Goal "[| -1 <= y; y <= 1 |] ==> sin(arcsin y) = y";
by (auto_tac (claset() addIs [sin_arcsin],simpset()));
qed "sin_arcsin2";
Addsimps [sin_arcsin2];
      
Goal "[| - 1 <= y; y <= 1 |] \
\     ==> -(pi/2) <= arcsin y & arcsin y <= pi/2";
by (blast_tac (claset() addDs [arcsin]) 1);
qed "arcsin_bounded";

Goal "[| - 1 <= y; y <= 1 |] ==> -(pi/2) <= arcsin y";
by (blast_tac (claset() addDs [arcsin]) 1);
qed "arcsin_lbound";

Goal "[| - 1 <= y; y <= 1 |] ==> arcsin y <= pi/2";
by (blast_tac (claset() addDs [arcsin]) 1);
qed "arcsin_ubound";

Goal "[| - 1 < y; y < 1 |] \
\     ==> -(pi/2) < arcsin y & arcsin y < pi/2";
by (ftac order_less_imp_le 1);
by (forw_inst_tac [("y","y")] order_less_imp_le 1);
by (ftac arcsin_bounded 1);
by (Step_tac 1 THEN Asm_full_simp_tac 1);
by (dres_inst_tac [("y","arcsin y")] order_le_imp_less_or_eq 1);
by (dres_inst_tac [("y","pi/2")] order_le_imp_less_or_eq 2);
by (Step_tac 1);
by (ALLGOALS(dres_inst_tac [("f","sin")] arg_cong));
by (Auto_tac);
qed "arcsin_lt_bounded";

Goalw [arcsin_def] 
  "[|-(pi/2) <= x; x <= pi/2 |] ==> arcsin(sin x) = x";
by (rtac some1_equality 1);
by (rtac sin_total 1);
by Auto_tac;
qed "arcsin_sin";

Goal "[| - 1 <= y; y <= 1 |] \
\     ==> 0 <= arcos y & arcos y <= pi & cos(arcos y) = y";
by (dtac cos_total 1 THEN assume_tac 1);
by (etac ex1E 1);
by (rewtac arcos_def);
by (rtac someI2 1);
by (ALLGOALS(Blast_tac));
qed "arcos";

Goal "[| - 1 <= y; y <= 1 |] ==> cos(arcos y) = y";
by (blast_tac (claset() addDs [arcos]) 1);
qed "cos_arcos";
Addsimps [cos_arcos];
      
Goal "[| -1 <= y; y <= 1 |] ==> cos(arcos y) = y";
by (auto_tac (claset() addIs [cos_arcos],simpset()));
qed "cos_arcos2";
Addsimps [cos_arcos2];
      
Goal "[| - 1 <= y; y <= 1 |] ==> 0 <= arcos y & arcos y <= pi";
by (blast_tac (claset() addDs [arcos]) 1);
qed "arcos_bounded";

Goal "[| - 1 <= y; y <= 1 |] ==> 0 <= arcos y";
by (blast_tac (claset() addDs [arcos]) 1);
qed "arcos_lbound";

Goal "[| - 1 <= y; y <= 1 |] ==> arcos y <= pi";
by (blast_tac (claset() addDs [arcos]) 1);
qed "arcos_ubound";

Goal "[| - 1 < y; y < 1 |] \
\     ==> 0 < arcos y & arcos y < pi";
by (ftac order_less_imp_le 1);
by (forw_inst_tac [("y","y")] order_less_imp_le 1);
by (ftac arcos_bounded 1);
by (Auto_tac);
by (dres_inst_tac [("y","arcos y")] order_le_imp_less_or_eq 1);
by (dres_inst_tac [("y","pi")] order_le_imp_less_or_eq 2);
by (Auto_tac);
by (ALLGOALS(dres_inst_tac [("f","cos")] arg_cong));
by (Auto_tac);
qed "arcos_lt_bounded";

Goalw [arcos_def] "[|0 <= x; x <= pi |] ==> arcos(cos x) = x";
by (auto_tac (claset() addSIs [some1_equality,cos_total],simpset()));
qed "arcos_cos";

Goalw [arcos_def] "[|x <= 0; -pi <= x |] ==> arcos(cos x) = -x";
by (auto_tac (claset() addSIs [some1_equality,cos_total],simpset()));
qed "arcos_cos2";

Goal "- (pi/2) < arctan y  & \
\     arctan y < pi/2 & tan (arctan y) = y";
by (cut_inst_tac [("y","y")] tan_total 1);
by (etac ex1E 1);
by (rewtac arctan_def);
by (rtac someI2 1);
by (ALLGOALS(Blast_tac));
qed "arctan";
Addsimps [arctan];

Goal "tan(arctan y) = y";
by (Auto_tac);
qed "tan_arctan";

Goal "- (pi/2) < arctan y  & arctan y < pi/2";
by (asm_full_simp_tac (HOL_ss addsimps [arctan]) 1); 
qed "arctan_bounded";

Goal "- (pi/2) < arctan y";
by (Auto_tac);
qed "arctan_lbound";

Goal "arctan y < pi/2";
by (asm_full_simp_tac (HOL_ss addsimps [arctan]) 1); 
qed "arctan_ubound";

Goalw [arctan_def]
      "[|-(pi/2) < x; x < pi/2 |] ==> arctan(tan x) = x";
by (rtac some1_equality 1);
by (rtac tan_total 1);
by Auto_tac;
qed "arctan_tan";

Goal "arctan 0 = 0";
by (rtac (asm_full_simplify (simpset()) 
     (read_instantiate [("x","0")] arctan_tan)) 1);
qed "arctan_zero_zero";
Addsimps [arctan_zero_zero];

(* ------------------------------------------------------------------------- *)
(* Differentiation of arctan.                                                *)
(* ------------------------------------------------------------------------- *)

Goal "cos(arctan x) ~= 0";
by (auto_tac (claset(),simpset() addsimps [cos_zero_iff]));
by (case_tac "n" 1);
by (case_tac "n" 3);
by (cut_inst_tac [("y","x")] arctan_ubound 2);
by (cut_inst_tac [("y","x")] arctan_lbound 4);
by (auto_tac (claset(),
     simpset() addsimps [real_of_nat_Suc, left_distrib,real_le_def, mult_less_0_iff] 
     delsimps [arctan]));
qed "cos_arctan_not_zero";
Addsimps [cos_arctan_not_zero];

Goal "cos x ~= 0 ==> 1 + tan(x) ^ 2 = inverse(cos x) ^ 2";
by (rtac (power_inverse RS subst) 1);
by (res_inst_tac [("c1","cos(x) ^ 2")] (real_mult_right_cancel RS iffD1) 1);
by (auto_tac (claset() addDs [realpow_not_zero], simpset() addsimps
    [power_mult_distrib,left_distrib,realpow_divide,
     tan_def,real_mult_assoc,power_inverse RS sym] 
     delsimps [realpow_Suc]));
qed "tan_sec";


(*--------------------------------------------------------------------------*)
(* Some more theorems- developed while at ICASE (07/2001)                   *)
(*--------------------------------------------------------------------------*)

Goal "sin (xa + 1 / 2 * real (Suc m) * pi) = \
\     cos (xa + 1 / 2 * real  (m) * pi)";
by (simp_tac (HOL_ss addsimps [cos_add,sin_add,
    real_of_nat_Suc,left_distrib,right_distrib]) 1);
by Auto_tac;
qed "lemma_sin_cos_eq";
Addsimps [lemma_sin_cos_eq];

Goal "sin (xa + real (Suc m) * pi / 2) = \
\     cos (xa + real (m) * pi / 2)";
by (simp_tac (HOL_ss addsimps [cos_add,sin_add,real_divide_def,
    real_of_nat_Suc,left_distrib,right_distrib]) 1);
by Auto_tac;
qed "lemma_sin_cos_eq2";
Addsimps [lemma_sin_cos_eq2];

Goal "DERIV (%x. sin (x + k)) xa :> cos (xa + k)";
by (rtac lemma_DERIV_subst 1);
by (res_inst_tac [("f","sin"),("g","%x. x + k")] DERIV_chain2 1);
by DERIV_tac;
by (Simp_tac 1);
qed "DERIV_sin_add";
Addsimps [DERIV_sin_add];

(* which further simplifies to (- 1 ^ m) !! *)
Goal "sin ((real m + 1/2) * pi) = cos (real m * pi)";
by (auto_tac (claset(),simpset() addsimps [right_distrib,
    sin_add,left_distrib] @ mult_ac));
qed "sin_cos_npi";
Addsimps [sin_cos_npi];

Goal "sin (real (Suc (2 * n)) * pi / 2) = (- 1) ^ n";
by (cut_inst_tac [("m","n")] sin_cos_npi 1);
by (auto_tac (claset(),HOL_ss addsimps [real_of_nat_Suc,
    left_distrib,real_divide_def]));
by Auto_tac;
qed "sin_cos_npi2";
Addsimps [ sin_cos_npi2];

Goal "cos (2 * real (n::nat) * pi) = 1";
by (auto_tac (claset(),simpset() addsimps [cos_double,
    real_mult_assoc,power_add RS sym,numeral_2_eq_2]));
  (*FIXME: just needs x^n for literals!*)
qed "cos_2npi";
Addsimps [cos_2npi];

Goal "cos (3 / 2 * pi) = 0";
by (rtac (CLAIM "(1::real) + 1/2 = 3/2" RS subst) 1);
by (stac left_distrib 1);
by (auto_tac (claset(),simpset() addsimps [cos_add] @ mult_ac));
qed "cos_3over2_pi";
Addsimps [cos_3over2_pi];

Goal "sin (2 * real (n::nat) * pi) = 0";
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc]));
qed "sin_2npi";
Addsimps [sin_2npi];

Goal "sin (3 / 2 * pi) = - 1";
by (rtac (CLAIM "(1::real) + 1/2 = 3/2" RS subst) 1);
by (stac left_distrib 1);
by (auto_tac (claset(),simpset() addsimps [sin_add] @mult_ac));
qed "sin_3over2_pi";
Addsimps [sin_3over2_pi];

Goal "cos(xa + 1 / 2 * real (Suc m) * pi) = \
\     -sin  (xa + 1 / 2 * real (m) * pi)";
by (simp_tac (HOL_ss addsimps [cos_add,sin_add,
    real_of_nat_Suc,right_distrib,left_distrib,
    minus_mult_right]) 1);
by Auto_tac;
qed "lemma_cos_sin_eq";
Addsimps [lemma_cos_sin_eq];

Goal "cos (xa + real (Suc m) * pi / 2) = \
\     -sin (xa + real (m) * pi / 2)";
by (simp_tac (HOL_ss addsimps [cos_add,sin_add,real_divide_def,
    real_of_nat_Suc,left_distrib,right_distrib]) 1);
by Auto_tac;
qed "lemma_cos_sin_eq2";
Addsimps [lemma_cos_sin_eq2];

Goal "cos (pi * real (Suc (2 * m)) / 2) = 0";
by (simp_tac (HOL_ss addsimps [cos_add,sin_add,real_divide_def,
    real_of_nat_Suc,left_distrib,right_distrib]) 1);
by Auto_tac;
qed "cos_pi_eq_zero";
Addsimps [cos_pi_eq_zero];

Goal "DERIV (%x. cos (x + k)) xa :> - sin (xa + k)";
by (rtac lemma_DERIV_subst 1);
by (res_inst_tac [("f","cos"),("g","%x. x + k")] DERIV_chain2 1);
by DERIV_tac;
by (Simp_tac 1);
qed "DERIV_cos_add";
Addsimps [DERIV_cos_add];

Goal "isCont cos x";
by (rtac (DERIV_cos RS DERIV_isCont) 1);
qed "isCont_cos";

Goal "isCont sin x";
by (rtac (DERIV_sin RS DERIV_isCont) 1);
qed "isCont_sin";

Goal "isCont exp x";
by (rtac (DERIV_exp RS DERIV_isCont) 1);
qed "isCont_exp";

val isCont_simp = [isCont_exp,isCont_sin,isCont_cos];
Addsimps isCont_simp;

(** more theorems: e.g. used in complex geometry  **)

Goal "sin x = 0 ==> abs(cos x) = 1";
by (auto_tac (claset(),simpset() addsimps [sin_zero_iff,even_mult_two_ex]));
qed "sin_zero_abs_cos_one";

Goal "(exp x = 1) = (x = 0)";
by Auto_tac;
by (dres_inst_tac [("f","ln")] arg_cong 1);
by Auto_tac;
qed "exp_eq_one_iff";
Addsimps [exp_eq_one_iff];

Goal "cos x = 1 ==> sin x = 0";
by (cut_inst_tac [("x","x")] sin_cos_squared_add3 1);
by Auto_tac;
qed "cos_one_sin_zero";

(*-------------------------------------------------------------------------------*)
(* A few extra theorems                                                          *)
(*-------------------------------------------------------------------------------*)

Goal "[| 0 <= x; x < y |] ==> root(Suc n) x < root(Suc n) y";
by (ftac order_le_less_trans 1);
by (assume_tac 1);
by (forw_inst_tac [("n1","n")] (real_root_pow_pos2 RS ssubst) 1);
by (rotate_tac 1 1);
by (assume_tac 1);
by (forw_inst_tac [("n1","n")] (real_root_pow_pos RS ssubst) 1);
by (rotate_tac 3 1 THEN assume_tac 1);
by (dres_inst_tac [("y","root (Suc n) y ^ Suc n")] order_less_imp_le 1 );
by (forw_inst_tac [("n","n")] real_root_pos_pos_le 1);
by (forw_inst_tac [("n","n")] real_root_pos_pos 1);
by (dres_inst_tac [("x","root (Suc n) x"),
    ("y","root (Suc n) y")] realpow_increasing 1);
by (assume_tac 1 THEN assume_tac 1);
by (dres_inst_tac [("x","root (Suc n) x")] order_le_imp_less_or_eq 1);
by Auto_tac;
by (dres_inst_tac [("f","%x. x ^ (Suc n)")] arg_cong 1);
by (auto_tac (claset(),simpset() addsimps [real_root_pow_pos2]
    delsimps [realpow_Suc]));
qed "real_root_less_mono";

Goal "[| 0 <= x; x <= y |] ==> root(Suc n) x <= root(Suc n) y";
by (dres_inst_tac [("y","y")] order_le_imp_less_or_eq 1 );
by (auto_tac (claset() addDs [real_root_less_mono]
    addIs [order_less_imp_le],simpset()));
qed "real_root_le_mono";

Goal "[| 0 <= x; 0 <= y |] ==> (root(Suc n) x < root(Suc n) y) = (x < y)";
by (auto_tac (claset() addIs [real_root_less_mono],simpset()));
by (rtac ccontr 1 THEN dtac (linorder_not_less RS iffD1) 1);
by (dres_inst_tac [("x","y"),("n","n")] real_root_le_mono 1);
by Auto_tac;
qed "real_root_less_iff";
Addsimps [real_root_less_iff];

Goal "[| 0 <= x; 0 <= y |] ==> (root(Suc n) x <= root(Suc n) y) = (x <= y)";
by (auto_tac (claset() addIs [real_root_le_mono],simpset()));
by (simp_tac (simpset() addsimps [real_le_def]) 1);
by Auto_tac;
by (dres_inst_tac [("x","y"),("n","n")] real_root_less_mono 1);
by Auto_tac;
qed "real_root_le_iff";
Addsimps [real_root_le_iff];

Goal "[| 0 <= x; 0 <= y |] ==> (root(Suc n) x = root(Suc n) y) = (x = y)";
by (auto_tac (claset() addSIs [real_le_anti_sym],simpset()));
by (res_inst_tac [("n1","n")] (real_root_le_iff RS iffD1) 1);
by (res_inst_tac [("n1","n")] (real_root_le_iff RS iffD1) 4);
by Auto_tac;
qed "real_root_eq_iff";
Addsimps [real_root_eq_iff];

Goal "[| 0 <= x; 0 <= y; y ^ (Suc n) = x |] ==> root (Suc n) x = y";
by (auto_tac (claset() addDs [real_root_pos2],
    simpset() delsimps [realpow_Suc]));
qed "real_root_pos_unique";

Goal "[| 0 <= x; 0 <= y |]\
\     ==> root(Suc n) (x * y) = root(Suc n) x * root(Suc n) y";
by (rtac real_root_pos_unique 1);
by (auto_tac (claset() addSIs [real_root_pos_pos_le],simpset() 
    addsimps [power_mult_distrib,zero_le_mult_iff,
    real_root_pow_pos2] delsimps [realpow_Suc]));
qed "real_root_mult";

Goal "0 <= x ==> (root(Suc n) (inverse x) = inverse(root(Suc n) x))";
by (rtac real_root_pos_unique 1);
by (auto_tac (claset() addIs [real_root_pos_pos_le],simpset() 
    addsimps [power_inverse RS sym,real_root_pow_pos2] 
    delsimps [realpow_Suc]));
qed "real_root_inverse";

Goalw [real_divide_def] 
     "[| 0 <= x; 0 <= y |] \
\     ==> (root(Suc n) (x / y) = root(Suc n) x / root(Suc n) y)";
by (auto_tac (claset(),simpset() addsimps [real_root_mult,
    real_root_inverse]));
qed "real_root_divide";

Goalw [sqrt_def] "[| 0 <= x; x < y |] ==> sqrt(x) < sqrt(y)";
by (auto_tac (claset() addIs [real_root_less_mono],simpset()));
qed "real_sqrt_less_mono";

Goalw [sqrt_def] "[| 0 <= x; x <= y |] ==> sqrt(x) <= sqrt(y)";
by (auto_tac (claset() addIs [real_root_le_mono],simpset()));
qed "real_sqrt_le_mono";

Goalw [sqrt_def] "[| 0 <= x; 0 <= y |] ==> (sqrt(x) < sqrt(y)) = (x < y)";
by Auto_tac;
qed "real_sqrt_less_iff";
Addsimps [real_sqrt_less_iff];

Goalw [sqrt_def] "[| 0 <= x; 0 <= y |] ==> (sqrt(x) <= sqrt(y)) = (x <= y)";
by Auto_tac;
qed "real_sqrt_le_iff";
Addsimps [real_sqrt_le_iff];

Goalw [sqrt_def] "[| 0 <= x; 0 <= y |] ==> (sqrt(x) = sqrt(y)) = (x = y)";
by Auto_tac;
qed "real_sqrt_eq_iff";
Addsimps [real_sqrt_eq_iff];

Goal "(sqrt(x ^ 2 + y ^ 2) < 1) = (x ^ 2 + y ^ 2 < 1)";
by (rtac (real_sqrt_one RS subst) 1);
by (Step_tac 1);
by (rtac real_sqrt_less_mono 2);
by (dtac (rotate_prems 2 (real_sqrt_less_iff RS iffD1)) 1);
by Auto_tac;
qed "real_sqrt_sos_less_one_iff";
Addsimps [real_sqrt_sos_less_one_iff];

Goal "(sqrt(x ^ 2 + y ^ 2) = 1) = (x ^ 2 + y ^ 2 = 1)";
by (rtac (real_sqrt_one RS subst) 1);
by (Step_tac 1);
by (dtac (rotate_prems 2 (real_sqrt_eq_iff RS iffD1)) 1);
by Auto_tac;
qed "real_sqrt_sos_eq_one_iff";
Addsimps [real_sqrt_sos_eq_one_iff];

Goalw [real_divide_def] "(((r::real) * a) / (r * r)) = a / r";
by (case_tac "r=0" 1);
by (auto_tac (claset(),simpset() addsimps [inverse_mult_distrib] @ mult_ac));
qed "real_divide_square_eq";
Addsimps [real_divide_square_eq];

(*-------------------------------------------------------------------------------*)
(* More theorems about sqrt, transcendental functions etc. needed in Complex.ML  *)
(*-------------------------------------------------------------------------------*)


Goalw [real_divide_def]
    "0 < x ==> 0 <= x/(sqrt (x * x + y * y))";
by (ftac ((real_sqrt_sum_squares_ge1 RSN (2,order_less_le_trans)) 
    RS (CLAIM "0 < x ==> 0 < inverse (x::real)")) 1);
by (rtac (real_mult_order RS order_less_imp_le) 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2]));
qed "lemma_real_divide_sqrt";

Goal "0 < x ==> -(1::real) <= x/(sqrt (x * x + y * y))";
by (rtac real_le_trans 1);
by (rtac lemma_real_divide_sqrt 2);
by Auto_tac;
qed "lemma_real_divide_sqrt_ge_minus_one";

Goal "x < 0 ==> 0 < sqrt (x * x + y * y)";
by (rtac real_sqrt_gt_zero 1);
by (rtac (ARITH_PROVE "[| 0 < x; 0 <= y |] ==> (0::real) < x + y") 1);
by (auto_tac (claset(),simpset() addsimps [zero_less_mult_iff]));
qed "real_sqrt_sum_squares_gt_zero1";

Goal "0 < x ==> 0 < sqrt (x * x + y * y)";
by (rtac real_sqrt_gt_zero 1);
by (rtac (ARITH_PROVE "[| 0 < x; 0 <= y |] ==> (0::real) < x + y") 1);
by (auto_tac (claset(),simpset() addsimps [zero_less_mult_iff]));
qed "real_sqrt_sum_squares_gt_zero2";

Goal "x ~= 0 ==> 0 < sqrt(x ^ 2 + y ^ 2)";
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by (auto_tac (claset() addIs [real_sqrt_sum_squares_gt_zero2,
    real_sqrt_sum_squares_gt_zero1],simpset() addsimps [numeral_2_eq_2]));
qed "real_sqrt_sum_squares_gt_zero3";

Goal "y ~= 0 ==> 0 < sqrt(x ^ 2 + y ^ 2)";
by (dres_inst_tac [("y","x")] real_sqrt_sum_squares_gt_zero3 1);
by (auto_tac (claset(),simpset() addsimps [real_add_commute]));
qed "real_sqrt_sum_squares_gt_zero3a";

Goal "sqrt(x ^ 2 + y ^ 2) = x ==> y = 0";
by (rtac ccontr 1);
by (forw_inst_tac [("x","x")] real_sum_squares_not_zero2 1);
by (dres_inst_tac [("f","%x. x ^ 2")] arg_cong 1);
by (forw_inst_tac [("x","x"),("y","y")] real_sum_square_gt_zero2 1);
by (dtac real_sqrt_gt_zero_pow2 1);
by Auto_tac;
qed "real_sqrt_sum_squares_eq_cancel";
Addsimps [real_sqrt_sum_squares_eq_cancel];

Goal "sqrt(x ^ 2 + y ^ 2) = y ==> x = 0";
by (res_inst_tac [("x","y")] real_sqrt_sum_squares_eq_cancel 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "real_sqrt_sum_squares_eq_cancel2";
Addsimps [real_sqrt_sum_squares_eq_cancel2];

Goal "x < 0 ==> x/(sqrt (x * x + y * y)) <= 1";
by (dtac (ARITH_PROVE "x < 0 ==> (0::real) < -x") 1);
by (dres_inst_tac [("y","y")] 
    lemma_real_divide_sqrt_ge_minus_one 1);
by (dtac (ARITH_PROVE "x <= y ==> -y <= -(x::real)") 1);
by Auto_tac;
qed "lemma_real_divide_sqrt_le_one";

Goal "x < 0 ==> -(1::real) <= x/(sqrt (x * x + y * y))";
by (case_tac "y = 0" 1);
by Auto_tac;
by (ftac abs_minus_eqI2 1);
by (auto_tac (claset(),simpset() addsimps [inverse_minus_eq]));
by (rtac order_less_imp_le 1);
by (res_inst_tac [("z1","sqrt(x * x + y * y)")] 
     (real_mult_less_iff1 RS iffD1) 1);
by (forw_inst_tac [("y2","y")] 
    (real_sqrt_sum_squares_gt_zero1 RS real_not_refl2 
    RS not_sym) 2);
by (auto_tac (claset() addIs [real_sqrt_sum_squares_gt_zero1],
    simpset() addsimps mult_ac));
by (rtac (ARITH_PROVE "-x < y ==> -y < (x::real)") 1);
by (cut_inst_tac [("x","-x"),("y","y")] real_sqrt_sum_squares_ge1 1);
by (dtac real_le_imp_less_or_eq 1);
by (Step_tac 1);
by (asm_full_simp_tac (simpset() addsimps [numeral_2_eq_2]) 1);
by (dtac (sym RS real_sqrt_sum_squares_eq_cancel) 1);
by Auto_tac;
qed "lemma_real_divide_sqrt_ge_minus_one2";

Goal "0 < x ==> x/(sqrt (x * x + y * y)) <= 1";
by (dtac (ARITH_PROVE "0 < x ==> -x < (0::real)") 1);
by (dres_inst_tac [("y","y")] 
    lemma_real_divide_sqrt_ge_minus_one2 1);
by (dtac (ARITH_PROVE "x <= y ==> -y <= -(x::real)") 1);
by Auto_tac;
qed "lemma_real_divide_sqrt_le_one2";
(* was qed "lemma_real_mult_self_rinv_sqrt_squared5" *)

Goal "-(1::real)<= x / sqrt (x * x + y * y)";
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by (Step_tac 1);
by (rtac lemma_real_divide_sqrt_ge_minus_one2 1);
by (rtac lemma_real_divide_sqrt_ge_minus_one 3);
by Auto_tac;
qed "cos_x_y_ge_minus_one";
Addsimps [cos_x_y_ge_minus_one];

Goal "-(1::real)<= y / sqrt (x * x + y * y)";
by (cut_inst_tac [("x","y"),("y","x")] cos_x_y_ge_minus_one 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "cos_x_y_ge_minus_one1a";
Addsimps [cos_x_y_ge_minus_one1a,
          simplify (simpset()) cos_x_y_ge_minus_one1a];

Goal "x / sqrt (x * x + y * y) <= 1";
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by (Step_tac 1);
by (rtac lemma_real_divide_sqrt_le_one 1);
by (rtac lemma_real_divide_sqrt_le_one2 3);
by Auto_tac;
qed "cos_x_y_le_one";
Addsimps [cos_x_y_le_one];

Goal "y / sqrt (x * x + y * y) <= 1";
by (cut_inst_tac [("x","y"),("y","x")] cos_x_y_le_one 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "cos_x_y_le_one2";
Addsimps [cos_x_y_le_one2];

Addsimps [[cos_x_y_ge_minus_one,cos_x_y_le_one] MRS cos_arcos];
Addsimps [[cos_x_y_ge_minus_one,cos_x_y_le_one] MRS arcos_bounded];

Addsimps [[cos_x_y_ge_minus_one1a,cos_x_y_le_one2] MRS cos_arcos];
Addsimps [[cos_x_y_ge_minus_one1a,cos_x_y_le_one2] MRS arcos_bounded];

Goal "-(1::real) <= abs(x) / sqrt (x * x + y * y)";
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by (auto_tac (claset(),simpset() addsimps [abs_minus_eqI2,abs_eqI2]));
by (dtac lemma_real_divide_sqrt_ge_minus_one 1 THEN Force_tac 1);
qed "cos_rabs_x_y_ge_minus_one";

Addsimps [cos_rabs_x_y_ge_minus_one,
          simplify (simpset()) cos_rabs_x_y_ge_minus_one];

Goal "abs(x) / sqrt (x * x + y * y) <= 1";
by (cut_inst_tac [("x","x"),("y","0")] linorder_less_linear 1);
by (auto_tac (claset(),simpset() addsimps [abs_minus_eqI2,abs_eqI2]));
by (dtac lemma_real_divide_sqrt_ge_minus_one2 1 THEN Force_tac 1);
qed "cos_rabs_x_y_le_one";
Addsimps [cos_rabs_x_y_le_one];

Addsimps [[cos_rabs_x_y_ge_minus_one,cos_rabs_x_y_le_one] MRS cos_arcos];
Addsimps [[cos_rabs_x_y_ge_minus_one,cos_rabs_x_y_le_one] MRS arcos_bounded];

Goal "-pi < 0";
by (Simp_tac 1);
qed "minus_pi_less_zero";
Addsimps [minus_pi_less_zero];
Addsimps [minus_pi_less_zero RS order_less_imp_le];

Goal "[| -(1::real) <= y; y <= 1 |] ==> -pi <= arcos y";
by (rtac real_le_trans 1);
by (rtac arcos_lbound 2);
by Auto_tac;
qed "arcos_ge_minus_pi";

Addsimps [[cos_x_y_ge_minus_one,cos_x_y_le_one] MRS arcos_ge_minus_pi];

(* How tedious! *)
Goal "[| x + (y::real) ~= 0; 1 - z = x/(x + y) \
\     |] ==> z = y/(x + y)";
by (res_inst_tac [("c1","x + y")] (real_mult_right_cancel RS iffD1) 1);
by (forw_inst_tac [("c1","x + y")] (real_mult_right_cancel RS iffD2) 2);
by (assume_tac 2);
by (rotate_tac 2 2);
by (dtac (real_mult_assoc RS subst) 2);
by (rotate_tac 2 2);
by (ftac (real_mult_inv_left RS subst) 2);
by (assume_tac 2);
by (thin_tac "(1 - z) * (x + y) = x /(x + y) * (x + y)" 2);
by (thin_tac "1 - z = x /(x + y)" 2);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc]));
by (auto_tac (claset(),simpset() addsimps [right_distrib,
    left_diff_distrib]));
qed "lemma_divide_rearrange";

Goal "[| 0 < x * x + y * y; \
\       1 - sin xa ^ 2 = (x / sqrt (x * x + y * y)) ^ 2 \
\     |] ==> sin xa ^ 2 = (y / sqrt (x * x + y * y)) ^ 2";
by (auto_tac (claset() addIs [lemma_divide_rearrange],simpset() 
    addsimps [realpow_divide,real_sqrt_gt_zero_pow2,
    real_power_two RS sym]));
qed "lemma_cos_sin_eq";

Goal "[| 0 < x * x + y * y; \
\       1 - cos xa ^ 2 = (y / sqrt (x * x + y * y)) ^ 2 \
\     |] ==> cos xa ^ 2 = (x / sqrt (x * x + y * y)) ^ 2";
by (auto_tac (claset(),
    simpset() addsimps [realpow_divide,
          real_sqrt_gt_zero_pow2,real_power_two RS sym]));
by (rtac (real_add_commute RS subst) 1);
by (rtac lemma_divide_rearrange 1); 
by (asm_full_simp_tac (simpset() addsimps []) 1);
by (asm_full_simp_tac (simpset() addsimps [add_commute]) 1);  
qed "lemma_sin_cos_eq";

Goal "[| x ~= 0; \
\        cos xa = x / sqrt (x * x + y * y) \
\     |] ==>  sin xa = y / sqrt (x * x + y * y) | \
\             sin xa = - y / sqrt (x * x + y * y)";
by (dres_inst_tac [("f","%x. x ^ 2")] arg_cong 1);
by (forw_inst_tac [("y","y")] real_sum_square_gt_zero 1);
by (asm_full_simp_tac (simpset() addsimps [cos_squared_eq]) 1);
by (subgoal_tac "sin xa ^ 2 =  (y / sqrt (x * x + y * y)) ^ 2" 1);
by (rtac lemma_cos_sin_eq 2);
by (Force_tac 2);
by (Asm_full_simp_tac 2);
by (auto_tac (claset(),simpset() addsimps [realpow_two_disj,numeral_2_eq_2] 
    delsimps [realpow_Suc]));
qed "sin_x_y_disj";

Goal "y ~= 0 ==> x / sqrt (x * x + y * y) ~= -(1::real)";
by Auto_tac;
by (dres_inst_tac [("f","%x. x ^ 2")] arg_cong 1);
by (auto_tac (claset(),simpset() addsimps [realpow_divide,
    real_power_two RS sym]));
by (forw_inst_tac [("x","x")] real_sum_squares_not_zero2 1);
by (asm_full_simp_tac (HOL_ss addsimps [real_power_two RS sym]) 1);
by (forw_inst_tac [("c1","x ^ 2 + y ^ 2")]
    (real_mult_right_cancel RS iffD2) 1);
by (assume_tac 1);
by (dres_inst_tac [("y","x ^ 2 + y ^ 2"),("x","x ^ 2")] 
    (CLAIM "y ~= (0::real) ==> (x/y) * y= x") 1);
by Auto_tac;
qed "cos_not_eq_minus_one";

Goalw [arcos_def] 
  "arcos (x / sqrt (x * x + y * y)) = pi ==> y = 0";
by (rtac ccontr 1);
by (rtac swap 1 THEN assume_tac 2);
by (rtac (([cos_x_y_ge_minus_one,cos_x_y_le_one] MRS cos_total) RS 
     ((CLAIM "EX! x. P x ==> EX x. P x") RS someI2_ex)) 1);
by (auto_tac (claset() addDs [cos_not_eq_minus_one],simpset()));
qed "arcos_eq_pi_cancel";

Goalw [real_divide_def] "x ~= 0 ==> x / sqrt (x * x + y * y) ~= 0";
by (forw_inst_tac [("y3","y")] (real_sqrt_sum_squares_gt_zero3 
    RS real_not_refl2 RS not_sym RS nonzero_imp_inverse_nonzero) 1);
by (auto_tac (claset(),simpset() addsimps [real_power_two]));
qed "lemma_cos_not_eq_zero";

Goal "[| x ~= 0; \
\        sin xa = y / sqrt (x * x + y * y) \
\     |] ==>  cos xa = x / sqrt (x * x + y * y) | \
\             cos xa = - x / sqrt (x * x + y * y)";
by (dres_inst_tac [("f","%x. x ^ 2")] arg_cong 1);
by (forw_inst_tac [("y","y")] real_sum_square_gt_zero 1);
by (asm_full_simp_tac (simpset() addsimps [sin_squared_eq] 
    delsimps [realpow_Suc]) 1);
by (subgoal_tac "cos xa ^ 2 =  (x / sqrt (x * x + y * y)) ^ 2" 1);
by (rtac lemma_sin_cos_eq 2);
by (Force_tac 2);
by (Asm_full_simp_tac 2);
by (auto_tac (claset(),simpset() addsimps [realpow_two_disj,
    numeral_2_eq_2] delsimps [realpow_Suc]));
qed "cos_x_y_disj";

Goal "0 < y ==> - y / sqrt (x * x + y * y) < 0";
by (case_tac "x = 0" 1);
by (auto_tac (claset(),simpset() addsimps [abs_eqI2]));
by (dres_inst_tac [("y","y")] real_sqrt_sum_squares_gt_zero3 1);
by (auto_tac (claset(),simpset() addsimps [zero_less_mult_iff,
    real_divide_def,real_power_two])); 
qed "real_sqrt_divide_less_zero";

Goal "[| x ~= 0; 0 < y |] ==> EX r a. x = r * cos a & y = r * sin a";
by (res_inst_tac [("x","sqrt(x ^ 2 + y ^ 2)")] exI 1);
by (res_inst_tac [("x","arcos(x / sqrt (x * x + y * y))")] exI 1);
by Auto_tac;
by (dres_inst_tac [("y2","y")] (real_sqrt_sum_squares_gt_zero3 
    RS real_not_refl2 RS not_sym) 1);
by (auto_tac (claset(),simpset() addsimps [real_power_two]));
by (rewtac arcos_def);
by (cut_inst_tac [("x1","x"),("y1","y")] ([cos_x_y_ge_minus_one,cos_x_y_le_one] 
    MRS cos_total) 1);
by (rtac someI2_ex 1 THEN Blast_tac 1);
by (thin_tac 
    "EX! xa. 0 <= xa & xa <= pi & cos xa = x / sqrt (x * x + y * y)" 1);
by (ftac sin_x_y_disj 1 THEN Blast_tac 1);
by (dres_inst_tac [("y2","y")] (real_sqrt_sum_squares_gt_zero3 
    RS real_not_refl2 RS not_sym) 1);
by (auto_tac (claset(),simpset() addsimps [real_power_two]));
by (dtac sin_ge_zero 1 THEN assume_tac 1);
by (dres_inst_tac [("x","x")] real_sqrt_divide_less_zero 1 THEN Auto_tac);
qed "polar_ex1";

Goal "x * x = -(y * y) ==> y = (0::real)";
by (auto_tac (claset() addIs [real_sum_squares_cancel],simpset()));
qed "real_sum_squares_cancel2a";

Goal "[| x ~= 0; y < 0 |] ==> EX r a. x = r * cos a & y = r * sin a";
by (cut_inst_tac [("x","0"),("y","x")] linorder_less_linear 1);
by Auto_tac;
by (res_inst_tac [("x","sqrt(x ^ 2 + y ^ 2)")] exI 1);
by (res_inst_tac [("x","arcsin(y / sqrt (x * x + y * y))")] exI 1);
by (auto_tac (claset() addDs [real_sum_squares_cancel2a],
    simpset() addsimps [real_power_two]));
by (rewtac arcsin_def);
by (cut_inst_tac [("x1","x"),("y1","y")] ([cos_x_y_ge_minus_one1a,
    cos_x_y_le_one2] MRS sin_total) 1);
by (rtac someI2_ex 1 THEN Blast_tac 1);
by (thin_tac "EX! xa. - (pi/2) <= xa & \
\                xa <= pi/2 & sin xa = y / sqrt (x * x + y * y)" 1);
by (ftac ((CLAIM "0 < x ==> (x::real) ~= 0") RS cos_x_y_disj) 1 THEN Blast_tac 1);
by Auto_tac;
by (dtac cos_ge_zero 1 THEN Force_tac 1);
by (dres_inst_tac [("x","y")] real_sqrt_divide_less_zero 1);
by (auto_tac (claset(),simpset() addsimps [real_add_commute]));
by (dtac (ARITH_PROVE "(y::real) < 0 ==> 0 < - y") 1);
by (dtac (CLAIM "x < (0::real) ==> x ~= 0" RS polar_ex1) 1 THEN assume_tac 1);
by (REPEAT(etac exE 1));
by (res_inst_tac [("x","r")] exI 1);
by (res_inst_tac [("x","-a")] exI 1);
by Auto_tac;
qed "polar_ex2";

Goal "EX r a. x = r * cos a & y = r * sin a";
by (case_tac "x = 0" 1);
by Auto_tac;
by (res_inst_tac [("x","y")] exI 1);
by (res_inst_tac [("x","pi/2")] exI 1 THEN Auto_tac);
by (cut_inst_tac [("x","0"),("y","y")] linorder_less_linear 1);
by Auto_tac;
by (res_inst_tac [("x","x")] exI 2);
by (res_inst_tac [("x","0")] exI 2 THEN Auto_tac);
by (ALLGOALS(blast_tac (claset() addIs [polar_ex1,polar_ex2])));
qed "polar_Ex";

Goal "abs x <= sqrt (x ^ 2 + y ^ 2)";
by (res_inst_tac [("n","1")] realpow_increasing 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2 RS sym]));
by (simp_tac (simpset() addsimps [numeral_2_eq_2]) 1);
qed "real_sqrt_ge_abs1";

Goal "abs y <= sqrt (x ^ 2 + y ^ 2)";
by (rtac (real_add_commute RS subst) 1);
by (rtac real_sqrt_ge_abs1 1);
qed "real_sqrt_ge_abs2";
Addsimps [real_sqrt_ge_abs1,real_sqrt_ge_abs2];

Goal "0 < sqrt 2";
by (auto_tac (claset() addIs [real_sqrt_gt_zero],simpset()));
qed "real_sqrt_two_gt_zero";
Addsimps [real_sqrt_two_gt_zero];

Goal "0 <= sqrt 2";
by (auto_tac (claset() addIs [real_sqrt_ge_zero],simpset()));
qed "real_sqrt_two_ge_zero";
Addsimps [real_sqrt_two_ge_zero];

Goal "1 < sqrt 2";
by (res_inst_tac [("y","7/5")] order_less_le_trans 1);
by (res_inst_tac [("n","1")] realpow_increasing 2);
by (auto_tac (claset(),simpset() addsimps [real_sqrt_gt_zero_pow2,numeral_2_eq_2 RS sym] 
    delsimps [realpow_Suc]));
by (simp_tac (simpset() addsimps [numeral_2_eq_2]) 1);
qed "real_sqrt_two_gt_one";
Addsimps [real_sqrt_two_gt_one];

Goal "0 < u ==> u / sqrt 2 < u";
by (res_inst_tac [("z1","inverse u")] (real_mult_less_iff1 RS iffD1) 1);
by Auto_tac;
by (res_inst_tac [("z1","sqrt 2")] (real_mult_less_iff1 RS iffD1) 1);
by Auto_tac;
qed "lemma_real_divide_sqrt_less";

(* needed for infinitely close relation over the nonstandard complex numbers *)
Goal "[| 0 < u; x < u/2; y < u/2; 0 <= x; 0 <= y |] ==> sqrt (x ^ 2 + y ^ 2) < u";
by (res_inst_tac [("y","u/sqrt 2")] order_le_less_trans 1);
by (etac lemma_real_divide_sqrt_less 2);
by (res_inst_tac [("n","1")] realpow_increasing 1);
by (auto_tac (claset(),
    simpset() addsimps [real_0_le_divide_iff,realpow_divide,
    real_sqrt_gt_zero_pow2,numeral_2_eq_2 RS sym] delsimps [realpow_Suc]));
by (res_inst_tac [("t","u ^ 2")] (real_sum_of_halves RS subst) 1);
by (rtac add_mono 1);
by (auto_tac (claset(),simpset() delsimps [realpow_Suc]));
by (ALLGOALS(rtac ((CLAIM "(2::real) ^ 2 = 4") RS subst)));
by (ALLGOALS(rtac (power_mult_distrib RS subst)));
by (ALLGOALS(rtac power_mono));
by Auto_tac;
qed "lemma_sqrt_hcomplex_capprox";

Addsimps [real_sqrt_sum_squares_ge_zero RS abs_eqI1];

(* A few theorems involving ln and derivatives, etc *)

Goal "DERIV ln z :> l ==> DERIV (%x. exp (ln x)) z :> exp (ln z) * l";
by (etac DERIV_fun_exp 1);
qed "lemma_DERIV_ln";

Goal "0 < z ==> ( *f* (%x. exp (ln x))) z = z";
by (res_inst_tac [("z","z")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_def,hypreal_less]));
qed "STAR_exp_ln";

Goal "[|e : Infinitesimal; 0 < x |] ==> 0 < hypreal_of_real x + e";
by (res_inst_tac [("c1","-e")] (add_less_cancel_right RS iffD1) 1);
by (auto_tac (claset() addIs [Infinitesimal_less_SReal],simpset()));
qed "hypreal_add_Infinitesimal_gt_zero";

Goalw [nsderiv_def,NSLIM_def] "0 < z ==> NSDERIV (%x. exp (ln x)) z :> 1";
by Auto_tac;
by (rtac ccontr 1);
by (subgoal_tac "0 < hypreal_of_real z + h" 1);
by (dtac STAR_exp_ln 1);
by (rtac hypreal_add_Infinitesimal_gt_zero 2);
by (dtac (CLAIM "h ~= 0 ==> h/h = (1::hypreal)") 1);
by (auto_tac (claset(),simpset() addsimps [exp_ln_iff RS sym] 
    delsimps [exp_ln_iff]));
qed "NSDERIV_exp_ln_one";

Goal "0 < z ==> DERIV (%x. exp (ln x)) z :> 1";
by (auto_tac (claset() addIs [NSDERIV_exp_ln_one],
    simpset() addsimps [NSDERIV_DERIV_iff RS sym]));
qed "DERIV_exp_ln_one";

Goal "[| 0 < z; DERIV ln z :> l |] ==>  exp (ln z) * l = 1";
by (rtac DERIV_unique 1);
by (rtac lemma_DERIV_ln 1);
by (rtac DERIV_exp_ln_one 2);
by Auto_tac;
qed "lemma_DERIV_ln2";

Goal "[| 0 < z; DERIV ln z :> l |] ==>  l = 1/(exp (ln z))";
by (res_inst_tac [("c1","exp(ln z)")] (real_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset() addIs [lemma_DERIV_ln2],simpset()));
qed "lemma_DERIV_ln3";

Goal "[| 0 < z; DERIV ln z :> l |] ==>  l = 1/z";
by (res_inst_tac [("t","z")] (exp_ln_iff RS iffD2 RS subst) 1);
by (auto_tac (claset() addIs [lemma_DERIV_ln3],simpset()));
qed "lemma_DERIV_ln4";

(* need to rename second isCont_inverse *)

Goal "[| 0 < d; ALL z. abs(z - x) <= d --> g(f(z)) = z; \
\        ALL z. abs(z - x) <= d --> isCont f z |] \
\     ==> isCont g (f x)";
by (simp_tac (simpset() addsimps [isCont_iff,LIM_def]) 1);
by (Step_tac 1);
by (dres_inst_tac [("d1.0","r")] real_lbound_gt_zero 1);
by (assume_tac 1 THEN Step_tac 1);
by (subgoal_tac "ALL z. abs(z - x) <= e --> (g(f z) = z)" 1);
by (Force_tac 2);
by (subgoal_tac "ALL z. abs(z - x) <= e --> isCont f z" 1);
by (Force_tac 2);
by (dres_inst_tac [("d","e")] isCont_inj_range 1);
by (assume_tac 2 THEN assume_tac 1);
by (Step_tac 1);
by (res_inst_tac [("x","ea")] exI 1);
by Auto_tac;
by (rotate_tac 4 1);
by (dres_inst_tac [("x","f(x) + xa")] spec 1);
by Auto_tac;
by (dtac sym 1 THEN Auto_tac);
by (arith_tac 1);
qed "isCont_inv_fun";

(*
Goalw [isCont_def]  
      "[| isCont f x; f x ~= 0 |] ==> isCont (%x. inverse (f x)) x";
by (blast_tac (claset() addIs [LIM_inverse]) 1);
qed "isCont_inverse";
*)


Goal "[| 0 < d; \
\        ALL z. abs(z - x) <= d --> g(f(z)) = z; \
\        ALL z. abs(z - x) <= d --> isCont f z |] \
\      ==> EX e. 0 < (e::real) & \
\            (ALL y. 0 < abs(y - f(x::real)) & abs(y - f(x)) < e --> f(g(y)) = y)";
by (dtac isCont_inj_range 1);
by (assume_tac 2 THEN assume_tac 1);
by Auto_tac;
by (res_inst_tac [("x","e")] exI 1 THEN Auto_tac);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","y")] spec 1 THEN Auto_tac);
qed "isCont_inv_fun_inv";


(* Bartle/Sherbert: Introduction to Real Analysis, Theorem 4.2.9, p. 110*)
Goal "[| f -- c --> l; 0 < l |] \
\        ==> EX r. 0 < r & (ALL x. x ~= c & abs (c - x) < r --> 0 < f x)";
by (auto_tac (claset(),simpset() addsimps [LIM_def]));
by (dres_inst_tac [("x","l/2")] spec 1);
by (Step_tac 1);
by (Force_tac 1);
by (res_inst_tac [("x","s")] exI 1);
by (Step_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","x")] spec 1);
by (auto_tac (claset(),HOL_ss addsimps [abs_interval_iff]));
by (auto_tac (claset(),simpset() addsimps [CLAIM "(l::real) + -(l/2) = l/2",
    CLAIM "(a < f + - l) = (l + a < (f::real))"]));
qed "LIM_fun_gt_zero";

Goal "[| f -- c --> l; l < 0 |] \
\        ==> EX r. 0 < r & (ALL x. x ~= c & abs (c - x) < r --> f x < 0)";
by (auto_tac (claset(),simpset() addsimps [LIM_def]));
by (dres_inst_tac [("x","-l/2")] spec 1);
by (Step_tac 1);
by (Force_tac 1);
by (res_inst_tac [("x","s")] exI 1);
by (Step_tac 1);
by (rotate_tac 2 1);
by (dres_inst_tac [("x","x")] spec 1);
by (auto_tac (claset(),HOL_ss addsimps [abs_interval_iff]));
by (auto_tac (claset(),simpset() addsimps [CLAIM "(l::real) + -(l/2) = l/2",
    CLAIM "(f + - l < a) = ((f::real) < l + a)"]));
qed "LIM_fun_less_zero";


Goal "[| f -- c --> l; l ~= 0 |] \
\        ==> EX r. 0 < r & (ALL x. x ~= c & abs (c - x) < r --> f x ~= 0)";
by (cut_inst_tac [("x","l"),("y","0")] linorder_less_linear 1);
by Auto_tac;
by (dtac LIM_fun_less_zero 1);
by (dtac LIM_fun_gt_zero 3);
by Auto_tac;
by (ALLGOALS(res_inst_tac [("x","r")] exI));
by Auto_tac;
qed "LIM_fun_not_zero";

(*  Title       : RealPow.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural Powers of reals theory
*)

bind_thm ("realpow_Suc", thm "realpow_Suc");

Goal "(0::real) ^ (Suc n) = 0";
by Auto_tac;
qed "realpow_zero";
Addsimps [realpow_zero];

Goal "r ~= (0::real) --> r ^ n ~= 0";
by (induct_tac "n" 1);
by Auto_tac; 
qed_spec_mp "realpow_not_zero";

Goal "r ^ n = (0::real) ==> r = 0";
by (rtac ccontr 1);
by (auto_tac (claset() addDs [realpow_not_zero], simpset()));
qed "realpow_zero_zero";

Goal "inverse ((r::real) ^ n) = (inverse r) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [real_inverse_distrib]));
qed "realpow_inverse";

Goal "abs (r::real) ^ n = abs (r ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [abs_mult]));
qed "realpow_abs";

Goal "(r::real) ^ (n + m) = (r ^ n) * (r ^ m)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "realpow_add";

Goal "(r::real) ^ 1 = r";
by (Simp_tac 1);
qed "realpow_one";
Addsimps [realpow_one];

Goal "(r::real)^ (Suc (Suc 0)) = r * r";
by (Simp_tac 1);
qed "realpow_two";

Goal "(0::real) < r --> 0 < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_mult_order],
	      simpset() addsimps [real_zero_less_one]));
qed_spec_mp "realpow_gt_zero";

Goal "(0::real) <= r --> 0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [real_0_le_mult_iff]));
qed_spec_mp "realpow_ge_zero";

Goal "(0::real) <= x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_mono], simpset()));
by (asm_simp_tac (simpset() addsimps [realpow_ge_zero]) 1);
qed_spec_mp "realpow_le";

Goal "(0::real) < x & x < y & 0 < n --> x ^ n < y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_mult_less_mono, gr0I] 
                       addDs [realpow_gt_zero],
    simpset()));
qed_spec_mp "realpow_less";

Goal "1 ^ n = (1::real)";
by (induct_tac "n" 1);
by Auto_tac;
qed "realpow_eq_one";
Addsimps [realpow_eq_one];

Goal "abs((-1) ^ n) = (1::real)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [abs_mult]));
qed "abs_realpow_minus_one";
Addsimps [abs_realpow_minus_one];

Goal "((r::real) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "realpow_mult";

Goal "(0::real) <= r^ Suc (Suc 0)";
by (simp_tac (simpset() addsimps [real_le_square]) 1);
qed "realpow_two_le";
Addsimps [realpow_two_le];

Goal "abs((x::real)^Suc (Suc 0)) = x^Suc (Suc 0)";
by (simp_tac (simpset() addsimps [abs_eqI1, 
				  real_le_square]) 1);
qed "abs_realpow_two";
Addsimps [abs_realpow_two];

Goal "abs(x::real)^Suc (Suc 0) = x^Suc (Suc 0)";
by (simp_tac (simpset() addsimps [realpow_abs,abs_eqI1]
                        delsimps [realpow_Suc]) 1);
qed "realpow_two_abs";
Addsimps [realpow_two_abs];

Goal "(1::real) < r ==> 1 < r^ (Suc (Suc 0))";
by Auto_tac;
by (cut_facts_tac [real_zero_less_one] 1);
by (forw_inst_tac [("x","0")] order_less_trans 1);
by (assume_tac 1);
by (dres_inst_tac [("z","r"),("x","1")] 
    (real_mult_less_mono1) 1);
by (auto_tac (claset() addIs [order_less_trans], simpset()));
qed "realpow_two_gt_one";

Goal "(1::real) < r --> 1 <= r ^ n";
by (induct_tac "n" 1);
by Auto_tac;  
by (subgoal_tac "1*1 <= r * r^n" 1);
by (rtac real_mult_le_mono 2); 
by Auto_tac;  
qed_spec_mp "realpow_ge_one";

Goal "(1::real) <= r ==> 1 <= r ^ n";
by (dtac order_le_imp_less_or_eq 1); 
by (auto_tac (claset() addDs [realpow_ge_one], simpset()));
qed "realpow_ge_one2";

Goal "(1::real) <= 2 ^ n";
by (res_inst_tac [("y","1 ^ n")] order_trans 1);
by (rtac realpow_le 2);
by (auto_tac (claset() addIs [order_less_imp_le], simpset()));
qed "two_realpow_ge_one";

Goal "real (n::nat) < 2 ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [real_of_nat_Suc]));
by (stac real_mult_2 1);
by (rtac real_add_less_le_mono 1);
by (auto_tac (claset(), simpset() addsimps [two_realpow_ge_one]));
qed "two_realpow_gt";
Addsimps [two_realpow_gt,two_realpow_ge_one];

Goal "(-1) ^ (2*n) = (1::real)";
by (induct_tac "n" 1);
by Auto_tac;
qed "realpow_minus_one";
Addsimps [realpow_minus_one];

Goal "(-1) ^ Suc (2*n) = -(1::real)";
by Auto_tac;
qed "realpow_minus_one_odd";
Addsimps [realpow_minus_one_odd];

Goal "(-1) ^ Suc (Suc (2*n)) = (1::real)";
by Auto_tac;
qed "realpow_minus_one_even";
Addsimps [realpow_minus_one_even];

Goal "(0::real) < r & r < (1::real) --> r ^ Suc n < r ^ n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "realpow_Suc_less";

Goal "0 <= r & r < (1::real) --> r ^ Suc n <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [order_less_imp_le] 
                       addSDs [order_le_imp_less_or_eq],
              simpset()));
qed_spec_mp "realpow_Suc_le";

Goal "(0::real) <= 0 ^ n";
by (case_tac "n" 1);
by Auto_tac;
qed "realpow_zero_le";
Addsimps [realpow_zero_le];

Goal "0 < r & r < (1::real) --> r ^ Suc n <= r ^ n";
by (blast_tac (claset() addSIs [order_less_imp_le,
    realpow_Suc_less]) 1);
qed_spec_mp "realpow_Suc_le2";

Goal "[| 0 <= r; r < (1::real) |] ==> r ^ Suc n <= r ^ n";
by (etac (order_le_imp_less_or_eq RS disjE) 1);
by (rtac realpow_Suc_le2 1);
by Auto_tac;
qed "realpow_Suc_le3";

Goal "0 <= r & r < (1::real) & n < N --> r ^ N <= r ^ n";
by (induct_tac "N" 1);
by (ALLGOALS Asm_simp_tac); 
by (Clarify_tac 1);
by (subgoal_tac "r * r ^ na <= 1 * r ^ n" 1); 
by (Asm_full_simp_tac 1); 
by (rtac real_mult_le_mono 1); 
by (auto_tac (claset(), simpset() addsimps [realpow_ge_zero, less_Suc_eq]));  
qed_spec_mp "realpow_less_le";

Goal "[| 0 <= r; r < (1::real); n <= N |] ==> r ^ N <= r ^ n";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_less_le],
    simpset()));
qed "realpow_le_le";

Goal "[| 0 < r; r < (1::real) |] ==> r ^ Suc n <= r";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    (order_less_imp_le RS realpow_le_le) 1);
by Auto_tac;
qed "realpow_Suc_le_self";

Goal "[| 0 < r; r < (1::real) |] ==> r ^ Suc n < 1";
by (blast_tac (claset() addIs [realpow_Suc_le_self, order_le_less_trans]) 1);
qed "realpow_Suc_less_one";

Goal "(1::real) <= r --> r ^ n <= r ^ Suc n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "realpow_le_Suc";

Goal "(1::real) < r --> r ^ n < r ^ Suc n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "realpow_less_Suc";

Goal "(1::real) < r --> r ^ n <= r ^ Suc n";
by (blast_tac (claset() addSIs [order_less_imp_le, realpow_less_Suc]) 1);
qed_spec_mp "realpow_le_Suc2";

Goal "(1::real) < r & n < N --> r ^ n <= r ^ N";
by (induct_tac "N" 1);
by Auto_tac;
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_one));
by (ALLGOALS(dtac (real_mult_self_le)));
by (assume_tac 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [order_trans],
              simpset() addsimps [less_Suc_eq]));
qed_spec_mp "realpow_gt_ge";

Goal "(1::real) <= r & n < N --> r ^ n <= r ^ N";
by (induct_tac "N" 1);
by Auto_tac;
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_one2));
by (ALLGOALS(dtac (real_mult_self_le2)));
by (assume_tac 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [order_trans],
              simpset() addsimps [less_Suc_eq]));
qed_spec_mp "realpow_gt_ge2";

Goal "[| (1::real) < r; n <= N |] ==> r ^ n <= r ^ N";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_gt_ge], simpset()));
qed "realpow_ge_ge";

Goal "[| (1::real) <= r; n <= N |] ==> r ^ n <= r ^ N";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_gt_ge2], simpset()));
qed "realpow_ge_ge2";

Goal "(1::real) < r ==> r <= r ^ Suc n";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    realpow_ge_ge 1);
by Auto_tac;
qed_spec_mp "realpow_Suc_ge_self";

Goal "(1::real) <= r ==> r <= r ^ Suc n";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    realpow_ge_ge2 1);
by Auto_tac;
qed_spec_mp "realpow_Suc_ge_self2";

Goal "[| (1::real) < r; 0 < n |] ==> r <= r ^ n";
by (dtac (less_not_refl2 RS  not0_implies_Suc) 1);
by (auto_tac (claset() addSIs 
    [realpow_Suc_ge_self],simpset()));
qed "realpow_ge_self";

Goal "[| (1::real) <= r; 0 < n |] ==> r <= r ^ n";
by (dtac (less_not_refl2 RS  not0_implies_Suc) 1);
by (auto_tac (claset() addSIs [realpow_Suc_ge_self2],simpset()));
qed "realpow_ge_self2";

Goal "0 < n --> (x::real) ^ (n - 1) * x = x ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() 
    addsimps [real_mult_commute]));
qed_spec_mp "realpow_minus_mult";
Addsimps [realpow_minus_mult];

Goal "r ~= 0 ==> r * inverse r ^Suc (Suc 0) = inverse (r::real)";
by (asm_simp_tac (simpset() addsimps [realpow_two,
                  real_mult_assoc RS sym]) 1);
qed "realpow_two_mult_inverse";
Addsimps [realpow_two_mult_inverse];

(* 05/00 *)
Goal "(-x)^Suc (Suc 0) = (x::real)^Suc (Suc 0)";
by (Simp_tac 1);
qed "realpow_two_minus";
Addsimps [realpow_two_minus];

Goalw [real_diff_def] "(x::real)^Suc (Suc 0) - y^Suc (Suc 0) = (x - y) * (x + y)";
by (simp_tac (simpset() addsimps 
              [real_add_mult_distrib2, real_add_mult_distrib, 
               real_minus_mult_eq2 RS sym] @ real_mult_ac) 1);
qed "realpow_two_diff";

Goalw [real_diff_def] "((x::real)^Suc (Suc 0) = y^Suc (Suc 0)) = (x = y | x = -y)";
by (cut_inst_tac [("x","x"),("y","y")] realpow_two_diff 1);
by (auto_tac (claset(), simpset() delsimps [realpow_Suc]));
qed "realpow_two_disj";

(* used in Transc *)
Goal  "[|(x::real) ~= 0; m <= n |] ==> x ^ (n - m) = x ^ n * inverse (x ^ m)";
by (auto_tac (claset(),
       simpset() addsimps [le_eq_less_or_eq, less_iff_Suc_add, realpow_add,
                           realpow_not_zero] @ real_mult_ac));
qed "realpow_diff";

Goal "real (m::nat) ^ n = real (m ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),
              simpset() addsimps [real_of_nat_one, real_of_nat_mult]));
qed "realpow_real_of_nat";

Goal "0 < real (Suc (Suc 0) ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),
          simpset() addsimps [real_of_nat_mult, real_0_less_mult_iff]));
qed "realpow_real_of_nat_two_pos";
Addsimps [realpow_real_of_nat_two_pos];


Goal "(0::real) <= x --> 0 <= y --> x ^ Suc n <= y ^ Suc n --> x <= y";
by (induct_tac "n" 1);
by Auto_tac;
by (asm_full_simp_tac (simpset() addsimps [linorder_not_less RS sym]) 1); 
by (swap_res_tac [real_mult_less_mono'] 1);
by Auto_tac;
by (auto_tac (claset(), simpset() addsimps [real_0_le_mult_iff]));
by (auto_tac (claset(), simpset() addsimps [linorder_not_less RS sym]));    
by (dres_inst_tac [("n","n")] realpow_gt_zero 1);   
by Auto_tac;  
qed_spec_mp "realpow_increasing";
  
Goal "[| (0::real) <= x; 0 <= y; x ^ Suc n = y ^ Suc n |] ==> x = y";
by (blast_tac (claset() addIs [realpow_increasing, order_antisym, 
			       order_eq_refl, sym]) 1);
qed_spec_mp "realpow_Suc_cancel_eq";

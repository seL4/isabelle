(*  Title       : RealAbs.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Absolute value function for the reals
*) 

(*----------------------------------------------------------------------------
       Properties of the absolute value function over the reals
       (adapted version of previously proved theorems about abs)
 ----------------------------------------------------------------------------*)
Goalw [rabs_def] "rabs r = (if 0r<=r then r else -r)";
by Auto_tac;
qed "rabs_iff";

Goalw [rabs_def] "rabs 0r = 0r";
by (rtac (real_le_refl RS if_P) 1);
qed "rabs_zero";

Addsimps [rabs_zero];

Goalw [rabs_def] "rabs 0r = -0r";
by (Simp_tac 1);
qed "rabs_minus_zero";

Goalw [rabs_def] "0r<=x ==> rabs x = x";
by (Asm_simp_tac 1);
qed "rabs_eqI1";

Goalw [rabs_def] "0r<x ==> rabs x = x";
by (Asm_simp_tac 1);
qed "rabs_eqI2";

Goalw [rabs_def,real_le_def] "x<0r ==> rabs x = -x";
by (Asm_simp_tac 1);
qed "rabs_minus_eqI2";

Goalw [rabs_def] "x<=0r ==> rabs x = -x";
by (asm_full_simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_minus_eqI1";

Goalw [rabs_def] "0r<= rabs x";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_ge_zero";

Goalw [rabs_def] "rabs(rabs x)=rabs x";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_idempotent";

Goalw [rabs_def] "(x=0r) = (rabs x = 0r)";
by (Full_simp_tac 1);
qed "rabs_zero_iff";

Goal  "(x ~= 0r) = (rabs x ~= 0r)";
by (full_simp_tac (simpset() addsimps [rabs_zero_iff RS sym]) 1);
qed "rabs_not_zero_iff";

Goalw [rabs_def] "x<=rabs x";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_ge_self";

Goalw [rabs_def] "-x<=rabs x";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_ge_minus_self";

(* case splits nightmare *)
Goalw [rabs_def] "rabs(x*y) = (rabs x)*(rabs y)";
by (auto_tac (claset(),
	      simpset() addsimps [real_minus_mult_eq1, real_minus_mult_commute,
				  real_minus_mult_eq2]));
by (blast_tac (claset() addDs [real_le_mult_order]) 1);
by (auto_tac (claset() addSDs [not_real_leE], simpset()));
by (EVERY1[dtac real_mult_le_zero, assume_tac, dtac real_le_anti_sym]);
by (EVERY[dtac real_mult_le_zero 3, assume_tac 3, dtac real_le_anti_sym 3]);
by (dtac real_mult_less_zero1 5 THEN assume_tac 5);
by (auto_tac (claset() addDs [real_less_asym,sym],
	      simpset() addsimps [real_minus_mult_eq2 RS sym] @real_mult_ac));
qed "rabs_mult";

Goalw [rabs_def] "x~= 0r ==> rabs(rinv(x)) = rinv(rabs(x))";
by (auto_tac (claset(), simpset() addsimps [real_minus_rinv]));
by (ALLGOALS(dtac not_real_leE));
by (etac real_less_asym 1);
by (blast_tac (claset() addDs [real_le_imp_less_or_eq, real_rinv_gt_zero]) 1);
by (dtac (rinv_not_zero RS not_sym) 1);
by (rtac (real_rinv_less_zero RSN (2,real_less_asym)) 1);
by (assume_tac 2);
by (blast_tac (claset() addSDs [real_le_imp_less_or_eq]) 1);
qed "rabs_rinv";

Goal "y ~= 0r ==> rabs(x*rinv(y)) = rabs(x)*rinv(rabs(y))";
by (asm_simp_tac (simpset() addsimps [rabs_mult, rabs_rinv]) 1);
qed "rabs_mult_rinv";

Goalw [rabs_def] "rabs(x+y) <= rabs x + rabs y";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_triangle_ineq";

(*Unused, but perhaps interesting as an example*)
Goal "rabs(w + x + y + z) <= rabs(w) + rabs(x) + rabs(y) + rabs(z)";
by (simp_tac (simpset() addsimps [rabs_triangle_ineq RS order_trans]) 1);
qed "rabs_triangle_ineq_four";

Goalw [rabs_def] "rabs(-x)=rabs(x)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_minus_cancel";

Goalw [rabs_def] "rabs(x + (-y)) = rabs (y + (-x))";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_minus_add_cancel";

Goalw [rabs_def] "rabs(x + (-y)) <= rabs x + rabs y";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_triangle_minus_ineq";

Goalw [rabs_def] "rabs x < r --> rabs y < s --> rabs(x+y) < r+s";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed_spec_mp "rabs_add_less";

Goalw [rabs_def] "rabs x < r --> rabs y < s --> rabs(x+ (-y)) < r+s";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "rabs_add_minus_less";

(* lemmas manipulating terms *)
Goal "(0r*x<r)=(0r<r)";
by (Simp_tac 1);
qed "real_mult_0_less";

Goal "[| 0r<y; x<r; y*r<t*s |] ==> y*x<t*s";
by (blast_tac (claset() addSIs [real_mult_less_mono2]
	                addIs  [real_less_trans]) 1);
qed "real_mult_less_trans";

Goal "[| 0r<=y; x<r; y*r<t*s; 0r<t*s|] ==> y*x<t*s";
by (dtac real_le_imp_less_or_eq 1);
by (fast_tac (HOL_cs addEs [real_mult_0_less RS iffD2,
			    real_mult_less_trans]) 1);
qed "real_mult_le_less_trans";

(* proofs lifted from previous older version
   FIXME: use a stronger version of real_mult_less_mono *)
Goal "[| rabs x<r; rabs y<s |] ==> rabs(x*y)<r*s";
by (simp_tac (simpset() addsimps [rabs_mult]) 1);
by (rtac real_mult_le_less_trans 1);
by (rtac rabs_ge_zero 1);
by (assume_tac 1);
by (blast_tac (HOL_cs addIs [rabs_ge_zero, real_mult_less_mono1, 
			     real_le_less_trans]) 1);
by (blast_tac (HOL_cs addIs [rabs_ge_zero, real_mult_order, 
			     real_le_less_trans]) 1);
qed "rabs_mult_less";

Goal "[| rabs x < r; rabs y < s |] ==> rabs(x)*rabs(y)<r*s";
by (auto_tac (claset() addIs [rabs_mult_less],
              simpset() addsimps [rabs_mult RS sym]));
qed "rabs_mult_less2";

Goal "1r < rabs x ==> rabs y <= rabs(x*y)";
by (cut_inst_tac [("x1","y")] (rabs_ge_zero RS real_le_imp_less_or_eq) 1);
by (EVERY1[etac disjE,rtac real_less_imp_le]);
by (dres_inst_tac [("W","1r")]  real_less_sum_gt_zero 1);
by (forw_inst_tac [("y","rabs x + (-1r)")] real_mult_order 1);
by (assume_tac 1);
by (rtac real_sum_gt_zero_less 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
					   real_mult_commute, rabs_mult]) 1);
by (dtac sym 1);
by (asm_full_simp_tac (simpset() addsimps [rabs_mult]) 1);
qed "rabs_mult_le";

Goal "[| 1r < rabs x; r < rabs y|] ==> r < rabs(x*y)";
by (blast_tac (HOL_cs addIs [rabs_mult_le, real_less_le_trans]) 1);
qed "rabs_mult_gt";

Goal "rabs(x)<r ==> 0r<r";
by (blast_tac (claset() addSIs [real_le_less_trans,rabs_ge_zero]) 1);
qed "rabs_less_gt_zero";

Goalw [rabs_def] "rabs 1r = 1r";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0, one_eq_numeral_1]) 1);
qed "rabs_one";

Goalw [rabs_def] "rabs x =x | rabs x = -x";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "rabs_disj";

Goalw [rabs_def] "(rabs x < r) = (-r<x & x<r)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "rabs_interval_iff";

Goalw [rabs_def] "(rabs x <= r) = (-r<=x & x<=r)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "rabs_le_interval_iff";

Goalw [rabs_def] "(rabs (x + (-y)) < r) = (y + (-r) < x & x < y + r)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "rabs_add_minus_interval_iff";

Goalw [rabs_def] "0r < k ==> 0r < k + rabs(x)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "rabs_add_pos_gt_zero";

Goalw [rabs_def] "0r < 1r + rabs(x)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0, one_eq_numeral_1]));
qed "rabs_add_one_gt_zero";
Addsimps [rabs_add_one_gt_zero];


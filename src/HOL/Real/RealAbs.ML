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
Goalw [abs_real_def] "abs r = (if 0r<=r then r else -r)";
by Auto_tac;
qed "abs_iff";

Goalw [abs_real_def] "abs 0r = 0r";
by (rtac (real_le_refl RS if_P) 1);
qed "abs_zero";

Addsimps [abs_zero];

Goalw [abs_real_def] "abs 0r = -0r";
by (Simp_tac 1);
qed "abs_minus_zero";

Goalw [abs_real_def] "0r<=x ==> abs x = x";
by (Asm_simp_tac 1);
qed "abs_eqI1";

Goalw [abs_real_def] "0r<x ==> abs x = x";
by (Asm_simp_tac 1);
qed "abs_eqI2";

Goalw [abs_real_def,real_le_def] "x<0r ==> abs x = -x";
by (Asm_simp_tac 1);
qed "abs_minus_eqI2";

Goalw [abs_real_def] "x<=0r ==> abs x = -x";
by (asm_full_simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_minus_eqI1";

Goalw [abs_real_def] "0r<= abs x";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_ge_zero";

Goalw [abs_real_def] "abs(abs x)=abs (x::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_idempotent";

Goalw [abs_real_def] "(x=0r) = (abs x = 0r)";
by (Full_simp_tac 1);
qed "abs_zero_iff";

Goal  "(x ~= 0r) = (abs x ~= 0r)";
by (full_simp_tac (simpset() addsimps [abs_zero_iff RS sym]) 1);
qed "abs_not_zero_iff";

Goalw [abs_real_def] "x<=abs (x::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_ge_self";

Goalw [abs_real_def] "-x<=abs (x::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_ge_minus_self";

(* case splits nightmare *)
Goalw [abs_real_def] "abs (x * y) = abs x * abs (y::real)";
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
qed "abs_mult";

Goalw [abs_real_def] "x~= 0r ==> abs(rinv(x)) = rinv(abs(x))";
by (auto_tac (claset(), simpset() addsimps [real_minus_rinv]));
by (ALLGOALS(dtac not_real_leE));
by (etac real_less_asym 1);
by (blast_tac (claset() addDs [real_le_imp_less_or_eq, real_rinv_gt_zero]) 1);
by (dtac (rinv_not_zero RS not_sym) 1);
by (rtac (real_rinv_less_zero RSN (2,real_less_asym)) 1);
by (assume_tac 2);
by (blast_tac (claset() addSDs [real_le_imp_less_or_eq]) 1);
qed "abs_rinv";

Goal "y ~= 0r ==> abs(x*rinv(y)) = abs(x)*rinv(abs(y))";
by (asm_simp_tac (simpset() addsimps [abs_mult, abs_rinv]) 1);
qed "abs_mult_rinv";

Goalw [abs_real_def] "abs(x+y) <= abs x + abs (y::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_triangle_ineq";

(*Unused, but perhaps interesting as an example*)
Goal "abs(w + x + y + z) <= abs(w) + abs(x) + abs(y) + abs(z::real)";
by (simp_tac (simpset() addsimps [abs_triangle_ineq RS order_trans]) 1);
qed "abs_triangle_ineq_four";

Goalw [abs_real_def] "abs(-x)=abs(x::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_minus_cancel";

Goalw [abs_real_def] "abs(x + (-y)) = abs (y + (-(x::real)))";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_minus_add_cancel";

Goalw [abs_real_def] "abs(x + (-y)) <= abs x + abs (y::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_triangle_minus_ineq";

Goalw [abs_real_def] "abs x < r --> abs y < s --> abs(x+y) < r+(s::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed_spec_mp "abs_add_less";

Goalw [abs_real_def] "abs x < r --> abs y < s --> abs(x+ (-y)) < r+(s::real)";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0]) 1);
qed "abs_add_minus_less";

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
Goal "[| abs x<r; abs y<s |] ==> abs(x*y)<r*(s::real)";
by (simp_tac (simpset() addsimps [abs_mult]) 1);
by (rtac real_mult_le_less_trans 1);
by (rtac abs_ge_zero 1);
by (assume_tac 1);
by (blast_tac (HOL_cs addIs [abs_ge_zero, real_mult_less_mono1, 
			     real_le_less_trans]) 1);
by (blast_tac (HOL_cs addIs [abs_ge_zero, real_mult_order, 
			     real_le_less_trans]) 1);
qed "abs_mult_less";

Goal "[| abs x < r; abs y < s |] ==> abs(x)*abs(y)<r*(s::real)";
by (auto_tac (claset() addIs [abs_mult_less],
              simpset() addsimps [abs_mult RS sym]));
qed "abs_mult_less2";

Goal "1r < abs x ==> abs y <= abs(x*y)";
by (cut_inst_tac [("x1","y")] (abs_ge_zero RS real_le_imp_less_or_eq) 1);
by (EVERY1[etac disjE,rtac real_less_imp_le]);
by (dres_inst_tac [("W","1r")]  real_less_sum_gt_zero 1);
by (forw_inst_tac [("y","abs x + (-1r)")] real_mult_order 1);
by (assume_tac 1);
by (rtac real_sum_gt_zero_less 1);
by (asm_full_simp_tac (simpset() addsimps [real_add_mult_distrib2,
					   real_mult_commute, abs_mult]) 1);
by (dtac sym 1);
by (asm_full_simp_tac (simpset() addsimps [abs_mult]) 1);
qed "abs_mult_le";

Goal "[| 1r < abs x; r < abs y|] ==> r < abs(x*y)";
by (blast_tac (HOL_cs addIs [abs_mult_le, real_less_le_trans]) 1);
qed "abs_mult_gt";

Goal "abs(x)<r ==> 0r<r";
by (blast_tac (claset() addSIs [real_le_less_trans,abs_ge_zero]) 1);
qed "abs_less_gt_zero";

Goalw [abs_real_def] "abs 1r = 1r";
by (simp_tac (simpset() addsimps [zero_eq_numeral_0, one_eq_numeral_1]) 1);
qed "abs_one";

Goalw [abs_real_def] "abs x =x | abs x = -(x::real)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "abs_disj";

Goalw [abs_real_def] "(abs x < r) = (-r<x & x<(r::real))";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "abs_interval_iff";

Goalw [abs_real_def] "(abs x <= r) = (-r<=x & x<=(r::real))";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "abs_le_interval_iff";

Goalw [abs_real_def] "(abs (x + (-y)) < r) = (y + (-r) < x & x < y + (r::real))";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "abs_add_minus_interval_iff";

Goalw [abs_real_def] "0r < k ==> 0r < k + abs(x)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0]));
qed "abs_add_pos_gt_zero";

Goalw [abs_real_def] "0r < 1r + abs(x)";
by (auto_tac (claset(), simpset() addsimps [zero_eq_numeral_0, one_eq_numeral_1]));
qed "abs_add_one_gt_zero";
Addsimps [abs_add_one_gt_zero];

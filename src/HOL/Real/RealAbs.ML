(*  Title       : RealAbs.ML
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
by (stac real_minus_zero 1);
by (rtac if_cancel 1);
qed "rabs_minus_zero";

val [prem] = goalw thy [rabs_def] "0r<=x ==> rabs x = x";
by (rtac (prem RS if_P) 1);
qed "rabs_eqI1";

val [prem] = goalw thy [rabs_def] "0r<x ==> rabs x = x";
by (simp_tac (simpset() addsimps [(prem RS real_less_imp_le),rabs_eqI1]) 1);
qed "rabs_eqI2";

val [prem] = goalw thy [rabs_def,real_le_def] "x<0r ==> rabs x = -x";
by (simp_tac (simpset() addsimps [prem,if_not_P]) 1);
qed "rabs_minus_eqI2";

Goal "x<=0r ==> rabs x = -x";
by (dtac real_le_imp_less_or_eq 1);
by (blast_tac (HOL_cs addIs [rabs_minus_zero,rabs_minus_eqI2]) 1);
qed "rabs_minus_eqI1";

Goalw [rabs_def,real_le_def] "0r<= rabs x";
by (Full_simp_tac 1);
by (blast_tac (claset() addDs [real_minus_zero_less_iff RS iffD2,
			       real_less_asym]) 1);
qed "rabs_ge_zero";

Goal "rabs(rabs x)=rabs x";
by (res_inst_tac [("r1","rabs x")] (rabs_iff RS ssubst) 1);
by (blast_tac (claset() addIs [if_P,rabs_ge_zero]) 1);
qed "rabs_idempotent";

Goalw [rabs_def] "(x=0r) = (rabs x = 0r)";
by (Full_simp_tac 1);
qed "rabs_zero_iff";

Goal  "(x ~= 0r) = (rabs x ~= 0r)";
by (full_simp_tac (simpset() addsimps [rabs_zero_iff RS sym]) 1);
qed "rabs_not_zero_iff";

Goalw [rabs_def] "x<=rabs x";
by (Full_simp_tac 1);
by (auto_tac (claset() addDs [not_real_leE RS real_less_imp_le],
	      simpset() addsimps [real_le_zero_iff]));
qed "rabs_ge_self";

Goalw [rabs_def] "-x<=rabs x";
by (full_simp_tac (simpset() addsimps [real_ge_zero_iff]) 1);
qed "rabs_ge_minus_self";

(* case splits nightmare *)
Goalw [rabs_def] "rabs(x*y) = (rabs x)*(rabs y)";
by (auto_tac (claset(),simpset() addsimps [real_minus_mult_eq1,
   real_minus_mult_commute,real_minus_mult_eq2]));
by (blast_tac (claset() addDs [real_le_mult_order]) 1);
by (auto_tac (claset() addSDs [not_real_leE],simpset()));
by (EVERY1[dtac real_mult_le_zero, assume_tac, dtac real_le_anti_sym]);
by (EVERY[dtac real_mult_le_zero 3, assume_tac 3, dtac real_le_anti_sym 3]);
by (dtac real_mult_less_zero1 5 THEN assume_tac 5);
by (auto_tac (claset() addDs [real_less_asym,sym],
    simpset() addsimps [real_minus_mult_eq2 RS sym] @real_mult_ac));
qed "rabs_mult";

Goalw [rabs_def] "x~= 0r ==> rabs(rinv(x)) = rinv(rabs(x))";
by (auto_tac (claset(),simpset() addsimps [real_minus_rinv] 
   ));
by (ALLGOALS(dtac not_real_leE));
by (etac real_less_asym 1);
by (blast_tac (claset() addDs [real_le_imp_less_or_eq,
          real_rinv_gt_zero]) 1);
by (dtac (rinv_not_zero RS not_sym) 1);
by (rtac (real_rinv_less_zero RSN (2,real_less_asym)) 1);
by (assume_tac 2);
by (blast_tac (claset() addSDs [real_le_imp_less_or_eq]) 1);
qed "rabs_rinv";

val [prem] = goal thy "y ~= 0r ==> rabs(x*rinv(y)) = rabs(x)*rinv(rabs(y))";
by (res_inst_tac [("c1","rabs y")] (real_mult_left_cancel RS subst) 1);
by (simp_tac (simpset() addsimps [(rabs_not_zero_iff RS sym), prem]) 1);
by (simp_tac (simpset() addsimps [(rabs_mult RS sym) ,real_mult_inv_right, 
    prem,rabs_not_zero_iff RS sym] @ real_mult_ac) 1);
qed "rabs_mult_rinv";

Goal "rabs(x+y) <= rabs x + rabs y";
by (EVERY1 [res_inst_tac [("Q1","0r<=x+y")] (expand_if RS ssubst), rtac conjI]);
by (asm_simp_tac
    (simpset() addsimps [rabs_eqI1,real_add_le_mono,rabs_ge_self]) 1);
by (asm_simp_tac 
    (simpset() addsimps [not_real_leE,rabs_minus_eqI2,real_add_le_mono,
			 rabs_ge_minus_self]) 1);
qed "rabs_triangle_ineq";

Goal "rabs(w + x + y + z) <= rabs(w) + rabs(x) + rabs(y) + rabs(z)";
by (full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (blast_tac (claset() addSIs [(rabs_triangle_ineq RS real_le_trans),
				real_add_left_le_mono1]) 1);
qed "rabs_triangle_ineq_four";

Goalw [rabs_def] "rabs(-x)=rabs(x)";
by (auto_tac (claset() addSDs [not_real_leE,real_less_asym] addIs [real_le_anti_sym],
   simpset() addsimps [real_ge_zero_iff]));
qed "rabs_minus_cancel";

Goal "rabs(x + -y) = rabs (y + -x)";
by (rtac (rabs_minus_cancel RS subst) 1);
by (simp_tac (simpset() addsimps 
    [real_add_commute]) 1);
qed "rabs_minus_add_cancel";

Goal "rabs(x + -y) <= rabs x + rabs y";
by (res_inst_tac [("x1","y")] (rabs_minus_cancel RS subst) 1);
by (rtac rabs_triangle_ineq 1);
qed "rabs_triangle_minus_ineq";

Goal "rabs (x + y + (-l + -m)) <= rabs(x + -l) + rabs(y + -m)";
by (full_simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (res_inst_tac [("x1","y")] (real_add_left_commute RS ssubst) 1);
by (rtac (real_add_assoc RS subst) 1);
by (rtac rabs_triangle_ineq 1);
qed "rabs_sum_triangle_ineq";

Goal "rabs(x) <= rabs(x + -y) + rabs(y)";
by (res_inst_tac [("j","rabs(x + -y + y)")] real_le_trans 1);
by (simp_tac (simpset() addsimps [real_add_assoc]) 1);
by (simp_tac (simpset() addsimps [real_add_assoc RS sym,
              rabs_triangle_ineq]) 1);
qed "rabs_triangle_ineq_minus_cancel";

Goal "[| rabs x < r; rabs y < s |] ==> rabs(x+y) < r+s";
by (rtac real_le_less_trans 1);
by (rtac rabs_triangle_ineq 1);
by (REPEAT (ares_tac [real_add_less_mono] 1));
qed "rabs_add_less";

Goal "[| rabs x < r; rabs y < s |] ==> rabs(x+ -y) < r+s";
by (rotate_tac 1 1);
by (dtac (rabs_minus_cancel RS ssubst) 1);
by (asm_simp_tac (simpset() addsimps [rabs_add_less]) 1);
qed "rabs_add_minus_less";

(* lemmas manipulating terms *)
Goal "(0r*x<r)=(0r<r)";
by (Simp_tac 1);
qed "real_mult_0_less";

Goal "[| 0r<y; x<r; y*r<t*s |] ==> y*x<t*s";
by (blast_tac (claset() addSIs [real_mult_less_mono2]
	                addIs  [real_less_trans]) 1);
qed "real_mult_less_trans";

Goal "!!(x::real) y.[| 0r<=y; x<r; y*r<t*s; 0r<t*s|] ==> y*x<t*s";
by (dtac real_le_imp_less_or_eq 1);
by (fast_tac (HOL_cs addEs [real_mult_0_less RS iffD2,
			    real_mult_less_trans]) 1);
qed "real_mult_le_less_trans";

(* proofs lifted from previous older version *)
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
by (forw_inst_tac [("y","rabs x + -1r")] real_mult_order 1);
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
by (auto_tac (claset() addSDs [not_real_leE RS real_less_asym],
   simpset() addsimps [real_zero_less_one]));
qed "rabs_one";

Goal "[| 0r < x ; x < r |] ==> rabs x < r";
by (asm_simp_tac (simpset() addsimps [rabs_eqI2]) 1);
qed "rabs_lessI";

Goal "rabs x =x | rabs x = -x";
by (cut_inst_tac [("R1.0","0r"),("R2.0","x")] real_linear 1);
by (blast_tac (claset() addIs [rabs_eqI2,rabs_minus_eqI2,
                            rabs_zero,rabs_minus_zero]) 1);
qed "rabs_disj";

Goal "rabs x = y ==> x = y | -x = y";
by (dtac sym 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("x1","x")] (rabs_disj RS disjE) 1);
by (REPEAT(Asm_simp_tac 1));
qed "rabs_eq_disj";

Goal "(rabs x < r) = (-r<x & x<r)";
by Safe_tac;
by (rtac (real_less_swap_iff RS iffD2) 1);
by (asm_simp_tac (simpset() addsimps [(rabs_ge_minus_self 
    RS real_le_less_trans)]) 1);
by (asm_simp_tac (simpset() addsimps [(rabs_ge_self 
    RS real_le_less_trans)]) 1);
by (EVERY1 [dtac (real_less_swap_iff RS iffD1), rotate_tac 1, 
            dtac (real_minus_minus RS subst), 
            cut_inst_tac [("x","x")] rabs_disj, dtac disjE ]);
by (assume_tac 3 THEN Auto_tac);
qed "rabs_interval_iff";

Goal "(rabs x < r) = (-x < r & x < r)";
by (auto_tac (claset(),simpset() addsimps [rabs_interval_iff]));
by (dtac (real_less_swap_iff RS iffD1) 1);
by (dtac (real_less_swap_iff RS iffD1) 2);
by (Auto_tac);
qed "rabs_interval_iff2";

Goal "!!x. rabs x <= r ==> -r<=x & x<=r";
by (dtac real_le_imp_less_or_eq 1);
by (auto_tac (claset() addSDs [real_less_imp_le],
    simpset() addsimps [rabs_interval_iff,rabs_ge_self]));
by (auto_tac (claset(),simpset() addsimps [real_le_def]));
by (dtac (real_less_swap_iff RS iffD1) 1);
by (auto_tac (claset() addSDs [rabs_ge_minus_self 
    RS real_le_less_trans],simpset() addsimps [real_less_not_refl]));
qed "rabs_leD";

Goal "!!x. [| -r<x; x<=r |] ==> rabs x <= r";
by (dtac real_le_imp_less_or_eq 1);
by (Step_tac 1);
by (blast_tac (claset() addIs 
    [rabs_interval_iff RS iffD2 RS real_less_imp_le]) 1);
by (auto_tac (claset() addSDs [rabs_eqI2],simpset() addsimps 
    [real_le_def,real_gt_zero_iff RS sym,real_less_not_refl]));
qed "rabs_leI1";

Goal "!!x. [| -r<=x; x<=r |] ==> rabs x <= r";
by (REPEAT(dtac real_le_imp_less_or_eq 1));
by (Step_tac 1);
by (blast_tac (claset() addIs 
    [rabs_interval_iff RS iffD2 RS real_less_imp_le]) 1);
by (auto_tac (claset() addSDs [rabs_eqI2],simpset() addsimps 
    [real_le_def,real_gt_zero_iff RS sym,real_less_not_refl,
    rabs_minus_cancel]));
by (cut_inst_tac [("x","r")] rabs_disj 1);
by (rotate_tac 1 1);
by (auto_tac (claset(),simpset() addsimps [real_less_not_refl]));
qed "rabs_leI";

Goal "(rabs x <= r) = (-r<=x & x<=r)";
by (blast_tac (claset() addSIs [rabs_leD,rabs_leI]) 1);
qed "rabs_le_interval_iff";

Goal 
     "(rabs (x + -y) < r) = (y + -r < x & x < y + r)";
by (auto_tac (claset(),simpset() addsimps 
     [rabs_interval_iff]));
by (ALLGOALS(dtac real_less_sum_gt_zero));
by (ALLGOALS(dtac real_less_sum_gt_zero));
by (ALLGOALS(rtac real_sum_gt_zero_less));
by (auto_tac (claset(),simpset() addsimps 
    [real_minus_add_distrib] addsimps real_add_ac));
qed "rabs_add_minus_interval_iff";

Goal "!!k. 0r < k ==> 0r < k + rabs(x)";
by (res_inst_tac [("t","0r")] (real_add_zero_right RS subst) 1);
by (etac (rabs_ge_zero RSN (2,real_add_less_le_mono)) 1);
qed "rabs_add_pos_gt_zero";

Goal "0r < 1r + rabs(x)";
by (rtac (real_zero_less_one RS rabs_add_pos_gt_zero) 1);
qed "rabs_add_one_gt_zero";
Addsimps [rabs_add_one_gt_zero];


(*  Title       : RealPow.ML
    ID          : $Id$
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural Powers of reals theory
*)

bind_thm ("realpow_Suc", thm "realpow_Suc");

Goal "(#0::real) ^ (Suc n) = #0";
by Auto_tac;
qed "realpow_zero";
Addsimps [realpow_zero];

Goal "r ~= (#0::real) --> r ^ n ~= #0";
by (induct_tac "n" 1);
by Auto_tac; 
qed_spec_mp "realpow_not_zero";

Goal "r ^ n = (#0::real) ==> r = #0";
by (rtac ccontr 1);
by (auto_tac (claset() addDs [realpow_not_zero], simpset()));
qed "realpow_zero_zero";

Goal "inverse ((r::real) ^ n) = (inverse r) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [real_inverse_distrib]));
qed "realpow_inverse";

Goal "abs (r::real) ^ n = abs (r ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [abs_mult,abs_one]));
qed "realpow_abs";

Goal "(r::real) ^ (n + m) = (r ^ n) * (r ^ m)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "realpow_add";

Goal "(r::real) ^ 1 = r";
by (Simp_tac 1);
qed "realpow_one";
Addsimps [realpow_one];

Goal "(r::real) ^ 2 = r * r";
by (Simp_tac 1);
qed "realpow_two";

Goal "(#0::real) < r --> #0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addDs [real_less_imp_le] 
	               addIs [rename_numerals real_le_mult_order],
	      simpset()));
qed_spec_mp "realpow_ge_zero";

Goal "(#0::real) < r --> #0 < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [rename_numerals real_mult_order],
	      simpset() addsimps [real_zero_less_one]));
qed_spec_mp "realpow_gt_zero";

Goal "(#0::real) <= r --> #0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [rename_numerals real_le_mult_order],
              simpset()));
qed_spec_mp "realpow_ge_zero2";

Goal "(#0::real) < x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_mono],
    simpset()));
by (asm_simp_tac (simpset() addsimps [realpow_ge_zero]) 1);
qed_spec_mp "realpow_le";

Goal "(#0::real) <= x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_mono4],
    simpset()));
by (asm_simp_tac (simpset() addsimps [realpow_ge_zero2]) 1);
qed_spec_mp "realpow_le2";

Goal "(#0::real) < x & x < y & 0 < n --> x ^ n < y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [rename_numerals real_mult_less_mono, gr0I] 
                       addDs [realpow_gt_zero],
    simpset()));
qed_spec_mp "realpow_less";

Goal  "#1 ^ n = (#1::real)";
by (induct_tac "n" 1);
by Auto_tac;
qed "realpow_eq_one";
Addsimps [realpow_eq_one];

Goal "abs(-(#1 ^ n)) = (#1::real)";
by (simp_tac (simpset() addsimps 
    [abs_minus_cancel,abs_one]) 1);
qed "abs_minus_realpow_one";
Addsimps [abs_minus_realpow_one];

Goal "abs((#-1) ^ n) = (#1::real)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [abs_mult,
         abs_minus_cancel,abs_one]));
qed "abs_realpow_minus_one";
Addsimps [abs_realpow_minus_one];

Goal "((r::real) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "realpow_mult";

Goal "(#0::real) <= r ^ 2";
by (simp_tac (simpset() addsimps [rename_numerals real_le_square]) 1);
qed "realpow_two_le";
Addsimps [realpow_two_le];

Goal "abs((x::real) ^ 2) = x ^ 2";
by (simp_tac (simpset() addsimps [abs_eqI1, 
				  rename_numerals real_le_square]) 1);
qed "abs_realpow_two";
Addsimps [abs_realpow_two];

Goal "abs(x::real) ^ 2 = x ^ 2";
by (simp_tac (simpset() addsimps [realpow_abs,abs_eqI1]
                        delsimps [realpow_Suc]) 1);
qed "realpow_two_abs";
Addsimps [realpow_two_abs];

Goal "(#1::real) < r ==> #1 < r ^ 2";
by Auto_tac;
by (cut_facts_tac [rename_numerals real_zero_less_one] 1);
by (forw_inst_tac [("R1.0","#0")] real_less_trans 1);
by (assume_tac 1);
by (dres_inst_tac [("z","r"),("x","#1")] 
    (rename_numerals real_mult_less_mono1) 1);
by (auto_tac (claset() addIs [real_less_trans],simpset()));
qed "realpow_two_gt_one";

Goal "(#1::real) < r --> #1 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq],
	      simpset()));
by (dtac (rename_numerals (real_zero_less_one RS real_mult_less_mono)) 1);
by (dtac sym 4);
by (auto_tac (claset() addSIs [real_less_imp_le],
	      simpset() addsimps [real_zero_less_one]));
qed_spec_mp "realpow_ge_one";

Goal "(#1::real) < r ==> #1 < r ^ (Suc n)";
by (forw_inst_tac [("n","n")] realpow_ge_one 1);
by (dtac real_le_imp_less_or_eq 1 THEN Step_tac 1);
by (dtac sym 2);
by (ftac (rename_numerals (real_zero_less_one RS real_less_trans)) 1);
by (dres_inst_tac [("y","r ^ n")] 
    (rename_numerals real_mult_less_mono2) 1);
by (assume_tac 1);
by (auto_tac (claset() addDs [real_less_trans],
     simpset()));
qed "realpow_Suc_gt_one";

Goal "(#1::real) <= r ==> #1 <= r ^ n";
by (dtac real_le_imp_less_or_eq 1); 
by (auto_tac (claset() addDs [realpow_ge_one], simpset()));
qed "realpow_ge_one2";

Goal "(#0::real) < r ==> #0 < r ^ Suc n";
by (forw_inst_tac [("n","n")] realpow_ge_zero 1);
by (forw_inst_tac [("n1","n")]
    ((real_not_refl2 RS not_sym) RS realpow_not_zero RS not_sym) 1);
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq]
                       addIs [rename_numerals real_mult_order],
              simpset()));
qed "realpow_Suc_gt_zero";

Goal "(#0::real) <= r ==> #0 <= r ^ Suc n";
by (etac (real_le_imp_less_or_eq RS disjE) 1);
by (etac (realpow_ge_zero) 1);
by (dtac sym 1);
by (Asm_simp_tac 1);
qed "realpow_Suc_ge_zero";

Goal "(#1::real) <= #2 ^ n";
by (res_inst_tac [("j","#1 ^ n")] real_le_trans 1);
by (rtac realpow_le 2);
by (auto_tac (claset() addIs [real_less_imp_le],simpset()));
qed "two_realpow_ge_one";

Goal "real_of_nat n < #2 ^ n";
by (induct_tac "n" 1);
by Auto_tac;
by (stac real_mult_2 1);
by (rtac real_add_less_le_mono 1);
by (auto_tac (claset(),
	      simpset() addsimps [two_realpow_ge_one]));
qed "two_realpow_gt";
Addsimps [two_realpow_gt,two_realpow_ge_one];

Goal "(#-1) ^ (#2*n) = (#1::real)";
by (induct_tac "n" 1);
by Auto_tac;
qed "realpow_minus_one";
Addsimps [realpow_minus_one];

Goal "(#-1) ^ Suc (#2*n) = -(#1::real)";
by Auto_tac;
qed "realpow_minus_one_odd";
Addsimps [realpow_minus_one_odd];

Goal "(#-1) ^ Suc (Suc (#2*n)) = (#1::real)";
by Auto_tac;
qed "realpow_minus_one_even";
Addsimps [realpow_minus_one_even];

Goal "(#0::real) < r & r < (#1::real) --> r ^ Suc n < r ^ n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "realpow_Suc_less";

Goal "#0 <= r & r < (#1::real) --> r ^ Suc n <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_less_imp_le] addSDs
     [real_le_imp_less_or_eq],simpset()));
qed_spec_mp "realpow_Suc_le";

Goal "(#0::real) <= #0 ^ n";
by (case_tac "n" 1);
by Auto_tac;
qed "realpow_zero_le";
Addsimps [realpow_zero_le];

Goal "#0 < r & r < (#1::real) --> r ^ Suc n <= r ^ n";
by (blast_tac (claset() addSIs [real_less_imp_le,
    realpow_Suc_less]) 1);
qed_spec_mp "realpow_Suc_le2";

Goal "[| #0 <= r; r < (#1::real) |] ==> r ^ Suc n <= r ^ n";
by (etac (real_le_imp_less_or_eq RS disjE) 1);
by (rtac realpow_Suc_le2 1);
by Auto_tac;
qed "realpow_Suc_le3";

Goal "#0 <= r & r < (#1::real) & n < N --> r ^ N <= r ^ n";
by (induct_tac "N" 1);
by Auto_tac;
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_zero2));
by (ALLGOALS(dtac (rename_numerals real_mult_le_mono3)));
by (REPEAT(assume_tac 1));
by (REPEAT(assume_tac 3));
by (auto_tac (claset(),simpset() addsimps 
    [less_Suc_eq]));
qed_spec_mp "realpow_less_le";

Goal "[| #0 <= r; r < (#1::real); n <= N |] ==> r ^ N <= r ^ n";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_less_le],
    simpset()));
qed "realpow_le_le";

Goal "[| #0 < r; r < (#1::real) |] ==> r ^ Suc n <= r";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    (real_less_imp_le RS realpow_le_le) 1);
by Auto_tac;
qed "realpow_Suc_le_self";

Goal "[| #0 < r; r < (#1::real) |] ==> r ^ Suc n < #1";
by (blast_tac (claset() addIs [realpow_Suc_le_self,
               real_le_less_trans]) 1);
qed "realpow_Suc_less_one";

Goal "(#1::real) <= r --> r ^ n <= r ^ Suc n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "realpow_le_Suc";

Goal "(#1::real) < r --> r ^ n < r ^ Suc n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "realpow_less_Suc";

Goal "(#1::real) < r --> r ^ n <= r ^ Suc n";
by (blast_tac (claset() addSIs [real_less_imp_le,
    realpow_less_Suc]) 1);
qed_spec_mp "realpow_le_Suc2";

Goal "(#1::real) < r & n < N --> r ^ n <= r ^ N";
by (induct_tac "N" 1);
by Auto_tac;
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_one));
by (ALLGOALS(dtac (rename_numerals real_mult_self_le)));
by (assume_tac 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [real_le_trans],
    simpset() addsimps [less_Suc_eq]));
qed_spec_mp "realpow_gt_ge";

Goal "(#1::real) <= r & n < N --> r ^ n <= r ^ N";
by (induct_tac "N" 1);
by Auto_tac;
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_one2));
by (ALLGOALS(dtac (rename_numerals real_mult_self_le2)));
by (assume_tac 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [real_le_trans],
    simpset() addsimps [less_Suc_eq]));
qed_spec_mp "realpow_gt_ge2";

Goal "[| (#1::real) < r; n <= N |] ==> r ^ n <= r ^ N";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_gt_ge],simpset()));
qed "realpow_ge_ge";

Goal "[| (#1::real) <= r; n <= N |] ==> r ^ n <= r ^ N";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_gt_ge2],simpset()));
qed "realpow_ge_ge2";

Goal "(#1::real) < r ==> r <= r ^ Suc n";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    realpow_ge_ge 1);
by Auto_tac;
qed_spec_mp "realpow_Suc_ge_self";

Goal "(#1::real) <= r ==> r <= r ^ Suc n";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    realpow_ge_ge2 1);
by Auto_tac;
qed_spec_mp "realpow_Suc_ge_self2";

Goal "[| (#1::real) < r; 0 < n |] ==> r <= r ^ n";
by (dtac (less_not_refl2 RS  not0_implies_Suc) 1);
by (auto_tac (claset() addSIs 
    [realpow_Suc_ge_self],simpset()));
qed "realpow_ge_self";

Goal "[| (#1::real) <= r; 0 < n |] ==> r <= r ^ n";
by (dtac (less_not_refl2 RS  not0_implies_Suc) 1);
by (auto_tac (claset() addSIs [realpow_Suc_ge_self2],simpset()));
qed "realpow_ge_self2";

Goal "0 < n --> (x::real) ^ (n - 1) * x = x ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() 
    addsimps [real_mult_commute]));
qed_spec_mp "realpow_minus_mult";
Addsimps [realpow_minus_mult];

Goal "r ~= #0 ==> r * inverse r ^ 2 = inverse (r::real)";
by (asm_simp_tac (simpset() addsimps [realpow_two,
                  real_mult_assoc RS sym]) 1);
qed "realpow_two_mult_inverse";
Addsimps [realpow_two_mult_inverse];

(* 05/00 *)
Goal "(-x) ^ 2 = (x::real) ^ 2";
by (Simp_tac 1);
qed "realpow_two_minus";
Addsimps [realpow_two_minus];

Goal "(x::real) ^ 2 + - (y ^ 2) = (x + -y) * (x + y)";
by (simp_tac (simpset() addsimps [real_add_mult_distrib2,
    real_add_mult_distrib, real_minus_mult_eq2 RS sym] 
    @ real_mult_ac) 1);
qed "realpow_two_add_minus";

Goalw [real_diff_def] 
      "(x::real) ^ 2 - y ^ 2 = (x - y) * (x + y)";
by (simp_tac (simpset() addsimps [realpow_two_add_minus]
                        delsimps [realpow_Suc]) 1);
qed "realpow_two_diff";

Goalw [real_diff_def] 
      "((x::real) ^ 2 = y ^ 2) = (x = y | x = -y)";
by (auto_tac (claset(),simpset() delsimps [realpow_Suc]));
by (dtac (rename_numerals (real_eq_minus_iff RS iffD1 RS sym)) 1);
by (auto_tac (claset() addDs [rename_numerals real_add_minus_eq_minus], 
          simpset() addsimps [realpow_two_add_minus] delsimps [realpow_Suc]));
qed "realpow_two_disj";

(* used in Transc *)
Goal  "[|(x::real) ~= #0; m <= n |] ==> x ^ (n - m) = x ^ n * inverse (x ^ m)";
by (auto_tac (claset(),
              simpset() addsimps [le_eq_less_or_eq,
                                  less_iff_Suc_add,realpow_add,
                                  realpow_not_zero] @ real_mult_ac));
qed "realpow_diff";

Goal "real_of_nat (m) ^ n = real_of_nat (m ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),
              simpset() addsimps [real_of_nat_one, real_of_nat_mult]));
qed "realpow_real_of_nat";

Goal "#0 < real_of_nat (2 ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),
          simpset() addsimps [real_of_nat_mult, real_zero_less_mult_iff]));
qed "realpow_real_of_nat_two_pos";
Addsimps [realpow_real_of_nat_two_pos];


Goal "(#0::real) <= x --> #0 <= y --> x ^ Suc n <= y ^ Suc n --> x <= y";
by (induct_tac "n" 1);
by Auto_tac;
by (rtac real_leI 1);
by (auto_tac (claset(), 
              simpset() addsimps [inst "x" "#0" order_le_less,
                                  real_mult_le_0_iff])); 
by (subgoal_tac "inverse x * (x * (x * x ^ n)) <= inverse y * (y * (y * y ^ n))" 1);
by (rtac real_mult_le_mono 2);
by (asm_full_simp_tac (simpset() addsimps [realpow_ge_zero, real_0_le_mult_iff]) 4); 
by (asm_full_simp_tac (simpset() addsimps [real_inverse_le_iff]) 3);
by (asm_full_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
by (rtac real_inverse_gt_zero 1);  
by Auto_tac; 
qed_spec_mp "realpow_increasing";
  
Goal "[| (#0::real) <= x; #0 <= y; x ^ Suc n = y ^ Suc n |] ==> x = y";
by (blast_tac (claset() addIs [realpow_increasing, order_antisym, 
			       order_eq_refl, sym]) 1);
qed_spec_mp "realpow_Suc_cancel_eq";

(*  Title       : HyperPow.ML
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural Powers of hyperreals theory

Exponentials on the hyperreals
*)

Goal "(0::hypreal) ^ (Suc n) = 0";
by Auto_tac;
qed "hrealpow_zero";
Addsimps [hrealpow_zero];

Goal "r ~= (0::hypreal) --> r ^ n ~= 0";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "hrealpow_not_zero";

Goal "r ~= (0::hypreal) --> inverse(r ^ n) = (inverse r) ^ n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "hrealpow_inverse";

Goal "abs (r::hypreal) ^ n = abs (r ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [hrabs_mult]));
qed "hrealpow_hrabs";

Goal "(r::hypreal) ^ (n + m) = (r ^ n) * (r ^ m)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps mult_ac));
qed "hrealpow_add";

Goal "(r::hypreal) ^ Suc 0 = r";
by (Simp_tac 1);
qed "hrealpow_one";
Addsimps [hrealpow_one];

Goal "(r::hypreal) ^ Suc (Suc 0) = r * r";
by (Simp_tac 1);
qed "hrealpow_two";

Goal "(0::hypreal) <= r --> 0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [zero_le_mult_iff]));
qed_spec_mp "hrealpow_ge_zero";

Goal "(0::hypreal) < r --> 0 < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [zero_less_mult_iff]));
qed_spec_mp "hrealpow_gt_zero";

Goal "x <= y & (0::hypreal) < x --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [mult_mono], simpset()));
by (asm_simp_tac (simpset() addsimps [hrealpow_ge_zero]) 1);
qed_spec_mp "hrealpow_le";

Goal "x < y & (0::hypreal) < x & 0 < n --> x ^ n < y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [hypreal_mult_less_mono,gr0I],
              simpset() addsimps [hrealpow_gt_zero]));
qed "hrealpow_less";

Goal "1 ^ n = (1::hypreal)";
by (induct_tac "n" 1);
by Auto_tac;
qed "hrealpow_eq_one";
Addsimps [hrealpow_eq_one];

Goal "abs(-(1 ^ n)) = (1::hypreal)";
by Auto_tac;  
qed "hrabs_minus_hrealpow_one";
Addsimps [hrabs_minus_hrealpow_one];

Goal "abs(-1 ^ n) = (1::hypreal)";
by (induct_tac "n" 1);
by Auto_tac;  
qed "hrabs_hrealpow_minus_one";
Addsimps [hrabs_hrealpow_minus_one];

Goal "((r::hypreal) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps mult_ac));
qed "hrealpow_mult";

Goal "(0::hypreal) <= r ^ Suc (Suc 0)";
by (auto_tac (claset(), simpset() addsimps [zero_le_mult_iff]));
qed "hrealpow_two_le";
Addsimps [hrealpow_two_le];

Goal "(0::hypreal) <= u ^ Suc (Suc 0) + v ^ Suc (Suc 0)";
by (simp_tac (HOL_ss addsimps [hrealpow_two_le, hypreal_le_add_order]) 1); 
qed "hrealpow_two_le_add_order";
Addsimps [hrealpow_two_le_add_order];

Goal "(0::hypreal) <= u ^ Suc (Suc 0) + v ^ Suc (Suc 0) + w ^ Suc (Suc 0)";
by (simp_tac (HOL_ss addsimps [hrealpow_two_le, hypreal_le_add_order]) 1); 
qed "hrealpow_two_le_add_order2";
Addsimps [hrealpow_two_le_add_order2];

Goal "[| 0 <= x; 0 <= y |] ==> (x+y = 0) = (x = 0 & y = (0::hypreal))";
by (auto_tac (claset() addIs [order_antisym], simpset()));
qed "hypreal_add_nonneg_eq_0_iff";

Goal "(x*x + y*y + z*z = 0) = (x = 0 & y = 0 & z = (0::hypreal))";
by (simp_tac (HOL_ss addsimps [zero_le_square, hypreal_le_add_order, 
                         hypreal_add_nonneg_eq_0_iff]) 1);
by Auto_tac;
qed "hypreal_three_squares_add_zero_iff";

Goal "(x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + z ^ Suc (Suc 0) = (0::hypreal)) = (x = 0 & y = 0 & z = 0)";
by (simp_tac (HOL_ss addsimps
               [hypreal_three_squares_add_zero_iff, hrealpow_two]) 1);
qed "hrealpow_three_squares_add_zero_iff";
Addsimps [hrealpow_three_squares_add_zero_iff];

Goal "abs(x ^ Suc (Suc 0)) = (x::hypreal) ^ Suc (Suc 0)";
by (auto_tac (claset(), 
              simpset() addsimps [hrabs_def, zero_le_mult_iff])); 
qed "hrabs_hrealpow_two";
Addsimps [hrabs_hrealpow_two];

Goal "abs(x) ^ Suc (Suc 0) = (x::hypreal) ^ Suc (Suc 0)";
by (simp_tac (simpset() addsimps [hrealpow_hrabs, hrabs_eqI1] 
                        delsimps [hpowr_Suc]) 1);
qed "hrealpow_two_hrabs";
Addsimps [hrealpow_two_hrabs];

Goal "(1::hypreal) < r ==> 1 < r ^ Suc (Suc 0)";
by (auto_tac (claset(), simpset() addsimps [hrealpow_two]));
by (res_inst_tac [("y","1*1")] order_le_less_trans 1); 
by (rtac hypreal_mult_less_mono 2); 
by Auto_tac;  
qed "hrealpow_two_gt_one";

Goal "(1::hypreal) <= r ==> 1 <= r ^ Suc (Suc 0)";
by (etac (order_le_imp_less_or_eq RS disjE) 1);
by (etac (hrealpow_two_gt_one RS order_less_imp_le) 1);
by Auto_tac;  
qed "hrealpow_two_ge_one";

Goal "(1::hypreal) <= 2 ^ n";
by (res_inst_tac [("y","1 ^ n")] order_trans 1);
by (rtac hrealpow_le 2);
by Auto_tac;
qed "two_hrealpow_ge_one";

Goal "hypreal_of_nat n < 2 ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),
        simpset() addsimps [hypreal_of_nat_Suc, left_distrib]));
by (cut_inst_tac [("n","n")] two_hrealpow_ge_one 1);
by (arith_tac 1);
qed "two_hrealpow_gt";
Addsimps [two_hrealpow_gt,two_hrealpow_ge_one];

Goal "-1 ^ (2*n) = (1::hypreal)";
by (induct_tac "n" 1);
by Auto_tac;
qed "hrealpow_minus_one";

Goal "n+n = (2*n::nat)";
by Auto_tac; 
qed "double_lemma";

(*ugh: need to get rid fo the n+n*)
Goal "-1 ^ (n + n) = (1::hypreal)";
by (auto_tac (claset(), 
              simpset() addsimps [double_lemma, hrealpow_minus_one]));
qed "hrealpow_minus_one2";
Addsimps [hrealpow_minus_one2];

Goal "(-(x::hypreal)) ^ Suc (Suc 0) = x ^ Suc (Suc 0)";
by Auto_tac;
qed "hrealpow_minus_two";
Addsimps [hrealpow_minus_two];

Goal "(0::hypreal) < r & r < 1 --> r ^ Suc n < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_mult_less_mono2]));
qed_spec_mp "hrealpow_Suc_less";

Goal "(0::hypreal) <= r & r < 1 --> r ^ Suc n <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [order_less_imp_le]
                       addSDs [order_le_imp_less_or_eq,hrealpow_Suc_less],
              simpset() addsimps [hypreal_mult_less_mono2]));
qed_spec_mp "hrealpow_Suc_le";

Goal "Abs_hypreal(hyprel``{%n. X n}) ^ m = Abs_hypreal(hyprel``{%n. (X n) ^ m})";
by (induct_tac "m" 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_one_def, hypreal_mult]));
qed "hrealpow";

Goal "(x + (y::hypreal)) ^ Suc (Suc 0) = \
\     x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + (hypreal_of_nat (Suc (Suc 0)))*x*y";
by (simp_tac (simpset() addsimps
              [right_distrib, left_distrib, 
               hypreal_of_nat_zero, hypreal_of_nat_Suc]) 1);
qed "hrealpow_sum_square_expand";


(*** Literal arithmetic involving powers, type hypreal ***)

Goal "hypreal_of_real (x ^ n) = hypreal_of_real x ^ n";
by (induct_tac "n" 1); 
by (ALLGOALS (asm_simp_tac (simpset() addsimps [nat_mult_distrib])));
qed "hypreal_of_real_power";
Addsimps [hypreal_of_real_power];

Goal "(number_of v :: hypreal) ^ n = hypreal_of_real ((number_of v) ^ n)";
by (simp_tac (HOL_ss addsimps [hypreal_number_of_def, 
                               hypreal_of_real_power]) 1);
qed "power_hypreal_of_real_number_of";

Addsimps [inst "n" "number_of ?w" power_hypreal_of_real_number_of];

(*---------------------------------------------------------------
   we'll prove the following theorem by going down to the
   level of the ultrafilter and relying on the analogous
   property for the real rather than prove it directly 
   using induction: proof is much simpler this way!
 ---------------------------------------------------------------*)
Goal "[|(0::hypreal) <= x; 0 <= y;x ^ Suc n <= y ^ Suc n |] ==> x <= y";
by (full_simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hrealpow,hypreal_le,hypreal_mult]));
by (ultra_tac (claset() addIs [realpow_increasing], simpset()) 1);
qed "hrealpow_increasing";

(*By antisymmetry with the above we conclude x=y, replacing the deleted 
  theorem hrealpow_Suc_cancel_eq*)

Goal "x : HFinite --> x ^ n : HFinite";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [HFinite_mult], simpset()));
qed_spec_mp "hrealpow_HFinite";

(*---------------------------------------------------------------
                  Hypernaturals Powers
 --------------------------------------------------------------*)
Goalw [congruent_def]
     "congruent hyprel \
\    (%X Y. hyprel``{%n. ((X::nat=>real) n ^ (Y::nat=>nat) n)})";
by (auto_tac (claset() addSIs [ext], simpset()));
by (ALLGOALS(Fuf_tac));
qed "hyperpow_congruent";

Goalw [hyperpow_def]
  "Abs_hypreal(hyprel``{%n. X n}) pow Abs_hypnat(hypnatrel``{%n. Y n}) = \
\  Abs_hypreal(hyprel``{%n. X n ^ Y n})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (auto_tac (claset() addSIs [lemma_hyprel_refl,bexI],
    simpset() addsimps [hyprel_in_hypreal RS 
    Abs_hypreal_inverse,equiv_hyprel,hyperpow_congruent]));
by (Fuf_tac 1);
qed "hyperpow";

Goalw [hypnat_one_def] "(0::hypreal) pow (n + (1::hypnat)) = 0";
by (simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow,hypnat_add]));
qed "hyperpow_zero";
Addsimps [hyperpow_zero];

Goal "r ~= (0::hypreal) --> r pow n ~= 0";
by (simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (fuf_empty_tac (claset() addIs [realpow_not_zero RS notE],
    simpset()) 1);
qed_spec_mp "hyperpow_not_zero";

Goal "r ~= (0::hypreal) --> inverse(r pow n) = (inverse r) pow n";
by (simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [FreeUltrafilterNat_Compl_mem],
              simpset() addsimps [hypreal_inverse,hyperpow]));
by (rtac FreeUltrafilterNat_subset 1);
by (auto_tac (claset() addDs [realpow_not_zero] 
                       addIs [realpow_inverse], 
              simpset()));
qed "hyperpow_inverse";

Goal "abs r pow n = abs (r pow n)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_hrabs, hyperpow,realpow_abs RS sym]));
qed "hyperpow_hrabs";

Goal "r pow (n + m) = (r pow n) * (r pow m)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
          simpset() addsimps [hyperpow,hypnat_add, hypreal_mult,realpow_add]));
qed "hyperpow_add";

Goalw [hypnat_one_def] "r pow (1::hypnat) = r";
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
qed "hyperpow_one";
Addsimps [hyperpow_one];

Goalw [hypnat_one_def] 
     "r pow ((1::hypnat) + (1::hypnat)) = r * r";
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hyperpow,hypnat_add, hypreal_mult]));
qed "hyperpow_two";

Goal "(0::hypreal) < r --> 0 < r pow n";
by (simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSEs [FreeUltrafilterNat_subset, realpow_gt_zero],
              simpset() addsimps [hyperpow,hypreal_less, hypreal_le]));
qed_spec_mp "hyperpow_gt_zero";

Goal "(0::hypreal) <= r --> 0 <= r pow n";
by (simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSEs [FreeUltrafilterNat_subset, realpow_ge_zero],
              simpset() addsimps [hyperpow,hypreal_le]));
qed "hyperpow_ge_zero";

Goal "(0::hypreal) < x & x <= y --> x pow n <= y pow n";
by (full_simp_tac (simpset() addsimps [hypreal_zero_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hyperpow,hypreal_le,hypreal_less]));
by (etac (FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset) 1
    THEN assume_tac 1);
by (auto_tac (claset() addIs [realpow_le], simpset()));
qed_spec_mp "hyperpow_le";

Goal "1 pow n = (1::hypreal)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_one_def, hyperpow]));
qed "hyperpow_eq_one";
Addsimps [hyperpow_eq_one];

Goal "abs(-(1 pow n)) = (1::hypreal)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), 
              simpset() addsimps [hyperpow, hypreal_hrabs, hypreal_one_def]));
qed "hrabs_minus_hyperpow_one";
Addsimps [hrabs_minus_hyperpow_one];

Goal "abs(-1 pow n) = (1::hypreal)";
by (subgoal_tac "abs((- (1::hypreal)) pow n) = (1::hypreal)" 1);
by (Asm_full_simp_tac 1); 
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_one_def, hyperpow,hypreal_minus,
                                  hypreal_hrabs]));
qed "hrabs_hyperpow_minus_one";
Addsimps [hrabs_hyperpow_minus_one];

Goal "(r * s) pow n = (r pow n) * (s pow n)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","s")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
       simpset() addsimps [hyperpow, hypreal_mult,realpow_mult]));
qed "hyperpow_mult";

Goal "(0::hypreal) <= r pow ((1::hypnat) + (1::hypnat))";
by (auto_tac (claset(), 
              simpset() addsimps [hyperpow_two, zero_le_mult_iff]));
qed "hyperpow_two_le";
Addsimps [hyperpow_two_le];

Goal "abs(x pow ((1::hypnat) + (1::hypnat))) = x pow ((1::hypnat) + (1::hypnat))";
by (simp_tac (simpset() addsimps [hrabs_eqI1]) 1);
qed "hrabs_hyperpow_two";
Addsimps [hrabs_hyperpow_two];

Goal "abs(x) pow ((1::hypnat) + (1::hypnat))  = x pow ((1::hypnat) + (1::hypnat))";
by (simp_tac (simpset() addsimps [hyperpow_hrabs,hrabs_eqI1]) 1);
qed "hyperpow_two_hrabs";
Addsimps [hyperpow_two_hrabs];

(*? very similar to hrealpow_two_gt_one *)
Goal "(1::hypreal) < r ==> 1 < r pow ((1::hypnat) + (1::hypnat))";
by (auto_tac (claset(), simpset() addsimps [hyperpow_two]));
by (res_inst_tac [("y","1*1")] order_le_less_trans 1); 
by (rtac hypreal_mult_less_mono 2); 
by Auto_tac;  
qed "hyperpow_two_gt_one";

Goal "(1::hypreal) <= r ==> 1 <= r pow ((1::hypnat) + (1::hypnat))";
by (auto_tac (claset() addSDs [order_le_imp_less_or_eq] 
                       addIs [hyperpow_two_gt_one,order_less_imp_le],
              simpset()));
qed "hyperpow_two_ge_one";

Goal "(1::hypreal) <= 2 pow n";
by (res_inst_tac [("y","1 pow n")] order_trans 1);
by (rtac hyperpow_le 2);
by Auto_tac;
qed "two_hyperpow_ge_one";
Addsimps [two_hyperpow_ge_one];

Addsimps [simplify (simpset()) realpow_minus_one];

Goal "-1 pow (((1::hypnat) + (1::hypnat))*n) = (1::hypreal)";
by (subgoal_tac "(-((1::hypreal))) pow (((1::hypnat) + (1::hypnat))*n) = (1::hypreal)" 1);
by (Asm_full_simp_tac 1); 
by (simp_tac (HOL_ss addsimps [hypreal_one_def]) 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [double_lemma, hyperpow, hypnat_add,
                                  hypreal_minus]));
qed "hyperpow_minus_one2";
Addsimps [hyperpow_minus_one2];

Goalw [hypnat_one_def]
     "(0::hypreal) < r & r < 1 --> r pow (n + (1::hypnat)) < r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [conjI RS realpow_Suc_less] 
                  addEs [FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset],
              simpset() addsimps [hypreal_zero_def, hypreal_one_def, 
                                  hyperpow, hypreal_less, hypnat_add]));
qed_spec_mp "hyperpow_Suc_less";

Goalw [hypnat_one_def]
     "0 <= r & r < (1::hypreal) --> r pow (n + (1::hypnat)) <= r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [conjI RS realpow_Suc_le] 
                 addEs [FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset],
              simpset() addsimps [hypreal_zero_def, hypreal_one_def, hyperpow,
                                  hypreal_le,hypnat_add, hypreal_less]));
qed_spec_mp "hyperpow_Suc_le";

Goalw [hypnat_one_def]
     "(0::hypreal) <= r & r < 1 & n < N --> r pow N <= r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hyperpow, hypreal_le,hypreal_less,
                           hypnat_less, hypreal_zero_def, hypreal_one_def]));
by (etac (FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset) 1);
by (etac FreeUltrafilterNat_Int 1);
by (auto_tac (claset() addSDs [conjI RS realpow_less_le], simpset()));
qed_spec_mp "hyperpow_less_le";

Goal "[| (0::hypreal) <= r;  r < 1 |]  \
\     ==> ALL N n. n < N --> r pow N <= r pow n";
by (blast_tac (claset() addSIs [hyperpow_less_le]) 1);
qed "hyperpow_less_le2";

Goal "[| 0 <= r;  r < (1::hypreal);  N : HNatInfinite |]  \
\     ==> ALL n: Nats. r pow N <= r pow n";
by (auto_tac (claset() addSIs [hyperpow_less_le],
              simpset() addsimps [HNatInfinite_iff]));
qed "hyperpow_SHNat_le";

Goalw [hypreal_of_real_def,hypnat_of_nat_def] 
      "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)";
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
qed "hyperpow_realpow";

Goalw [SReal_def] "(hypreal_of_real r) pow (hypnat_of_nat n) : Reals";
by (simp_tac (simpset() delsimps [hypreal_of_real_power]
			addsimps [hyperpow_realpow]) 1); 
qed "hyperpow_SReal";
Addsimps [hyperpow_SReal];

Goal "N : HNatInfinite ==> (0::hypreal) pow N = 0";
by (dtac HNatInfinite_is_Suc 1);
by Auto_tac;
qed "hyperpow_zero_HNatInfinite";
Addsimps [hyperpow_zero_HNatInfinite];

Goal "[| (0::hypreal) <= r; r < 1; n <= N |] ==> r pow N <= r pow n";
by (dres_inst_tac [("y","N")] hypnat_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [hyperpow_less_le], simpset()));
qed "hyperpow_le_le";

Goal "[| (0::hypreal) < r; r < 1 |] ==> r pow (n + (1::hypnat)) <= r";
by (dres_inst_tac [("n","(1::hypnat)")] (order_less_imp_le RS hyperpow_le_le) 1);
by Auto_tac;
qed "hyperpow_Suc_le_self";

Goal "[| (0::hypreal) <= r; r < 1 |] ==> r pow (n + (1::hypnat)) <= r";
by (dres_inst_tac [("n","(1::hypnat)")] hyperpow_le_le 1);
by Auto_tac;
qed "hyperpow_Suc_le_self2";

Goalw [Infinitesimal_def]
     "[| x : Infinitesimal; 0 < N |] ==> abs (x pow N) <= abs x";
by (auto_tac (claset() addSIs [hyperpow_Suc_le_self2],
              simpset() addsimps [hyperpow_hrabs RS sym,
                                  hypnat_gt_zero_iff2, hrabs_ge_zero]));
qed "lemma_Infinitesimal_hyperpow";

Goal "[| x : Infinitesimal; 0 < N |] ==> x pow N : Infinitesimal";
by (rtac hrabs_le_Infinitesimal 1);
by (rtac lemma_Infinitesimal_hyperpow 2); 
by Auto_tac;  
qed "Infinitesimal_hyperpow";

Goalw [hypnat_of_nat_def] 
     "(x ^ n : Infinitesimal) = (x pow (hypnat_of_nat n) : Infinitesimal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hrealpow, hyperpow]));
qed "hrealpow_hyperpow_Infinitesimal_iff";

Goal "[| x : Infinitesimal; 0 < n |] ==> x ^ n : Infinitesimal";
by (auto_tac (claset() addSIs [Infinitesimal_hyperpow],
    simpset() addsimps [hrealpow_hyperpow_Infinitesimal_iff,
                        hypnat_of_nat_less_iff,hypnat_of_nat_zero] 
              delsimps [hypnat_of_nat_less_iff RS sym]));
qed "Infinitesimal_hrealpow";

(* MOVE UP *)
Goal "(0::hypreal) <= x * x";
by (auto_tac (claset(),simpset() addsimps 
    [zero_le_mult_iff]));
qed "hypreal_mult_self_ge_zero";
Addsimps [hypreal_mult_self_ge_zero];

Goal "[|(0::hypreal) <= x; 0 <= y; x ^ Suc n = y ^ Suc n |] ==> x = y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps 
    [hrealpow,hypreal_mult,hypreal_le,hypreal_zero_num]));
by (ultra_tac (claset() addIs [realpow_Suc_cancel_eq],
    simpset()) 1);
qed "hrealpow_Suc_cancel_eq";


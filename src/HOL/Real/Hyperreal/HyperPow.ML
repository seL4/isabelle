(*  Title       : HyperPow.ML
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural Powers of hyperreals theory

*)

Goal "(0::hypreal) ^ (Suc n) = 0";
by (Auto_tac);
qed "hrealpow_zero";
Addsimps [hrealpow_zero];

Goal "r ~= (0::hypreal) --> r ^ n ~= 0";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [hypreal_mult_not_0E],
    simpset() addsimps [hypreal_zero_not_eq_one RS not_sym]));
qed_spec_mp "hrealpow_not_zero";

Goal "r ~= (0::hypreal) --> inverse(r ^ n) = (inverse r) ^ n";
by (induct_tac "n" 1);
by (Auto_tac);
by (forw_inst_tac [("n","n")] hrealpow_not_zero 1);
by (auto_tac (claset(), simpset() addsimps [hypreal_inverse_distrib]));
qed_spec_mp "hrealpow_inverse";

Goal "abs (r::hypreal) ^ n = abs (r ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [hrabs_mult,hrabs_one]));
qed "hrealpow_hrabs";

Goal "(r::hypreal) ^ (n + m) = (r ^ n) * (r ^ m)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps hypreal_mult_ac));
qed "hrealpow_add";

Goal "(r::hypreal) ^ 1 = r";
by (Simp_tac 1);
qed "hrealpow_one";
Addsimps [hrealpow_one];

Goal "(r::hypreal) ^ 2 = r * r";
by (Simp_tac 1);
qed "hrealpow_two";

Goal "(0::hypreal) < r --> 0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addDs [hypreal_less_imp_le] 
                       addIs [hypreal_le_mult_order],
             simpset() addsimps [hypreal_zero_less_one RS hypreal_less_imp_le]));
qed_spec_mp "hrealpow_ge_zero";

Goal "(0::hypreal) < r --> 0 < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [hypreal_mult_order],
              simpset() addsimps [hypreal_zero_less_one]));
qed_spec_mp "hrealpow_gt_zero";

Goal "(0::hypreal) <= r --> 0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [hypreal_le_mult_order],
          simpset() addsimps [hypreal_zero_less_one RS hypreal_less_imp_le]));
qed_spec_mp "hrealpow_ge_zero2";

Goal "(0::hypreal) < x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [hypreal_mult_le_mono],
              simpset() addsimps [hypreal_le_refl]));
by (asm_simp_tac (simpset() addsimps [hrealpow_ge_zero]) 1);
qed_spec_mp "hrealpow_le";

Goal "(0::hypreal) < x & x < y & 0 < n --> x ^ n < y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [hypreal_mult_less_mono,gr0I] 
                       addDs [hrealpow_gt_zero],
              simpset()));
qed "hrealpow_less";

Goal "1hr ^ n = 1hr";
by (induct_tac "n" 1);
by (Auto_tac);
qed "hrealpow_eq_one";
Addsimps [hrealpow_eq_one];

Goal "abs(-(1hr ^ n)) = 1hr";
by (simp_tac (simpset() addsimps [hrabs_one]) 1);
qed "hrabs_minus_hrealpow_one";
Addsimps [hrabs_minus_hrealpow_one];

Goal "abs((-1hr) ^ n) = 1hr";
by (induct_tac "n" 1);
by (auto_tac (claset(),
      simpset() addsimps [hrabs_mult, hrabs_one]));
qed "hrabs_hrealpow_minus_one";
Addsimps [hrabs_hrealpow_minus_one];

Goal "((r::hypreal) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps hypreal_mult_ac));
qed "hrealpow_mult";

Goal "(0::hypreal) <= r ^ 2";
by (simp_tac (simpset() addsimps [hrealpow_two]) 1);
qed "hrealpow_two_le";
Addsimps [hrealpow_two_le];

Goal "(0::hypreal) <= u ^ 2 + v ^ 2";
by (auto_tac (claset() addIs [hypreal_le_add_order], simpset()));
qed "hrealpow_two_le_add_order";
Addsimps [hrealpow_two_le_add_order];

Goal "(0::hypreal) <= u ^ 2 + v ^ 2 + w ^ 2";
by (auto_tac (claset() addSIs [hypreal_le_add_order], simpset()));
qed "hrealpow_two_le_add_order2";
Addsimps [hrealpow_two_le_add_order2];

Goal "(x ^ 2 + y ^ 2 + z ^ 2 = (0::hypreal)) = (x = 0 & y = 0 & z = 0)";
by (simp_tac (HOL_ss addsimps [hypreal_three_squares_add_zero_iff, 
                               hrealpow_two]) 1);
qed "hrealpow_three_squares_add_zero_iff";
Addsimps [hrealpow_three_squares_add_zero_iff];

Goal "abs(x ^ 2) = (x::hypreal) ^ 2";
by (simp_tac (simpset() addsimps [hrabs_eqI1]) 1);
qed "hrabs_hrealpow_two";
Addsimps [hrabs_hrealpow_two];

Goal "abs(x) ^ 2 = (x::hypreal) ^ 2";
by (simp_tac (simpset() addsimps [hrealpow_hrabs, hrabs_eqI1] 
                        delsimps [hpowr_Suc]) 1);
qed "hrealpow_two_hrabs";
Addsimps [hrealpow_two_hrabs];

Goal "!!r. 1hr < r ==> 1hr < r ^ 2";
by (auto_tac (claset(), simpset() addsimps [hrealpow_two]));
by (cut_facts_tac [hypreal_zero_less_one] 1);
by (forw_inst_tac [("R1.0","0")] hypreal_less_trans 1);
by (assume_tac 1);
by (dres_inst_tac [("z","r"),("x","1hr")] hypreal_mult_less_mono1 1);
by (auto_tac (claset() addIs [hypreal_less_trans], simpset()));
qed "hrealpow_two_gt_one";

Goal "!!r. 1hr <= r ==> 1hr <= r ^ 2";
by (etac (hypreal_le_imp_less_or_eq RS disjE) 1);
by (etac (hrealpow_two_gt_one RS hypreal_less_imp_le) 1);
by (asm_simp_tac (simpset() addsimps [hypreal_le_refl]) 1);
qed "hrealpow_two_ge_one";

Goal "!!r. (0::hypreal) < r ==> 0 < r ^ Suc n";
by (forw_inst_tac [("n","n")] hrealpow_ge_zero 1);
by (forw_inst_tac [("n1","n")]
    ((hypreal_not_refl2 RS not_sym) RS hrealpow_not_zero RS not_sym) 1);
by (auto_tac (claset() addSDs [hypreal_le_imp_less_or_eq]
                       addIs [hypreal_mult_order],
              simpset()));
qed "hrealpow_Suc_gt_zero";

Goal "!!r. (0::hypreal) <= r ==> 0 <= r ^ Suc n";
by (etac (hypreal_le_imp_less_or_eq RS disjE) 1);
by (etac (hrealpow_ge_zero) 1);
by (asm_simp_tac (simpset() addsimps [hypreal_le_refl]) 1);
qed "hrealpow_Suc_ge_zero";

Goal "1hr <= (1hr +1hr) ^ n";
by (res_inst_tac [("j","1hr ^ n")] hypreal_le_trans 1);
by (rtac hrealpow_le 2);
by (auto_tac (claset() addIs [hypreal_less_imp_le],
    simpset() addsimps [hypreal_zero_less_one,
    hypreal_one_less_two,hypreal_le_refl]));
qed "two_hrealpow_ge_one";

Goal "hypreal_of_nat n < (1hr + 1hr) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),
        simpset() addsimps [hypreal_of_nat_Suc,hypreal_of_nat_zero,
          hypreal_zero_less_one,hypreal_add_mult_distrib,hypreal_of_nat_one]));
by (blast_tac (claset() addSIs [hypreal_add_less_le_mono,
    two_hrealpow_ge_one]) 1);
qed "two_hrealpow_gt";
Addsimps [two_hrealpow_gt,two_hrealpow_ge_one];

Goal "(-1hr) ^ (2*n) = 1hr";
by (induct_tac "n" 1);
by (Auto_tac);
qed "hrealpow_minus_one";

Goal "(-1hr) ^ (n + n) = 1hr";
by (induct_tac "n" 1);
by (Auto_tac);
qed "hrealpow_minus_one2";
Addsimps [hrealpow_minus_one2];

Goal "(-(x::hypreal)) ^ 2 = x ^ 2";
by (Auto_tac);
qed "hrealpow_minus_two";
Addsimps [hrealpow_minus_two];

Goal "(0::hypreal) < r & r < 1hr --> r ^ Suc n < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_mult_less_mono2]));
qed_spec_mp "hrealpow_Suc_less";

Goal "(0::hypreal) <= r & r < 1hr --> r ^ Suc n <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [hypreal_less_imp_le]
                       addSDs [hypreal_le_imp_less_or_eq,hrealpow_Suc_less],
      simpset() addsimps [hypreal_le_refl,hypreal_mult_less_mono2]));
qed_spec_mp "hrealpow_Suc_le";

(* a few more theorems needed here *)
Goal "1hr <= r --> r ^ n <= r ^ Suc n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [hypreal_mult_le_le_mono1], simpset()));
by (rtac ccontr 1 THEN dtac not_hypreal_leE 1);
by (dtac hypreal_le_less_trans 1 THEN assume_tac 1);
by (etac (hypreal_zero_less_one RS hypreal_less_asym) 1);
qed "hrealpow_less_Suc";

Goal "Abs_hypreal(hyprel^^{%n. X n}) ^ m = Abs_hypreal(hyprel^^{%n. (X n) ^ m})";
by (nat_ind_tac "m" 1);
by (auto_tac (claset(),
              simpset() addsimps [hypreal_one_def,hypreal_mult]));
qed "hrealpow";

Goal "(x + (y::hypreal)) ^ 2 = \
\     x ^ 2 + y ^ 2 + (hypreal_of_nat 2)*x*y";
by (simp_tac (simpset() addsimps [hypreal_add_mult_distrib2,
    hypreal_add_mult_distrib,hypreal_of_nat_two] 
    @ hypreal_add_ac @ hypreal_mult_ac) 1);
qed "hrealpow_sum_square_expand";

(*---------------------------------------------------------------
   we'll prove the following theorem by going down to the
   level of the ultrafilter and relying on the analogous
   property for the real rather than prove it directly 
   using induction: proof is much simpler this way!
 ---------------------------------------------------------------*)
Goalw [hypreal_zero_def] 
  "[|(0::hypreal) <= x;0 <= y;x ^ Suc n <= y ^ Suc n |] ==> x <= y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
              simpset() addsimps [hrealpow,hypreal_le,hypreal_mult]));
by (ultra_tac (claset() addIs [realpow_increasing], simpset()) 1);
qed "hrealpow_increasing";

goalw HyperPow.thy [hypreal_zero_def] 
  "!!x. [|(0::hypreal) <= x;0 <= y;x ^ Suc n = y ^ Suc n |] ==> x = y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hrealpow,hypreal_mult,hypreal_le]));
by (ultra_tac (claset() addIs [realpow_Suc_cancel_eq],
    simpset()) 1);
qed "hrealpow_Suc_cancel_eq";

Goal "x : HFinite --> x ^ n : HFinite";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [HFinite_mult], simpset()));
qed_spec_mp "hrealpow_HFinite";

(*---------------------------------------------------------------
                  Hypernaturals Powers
 --------------------------------------------------------------*)
Goalw [congruent_def]
     "congruent hyprel \
\    (%X Y. hyprel^^{%n. ((X::nat=>real) n ^ (Y::nat=>nat) n)})";
by (safe_tac (claset() addSIs [ext]));
by (ALLGOALS(Fuf_tac));
qed "hyperpow_congruent";

Goalw [hyperpow_def]
  "Abs_hypreal(hyprel^^{%n. X n}) pow Abs_hypnat(hypnatrel^^{%n. Y n}) = \
\  Abs_hypreal(hyprel^^{%n. X n ^ Y n})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by (auto_tac (claset() addSIs [lemma_hyprel_refl,bexI],
    simpset() addsimps [hyprel_in_hypreal RS 
    Abs_hypreal_inverse,equiv_hyprel,hyperpow_congruent]));
by (Fuf_tac 1);
qed "hyperpow";

Goalw [hypreal_zero_def,hypnat_one_def]
      "(0::hypreal) pow (n + 1hn) = 0";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow,hypnat_add]));
qed "hyperpow_zero";
Addsimps [hyperpow_zero];

Goalw [hypreal_zero_def]
      "r ~= (0::hypreal) --> r pow n ~= 0";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
by (dtac FreeUltrafilterNat_Compl_mem 1);
by (fuf_empty_tac (claset() addIs [realpow_not_zero RS notE],
    simpset()) 1);
qed_spec_mp "hyperpow_not_zero";

Goalw [hypreal_zero_def] 
      "r ~= (0::hypreal) --> inverse(r pow n) = (inverse r) pow n";
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
              simpset() addsimps [hypreal_hrabs, hyperpow,realpow_abs]));
qed "hyperpow_hrabs";

Goal "r pow (n + m) = (r pow n) * (r pow m)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
          simpset() addsimps [hyperpow,hypnat_add, hypreal_mult,realpow_add]));
qed "hyperpow_add";

Goalw [hypnat_one_def] "r pow 1hn = r";
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
qed "hyperpow_one";
Addsimps [hyperpow_one];

Goalw [hypnat_one_def] 
      "r pow (1hn + 1hn) = r * r";
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
           simpset() addsimps [hyperpow,hypnat_add, hypreal_mult,realpow_two]));
qed "hyperpow_two";

Goalw [hypreal_zero_def]
      "(0::hypreal) < r --> 0 < r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSEs [FreeUltrafilterNat_subset, realpow_gt_zero],
       simpset() addsimps [hyperpow,hypreal_less, hypreal_le]));
qed_spec_mp "hyperpow_gt_zero";

Goal "(0::hypreal) < r --> 0 <= r pow n";
by (blast_tac (claset() addSIs [hyperpow_gt_zero, hypreal_less_imp_le]) 1);
qed_spec_mp "hyperpow_ge_zero";

Goalw [hypreal_zero_def]
      "(0::hypreal) <= r --> 0 <= r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSEs [FreeUltrafilterNat_subset, realpow_ge_zero2],
              simpset() addsimps [hyperpow,hypreal_le]));
qed "hyperpow_ge_zero2";

Goalw [hypreal_zero_def]
      "(0::hypreal) < x & x <= y --> x pow n <= y pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset() addIs [realpow_le,
    (FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset)],
    simpset() addsimps [hyperpow,hypreal_le,hypreal_less]));
qed_spec_mp "hyperpow_le";

Goalw [hypreal_one_def] "1hr pow n = 1hr";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
qed "hyperpow_eq_one";
Addsimps [hyperpow_eq_one];

Goalw [hypreal_one_def]
      "abs(-(1hr pow n)) = 1hr";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(), 
      simpset() addsimps [abs_one, hyperpow,hypreal_hrabs]));
qed "hrabs_minus_hyperpow_one";
Addsimps [hrabs_minus_hyperpow_one];

Goalw [hypreal_one_def]
      "abs((-1hr) pow n) = 1hr";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
       simpset() addsimps [hyperpow,hypreal_minus,hypreal_hrabs]));
qed "hrabs_hyperpow_minus_one";
Addsimps [hrabs_hyperpow_minus_one];

Goal "(r * s) pow n = (r pow n) * (s pow n)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","s")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
       simpset() addsimps [hyperpow, hypreal_mult,realpow_mult]));
qed "hyperpow_mult";

Goal "(0::hypreal) <= r pow (1hn + 1hn)";
by (simp_tac (simpset() addsimps [hyperpow_two]) 1);
qed "hyperpow_two_le";
Addsimps [hyperpow_two_le];

Goal "abs(x pow (1hn + 1hn)) = x pow (1hn + 1hn)";
by (simp_tac (simpset() addsimps [hrabs_eqI1]) 1);
qed "hrabs_hyperpow_two";
Addsimps [hrabs_hyperpow_two];

Goal "abs(x) pow (1hn + 1hn)  = x pow (1hn + 1hn)";
by (simp_tac (simpset() addsimps [hyperpow_hrabs,hrabs_eqI1]) 1);
qed "hyperpow_two_hrabs";
Addsimps [hyperpow_two_hrabs];

Goal "!!r. 1hr < r ==> 1hr < r pow (1hn + 1hn)";
by (auto_tac (claset(), simpset() addsimps [hyperpow_two]));
by (cut_facts_tac [hypreal_zero_less_one] 1);
by (forw_inst_tac [("R1.0","0")] hypreal_less_trans 1);
by (assume_tac 1);
by (dres_inst_tac [("z","r"),("x","1hr")] 
    hypreal_mult_less_mono1 1);
by (auto_tac (claset() addIs [hypreal_less_trans], simpset()));
qed "hyperpow_two_gt_one";

Goal "!!r. 1hr <= r ==> 1hr <= r pow (1hn + 1hn)";
by (auto_tac (claset() addSDs [hypreal_le_imp_less_or_eq] 
     addIs [hyperpow_two_gt_one,hypreal_less_imp_le],
     simpset() addsimps [hypreal_le_refl]));
qed "hyperpow_two_ge_one";

Goalw [hypnat_one_def,hypreal_zero_def]
      "!!r. (0::hypreal) < r ==> 0 < r pow (n + 1hn)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSEs [FreeUltrafilterNat_subset]
                       addDs [realpow_Suc_gt_zero], 
              simpset() addsimps [hyperpow, hypreal_less,hypnat_add]));
qed "hyperpow_Suc_gt_zero";

Goal "!!r. (0::hypreal) <= r ==> 0 <= r pow (n + 1hn)";
by (auto_tac (claset() addSDs [hypreal_le_imp_less_or_eq] 
    addIs [hyperpow_ge_zero,hypreal_less_imp_le], 
    simpset() addsimps [hypreal_le_refl]));
qed "hyperpow_Suc_ge_zero";

Goal "1hr <= (1hr +1hr) pow n";
by (res_inst_tac [("j","1hr pow n")] hypreal_le_trans 1);
by (rtac hyperpow_le 2);
by (auto_tac (claset() addIs [hypreal_less_imp_le],
    simpset() addsimps [hypreal_zero_less_one,
    hypreal_one_less_two,hypreal_le_refl]));
qed "two_hyperpow_ge_one";
Addsimps [two_hyperpow_ge_one];

Addsimps [simplify (simpset()) realpow_minus_one];
Goalw [hypreal_one_def]
      "(-1hr) pow ((1hn + 1hn)*n) = 1hr";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),
              simpset() addsimps [hyperpow, hypnat_add,hypreal_minus]));
qed "hyperpow_minus_one2";
Addsimps [hyperpow_minus_one2];

Goalw [hypreal_zero_def,
      hypreal_one_def,hypnat_one_def]
     "(0::hypreal) < r & r < 1hr --> r pow (n + 1hn) < r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [conjI RS realpow_Suc_less] addEs
    [FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset ],
    simpset() addsimps [hyperpow,hypreal_less,hypnat_add]));
qed_spec_mp "hyperpow_Suc_less";

Goalw [hypreal_zero_def,
      hypreal_one_def,hypnat_one_def]
     "0 <= r & r < 1hr --> r pow (n + 1hn) <= r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset() addSDs [conjI RS realpow_Suc_le] addEs
    [FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset ],
    simpset() addsimps [hyperpow,hypreal_le,hypnat_add,
    hypreal_less]));
qed_spec_mp "hyperpow_Suc_le";

Goalw [hypreal_zero_def,
      hypreal_one_def,hypnat_one_def]
     "(0::hypreal) <= r & r < 1hr & n < N --> r pow N <= r pow n";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","N")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","r")] eq_Abs_hypreal 1);
by (auto_tac (claset(),
        simpset() addsimps [hyperpow, hypreal_le,hypreal_less,hypnat_less]));
by (etac (FreeUltrafilterNat_Int RS FreeUltrafilterNat_subset) 1);
by (etac FreeUltrafilterNat_Int 1);
by (auto_tac (claset() addSDs [conjI RS realpow_less_le],
    simpset()));
qed_spec_mp "hyperpow_less_le";

Goal "!!r. [| (0::hypreal) <= r; r < 1hr |] ==> \
\          ALL N n. n < N --> r pow N <= r pow n";
by (blast_tac (claset() addSIs [hyperpow_less_le]) 1);
qed "hyperpow_less_le2";

Goal "!!r. [| 0 <= r; r < 1hr; \
\             N : HNatInfinite \
\          |] ==> ALL n:SHNat. r pow N <= r pow n";
by (auto_tac (claset() addSIs [hyperpow_less_le],
              simpset() addsimps [HNatInfinite_iff]));
qed "hyperpow_SHNat_le";

Goalw [hypreal_of_real_def,hypnat_of_nat_def] 
      "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)";
by (auto_tac (claset(), simpset() addsimps [hyperpow]));
qed "hyperpow_realpow";

Goalw [SReal_def]
     "(hypreal_of_real r) pow (hypnat_of_nat n) : SReal";
by (auto_tac (claset(), simpset() addsimps [hyperpow_realpow]));
qed "hyperpow_SReal";
Addsimps [hyperpow_SReal];

Goal "!!N. N : HNatInfinite ==> (0::hypreal) pow N = 0";
by (dtac HNatInfinite_is_Suc 1);
by (Auto_tac);
qed "hyperpow_zero_HNatInfinite";
Addsimps [hyperpow_zero_HNatInfinite];

Goal "!!r. [| (0::hypreal) <= r; r < 1hr; n <= N |] ==> r pow N <= r pow n";
by (dres_inst_tac [("y","N")] hypnat_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [hyperpow_less_le],
    simpset() addsimps [hypreal_le_refl]));
qed "hyperpow_le_le";

Goal "!!r. [| (0::hypreal) < r; r < 1hr |] ==> r pow (n + 1hn) <= r";
by (dres_inst_tac [("n","1hn")] (hypreal_less_imp_le RS 
    hyperpow_le_le) 1);
by (Auto_tac);
qed "hyperpow_Suc_le_self";

Goal "!!r. [| (0::hypreal) <= r; r < 1hr |] ==> r pow (n + 1hn) <= r";
by (dres_inst_tac [("n","1hn")] hyperpow_le_le 1);
by (Auto_tac);
qed "hyperpow_Suc_le_self2";

Goalw [Infinitesimal_def]
     "!!x. [| x : Infinitesimal; 0 < N |] \
\          ==> (abs x) pow N <= abs x";
by (auto_tac (claset() addSIs [hyperpow_Suc_le_self2],
    simpset() addsimps [hyperpow_hrabs RS sym,
    hypnat_gt_zero_iff2,hrabs_ge_zero,SReal_one,
    hypreal_zero_less_one]));
qed "lemma_Infinitesimal_hyperpow";

Goal "!!x. [| x : Infinitesimal; 0 < N |] \
\           ==> x pow N : Infinitesimal";
by (rtac hrabs_le_Infinitesimal 1);
by (dtac Infinitesimal_hrabs 1);
by (auto_tac (claset() addSIs [lemma_Infinitesimal_hyperpow],
    simpset() addsimps [hyperpow_hrabs RS sym]));
qed "Infinitesimal_hyperpow";

goalw HyperPow.thy [hypnat_of_nat_def] 
     "(x ^ n : Infinitesimal) = \
\     (x pow (hypnat_of_nat n) : Infinitesimal)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(), simpset() addsimps [hrealpow, hyperpow]));
qed "hrealpow_hyperpow_Infinitesimal_iff";

goal HyperPow.thy 
     "!!x. [| x : Infinitesimal; 0 < n |] \
\           ==> x ^ n : Infinitesimal";
by (auto_tac (claset() addSIs [Infinitesimal_hyperpow],
    simpset() addsimps [hrealpow_hyperpow_Infinitesimal_iff,
                        hypnat_of_nat_less_iff,hypnat_of_nat_zero] 
              delsimps [hypnat_of_nat_less_iff RS sym]));
qed "Infinitesimal_hrealpow";








(*  Title       : RealPow.ML
    Author      : Jacques D. Fleuriot  
    Copyright   : 1998  University of Cambridge
    Description : Natural Powers of reals theory

*)

Goal "0r ^ (Suc n) = 0r";
by (Auto_tac);
qed "realpow_zero";
Addsimps [realpow_zero];

Goal "r ~= 0r --> r ^ n ~= 0r";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_mult_not_zeroE],
    simpset() addsimps [real_zero_not_eq_one RS not_sym]));
qed_spec_mp "realpow_not_zero";

Goal "!!r. r ^ n = 0r ==> r = 0r";
by (blast_tac (claset() addIs [ccontr] 
    addDs [realpow_not_zero]) 1);
qed "realpow_zero_zero";

Goal "r ~= 0r --> rinv(r ^ n) = (rinv r) ^ n";
by (induct_tac "n" 1);
by (Auto_tac);
by (forw_inst_tac [("n","n")] realpow_not_zero 1);
by (auto_tac (claset() addDs [real_rinv_distrib],
    simpset()));
qed_spec_mp "realpow_rinv";

Goal "rabs r ^ n = rabs (r ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps 
    [rabs_mult,rabs_one]));
qed "realpow_rabs";

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

Goal "0r < r --> 0r <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addDs [real_less_imp_le] 
    addIs [real_le_mult_order],simpset()));
qed_spec_mp "realpow_ge_zero";

Goal "0r < r --> 0r < r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_mult_order],
    simpset() addsimps [real_zero_less_one]));
qed_spec_mp "realpow_gt_zero";

Goal "0r <= r --> 0r <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_le_mult_order],
              simpset()));
qed_spec_mp "realpow_ge_zero2";

Goal "0r < x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_mono],
    simpset()));
by (asm_simp_tac (simpset() addsimps [realpow_ge_zero]) 1);
qed_spec_mp "realpow_le";

Goal "0r <= x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_mono4],
    simpset()));
by (asm_simp_tac (simpset() addsimps [realpow_ge_zero2]) 1);
qed_spec_mp "realpow_le2";

Goal "0r < x & x < y & 0 < n --> x ^ n < y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_mult_less_mono,
    gr0I] addDs [realpow_gt_zero],simpset()));
qed_spec_mp "realpow_less";

Goal  "1r ^ n = 1r";
by (induct_tac "n" 1);
by (Auto_tac);
qed "realpow_eq_one";
Addsimps [realpow_eq_one];

Goal "rabs(-(1r ^ n)) = 1r";
by (simp_tac (simpset() addsimps 
    [rabs_minus_cancel,rabs_one]) 1);
qed "rabs_minus_realpow_one";
Addsimps [rabs_minus_realpow_one];

Goal "rabs((-1r) ^ n) = 1r";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [rabs_mult,
         rabs_minus_cancel,rabs_one]));
qed "rabs_realpow_minus_one";
Addsimps [rabs_realpow_minus_one];

Goal "((r::real) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "realpow_mult";

Goal "0r <= r ^ 2";
by (simp_tac (simpset() addsimps [realpow_two]) 1);
qed "realpow_two_le";
Addsimps [realpow_two_le];

Goal "rabs(x ^ 2) = x ^ 2";
by (simp_tac (simpset() addsimps [rabs_eqI1]) 1);
qed "rabs_realpow_two";
Addsimps [rabs_realpow_two];

Goal "rabs(x) ^ 2 = x ^ 2";
by (simp_tac (simpset() addsimps 
    [realpow_rabs,rabs_eqI1] delsimps [realpow_Suc]) 1);
qed "realpow_two_rabs";
Addsimps [realpow_two_rabs];

Goal "!!r. 1r < r ==> 1r < r ^ 2";
by (auto_tac (claset(),simpset() addsimps [realpow_two]));
by (cut_facts_tac [real_zero_less_one] 1);
by (forw_inst_tac [("R1.0","0r")] real_less_trans 1);
by (assume_tac 1);
by (dres_inst_tac [("z","r"),("x","1r")] real_mult_less_mono1 1);
by (auto_tac (claset() addIs [real_less_trans],simpset()));
qed "realpow_two_gt_one";

Goal "!!r. 1r <= r ==> 1r <= r ^ 2";
by (etac (real_le_imp_less_or_eq RS disjE) 1);
by (etac (realpow_two_gt_one RS real_less_imp_le) 1);
by (asm_simp_tac (simpset()) 1);
qed "realpow_two_ge_one";

(* more general result *)
Goal "1r < r --> 1r <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq],
    simpset()));
by (dtac (real_zero_less_one RS real_mult_less_mono) 1);
by (dtac sym 4);
by (auto_tac (claset() addSIs [real_less_imp_le],
    simpset() addsimps [real_zero_less_one]));
qed_spec_mp "realpow_ge_one";

Goal "!!r. 1r < r ==> 1r < r ^ (Suc n)";
by (forw_inst_tac [("n","n")] realpow_ge_one 1);
by (dtac real_le_imp_less_or_eq 1 THEN Step_tac 1);
by (dtac sym 2);
by (forward_tac [real_zero_less_one RS real_less_trans] 1);
by (dres_inst_tac [("y","r ^ n")] real_mult_less_mono2 1);
by (auto_tac (claset() addDs [real_less_trans],
     simpset()));
qed "realpow_Suc_gt_one";

Goal "!!r. 1r <= r ==> 1r <= r ^ n";
by (dtac real_le_imp_less_or_eq 1); 
by (auto_tac (claset() addDs [realpow_ge_one],
    simpset()));
qed "realpow_ge_one2";

Goal "!!r. 0r < r ==> 0r < r ^ Suc n";
by (forw_inst_tac [("n","n")] realpow_ge_zero 1);
by (forw_inst_tac [("n1","n")]
    ((real_not_refl2 RS not_sym) RS realpow_not_zero RS not_sym) 1);
by (auto_tac (claset() addSDs [real_le_imp_less_or_eq]
     addIs [real_mult_order],simpset()));
qed "realpow_Suc_gt_zero";

Goal "!!r. 0r <= r ==> 0r <= r ^ Suc n";
by (etac (real_le_imp_less_or_eq RS disjE) 1);
by (etac (realpow_ge_zero) 1);
by (asm_simp_tac (simpset()) 1);
qed "realpow_Suc_ge_zero";

Goal "1r <= (1r +1r) ^ n";
by (res_inst_tac [("j","1r ^ n")] real_le_trans 1);
by (rtac realpow_le 2);
by (auto_tac (claset() addIs [real_less_imp_le],
    simpset() addsimps [real_zero_less_one,
    real_one_less_two]));
qed "two_realpow_ge_one";

Goal "real_of_nat n < (1r + 1r) ^ n";
by (induct_tac "n" 1);
by (rtac (lemmaS RS ssubst) 2);
by (rtac (real_of_nat_add RS subst) 2);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_zero,
    real_zero_less_one,real_add_mult_distrib,real_of_nat_one]));
by (blast_tac (claset() addSIs [real_add_less_le_mono,
    two_realpow_ge_one]) 1);
qed "two_realpow_gt";
Addsimps [two_realpow_gt,two_realpow_ge_one];

Goal "(-1r) ^ (2*n) = 1r";
by (induct_tac "n" 1);
by (Auto_tac);
qed "realpow_minus_one";
Addsimps [realpow_minus_one];

Goal "(-1r) ^ (n + n) = 1r";
by (induct_tac "n" 1);
by (Auto_tac);
qed "realpow_minus_one2";
Addsimps [realpow_minus_one2];

Goal "(-1r) ^ Suc (n + n) = -1r";
by (induct_tac "n" 1);
by (Auto_tac);
qed "realpow_minus_one_odd";
Addsimps [realpow_minus_one_odd];

Goal "(-1r) ^ Suc (Suc (n + n)) = 1r";
by (induct_tac "n" 1);
by (Auto_tac);
qed "realpow_minus_one_even";
Addsimps [realpow_minus_one_even];

Goal "0r < r & r < 1r --> r ^ Suc n < r ^ n";
by (induct_tac "n" 1);
by (Auto_tac);
qed_spec_mp "realpow_Suc_less";

Goal "0r <= r & r < 1r --> r ^ Suc n <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addIs [real_less_imp_le] addSDs
     [real_le_imp_less_or_eq],simpset()));
qed_spec_mp "realpow_Suc_le";

Goal "0r <= 0r ^ n";
by (exhaust_tac "n" 1);
by (Auto_tac);
qed "realpow_zero_le";
Addsimps [realpow_zero_le];

Goal "0r < r & r < 1r --> r ^ Suc n <= r ^ n";
by (blast_tac (claset() addSIs [real_less_imp_le,
    realpow_Suc_less]) 1);
qed_spec_mp "realpow_Suc_le2";

Goal "!!r. [| 0r <= r; r < 1r |] ==> r ^ Suc n <= r ^ n";
by (etac (real_le_imp_less_or_eq RS disjE) 1);
by (rtac realpow_Suc_le2 1);
by (Auto_tac);
qed "realpow_Suc_le3";

Goal "0r <= r & r < 1r & n < N --> r ^ N <= r ^ n";
by (induct_tac "N" 1);
by (Auto_tac);
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_zero2));
by (ALLGOALS(dtac real_mult_le_mono3));
by (REPEAT(assume_tac 1));
by (REPEAT(assume_tac 3));
by (auto_tac (claset(),simpset() addsimps 
    [less_Suc_eq]));
qed_spec_mp "realpow_less_le";

Goal "!!r. [| 0r <= r; r < 1r; n <= N |] \
\          ==> r ^ N <= r ^ n";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_less_le],
    simpset()));
qed "realpow_le_le";

Goal "!!r. [| 0r < r; r < 1r |] ==> r ^ Suc n <= r";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    (real_less_imp_le RS realpow_le_le) 1);
by (Auto_tac);
qed "realpow_Suc_le_self";

Goal "!!r. [| 0r < r; r < 1r |] ==> r ^ Suc n < 1r";
by (blast_tac (claset() addIs [realpow_Suc_le_self,
               real_le_less_trans]) 1);
qed "realpow_Suc_less_one";

Goal "1r <= r --> r ^ n <= r ^ Suc n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_le_mono1],simpset()));
by (rtac ccontr 1 THEN dtac not_real_leE 1);
by (dtac real_le_less_trans 1 THEN assume_tac 1);
by (etac (real_zero_less_one RS real_less_asym) 1);
qed_spec_mp "realpow_le_Suc";

Goal "1r < r --> r ^ n < r ^ Suc n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_less_mono2],simpset()));
by (rtac ccontr 1 THEN dtac real_leI 1);
by (dtac real_less_le_trans 1 THEN assume_tac 1);
by (etac (real_zero_less_one RS real_less_asym) 1);
qed_spec_mp "realpow_less_Suc";

Goal "1r < r --> r ^ n <= r ^ Suc n";
by (blast_tac (claset() addSIs [real_less_imp_le,
    realpow_less_Suc]) 1);
qed_spec_mp "realpow_le_Suc2";

Goal "1r < r & n < N --> r ^ n <= r ^ N";
by (induct_tac "N" 1);
by (Auto_tac);
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_one));
by (ALLGOALS(dtac real_mult_self_le));
by (assume_tac 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [real_le_trans],
    simpset() addsimps [less_Suc_eq]));
qed_spec_mp "realpow_gt_ge";

Goal "1r <= r & n < N --> r ^ n <= r ^ N";
by (induct_tac "N" 1);
by (Auto_tac);
by (ALLGOALS(forw_inst_tac [("n","na")] realpow_ge_one2));
by (ALLGOALS(dtac real_mult_self_le2));
by (assume_tac 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [real_le_trans],
    simpset() addsimps [less_Suc_eq]));
qed_spec_mp "realpow_gt_ge2";

Goal "!!r. [| 1r < r; n <= N |] ==> r ^ n <= r ^ N";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_gt_ge],simpset()));
qed "realpow_ge_ge";

Goal "!!r. [| 1r <= r; n <= N |] ==> r ^ n <= r ^ N";
by (dres_inst_tac [("n","N")] le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [realpow_gt_ge2],simpset()));
qed "realpow_ge_ge2";

Goal "!!r. 1r < r ==> r <= r ^ Suc n";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    realpow_ge_ge 1);
by (Auto_tac);
qed_spec_mp "realpow_Suc_ge_self";

Goal "!!r. 1r <= r ==> r <= r ^ Suc n";
by (dres_inst_tac [("n","1"),("N","Suc n")] 
    realpow_ge_ge2 1);
by (Auto_tac);
qed_spec_mp "realpow_Suc_ge_self2";

Goal "!!r. [| 1r < r; 0 < n |] ==> r <= r ^ n";
by (dtac (less_not_refl2 RS  not0_implies_Suc) 1);
by (auto_tac (claset() addSIs 
    [realpow_Suc_ge_self],simpset()));
qed "realpow_ge_self";

Goal "!!r. [| 1r <= r; 0 < n |] ==> r <= r ^ n";
by (dtac (less_not_refl2 RS  not0_implies_Suc) 1);
by (auto_tac (claset() addSIs [realpow_Suc_ge_self2],simpset()));
qed "realpow_ge_self2";

Goal "0 < n --> (x::real) ^ (n - 1) * x = x ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() 
    addsimps [real_mult_commute]));
qed_spec_mp "realpow_minus_mult";
Addsimps [realpow_minus_mult];

Goal "!!r. r ~= 0r ==> r * rinv(r) ^ 2 = rinv r";
by (asm_simp_tac (simpset() addsimps [realpow_two,
                  real_mult_assoc RS sym]) 1);
qed "realpow_two_mult_rinv";
Addsimps [realpow_two_mult_rinv];


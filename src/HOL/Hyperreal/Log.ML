(*  Title       : Log.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
    Description : standard logarithms only 
*)


Goalw [powr_def] "1 powr a = 1";
by (Simp_tac 1);
qed "powr_one_eq_one";
Addsimps [powr_one_eq_one];

Goalw [powr_def] "x powr 0 = 1";
by (Simp_tac 1);
qed "powr_zero_eq_one";
Addsimps [powr_zero_eq_one];

Goalw [powr_def] 
      "(x powr 1 = x) = (0 < x)";
by (Simp_tac 1);
qed "powr_one_gt_zero_iff";
Addsimps [powr_one_gt_zero_iff];
Addsimps [powr_one_gt_zero_iff RS iffD2];

Goalw [powr_def] 
      "[| 0 < x; 0 < y |] ==> (x * y) powr a = (x powr a) * (y powr a)";
by (asm_simp_tac (simpset() addsimps [exp_add RS sym,ln_mult,
    real_add_mult_distrib2]) 1);
qed "powr_mult";

Goalw [powr_def] "0 < x powr a";
by (Simp_tac 1);
qed "powr_gt_zero";
Addsimps [powr_gt_zero];

Goalw [powr_def] "x powr a ~= 0";
by (Simp_tac 1);
qed "powr_not_zero";
Addsimps [powr_not_zero];

Goal "[| 0 < x; 0 < y |] ==> (x / y) powr a = (x powr a)/(y powr a)";
by (asm_simp_tac (simpset() addsimps [real_divide_def,real_inverse_gt_0,
    powr_mult]) 1);
by (asm_simp_tac (simpset() addsimps [powr_def,exp_minus RS sym,
    exp_add RS sym,ln_inverse]) 1);
qed "powr_divide";

Goalw [powr_def] "x powr (a + b) = (x powr a) * (x powr b)";
by (asm_simp_tac (simpset() addsimps [exp_add RS sym,
    real_add_mult_distrib]) 1);
qed "powr_add";

Goalw [powr_def] "(x powr a) powr b = x powr (a * b)";
by (simp_tac (simpset() addsimps real_mult_ac) 1);
qed "powr_powr";

Goal "(x powr a) powr b = (x powr b) powr a";
by (simp_tac (simpset() addsimps [powr_powr,real_mult_commute]) 1);
qed "powr_powr_swap";

Goalw [powr_def] "x powr (-a) = inverse (x powr a)";
by (simp_tac (simpset() addsimps [exp_minus RS sym]) 1);
qed "powr_minus";

Goalw [real_divide_def] "x powr (-a) = 1/(x powr a)";
by (simp_tac (simpset() addsimps [powr_minus]) 1);
qed "powr_minus_divide";

Goalw [powr_def] 
   "[| a < b; 1 < x |] ==> x powr a < x powr b";
by Auto_tac;
qed "powr_less_mono";

Goalw [powr_def] 
   "[| x powr a < x powr b; 1 < x |] ==> a < b";
by (auto_tac (claset() addDs [ln_gt_zero],
    simpset() addsimps [rename_numerals real_mult_less_cancel2]));
qed "powr_less_cancel";

Goal "1 < x ==> (x powr a < x powr b) = (a < b)";
by (blast_tac (claset() addIs [powr_less_cancel,powr_less_mono]) 1);
qed "powr_less_cancel_iff";
Addsimps [powr_less_cancel_iff];

Goalw [real_le_def] "1 < x ==> (x powr a <= x powr b) = (a <= b)";
by (Auto_tac);
qed "powr_le_cancel_iff";
Addsimps [powr_le_cancel_iff];

Goalw [log_def] "ln x = log (exp(1)) x";
by (Simp_tac 1);
qed "log_ln";

Goalw [powr_def,log_def] 
    "[| 0 < a; a ~= 1; 0 < x |] ==> a powr (log a x) = x";
by Auto_tac;
qed "powr_log_cancel";
Addsimps [powr_log_cancel];

Goalw [log_def,powr_def] 
    "[| 0 < a; a ~= 1 |] ==> log a (a powr y) = y";
by (auto_tac (claset(),simpset() addsimps [real_divide_def,
    real_mult_assoc]));
qed "log_powr_cancel";
Addsimps [log_powr_cancel];

Goalw [log_def] 
     "[| 0 < a; a ~= 1; 0 < x; 0 < y  |] \
\     ==> log a (x * y) = log a x + log a y";
by (auto_tac (claset(),simpset() addsimps [ln_mult,real_divide_def,
    real_add_mult_distrib]));
qed "log_mult";

Goalw [log_def,real_divide_def]
     "[| 0 < a; a ~= 1; 0 < b; b ~= 1; 0 < x |] \
\     ==> log a x = (ln b/ln a) * log b x";
by Auto_tac;
qed "log_eq_div_ln_mult_log";

(* specific case *)
Goal "0 < x ==> log 10 x = (ln (exp 1) / ln 10) * ln x";
by (auto_tac (claset(),simpset() addsimps [log_def]));
qed "log_base_10_eq1";

Goal "0 < x ==> log 10 x = (log 10 (exp 1)) * ln x";
by (auto_tac (claset(),simpset() addsimps [log_def]));
qed "log_base_10_eq2";

Goalw [log_def] "log a 1 = 0";
by Auto_tac;
qed "log_one";
Addsimps [log_one];

Goalw [log_def] 
    "[| 0 < a; a ~= 1 |] ==> log a a = 1";
by Auto_tac;
qed "log_eq_one";
Addsimps [log_eq_one];

Goal "[| 0 < a; a ~= 1; 0 < x |] ==> log a (inverse x) = - log a x";
by (res_inst_tac [("x1","log a x")] (real_add_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [log_mult RS sym]));
qed "log_inverse";

Goal "[|0 < a; a ~= 1; 0 < x; 0 < y|] \
\     ==> log a (x/y) = log a x - log a y";
by (auto_tac (claset(),simpset() addsimps [log_mult,real_divide_def,
    log_inverse]));
qed "log_divide";

Goal "[| 1 < a; 0 < x; 0 < y |] ==> (log a x < log a y) = (x < y)";
by (Step_tac 1);
by (rtac powr_less_cancel 2);
by (dres_inst_tac [("a","log a x")] powr_less_mono 1);
by Auto_tac;
qed "log_less_cancel_iff";
Addsimps [log_less_cancel_iff];

Goal "[| 1 < a; 0 < x; 0 < y |] ==> (log a x <= log a y) = (x <= y)";
by (auto_tac (claset(),simpset() addsimps [real_le_def]));
qed "log_le_cancel_iff";
Addsimps [log_le_cancel_iff];


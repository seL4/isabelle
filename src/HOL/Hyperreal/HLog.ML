(*  Title       : HLog.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
    Description : hyperreal base logarithms
*)

Goalw [powhr_def]
    "(Abs_hypreal(hyprel `` {X})) powhr (Abs_hypreal(hyprel `` {Y})) = \
\    Abs_hypreal(hyprel `` {%n.  (X n) powr (Y n)})";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_mult,
    powr_def]));
qed "powhr";

Goal "1 powhr a = 1";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_one_num]));
qed "powhr_one_eq_one";
Addsimps [powhr_one_eq_one];

Goal "[| 0 < x; 0 < y |] ==> (x * y) powhr a = (x powhr a) * (y powhr a)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_zero_num,
    hypreal_mult,hypreal_less]));
by (ultra_tac (claset(),simpset() addsimps [powr_mult]) 1);
qed "powhr_mult";

Goalw [hypreal_zero_def] "0 < x powhr a";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_less,hypreal_zero_num]));
qed "powhr_gt_zero";
Addsimps [powhr_gt_zero];

Goal "x powhr a ~= 0";
by (rtac ((powhr_gt_zero RS hypreal_not_refl2) RS not_sym) 1);
qed "powhr_not_zero";
Addsimps [powhr_not_zero];

Goalw [hypreal_divide_def]
     "(Abs_hypreal(hyprel `` {X}))/(Abs_hypreal(hyprel `` {Y})) = \
\     (Abs_hypreal(hyprel `` {%n. (X n)/(Y n)}))";
by (case_tac "Abs_hypreal (hyprel `` {Y}) = 0" 1);
by (auto_tac (claset(),
  simpset() addsimps [hypreal_zero_num,hypreal_inverse,hypreal_mult]));
by (ALLGOALS(ultra_tac (claset(),simpset() addsimps [real_divide_def])));
qed "hypreal_divide";

Goal "[| 0 < x; 0 < y |] ==> (x / y) powhr a = (x powhr a)/(y powhr a)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_divide,
    hypreal_zero_num,hypreal_less]));
by (ultra_tac (claset(),simpset() addsimps [powr_divide]) 1);
qed "powhr_divide";

Goal "x powhr (a + b) = (x powhr a) * (x powhr b)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_add,hypreal_mult,
    powr_add]));
qed "powhr_add";

Goal "(x powhr a) powhr b = x powhr (a * b)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_mult,
    powr_powr]));
qed "powhr_powhr";

Goal "(x powhr a) powhr b = (x powhr b) powhr a";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,powr_powr_swap]));
qed "powhr_powhr_swap";

Goal "x powhr (-a) = inverse (x powhr a)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_minus,
    hypreal_inverse,hypreal_less,powr_minus]));
qed "powhr_minus";

Goalw [hypreal_divide_def] "x powhr (-a) = 1/(x powhr a)";
by (simp_tac (simpset() addsimps [powhr_minus]) 1);
qed "powhr_minus_divide";

Goal "[| a < b; 1 < x |] ==> x powhr a < x powhr b";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_one_num,
    hypreal_less]));
by (ultra_tac (claset(),simpset() addsimps [powr_less_mono]) 1);
qed "powhr_less_mono";

Goal "[| x powhr a < x powhr b; 1 < x |] ==> a < b";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,hypreal_one_num,
    hypreal_less]));
by (ultra_tac (claset() addDs [powr_less_cancel],simpset()) 1);
qed "powhr_less_cancel";

Goal "1 < x ==> (x powhr a < x powhr b) = (a < b)";
by (blast_tac (claset() addIs [powhr_less_cancel,powhr_less_mono]) 1);
qed "powhr_less_cancel_iff";
Addsimps [powhr_less_cancel_iff];

Goal "1 < x ==> (x powhr a <= x powhr b) = (a <= b)";
by (auto_tac (claset(),simpset() addsimps [linorder_not_less RS sym]));
qed "powhr_le_cancel_iff";
Addsimps [powhr_le_cancel_iff];

Goalw [hlog_def]
     "hlog (Abs_hypreal(hyprel `` {X})) (Abs_hypreal(hyprel `` {Y})) = \
\     Abs_hypreal(hyprel `` {%n. log (X n) (Y n)})";
by (res_inst_tac [("f","Abs_hypreal")] arg_cong 1);
by Auto_tac;
by (Ultra_tac 1);
qed "hlog";

Goal "( *f* ln) x = hlog (( *f* exp) 1) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hlog,log_ln,
    hypreal_one_num]));
qed "hlog_starfun_ln";

Goal "[| 0 < a; a ~= 1; 0 < x |] ==> a powhr (hlog a x) = x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hlog,powhr,hypreal_zero_num,
    hypreal_less,hypreal_one_num]));
by (Ultra_tac 1);
qed "powhr_hlog_cancel";
Addsimps [powhr_hlog_cancel];

Goal "[| 0 < a; a ~= 1 |] ==> hlog a (a powhr y) = y";
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hlog,powhr,hypreal_zero_num,
    hypreal_less,hypreal_one_num]));
by (ultra_tac (claset() addIs [log_powr_cancel],simpset()) 1);
qed "hlog_powhr_cancel";
Addsimps [hlog_powhr_cancel];

Goal "[| 0 < a; a ~= 1; 0 < x; 0 < y  |] \
\     ==> hlog a (x * y) = hlog a x + hlog a y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hlog,powhr,hypreal_zero_num,
    hypreal_one_num,hypreal_less,hypreal_add,hypreal_mult]));
by (ultra_tac (claset(),simpset() addsimps [log_mult]) 1);
qed "hlog_mult";

Goal "[| 0 < a; a ~= 1 |] ==> hlog a x = ( *f* ln) x / ( *f* ln) a";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hlog,starfun,
    hypreal_zero_num,hypreal_one_num,hypreal_divide,log_def]));
qed "hlog_as_starfun";

Goal "[| 0 < a; a ~= 1; 0 < b; b ~= 1; 0 < x |] \
\     ==> hlog a x = (( *f* ln) b/( *f*ln) a) * hlog b x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","b")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hlog,starfun,
    hypreal_zero_num,hypreal_one_num,hypreal_less,
    hypreal_divide,hypreal_mult]));
by (ultra_tac (claset() addDs [log_eq_div_ln_mult_log],simpset()) 1);
qed "hlog_eq_div_starfun_ln_mult_hlog";

Goal "x powhr a = ( *f* exp) (a * ( *f* ln) x)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [powhr,starfun,
    hypreal_mult,powr_def]));
qed "powhr_as_starfun";

Goal "[| x : HInfinite; 0 < x; a : HFinite - Infinitesimal; \
\        0 < a |] ==> x powhr a : HInfinite";
by (auto_tac (claset() addSIs [starfun_ln_ge_zero,
    starfun_ln_HInfinite,HInfinite_HFinite_not_Infinitesimal_mult2,
    starfun_exp_HInfinite],simpset() addsimps [order_less_imp_le,
    HInfinite_gt_zero_gt_one,powhr_as_starfun,
    zero_le_mult_iff]));
qed "HInfinite_powhr";

Goal "[| x : HFinite - Infinitesimal; a : HInfinite; 0 < a |] \
\     ==> hlog a (abs x) : Infinitesimal";
by (ftac HInfinite_gt_zero_gt_one 1);
by (auto_tac (claset() addSIs [starfun_ln_HFinite_not_Infinitesimal,
    HInfinite_inverse_Infinitesimal,Infinitesimal_HFinite_mult2],
    simpset() addsimps [starfun_ln_HInfinite,not_Infinitesimal_not_zero,
    hlog_as_starfun,hypreal_not_refl2 RS not_sym,hypreal_divide_def]));
qed "hlog_hrabs_HInfinite_Infinitesimal";

Goal "[| a : HInfinite; 0 < a |] ==> hlog a x = ( *f* ln) x / ( *f* ln) a";
by (rtac hlog_as_starfun 1);
by Auto_tac;
qed "hlog_HInfinite_as_starfun";

Goal "hlog a 1 = 0";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_one_num,
    hypreal_zero_num,hlog]));
qed "hlog_one";
Addsimps [hlog_one];

Goal "[| 0 < a; a ~= 1 |] ==> hlog a a = 1";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_one_num,
    hypreal_zero_num,hlog,hypreal_less]));
by (ultra_tac (claset() addIs [log_eq_one],simpset()) 1);
qed "hlog_eq_one";
Addsimps [hlog_eq_one];

Goal "[| 0 < a; a ~= 1; 0 < x |] ==> hlog a (inverse x) = - hlog a x";
by (res_inst_tac [("a1","hlog a x")] (add_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_not_refl2 RS not_sym,
    hlog_mult RS sym,positive_imp_inverse_positive]));
qed "hlog_inverse";

Goal "[| 0 < a; a ~= 1; 0 < x; 0 < y|] \
\     ==> hlog a (x/y) = hlog a x - hlog a y";
by (auto_tac (claset(),
    simpset() addsimps [positive_imp_inverse_positive,hlog_mult, hlog_inverse,hypreal_diff_def,hypreal_divide_def]));
qed "hlog_divide";

Goal "[| 1 < a; 0 < x; 0 < y |] ==> (hlog a x < hlog a y) = (x < y)";
by (res_inst_tac [("z","a")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hlog,hypreal_less,
    hypreal_zero_num,hypreal_one_num]));
by (ALLGOALS(Ultra_tac));
qed "hlog_less_cancel_iff";
Addsimps [hlog_less_cancel_iff];

Goal "[| 1 < a; 0 < x; 0 < y |] ==> (hlog a x <= hlog a y) = (x <= y)";
by (auto_tac (claset(),simpset() addsimps [linorder_not_less RS sym]));
qed "hlog_le_cancel_iff";
Addsimps [hlog_le_cancel_iff];

(* should be in NSA.ML *)
goalw HLog.thy [epsilon_def] "0 <= epsilon";
by (auto_tac (claset(),simpset() addsimps [hypreal_zero_num,hypreal_le]));
qed "epsilon_ge_zero";
Addsimps [epsilon_ge_zero];

goal HLog.thy "epsilon : {x. 0 <= x & x : HFinite}";
by Auto_tac;
qed "hpfinite_witness";


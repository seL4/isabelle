(*  Title       : HTranscendental.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh
    Description : Nonstandard extensions of transcendental functions
*)

(*-------------------------------------------------------------------------*)
(* NS extension of square root function                                    *)
(*-------------------------------------------------------------------------*)

Goal "( *f* sqrt) 0 = 0";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_zero_num]));
qed "STAR_sqrt_zero";
Addsimps [STAR_sqrt_zero];

Goal "( *f* sqrt) 1 = 1";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_one_num]));
qed "STAR_sqrt_one";
Addsimps [STAR_sqrt_one];

Goal "(( *f* sqrt)(x) ^ 2 = x) = (0 <= x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_le,
    hypreal_zero_num, starfun,hrealpow,real_sqrt_pow2_iff] 
    delsimps [hpowr_Suc,realpow_Suc]));
qed "hypreal_sqrt_pow2_iff";

Goal "0 < x ==> ( *f* sqrt) (x) ^ 2 = x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset() addIs [FreeUltrafilterNat_subset,
    real_sqrt_gt_zero_pow2],simpset() addsimps 
    [hypreal_less,starfun,hrealpow,hypreal_zero_num] 
    delsimps [hpowr_Suc,realpow_Suc]));
qed "hypreal_sqrt_gt_zero_pow2";

Goal "0 < x ==> 0 < ( *f* sqrt) (x) ^ 2";
by (forward_tac [hypreal_sqrt_gt_zero_pow2] 1);
by (Auto_tac);
qed "hypreal_sqrt_pow2_gt_zero";

Goal "0 < x ==> ( *f* sqrt) (x) ~= 0";
by (forward_tac [hypreal_sqrt_pow2_gt_zero] 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2]));
qed "hypreal_sqrt_not_zero";

Goal "0 < x ==> inverse (( *f* sqrt)(x)) ^ 2 = inverse x";
by (forward_tac [hypreal_sqrt_not_zero] 1);
by (dres_inst_tac [("n1","2"),("r1","( *f* sqrt) x")] (hrealpow_inverse RS sym) 1);
by (auto_tac (claset() addDs [hypreal_sqrt_gt_zero_pow2],simpset()));
qed "hypreal_inverse_sqrt_pow2";

Goalw [hypreal_zero_def] 
    "[|0 < x; 0 <y |] ==> \
\   ( *f* sqrt)(x*y) =  ( *f* sqrt)(x) * ( *f* sqrt)(y)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_mult,hypreal_less,hypreal_zero_num]));
by (ultra_tac (claset() addIs [real_sqrt_mult_distrib],simpset()) 1);
qed "hypreal_sqrt_mult_distrib";

Goal "[|0<=x; 0<=y |] ==> \
\    ( *f* sqrt)(x*y) =  ( *f* sqrt)(x) * ( *f* sqrt)(y)";
by (auto_tac (claset() addIs [hypreal_sqrt_mult_distrib],
    simpset() addsimps [hypreal_le_eq_less_or_eq]));
qed "hypreal_sqrt_mult_distrib2";

Goal "0 < x ==> (( *f* sqrt)(x) @= 0) = (x @= 0)";
by (auto_tac (claset(),simpset() addsimps [mem_infmal_iff RS sym]));
by (rtac (hypreal_sqrt_gt_zero_pow2 RS subst) 1);
by (auto_tac (claset() addIs [Infinitesimal_mult] 
    addSDs [(hypreal_sqrt_gt_zero_pow2 RS ssubst)],simpset() addsimps [numeral_2_eq_2]));
qed "hypreal_sqrt_approx_zero";
Addsimps [hypreal_sqrt_approx_zero];

Goal "0 <= x ==> (( *f* sqrt)(x) @= 0) = (x @= 0)";
by (auto_tac (claset() addSDs [hypreal_le_imp_less_or_eq],
              simpset()));
qed "hypreal_sqrt_approx_zero2";
Addsimps [hypreal_sqrt_approx_zero2];

Goal "(( *f* sqrt)(x*x + y*y + z*z) @= 0) = (x*x + y*y + z*z @= 0)";
by (rtac hypreal_sqrt_approx_zero2 1);
by (REPEAT(rtac hypreal_le_add_order 1));
by Auto_tac;
qed "hypreal_sqrt_sum_squares";
Addsimps [hypreal_sqrt_sum_squares];

Goal  "(( *f* sqrt)(x*x + y*y) @= 0) = (x*x + y*y @= 0)";
by (rtac hypreal_sqrt_approx_zero2 1);
by (rtac hypreal_le_add_order 1);
by Auto_tac;
qed "hypreal_sqrt_sum_squares2";
Addsimps [hypreal_sqrt_sum_squares2];

Goal "0 < x ==> 0 < ( *f* sqrt)(x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps 
    [starfun,hypreal_zero_def,hypreal_less,hypreal_zero_num]));
by (ultra_tac (claset() addIs [real_sqrt_gt_zero], simpset()) 1);
qed "hypreal_sqrt_gt_zero";

Goal "0 <= x ==> 0 <= ( *f* sqrt)(x)";
by (auto_tac (claset() addIs [hypreal_sqrt_gt_zero],
    simpset() addsimps [hypreal_le_eq_less_or_eq ]));
qed "hypreal_sqrt_ge_zero";

Goal "( *f* sqrt)(x ^ 2) = abs(x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_hrabs,hypreal_mult,numeral_2_eq_2]));
qed "hypreal_sqrt_hrabs";
Addsimps [hypreal_sqrt_hrabs];

Goal "( *f* sqrt)(x*x) = abs(x)";
by (rtac (hrealpow_two RS subst) 1);
by (rtac (numeral_2_eq_2 RS subst) 1);
by (rtac hypreal_sqrt_hrabs 1);
qed "hypreal_sqrt_hrabs2";
Addsimps [hypreal_sqrt_hrabs2];

Goal "( *f* sqrt)(x pow (hypnat_of_nat 2)) = abs(x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_hrabs,hypnat_of_nat_def,hyperpow]));
qed "hypreal_sqrt_hyperpow_hrabs";
Addsimps [hypreal_sqrt_hyperpow_hrabs];

Goal "[| x: HFinite; 0 <= x |] ==> st(( *f* sqrt) x) = ( *f* sqrt)(st x)";
by (res_inst_tac [("n","1")] hrealpow_Suc_cancel_eq 1);
by (auto_tac (claset() addSIs [st_zero_le,hypreal_sqrt_ge_zero],simpset()));
by (rtac (st_mult RS subst) 2);
by (rtac (hypreal_sqrt_mult_distrib2 RS subst) 4);
by (rtac (hypreal_sqrt_mult_distrib2 RS subst) 6);
by (auto_tac (claset(), simpset() addsimps [st_hrabs,st_zero_le]));
by (ALLGOALS(rtac (HFinite_square_iff RS iffD1)));
by (auto_tac (claset(),simpset() addsimps 
    [hypreal_sqrt_mult_distrib2 RS sym] 
    delsimps [HFinite_square_iff]));
qed "st_hypreal_sqrt";

Goal "x <= ( *f* sqrt)(x ^ 2 + y ^ 2)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_add,
    hrealpow,hypreal_le] delsimps [hpowr_Suc,realpow_Suc]));
qed "hypreal_sqrt_sum_squares_ge1";
Addsimps [hypreal_sqrt_sum_squares_ge1];

Goal "[| 0 <= x; x : HFinite |] ==> ( *f* sqrt) x : HFinite";
by (auto_tac (claset(),simpset() addsimps [hypreal_le_eq_less_or_eq]));
by (rtac (HFinite_square_iff RS iffD1) 1);
by (dtac hypreal_sqrt_gt_zero_pow2 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2]));
qed "HFinite_hypreal_sqrt";

Goal "[| 0 <= x; ( *f* sqrt) x : HFinite |] ==> x : HFinite";
by (auto_tac (claset(),simpset() addsimps [hypreal_le_eq_less_or_eq]));
by (dtac (HFinite_square_iff RS iffD2) 1);
by (dtac hypreal_sqrt_gt_zero_pow2 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2] delsimps [HFinite_square_iff]));
qed "HFinite_hypreal_sqrt_imp_HFinite";

Goal "0 <= x ==> (( *f* sqrt) x : HFinite) = (x : HFinite)";
by (blast_tac (claset() addIs [HFinite_hypreal_sqrt,
    HFinite_hypreal_sqrt_imp_HFinite]) 1);
qed "HFinite_hypreal_sqrt_iff";
Addsimps [HFinite_hypreal_sqrt_iff];

Goal  "(( *f* sqrt)(x*x + y*y) : HFinite) = (x*x + y*y : HFinite)";
by (rtac HFinite_hypreal_sqrt_iff 1);
by (rtac  hypreal_le_add_order 1);
by Auto_tac;
qed "HFinite_sqrt_sum_squares";
Addsimps [HFinite_sqrt_sum_squares];

Goal "[| 0 <= x; x : Infinitesimal |] ==> ( *f* sqrt) x : Infinitesimal";
by (auto_tac (claset(),simpset() addsimps [hypreal_le_eq_less_or_eq]));
by (rtac (Infinitesimal_square_iff RS iffD2) 1);
by (dtac hypreal_sqrt_gt_zero_pow2 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2]));
qed "Infinitesimal_hypreal_sqrt";

Goal "[| 0 <= x; ( *f* sqrt) x : Infinitesimal |] ==> x : Infinitesimal";
by (auto_tac (claset(),simpset() addsimps [hypreal_le_eq_less_or_eq]));
by (dtac (Infinitesimal_square_iff RS iffD1) 1);
by (dtac hypreal_sqrt_gt_zero_pow2 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2] 
    delsimps [Infinitesimal_square_iff RS sym]));
qed "Infinitesimal_hypreal_sqrt_imp_Infinitesimal";

Goal "0 <= x ==> (( *f* sqrt) x : Infinitesimal) = (x : Infinitesimal)";
by (blast_tac (claset() addIs [Infinitesimal_hypreal_sqrt_imp_Infinitesimal,
    Infinitesimal_hypreal_sqrt]) 1);
qed "Infinitesimal_hypreal_sqrt_iff";
Addsimps [Infinitesimal_hypreal_sqrt_iff];

Goal  "(( *f* sqrt)(x*x + y*y) : Infinitesimal) = (x*x + y*y : Infinitesimal)";
by (rtac Infinitesimal_hypreal_sqrt_iff 1);
by (rtac hypreal_le_add_order 1);
by Auto_tac;
qed "Infinitesimal_sqrt_sum_squares";
Addsimps [Infinitesimal_sqrt_sum_squares];

Goal "[| 0 <= x; x : HInfinite |] ==> ( *f* sqrt) x : HInfinite";
by (auto_tac (claset(),simpset() addsimps [hypreal_le_eq_less_or_eq]));
by (rtac (HInfinite_square_iff RS iffD1) 1);
by (dtac hypreal_sqrt_gt_zero_pow2 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2]));
qed "HInfinite_hypreal_sqrt";

Goal "[| 0 <= x; ( *f* sqrt) x : HInfinite |] ==> x : HInfinite";
by (auto_tac (claset(),simpset() addsimps [hypreal_le_eq_less_or_eq]));
by (dtac (HInfinite_square_iff RS iffD2) 1);
by (dtac hypreal_sqrt_gt_zero_pow2 1);
by (auto_tac (claset(),simpset() addsimps [numeral_2_eq_2] 
    delsimps [HInfinite_square_iff]));
qed "HInfinite_hypreal_sqrt_imp_HInfinite";

Goal "0 <= x ==> (( *f* sqrt) x : HInfinite) = (x : HInfinite)";
by (blast_tac (claset() addIs [HInfinite_hypreal_sqrt,
    HInfinite_hypreal_sqrt_imp_HInfinite]) 1);
qed "HInfinite_hypreal_sqrt_iff";
Addsimps [HInfinite_hypreal_sqrt_iff];

Goal  "(( *f* sqrt)(x*x + y*y) : HInfinite) = (x*x + y*y : HInfinite)";
by (rtac HInfinite_hypreal_sqrt_iff 1);
by (rtac hypreal_le_add_order 1);
by Auto_tac;
qed "HInfinite_sqrt_sum_squares";
Addsimps [HInfinite_sqrt_sum_squares];

Goal "sumhr (0, whn, %n. inverse (real (fact n)) * x ^ n) : HFinite";
by (auto_tac (claset() addSIs [NSBseq_HFinite_hypreal,NSconvergent_NSBseq],
    simpset() addsimps [starfunNat_sumr RS sym,starfunNat,hypnat_omega_def,
    convergent_NSconvergent_iff RS sym, summable_convergent_sumr_iff RS sym,
    summable_exp]));
qed "HFinite_exp";
Addsimps [HFinite_exp];

Goalw [exphr_def] "exphr 0 = 1";
by (res_inst_tac [("n1","1")] (sumhr_split_add RS subst) 1);
by (res_inst_tac [("t","1")] (hypnat_add_zero_left RS subst) 2);
by (rtac hypnat_one_less_hypnat_omega 1);
by (auto_tac (claset(),simpset() addsimps [sumhr,hypnat_zero_def,starfunNat,
    hypnat_one_def,hypnat_add,hypnat_omega_def,hypreal_add] 
    delsimps [hypnat_add_zero_left]));
by (simp_tac (simpset() addsimps [hypreal_one_num RS sym]) 1);
qed "exphr_zero";
Addsimps [exphr_zero];

Goalw [coshr_def] "coshr 0 = 1";
by (res_inst_tac [("n1","1")] (sumhr_split_add RS subst) 1);
by (res_inst_tac [("t","1")] (hypnat_add_zero_left RS subst) 2);
by (rtac hypnat_one_less_hypnat_omega 1);
by (auto_tac (claset(),simpset() addsimps [sumhr,hypnat_zero_def,starfunNat,
    hypnat_one_def,hypnat_add,hypnat_omega_def,st_add RS sym,
    (hypreal_one_def RS meta_eq_to_obj_eq) RS sym, 
    (hypreal_zero_def RS meta_eq_to_obj_eq) RS sym] delsimps [hypnat_add_zero_left]));
qed "coshr_zero";
Addsimps [coshr_zero];

Goalw [hypreal_zero_def,hypreal_one_def] "( *f* exp) 0 @= 1";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_one_num]));
qed "STAR_exp_zero_approx_one";
Addsimps [STAR_exp_zero_approx_one];

Goal "x: Infinitesimal ==> ( *f* exp) x @= 1";
by (case_tac "x = 0" 1);
by (cut_inst_tac [("x","0")] DERIV_exp 2);
by (auto_tac (claset(),simpset() addsimps [NSDERIV_DERIV_iff RS sym,
    nsderiv_def]));
by (dres_inst_tac [("x","x")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("c","x")] approx_mult1 1);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
    simpset() addsimps [hypreal_mult_assoc]));
by (res_inst_tac [("d","-1")] approx_add_right_cancel 1);
by (rtac (approx_sym RSN (2,approx_trans2)) 1);
by (auto_tac (claset(),simpset() addsimps [mem_infmal_iff]));
qed "STAR_exp_Infinitesimal";

Goal "( *f* exp) epsilon @= 1";
by (auto_tac (claset() addIs [STAR_exp_Infinitesimal],simpset()));
qed "STAR_exp_epsilon";
Addsimps [STAR_exp_epsilon];

Goal "( *f* exp)(x + y) = ( *f* exp) x * ( *f* exp) y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_add,
    hypreal_mult,exp_add]));
qed "STAR_exp_add";

Goalw [exphr_def] "exphr x = hypreal_of_real (exp x)";
by (rtac (st_hypreal_of_real  RS subst) 1);
by (rtac approx_st_eq 1);
by Auto_tac;
by (rtac (approx_minus_iff RS iffD2) 1);
by (auto_tac (claset(),simpset() addsimps [mem_infmal_iff RS sym,
    hypreal_of_real_def,hypnat_zero_def,hypnat_omega_def,sumhr,
    hypreal_minus,hypreal_add]));
by (rtac NSLIMSEQ_zero_Infinitesimal_hypreal 1);
by (cut_inst_tac [("x3","x")] (exp_converges RS ((sums_def RS 
    meta_eq_to_obj_eq) RS iffD1)) 1);
by (dres_inst_tac [("b","- exp x")] (LIMSEQ_const RSN (2,LIMSEQ_add)) 1);
by (auto_tac (claset(),simpset() addsimps [LIMSEQ_NSLIMSEQ_iff]));
qed "exphr_hypreal_of_real_exp_eq";

Goal "0 <= x ==> (1 + x) <= ( *f* exp) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_add,
    hypreal_le,hypreal_zero_num,hypreal_one_num]));
by (Ultra_tac 1);
qed "starfun_exp_ge_add_one_self";
Addsimps [starfun_exp_ge_add_one_self];

(* exp (oo) is infinite *)
Goal "[| x : HInfinite; 0 <= x |] ==> ( *f* exp) x : HInfinite";
by (ftac starfun_exp_ge_add_one_self 1);
by (rtac HInfinite_ge_HInfinite 1);
by (rtac hypreal_le_trans 2);
by (TRYALL(assume_tac) THEN Simp_tac 1);
qed "starfun_exp_HInfinite";

Goal "( *f* exp) (-x) = inverse(( *f* exp) x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_inverse,
    hypreal_minus,exp_minus]));
qed "starfun_exp_minus";

(* exp (-oo) is infinitesimal *)
Goal "[| x : HInfinite; x <= 0 |] ==> ( *f* exp) x : Infinitesimal";
by (subgoal_tac "EX y. x = - y" 1);
by (res_inst_tac [("x","- x")] exI 2);
by (auto_tac (claset() addSIs [HInfinite_inverse_Infinitesimal,
    starfun_exp_HInfinite] addIs [(starfun_exp_minus RS ssubst)],
     simpset() addsimps [HInfinite_minus_iff]));
qed "starfun_exp_Infinitesimal";

Goal "0 < x ==> 1 < ( *f* exp) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_one_num,
    hypreal_zero_num,hypreal_less]));
by (Ultra_tac 1);
qed "starfun_exp_gt_one";
Addsimps [starfun_exp_gt_one];

(* needs derivative of inverse function
   TRY a NS one today!!!

Goal "x @= 1 ==> ( *f* ln) x @= 1";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_one_def]));


Goalw [nsderiv_def] "0r < x ==> NSDERIV ln x :> inverse x";

*)


Goal "( *f* ln) (( *f* exp) x) = x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun]));
qed "starfun_ln_exp";
Addsimps [starfun_ln_exp];

Goal "(( *f* exp)(( *f* ln) x) = x) = (0 < x)";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_num,hypreal_less]));
qed "starfun_exp_ln_iff";
Addsimps [starfun_exp_ln_iff];

Goal "( *f* exp) u = x ==> ( *f* ln) x = u";
by (auto_tac (claset(),simpset() addsimps [starfun]));
qed "starfun_exp_ln_eq";

Goal "0 < x ==> ( *f* ln) x < x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_num,hypreal_less]));
by (Ultra_tac 1);
qed "starfun_ln_less_self";
Addsimps [starfun_ln_less_self];

Goal "1 <= x ==> 0 <= ( *f* ln) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_num,hypreal_le,hypreal_one_num]));
by (Ultra_tac 1);
qed "starfun_ln_ge_zero";
Addsimps [starfun_ln_ge_zero];

Goal "1 < x ==> 0 < ( *f* ln) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_num,hypreal_less,hypreal_one_num]));
by (Ultra_tac 1);
qed "starfun_ln_gt_zero";
Addsimps [starfun_ln_gt_zero];

Goal "[| 0 < x; x ~= 1 |] ==> ( *f* ln) x ~= 0";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_num,hypreal_less,hypreal_one_num]));
by (ultra_tac (claset() addIs [ccontr] addDs [ln_not_eq_zero],simpset()) 1);
qed "starfun_ln_not_eq_zero";
Addsimps [starfun_ln_not_eq_zero];

Goal "[| x: HFinite; 1 <= x |] ==> ( *f* ln) x : HFinite";
by (rtac HFinite_bounded 1);
by (rtac order_less_imp_le 2);
by (rtac starfun_ln_less_self 2);
by (rtac order_less_le_trans 2);
by Auto_tac;
qed "starfun_ln_HFinite";

Goal "0 < x ==> ( *f* ln) (inverse x) = -( *f* ln) x";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    hypreal_zero_num,hypreal_minus,hypreal_inverse,
    hypreal_less]));
by (Ultra_tac 1);
by (auto_tac (claset(),simpset() addsimps [ln_inverse]));
qed "starfun_ln_inverse";

Goal "x : HFinite ==> ( *f* exp) x : HFinite";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [starfun,
    HFinite_FreeUltrafilterNat_iff]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by Auto_tac;
by (res_inst_tac [("x","exp u")] exI 1);
by (Ultra_tac 1 THEN arith_tac 1);
qed "starfun_exp_HFinite";

Goal "[|x: Infinitesimal; z: HFinite |] ==> ( *f* exp) (z + x) @= ( *f* exp) z";
by (simp_tac (simpset() addsimps [STAR_exp_add]) 1);
by (ftac STAR_exp_Infinitesimal 1);
by (dtac approx_mult2 1);
by (auto_tac (claset() addIs [starfun_exp_HFinite],simpset()));
qed "starfun_exp_add_HFinite_Infinitesimal_approx";

(* using previous result to get to result *)
Goal "[| x : HInfinite; 0 < x |] ==> ( *f* ln) x : HInfinite";
by (rtac ccontr 1 THEN dtac (HFinite_HInfinite_iff RS iffD2) 1);
by (dtac starfun_exp_HFinite 1);
by (auto_tac (claset(),simpset() addsimps [starfun_exp_ln_iff RS iffD2,
    HFinite_HInfinite_iff]));
qed "starfun_ln_HInfinite";

Goal "x : HInfinite ==> ( *f* exp) x : HInfinite | ( *f* exp) x : Infinitesimal";
by (cut_inst_tac [("x","x")] (CLAIM "x <= (0::hypreal) | 0 <= x") 1);
by (auto_tac (claset() addIs [starfun_exp_HInfinite,starfun_exp_Infinitesimal],
    simpset()));
qed "starfun_exp_HInfinite_Infinitesimal_disj";

(* check out this proof!!! *)
Goal "[| x : HFinite - Infinitesimal; 0 < x |] ==> ( *f* ln) x : HFinite";
by (rtac ccontr 1 THEN dtac (HInfinite_HFinite_iff RS iffD2) 1);
by (dtac starfun_exp_HInfinite_Infinitesimal_disj 1);
by (auto_tac (claset(),simpset() addsimps [starfun_exp_ln_iff RS sym,
    HInfinite_HFinite_iff] delsimps [starfun_exp_ln_iff]));
qed "starfun_ln_HFinite_not_Infinitesimal";

(* we do proof by considering ln of 1/x *)
Goal "[| x : Infinitesimal; 0 < x |] ==> ( *f* ln) x : HInfinite";
by (dtac Infinitesimal_inverse_HInfinite 1);
by (ftac hypreal_inverse_gt_0 1);
by (dtac starfun_ln_HInfinite 2);
by (auto_tac (claset(),simpset() addsimps [starfun_ln_inverse,
    HInfinite_minus_iff]));
qed "starfun_ln_Infinitesimal_HInfinite";

Goal "[| 0 < x; x < 1 |] ==> ( *f* ln) x < 0";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_zero_num,
     hypreal_one_num,hypreal_less,starfun]));
by (ultra_tac (claset() addIs [ln_less_zero],simpset()) 1);
qed "starfun_ln_less_zero";

Goal "[| x : Infinitesimal; 0 < x |] ==> ( *f* ln) x < 0";
by (auto_tac (claset() addSIs [starfun_ln_less_zero],simpset() 
    addsimps [Infinitesimal_def]));
by (dres_inst_tac [("x","1")] bspec 1);
by (auto_tac (claset(),simpset() addsimps [hrabs_def]));
qed "starfun_ln_Infinitesimal_less_zero";

Goal "[| x : HInfinite; 0 < x |] ==> 0 < ( *f* ln) x";
by (auto_tac (claset() addSIs [starfun_ln_gt_zero],simpset() 
    addsimps [HInfinite_def]));
by (dres_inst_tac [("x","1")] bspec 1);
by (auto_tac (claset(),simpset() addsimps [hrabs_def]));
qed "starfun_ln_HInfinite_gt_zero";

(*
Goalw [NSLIM_def] "(%h. ((x powr h) - 1) / h) -- 0 --NS> ln x";
*)

Goal "sumhr (0, whn, %n. (if even(n) then 0 else \
\             ((- 1) ^ ((n - 1) div 2))/(real (fact n))) * x ^ n) \
\             : HFinite";
by (auto_tac (claset() addSIs [NSBseq_HFinite_hypreal,NSconvergent_NSBseq],
    simpset() addsimps [starfunNat_sumr RS sym,starfunNat,hypnat_omega_def,
    convergent_NSconvergent_iff RS sym, summable_convergent_sumr_iff RS sym]));
by (rtac (CLAIM "1 = Suc 0" RS ssubst) 1);
by (rtac summable_sin 1);
qed "HFinite_sin";
Addsimps [HFinite_sin];

Goal "( *f* sin) 0 = 0";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_zero_num]));
qed "STAR_sin_zero";
Addsimps [STAR_sin_zero];

Goal "x : Infinitesimal ==> ( *f* sin) x @= x";
by (case_tac "x = 0" 1);
by (cut_inst_tac [("x","0")] DERIV_sin 2);
by (auto_tac (claset(),simpset() addsimps [NSDERIV_DERIV_iff RS sym,
    nsderiv_def,hypreal_of_real_zero]));
by (dres_inst_tac [("x","x")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("c","x")] approx_mult1 1);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
    simpset() addsimps [hypreal_mult_assoc]));
qed "STAR_sin_Infinitesimal";
Addsimps [STAR_sin_Infinitesimal];

Goal "sumhr (0, whn, %n. (if even(n) then \
\           ((- 1) ^ (n div 2))/(real (fact n)) else \
\           0) * x ^ n) : HFinite";
by (auto_tac (claset() addSIs [NSBseq_HFinite_hypreal,NSconvergent_NSBseq],
    simpset() addsimps [starfunNat_sumr RS sym,starfunNat,hypnat_omega_def,
    convergent_NSconvergent_iff RS sym, summable_convergent_sumr_iff RS sym,
    summable_cos]));
qed "HFinite_cos";
Addsimps [HFinite_cos];

Goal "( *f* cos) 0 = 1";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_zero_num,
    hypreal_one_num]));
qed "STAR_cos_zero";
Addsimps [STAR_cos_zero];

Goal "x : Infinitesimal ==> ( *f* cos) x @= 1";
by (case_tac "x = 0" 1);
by (cut_inst_tac [("x","0")] DERIV_cos 2);
by (auto_tac (claset(),simpset() addsimps [NSDERIV_DERIV_iff RS sym,
    nsderiv_def,hypreal_of_real_zero]));
by (dres_inst_tac [("x","x")] bspec 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_of_real_zero,
    hypreal_of_real_one]));
by (dres_inst_tac [("c","x")] approx_mult1 1);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
    simpset() addsimps [hypreal_mult_assoc,hypreal_of_real_one]));
by (res_inst_tac [("d","-1")] approx_add_right_cancel 1);
by Auto_tac;
qed "STAR_cos_Infinitesimal";
Addsimps [STAR_cos_Infinitesimal];

Goal "( *f* tan) 0 = 0";
by (auto_tac (claset(),simpset() addsimps [starfun,hypreal_zero_num]));
qed "STAR_tan_zero";
Addsimps [STAR_tan_zero];

Goal "x : Infinitesimal ==> ( *f* tan) x @= x";
by (case_tac "x = 0" 1);
by (cut_inst_tac [("x","0")] DERIV_tan 2);
by (auto_tac (claset(),simpset() addsimps [NSDERIV_DERIV_iff RS sym,
    nsderiv_def,hypreal_of_real_zero]));
by (dres_inst_tac [("x","x")] bspec 1);
by Auto_tac;
by (dres_inst_tac [("c","x")] approx_mult1 1);
by (auto_tac (claset() addIs [Infinitesimal_subset_HFinite RS subsetD],
    simpset() addsimps [hypreal_mult_assoc]));
qed "STAR_tan_Infinitesimal";

Goal "x : Infinitesimal ==> ( *f* sin) x * ( *f* cos) x @= x";
by (rtac (simplify (simpset()) (read_instantiate  
          [("d","1")] approx_mult_HFinite)) 1);
by (auto_tac (claset(),simpset() addsimps [Infinitesimal_subset_HFinite 
    RS subsetD]));
qed "STAR_sin_cos_Infinitesimal_mult";

Goal "hypreal_of_real pi : HFinite";
by (Simp_tac 1);
qed "HFinite_pi";

(* lemmas *)

Goal "N : HNatInfinite \
\     ==> hypreal_of_real a = \
\         hypreal_of_hypnat N * (inverse(hypreal_of_hypnat N) * hypreal_of_real a)";
by (auto_tac (claset(),simpset() addsimps [hypreal_mult_assoc RS sym,
    HNatInfinite_not_eq_zero]));
val lemma_split_hypreal_of_real = result();

Goal "[|x : Infinitesimal; x ~= 0 |] ==> ( *f* sin) x/x @= 1";
by (cut_inst_tac [("x","0")] DERIV_sin 1);
by (auto_tac (claset(),simpset() addsimps [NSDERIV_DERIV_iff RS sym,
    nsderiv_def,hypreal_of_real_zero,hypreal_of_real_one]));
qed "STAR_sin_Infinitesimal_divide";

(*------------------------------------------------------------------------*) 
(* sin* (1/n) * 1/(1/n) @= 1 for n = oo                                   *)
(*------------------------------------------------------------------------*)

Goal "n : HNatInfinite \
\     ==> ( *f* sin) (inverse (hypreal_of_hypnat n))/(inverse (hypreal_of_hypnat n)) @= 1";
by (rtac STAR_sin_Infinitesimal_divide 1);
by Auto_tac;
val lemma_sin_pi = result();

Goal "n : HNatInfinite \
\     ==> ( *f* sin) (inverse (hypreal_of_hypnat n)) * hypreal_of_hypnat n @= 1";
by (forward_tac [lemma_sin_pi] 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_divide_def]));
qed "STAR_sin_inverse_HNatInfinite";

Goalw [hypreal_divide_def] 
     "N : HNatInfinite \
\     ==> hypreal_of_real pi/(hypreal_of_hypnat N) : Infinitesimal";
by (auto_tac (claset() addIs [Infinitesimal_HFinite_mult2],simpset()));
qed "Infinitesimal_pi_divide_HNatInfinite";

Goal "N : HNatInfinite \
\     ==> hypreal_of_real pi/(hypreal_of_hypnat N) ~= 0";
by Auto_tac;
qed "pi_divide_HNatInfinite_not_zero";
Addsimps [pi_divide_HNatInfinite_not_zero];

Goal "n : HNatInfinite \
\     ==> ( *f* sin) (hypreal_of_real pi/(hypreal_of_hypnat n)) * hypreal_of_hypnat n \
\         @= hypreal_of_real pi";
by (ftac ([Infinitesimal_pi_divide_HNatInfinite,pi_divide_HNatInfinite_not_zero] 
          MRS STAR_sin_Infinitesimal_divide) 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_inverse_distrib]));
by (res_inst_tac [("a","inverse(hypreal_of_real pi)")] approx_SReal_mult_cancel 1);
by (auto_tac (claset() addIs [SReal_inverse],simpset() addsimps [hypreal_divide_def] @ 
    hypreal_mult_ac));
qed "STAR_sin_pi_divide_HNatInfinite_approx_pi";

Goal "n : HNatInfinite \
\     ==> hypreal_of_hypnat n * \
\         ( *f* sin) (hypreal_of_real pi/(hypreal_of_hypnat n)) \
\         @= hypreal_of_real pi";
by (rtac (hypreal_mult_commute RS subst) 1);
by (etac STAR_sin_pi_divide_HNatInfinite_approx_pi 1);
qed "STAR_sin_pi_divide_HNatInfinite_approx_pi2";

(*** more theorems ***)

Goalw [real_divide_def] 
     "N : HNatInfinite \
\     ==> ( *fNat* (%x. pi / real x)) N : Infinitesimal";
by (auto_tac (claset() addSIs [Infinitesimal_HFinite_mult2],
    simpset() addsimps [starfunNat_mult RS sym,starfunNat_inverse RS sym,
    starfunNat_real_of_nat]));
qed "starfunNat_pi_divide_n_Infinitesimal";

Goal "N : HNatInfinite ==> \
\     ( *f* sin) (( *fNat* (%x. pi / real x)) N) @= \
\     hypreal_of_real pi/(hypreal_of_hypnat N)";
by (auto_tac (claset() addSIs [STAR_sin_Infinitesimal,
    Infinitesimal_HFinite_mult2],simpset() addsimps [starfunNat_mult RS sym,
    hypreal_divide_def,real_divide_def,starfunNat_inverse_real_of_nat_eq]));
qed "STAR_sin_pi_divide_n_approx";

(*** move to NSA ***)
Goalw [hypnat_zero_def] "(n <= (0::hypnat)) = (n = 0)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_le]));
qed "hypnat_le_zero_cancel";
AddIffs [hypnat_le_zero_cancel];

Goal "N : HNatInfinite ==> 0 < hypreal_of_hypnat N";
by (rtac ccontr 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_of_hypnat_zero RS sym,
    symmetric hypnat_le_def]));
qed "HNatInfinite_hypreal_of_hypnat_gt_zero";

bind_thm ("HNatInfinite_hypreal_of_hypnat_not_eq_zero",
          HNatInfinite_hypreal_of_hypnat_gt_zero RS hypreal_not_refl2 RS not_sym);
(*** END: move to NSA ***)

Goalw [NSLIMSEQ_def] "(%n. real n * sin (pi / real n)) ----NS> pi";
by (auto_tac (claset(),simpset() addsimps [starfunNat_mult RS sym,
    starfunNat_real_of_nat]));
by (res_inst_tac [("f1","sin")]  (starfun_stafunNat_o2 RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [starfunNat_mult RS sym,
    starfunNat_real_of_nat,real_divide_def]));
by (res_inst_tac [("f1","inverse")]  (starfun_stafunNat_o2 RS subst) 1);
by (auto_tac (claset() addDs [STAR_sin_pi_divide_HNatInfinite_approx_pi],
    simpset() addsimps [starfunNat_real_of_nat,hypreal_mult_commute,
    symmetric hypreal_divide_def]));
qed "NSLIMSEQ_sin_pi";

Goalw [NSLIMSEQ_def] "(%n. cos (pi / real n))----NS> 1";
by Auto_tac;
by (res_inst_tac [("f1","cos")]  (starfun_stafunNat_o2 RS subst) 1);
by (rtac STAR_cos_Infinitesimal 1);
by (auto_tac (claset() addSIs [Infinitesimal_HFinite_mult2],
    simpset() addsimps [starfunNat_mult RS sym,real_divide_def,
    starfunNat_inverse RS sym,starfunNat_real_of_nat]));
qed "NSLIMSEQ_cos_one";

Goal "(%n. real n * sin (pi / real n) * cos (pi / real n)) ----NS> pi";
by (rtac (simplify (simpset()) 
    ([NSLIMSEQ_sin_pi,NSLIMSEQ_cos_one] MRS NSLIMSEQ_mult)) 1);
qed "NSLIMSEQ_sin_cos_pi";

(*------------------------------------------------------------------------*)
(* A familiar approximation to cos x when x is small                      *)
(*------------------------------------------------------------------------*)

Goal "x : Infinitesimal ==> ( *f* cos) x @= 1 - x ^ 2";
by (rtac (STAR_cos_Infinitesimal RS approx_trans) 1);
by (auto_tac (claset(),simpset() addsimps [Infinitesimal_approx_minus RS sym,
    hypreal_diff_def,hypreal_add_assoc RS sym,numeral_2_eq_2]));
qed "STAR_cos_Infinitesimal_approx";

(* move to NSA *)
Goalw [hypreal_divide_def] 
  "[| x : Infinitesimal; y : Reals; y ~= 0 |] ==> x/y : Infinitesimal";
by (auto_tac (claset() addSIs [Infinitesimal_HFinite_mult]
    addSDs [SReal_inverse RS (SReal_subset_HFinite RS subsetD)],simpset()));
qed "Infinitesimal_SReal_divide";

Goal "x : Infinitesimal ==> ( *f* cos) x @= 1 - (x ^ 2)/2";
by (rtac (STAR_cos_Infinitesimal RS approx_trans) 1);
by (auto_tac (claset() addIs [Infinitesimal_SReal_divide],
    simpset() addsimps [Infinitesimal_approx_minus RS sym,
    numeral_2_eq_2]));
qed "STAR_cos_Infinitesimal_approx2";






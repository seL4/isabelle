(*lcp: lemmas needed now because 2 is a binary numeral!*)

Goal "m+m = m*(2::nat)";
by Auto_tac; 
qed "m_add_m_eq2";

(*lcp: needed for binary 2 MOVE UP???*)

Goal "(0::real) <= x^2";
by (asm_full_simp_tac (simpset() addsimps [numeral_2_eq_2]) 1); 
qed "zero_le_x_squared";
Addsimps [zero_le_x_squared];

fun multl_by_tac x i = 
       let val cancel_thm = 
           CLAIM "[| (0::real)<z; z*x<z*y |] ==> x<y" 
       in
           res_inst_tac [("z",x)] cancel_thm i 
       end;

fun multr_by_tac x i = 
       let val cancel_thm = 
           CLAIM "[| (0::real)<z; x*z<y*z |] ==> x<y" 
       in
           res_inst_tac [("z",x)] cancel_thm i 
       end;

(* unused? *)
Goal "ALL x y. x < y --> (f::real=>real) x < f y ==> inj f";
by (rtac injI 1 THEN rtac ccontr 1);
by (dtac (ARITH_PROVE "x ~= y ==> x < y | y < (x::real)") 1);
by (Step_tac 1);
by (auto_tac (claset() addSDs [spec],simpset()));
qed "real_monofun_inj";

(* HyperDef *)

Goal "0 = Abs_hypreal (hyprel `` {%n. 0})";
by (simp_tac (simpset() addsimps [hypreal_zero_def RS meta_eq_to_obj_eq RS sym]) 1);
qed "hypreal_zero_num";

Goal "1 = Abs_hypreal (hyprel `` {%n. 1})";
by (simp_tac (simpset() addsimps [hypreal_one_def RS meta_eq_to_obj_eq RS sym]) 1);
qed "hypreal_one_num";

(* RealOrd *)

Goalw [real_of_posnat_def] "0 < real_of_posnat n";
by (rtac (real_gt_zero_preal_Ex RS iffD2) 1);
by (Blast_tac 1);
qed "real_of_posnat_gt_zero";

Addsimps [real_of_posnat_gt_zero];

bind_thm ("real_inv_real_of_posnat_gt_zero",
          real_of_posnat_gt_zero RS real_inverse_gt_0);
Addsimps [real_inv_real_of_posnat_gt_zero];

bind_thm ("real_of_posnat_ge_zero",real_of_posnat_gt_zero RS order_less_imp_le);
Addsimps [real_of_posnat_ge_zero];

Goal "real_of_posnat n ~= 0";
by (rtac (real_of_posnat_gt_zero RS real_not_refl2 RS not_sym) 1);
qed "real_of_posnat_not_eq_zero";
Addsimps[real_of_posnat_not_eq_zero];

Addsimps [real_of_posnat_not_eq_zero RS real_mult_inv_left];
Addsimps [real_of_posnat_not_eq_zero RS real_mult_inv_right];

Goal "1 <= real_of_posnat n";
by (simp_tac (simpset() addsimps [real_of_posnat_one RS sym]) 1);
by (induct_tac "n" 1);
by (auto_tac (claset(),
	      simpset () addsimps [real_of_posnat_Suc,real_of_posnat_one,
				   order_less_imp_le]));
qed "real_of_posnat_ge_one";
Addsimps [real_of_posnat_ge_one];

Goal "inverse(real_of_posnat n) ~= 0";
by (rtac ((real_of_posnat_gt_zero RS 
    real_not_refl2 RS not_sym) RS real_inverse_not_zero) 1);
qed "real_of_posnat_real_inv_not_zero";
Addsimps [real_of_posnat_real_inv_not_zero];

Goal "inverse(real_of_posnat x) = inverse(real_of_posnat y) ==> x = y";
by (rtac (inj_real_of_posnat RS injD) 1);
by (res_inst_tac [("n2","x")] 
    (real_of_posnat_real_inv_not_zero RS real_mult_left_cancel RS iffD1) 1);
by (asm_full_simp_tac (simpset() addsimps [(real_of_posnat_gt_zero RS 
    real_not_refl2 RS not_sym) RS real_mult_inv_left]) 1);
qed "real_of_posnat_real_inv_inj";

Goal "r < r + inverse(real_of_posnat n)";
by Auto_tac;
qed "real_add_inv_real_of_posnat_less";
Addsimps [real_add_inv_real_of_posnat_less];

Goal "r <= r + inverse(real_of_posnat n)";
by Auto_tac;
qed "real_add_inv_real_of_posnat_le";
Addsimps [real_add_inv_real_of_posnat_le];

Goal "0 < r ==> r*(1 + -inverse(real_of_posnat n)) < r";
by (simp_tac (simpset() addsimps [real_add_mult_distrib2]) 1);
by (res_inst_tac [("C","-r")] real_less_add_left_cancel 1);
by (auto_tac (claset() addIs [real_mult_order],simpset() 
    addsimps [real_add_assoc RS sym,real_minus_zero_less_iff2]));
qed "real_mult_less_self";

Goal "(EX n. inverse(real_of_posnat n) < r) = (EX n. 1 < r * real_of_posnat n)";
by (Step_tac 1);
by (dres_inst_tac [("n1","n")] (real_of_posnat_gt_zero 
                       RS real_mult_less_mono1) 1);
by (dres_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
        real_inverse_gt_0 RS real_mult_less_mono1) 2);
by (auto_tac (claset(),
	      simpset() addsimps [(real_of_posnat_gt_zero RS 
    real_not_refl2 RS not_sym),real_mult_assoc]));
qed "real_of_posnat_inv_Ex_iff";

Goal "(inverse(real_of_posnat n) < r) = (1 < r * real_of_posnat n)";
by (Step_tac 1);
by (dres_inst_tac [("n1","n")] (real_of_posnat_gt_zero 
                       RS real_mult_less_mono1) 1);
by (dres_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
        real_inverse_gt_0 RS real_mult_less_mono1) 2);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc]));
qed "real_of_posnat_inv_iff";

Goal "[| (0::real) <=z; x<y |] ==> z*x<=z*y";
by (asm_simp_tac (simpset() addsimps [real_mult_commute,real_mult_le_less_mono1]) 1);
qed "real_mult_le_less_mono2";

Goal "[| (0::real) <=z; x<=y |] ==> z*x<=z*y";
by (dres_inst_tac [("x","x")] real_le_imp_less_or_eq 1);
by (auto_tac (claset() addIs [real_mult_le_less_mono2], simpset()));
qed "real_mult_le_le_mono1";

Goal "[| (0::real)<=z; x<=y |] ==> x*z<=y*z";
by (dtac (real_mult_le_le_mono1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_commute]));
qed "real_mult_le_le_mono2";

Goal "(inverse(real_of_posnat n) <= r) = (1 <= r * real_of_posnat n)";
by (Step_tac 1);
by (dres_inst_tac [("n2","n")] (real_of_posnat_gt_zero RS 
    order_less_imp_le RS real_mult_le_le_mono1) 1);
by (dres_inst_tac [("n3","n")] (real_of_posnat_gt_zero RS 
        real_inverse_gt_0 RS order_less_imp_le RS 
        real_mult_le_le_mono1) 2);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "real_of_posnat_inv_le_iff";

Goalw [real_of_posnat_def] 
      "(real_of_posnat n < real_of_posnat m) = (n < m)";
by Auto_tac;
qed "real_of_posnat_less_iff";
Addsimps [real_of_posnat_less_iff];

Goal "(real_of_posnat n <= real_of_posnat m) = (n <= m)";
by (auto_tac (claset() addDs [inj_real_of_posnat RS injD],
    simpset() addsimps [real_le_less,le_eq_less_or_eq]));
qed "real_of_posnat_le_iff";
Addsimps [real_of_posnat_le_iff];

Goal "[| (0::real)<z; x*z<y*z |] ==> x<y";
by Auto_tac;
qed "real_mult_less_cancel3";

Goal "[| (0::real)<z; z*x<z*y |] ==> x<y";
by Auto_tac;
qed "real_mult_less_cancel4";

Goal "0 < u  ==> (u < inverse (real_of_posnat n)) = (real_of_posnat n < inverse(u))";
by (Step_tac 1);
by (res_inst_tac [("n2","n")] ((real_of_posnat_gt_zero RS 
    real_inverse_gt_0) RS real_mult_less_cancel3) 1);
by (res_inst_tac [("x1","u")] ( real_inverse_gt_0
   RS real_mult_less_cancel3) 2);
by (auto_tac (claset(),
	      simpset() addsimps [real_not_refl2 RS not_sym]));
by (res_inst_tac [("z","u")] real_mult_less_cancel4 1);
by (res_inst_tac [("n1","n")] (real_of_posnat_gt_zero RS 
    real_mult_less_cancel4) 3);
by (auto_tac (claset(),
	      simpset() addsimps [real_not_refl2 RS not_sym,
              real_mult_assoc RS sym]));
qed "real_of_posnat_less_inv_iff";

Goal "0 < u ==> (u = inverse(real_of_posnat n)) = (real_of_posnat n = inverse u)";
by Auto_tac;
qed "real_of_posnat_inv_eq_iff";

Goal "0 <= 1 + -inverse(real_of_posnat n)";
by (res_inst_tac [("C","inverse(real_of_posnat n)")] real_le_add_right_cancel 1);
by (simp_tac (simpset() addsimps [real_add_assoc,
    real_of_posnat_inv_le_iff]) 1);
qed "real_add_one_minus_inv_ge_zero";

Goal "0 < r ==> 0 <= r*(1 + -inverse(real_of_posnat n))";
by (dtac (real_add_one_minus_inv_ge_zero RS real_mult_le_less_mono1) 1);
by (Auto_tac);
qed "real_mult_add_one_minus_ge_zero";

Goal "x*y = (1::real) ==> y = inverse x";
by (case_tac "x ~= 0" 1);
by (res_inst_tac [("c1","x")] (real_mult_left_cancel RS iffD1) 1);
by Auto_tac;
qed "real_inverse_unique";

Goal "[| (0::real) < x; x < 1 |] ==> 1 < inverse x";
by (auto_tac (claset() addDs [real_inverse_less_swap],simpset()));
qed "real_inverse_gt_one";

Goal "(0 < real (n::nat)) = (0 < n)";
by (rtac (real_of_nat_less_iff RS subst) 1);
by Auto_tac;
qed "real_of_nat_gt_zero_cancel_iff";
Addsimps [real_of_nat_gt_zero_cancel_iff];

Goal "(real (n::nat) <= 0) = (n = 0)";
by (rtac ((real_of_nat_zero) RS subst) 1);
by (rtac (real_of_nat_le_iff RS ssubst) 1);
by Auto_tac;
qed "real_of_nat_le_zero_cancel_iff";
Addsimps [real_of_nat_le_zero_cancel_iff];

Goal "~ real (n::nat) < 0";
by (simp_tac (simpset() addsimps [symmetric real_le_def,
    real_of_nat_ge_zero]) 1);
qed "not_real_of_nat_less_zero";
Addsimps [not_real_of_nat_less_zero];

Goalw [real_le_def,le_def] 
      "(0 <= real (n::nat)) = (0 <= n)";
by (Simp_tac 1);
qed "real_of_nat_ge_zero_cancel_iff";
Addsimps [real_of_nat_ge_zero_cancel_iff];

Goal "real n = (if n=0 then 0 else 1 + real ((n::nat) - 1))";
by (case_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc]));
qed "real_of_nat_num_if";

Goal "4 * real n = real (4 * (n::nat))";
by Auto_tac;
qed "real_of_nat_mult_num_4_eq";

(*REDUNDANT
    Goal "x * x = -(y * y) ==> x = (0::real)";
    by (auto_tac (claset() addIs [
	real_sum_squares_cancel],simpset()));
    qed "real_sum_squares_cancel1a";

    Goal "x * x = -(y * y) ==> y = (0::real)";
    by (auto_tac (claset() addIs [
	real_sum_squares_cancel],simpset()));
    qed "real_sum_squares_cancel2a";
*)

Goal "x * x = -(y * y) ==> x = (0::real) & y=0";
by (auto_tac (claset() addIs [real_sum_squares_cancel],simpset()));
qed "real_sum_squares_cancel_a";

Goal "x*x - (1::real) = (x + 1)*(x - 1)";
by (auto_tac (claset(),simpset() addsimps [real_add_mult_distrib,
    real_add_mult_distrib2,real_diff_def]));
qed "real_squared_diff_one_factored";

Goal "(x*x = (1::real)) = (x = 1 | x = - 1)";
by Auto_tac;
by (dtac (CLAIM "x = (y::real) ==> x - y = 0") 1);
by (auto_tac (claset(),simpset() addsimps [real_squared_diff_one_factored]));
qed "real_mult_is_one";
AddIffs [real_mult_is_one];

Goal "(x + y/2 <= (y::real)) = (x <= y /2)";
by Auto_tac;
qed "real_le_add_half_cancel";
Addsimps [real_le_add_half_cancel];

Goal "(x::real) - x/2 = x/2";
by Auto_tac;
qed "real_minus_half_eq";
Addsimps [real_minus_half_eq];

Goal "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> inverse x * y < inverse x1 * u";
by (multl_by_tac "x" 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym]));
by (simp_tac (simpset() addsimps real_mult_ac) 1);
by (multr_by_tac "x1" 1);
by (auto_tac (claset(),simpset() addsimps real_mult_ac));
qed "real_mult_inverse_cancel";

Goal "[|(0::real) < x;0 < x1; x1 * y < x * u |] ==> y * inverse x < u * inverse x1";
by (auto_tac (claset() addDs [real_mult_inverse_cancel],simpset() addsimps real_mult_ac));
qed "real_mult_inverse_cancel2";

Goal "0 < inverse (real (Suc n))";
by Auto_tac;
qed "inverse_real_of_nat_gt_zero";
Addsimps [ inverse_real_of_nat_gt_zero];

Goal "0 <= inverse (real (Suc n))";
by Auto_tac;
qed "inverse_real_of_nat_ge_zero";
Addsimps [ inverse_real_of_nat_ge_zero];

Goal "x ~= 0 ==> x * x + y * y ~= (0::real)";
by (rtac (CLAIM "!!x. ((x = y ==> False)) ==> x ~= y") 1);
by (dtac (real_sum_squares_cancel) 1);
by (Asm_full_simp_tac 1);
qed "real_sum_squares_not_zero";

Goal "y ~= 0 ==> x * x + y * y ~= (0::real)";
by (rtac (CLAIM "!!x. ((x = y ==> False)) ==> x ~= y") 1);
by (dtac (real_sum_squares_cancel2) 1);
by (Asm_full_simp_tac 1);
qed "real_sum_squares_not_zero2";

(* RealAbs *)

(* nice theorem *)
Goal "abs x * abs x = x * (x::real)";
by (cut_inst_tac [("R1.0","x"),("R2.0","0")] real_linear 1);
by (auto_tac (claset(),simpset() addsimps [abs_eqI2,abs_minus_eqI2]));
qed "abs_mult_abs";
Addsimps [abs_mult_abs];

(* RealPow *)
Goalw [real_divide_def]
    "(x/y) ^ n = ((x::real) ^ n/ y ^ n)";
by (auto_tac (claset(),simpset() addsimps [realpow_mult,
    realpow_inverse]));
qed "realpow_divide";

Goal "isCont (%x. x ^ n) x";
by (rtac (DERIV_pow RS DERIV_isCont) 1);
qed "isCont_realpow";
Addsimps [isCont_realpow];

Goal "(0::real) <= r --> 0 <= r ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [real_0_le_mult_iff]));
qed_spec_mp "realpow_ge_zero2";

Goal "(0::real) <= x & x <= y --> x ^ n <= y ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset() addSIs [real_mult_le_mono],
    simpset() addsimps [realpow_ge_zero2]));
qed_spec_mp "realpow_le2";

Goal "(1::real) < r ==> 1 < r ^ (Suc n)";
by (forw_inst_tac [("n","n")] realpow_ge_one 1);
by (dtac real_le_imp_less_or_eq 1 THEN Step_tac 1);
by (forward_tac [(real_zero_less_one RS real_less_trans)] 1);
by (dres_inst_tac [("y","r ^ n")] (real_mult_less_mono2) 1);
by (assume_tac 1);
by (auto_tac (claset() addDs [real_less_trans],simpset()));
qed "realpow_Suc_gt_one";

Goal "(x ^ 2 + y ^ 2 = (0::real)) = (x = 0 & y = 0)";
by (auto_tac (claset() addIs [real_sum_squares_cancel, real_sum_squares_cancel2], 
              simpset() addsimps [numeral_2_eq_2]));
qed "realpow_two_sum_zero_iff";
Addsimps [realpow_two_sum_zero_iff];

Goal "(0::real) <= u ^ 2 + v ^ 2";
by (rtac (real_le_add_order) 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "realpow_two_le_add_order";
Addsimps [realpow_two_le_add_order];

Goal "(0::real) <= u ^ 2 + v ^ 2 + w ^ 2";
by (REPEAT(rtac (real_le_add_order) 1));
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "realpow_two_le_add_order2";
Addsimps [realpow_two_le_add_order2];

Goal "(0::real) <= x*x + y*y";
by (cut_inst_tac [("u","x"),("v","y")] realpow_two_le_add_order 1);
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "real_mult_self_sum_ge_zero";
Addsimps [real_mult_self_sum_ge_zero];
Addsimps [real_mult_self_sum_ge_zero RS abs_eqI1];

Goal "x ~= 0 ==> (0::real) < x * x + y * y";
by (cut_inst_tac [("x","x"),("y","y")] real_mult_self_sum_ge_zero 1);
by (dtac real_le_imp_less_or_eq 1);
by (dres_inst_tac [("y","y")] real_sum_squares_not_zero 1);
by Auto_tac;
qed "real_sum_square_gt_zero";

Goal "y ~= 0 ==> (0::real) < x * x + y * y";
by (rtac (real_add_commute RS subst) 1);
by (etac real_sum_square_gt_zero 1);
qed "real_sum_square_gt_zero2";

Goal "-(u * u) <= (x * (x::real))";
by (res_inst_tac [("j","0")] real_le_trans 1);
by Auto_tac;
qed "real_minus_mult_self_le";
Addsimps [real_minus_mult_self_le];

Goal "-(u ^ 2) <= (x::real) ^ 2";
by (auto_tac (claset(), simpset() addsimps [numeral_2_eq_2])); 
qed "realpow_square_minus_le";
Addsimps [realpow_square_minus_le];

Goal "(m::real) ^ n = (if n=0 then 1 else m * m ^ (n - 1))";
by (case_tac "n" 1);
by Auto_tac;
qed "realpow_num_eq_if";

Goal "0 < (2::real) ^ (4*d)";
by (induct_tac "d" 1);
by (auto_tac (claset(),simpset() addsimps [realpow_num_eq_if]));
qed "real_num_zero_less_two_pow";
Addsimps [real_num_zero_less_two_pow];

Goal "x * (4::real)   < y ==> x * (2 ^ 8) < y * (2 ^ 6)";
by (subgoal_tac "(2::real) ^ 8 = 4 * (2 ^ 6)" 1);
by (asm_simp_tac (simpset() addsimps [real_mult_assoc RS sym]) 1);
by (auto_tac (claset(),simpset() addsimps [realpow_num_eq_if]));
qed "lemma_realpow_num_two_mono";

Goal "2 ^ 2 = (4::real)";
by (simp_tac (simpset() addsimps [realpow_num_eq_if]) 1);
val lemma_realpow_4 = result();
Addsimps [lemma_realpow_4];

Goal "2 ^ 4 = (16::real)";
by (simp_tac (simpset() addsimps [realpow_num_eq_if]) 1);
val lemma_realpow_16 = result();
Addsimps [lemma_realpow_16];

(* HyperOrd *)

Goal "[| (0::hypreal) < x; y < 0 |] ==> y*x < 0";
by (auto_tac (claset(),simpset() addsimps [hypreal_mult_commute,
    hypreal_mult_less_zero]));
qed "hypreal_mult_less_zero2";

(* HyperPow *)
Goal "(0::hypreal) <= x * x";
by (auto_tac (claset(),simpset() addsimps 
    [hypreal_0_le_mult_iff]));
qed "hypreal_mult_self_ge_zero";
Addsimps [hypreal_mult_self_ge_zero];

(* deleted from distribution but I prefer to have it *)
Goal "[|(0::hypreal) <= x; 0 <= y; x ^ Suc n = y ^ Suc n |] ==> x = y";
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (res_inst_tac [("z","y")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps 
    [hrealpow,hypreal_mult,hypreal_le,hypreal_zero_num]));
by (ultra_tac (claset() addIs [realpow_Suc_cancel_eq],
    simpset()) 1);
qed "hrealpow_Suc_cancel_eq";

(* NSA.ML: next two were there before? Not in distrib though *)

Goal "[| x + y : HInfinite; y: HFinite |] ==> x : HInfinite";
by (rtac ccontr 1);
by (dtac (HFinite_HInfinite_iff RS iffD2) 1);
by (auto_tac (claset() addDs [HFinite_add],simpset() 
    addsimps [HInfinite_HFinite_iff]));
qed "HInfinite_HFinite_add_cancel";

Goal "[| x : HInfinite; y : HFinite |] ==> x + y : HInfinite";
by (res_inst_tac [("y","-y")] HInfinite_HFinite_add_cancel 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_add_assoc,
    HFinite_minus_iff]));
qed "HInfinite_HFinite_add";

Goal "[| x : HInfinite; x <= y; 0 <= x |] ==> y : HInfinite";
by (auto_tac (claset() addIs [HFinite_bounded],simpset() 
    addsimps [HInfinite_HFinite_iff]));
qed "HInfinite_ge_HInfinite";

Goal "[| x : Infinitesimal; x ~= 0 |] ==> inverse x : HInfinite";
by (rtac ccontr 1 THEN dtac (HFinite_HInfinite_iff RS iffD2) 1);
by (auto_tac (claset() addDs [Infinitesimal_HFinite_mult2],simpset()));
qed "Infinitesimal_inverse_HInfinite";

Goal "n : HNatInfinite ==> inverse (hypreal_of_hypnat n) : Infinitesimal";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_of_hypnat,hypreal_inverse,
    HNatInfinite_FreeUltrafilterNat_iff,Infinitesimal_FreeUltrafilterNat_iff2]));
by (rtac bexI 1 THEN rtac lemma_hyprel_refl 2);
by Auto_tac;
by (dres_inst_tac [("x","m + 1")] spec 1);
by (Ultra_tac 1);
by (subgoal_tac "abs(inverse (real (Y x))) = inverse(real (Y x))" 1);
by (auto_tac (claset() addSIs [abs_eqI2],simpset()));
by (rtac real_inverse_less_swap 1);
by Auto_tac;
qed "HNatInfinite_inverse_Infinitesimal";
Addsimps [HNatInfinite_inverse_Infinitesimal];

Goal "n : HNatInfinite ==> inverse (hypreal_of_hypnat n) ~= 0";
by (auto_tac (claset() addSIs [hypreal_inverse_not_zero],simpset()));
qed "HNatInfinite_inverse_not_zero";
Addsimps [HNatInfinite_inverse_not_zero];

Goal "N : HNatInfinite \
\     ==> (*fNat* (%x. inverse (real x))) N : Infinitesimal";
by (res_inst_tac [("f1","inverse")]  (starfun_stafunNat_o2 RS subst) 1);
by (subgoal_tac "hypreal_of_hypnat N ~= 0" 1);
by (auto_tac (claset(),simpset() addsimps [starfunNat_real_of_nat]));
qed "starfunNat_inverse_real_of_nat_Infinitesimal";
Addsimps [starfunNat_inverse_real_of_nat_Infinitesimal];

Goal "[| x : HInfinite; y : HFinite - Infinitesimal |] \
\     ==> x * y : HInfinite";
by (rtac ccontr 1 THEN dtac (HFinite_HInfinite_iff RS iffD2) 1); 
by (ftac HFinite_Infinitesimal_not_zero 1);
by (dtac HFinite_not_Infinitesimal_inverse 1);
by (Step_tac 1 THEN dtac HFinite_mult 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_mult_assoc,
    HFinite_HInfinite_iff]));
qed "HInfinite_HFinite_not_Infinitesimal_mult";

Goal "[| x : HInfinite; y : HFinite - Infinitesimal |] \
\     ==> y * x : HInfinite";
by (auto_tac (claset(),simpset() addsimps [hypreal_mult_commute,
    HInfinite_HFinite_not_Infinitesimal_mult]));
qed "HInfinite_HFinite_not_Infinitesimal_mult2";

Goal "[| x : HInfinite; 0 < x; y : Reals |] ==> y < x";
by (auto_tac (claset() addSDs [bspec],simpset() addsimps 
    [HInfinite_def,hrabs_def,order_less_imp_le]));
qed "HInfinite_gt_SReal";

Goal "[| x : HInfinite; 0 < x |] ==> 1 < x";
by (auto_tac (claset() addIs [HInfinite_gt_SReal],simpset()));
qed "HInfinite_gt_zero_gt_one";

(* not added at proof?? *)
Addsimps [HInfinite_omega];

(* Add in HyperDef.ML? *)
Goalw [omega_def] "0 < omega";
by (auto_tac (claset(),simpset() addsimps [hypreal_less,hypreal_zero_num]));
qed "hypreal_omega_gt_zero";
Addsimps [hypreal_omega_gt_zero];

Goal "1 ~: HInfinite";
by (simp_tac (simpset() addsimps [HInfinite_HFinite_iff]) 1);
qed "not_HInfinite_one";
Addsimps [not_HInfinite_one];


(* RComplete.ML *)

Goal "0 < x ==> ALL y. EX (n::nat). y < real n * x";
by (Step_tac 1);
by (cut_inst_tac [("x","y*inverse(x)")] reals_Archimedean2 1);
by (Step_tac 1);
by (forw_inst_tac [("x","y * inverse x")] (real_mult_less_mono1) 1);
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc,real_of_nat_def]));
qed "reals_Archimedean3";


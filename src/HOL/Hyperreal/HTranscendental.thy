(*  Title       : HTranscendental.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2001 University of Edinburgh

Converted to Isar and polished by lcp
*)

header{*Nonstandard Extensions of Transcendental Functions*}

theory HTranscendental = Transcendental + IntFloor:

constdefs

  exphr :: "real => hypreal"
    --{*define exponential function using standard part *}
    "exphr x ==  st(sumhr (0, whn, %n. inverse(real (fact n)) * (x ^ n)))" 

  sinhr :: "real => hypreal"
    "sinhr x == st(sumhr (0, whn, %n. (if even(n) then 0 else
             ((-1) ^ ((n - 1) div 2))/(real (fact n))) * (x ^ n)))"
  
  coshr :: "real => hypreal"
    "coshr x == st(sumhr (0, whn, %n. (if even(n) then
            ((-1) ^ (n div 2))/(real (fact n)) else 0) * x ^ n))"


subsection{*Nonstandard Extension of Square Root Function*}

lemma STAR_sqrt_zero [simp]: "( *f* sqrt) 0 = 0"
by (simp add: starfun hypreal_zero_num)

lemma STAR_sqrt_one [simp]: "( *f* sqrt) 1 = 1"
by (simp add: starfun hypreal_one_num)

lemma hypreal_sqrt_pow2_iff: "(( *f* sqrt)(x) ^ 2 = x) = (0 \<le> x)"
apply (cases x)
apply (auto simp add: hypreal_le hypreal_zero_num starfun hrealpow 
                      real_sqrt_pow2_iff 
            simp del: hpowr_Suc realpow_Suc)
done

lemma hypreal_sqrt_gt_zero_pow2: "0 < x ==> ( *f* sqrt) (x) ^ 2 = x"
apply (cases x)
apply (auto intro: FreeUltrafilterNat_subset real_sqrt_gt_zero_pow2
            simp add: hypreal_less starfun hrealpow hypreal_zero_num 
            simp del: hpowr_Suc realpow_Suc)
done

lemma hypreal_sqrt_pow2_gt_zero: "0 < x ==> 0 < ( *f* sqrt) (x) ^ 2"
by (frule hypreal_sqrt_gt_zero_pow2, auto)

lemma hypreal_sqrt_not_zero: "0 < x ==> ( *f* sqrt) (x) \<noteq> 0"
apply (frule hypreal_sqrt_pow2_gt_zero)
apply (auto simp add: numeral_2_eq_2)
done

lemma hypreal_inverse_sqrt_pow2:
     "0 < x ==> inverse (( *f* sqrt)(x)) ^ 2 = inverse x"
apply (cut_tac n1 = 2 and a1 = "( *f* sqrt) x" in power_inverse [symmetric])
apply (auto dest: hypreal_sqrt_gt_zero_pow2)
done

lemma hypreal_sqrt_mult_distrib: 
    "[|0 < x; 0 <y |] ==> ( *f* sqrt)(x*y) =  ( *f* sqrt)(x) * ( *f* sqrt)(y)"
apply (cases x, cases y)
apply (simp add: hypreal_zero_def starfun hypreal_mult hypreal_less hypreal_zero_num, ultra)
apply (auto intro: real_sqrt_mult_distrib) 
done

lemma hypreal_sqrt_mult_distrib2:
     "[|0\<le>x; 0\<le>y |] ==>  
     ( *f* sqrt)(x*y) =  ( *f* sqrt)(x) * ( *f* sqrt)(y)"
by (auto intro: hypreal_sqrt_mult_distrib simp add: order_le_less)

lemma hypreal_sqrt_approx_zero [simp]:
     "0 < x ==> (( *f* sqrt)(x) @= 0) = (x @= 0)"
apply (auto simp add: mem_infmal_iff [symmetric])
apply (rule hypreal_sqrt_gt_zero_pow2 [THEN subst])
apply (auto intro: Infinitesimal_mult 
            dest!: hypreal_sqrt_gt_zero_pow2 [THEN ssubst] 
            simp add: numeral_2_eq_2)
done

lemma hypreal_sqrt_approx_zero2 [simp]:
     "0 \<le> x ==> (( *f* sqrt)(x) @= 0) = (x @= 0)"
by (auto simp add: order_le_less)

lemma hypreal_sqrt_sum_squares [simp]:
     "(( *f* sqrt)(x*x + y*y + z*z) @= 0) = (x*x + y*y + z*z @= 0)"
apply (rule hypreal_sqrt_approx_zero2)
apply (rule hypreal_le_add_order)+
apply (auto simp add: zero_le_square)
done

lemma hypreal_sqrt_sum_squares2 [simp]:
     "(( *f* sqrt)(x*x + y*y) @= 0) = (x*x + y*y @= 0)"
apply (rule hypreal_sqrt_approx_zero2)
apply (rule hypreal_le_add_order)
apply (auto simp add: zero_le_square)
done

lemma hypreal_sqrt_gt_zero: "0 < x ==> 0 < ( *f* sqrt)(x)"
apply (cases x)
apply (auto simp add: starfun hypreal_zero_def hypreal_less hypreal_zero_num, ultra)
apply (auto intro: real_sqrt_gt_zero)
done

lemma hypreal_sqrt_ge_zero: "0 \<le> x ==> 0 \<le> ( *f* sqrt)(x)"
by (auto intro: hypreal_sqrt_gt_zero simp add: order_le_less)

lemma hypreal_sqrt_hrabs [simp]: "( *f* sqrt)(x ^ 2) = abs(x)"
apply (cases x)
apply (simp add: starfun hypreal_hrabs hypreal_mult numeral_2_eq_2)
done

lemma hypreal_sqrt_hrabs2 [simp]: "( *f* sqrt)(x*x) = abs(x)"
apply (rule hrealpow_two [THEN subst])
apply (rule numeral_2_eq_2 [THEN subst])
apply (rule hypreal_sqrt_hrabs)
done

lemma hypreal_sqrt_hyperpow_hrabs [simp]:
     "( *f* sqrt)(x pow (hypnat_of_nat 2)) = abs(x)"
apply (cases x)
apply (simp add: starfun hypreal_hrabs hypnat_of_nat_eq hyperpow)
done

lemma star_sqrt_HFinite: "\<lbrakk>x \<in> HFinite; 0 \<le> x\<rbrakk> \<Longrightarrow> ( *f* sqrt) x \<in> HFinite"
apply (rule HFinite_square_iff [THEN iffD1])
apply (simp only: hypreal_sqrt_mult_distrib2 [symmetric], simp) 
done

lemma st_hypreal_sqrt:
     "[| x \<in> HFinite; 0 \<le> x |] ==> st(( *f* sqrt) x) = ( *f* sqrt)(st x)"
apply (rule power_inject_base [where n=1])
apply (auto intro!: st_zero_le hypreal_sqrt_ge_zero)
apply (rule st_mult [THEN subst])
apply (rule_tac [3] hypreal_sqrt_mult_distrib2 [THEN subst])
apply (rule_tac [5] hypreal_sqrt_mult_distrib2 [THEN subst])
apply (auto simp add: st_hrabs st_zero_le star_sqrt_HFinite)
done

lemma hypreal_sqrt_sum_squares_ge1 [simp]: "x \<le> ( *f* sqrt)(x ^ 2 + y ^ 2)"
apply (cases x, cases y)
apply (simp add: starfun hypreal_add hrealpow hypreal_le 
            del: hpowr_Suc realpow_Suc)
done

lemma HFinite_hypreal_sqrt:
     "[| 0 \<le> x; x \<in> HFinite |] ==> ( *f* sqrt) x \<in> HFinite"
apply (auto simp add: order_le_less)
apply (rule HFinite_square_iff [THEN iffD1])
apply (drule hypreal_sqrt_gt_zero_pow2)
apply (simp add: numeral_2_eq_2)
done

lemma HFinite_hypreal_sqrt_imp_HFinite:
     "[| 0 \<le> x; ( *f* sqrt) x \<in> HFinite |] ==> x \<in> HFinite"
apply (auto simp add: order_le_less)
apply (drule HFinite_square_iff [THEN iffD2])
apply (drule hypreal_sqrt_gt_zero_pow2)
apply (simp add: numeral_2_eq_2 del: HFinite_square_iff)
done

lemma HFinite_hypreal_sqrt_iff [simp]:
     "0 \<le> x ==> (( *f* sqrt) x \<in> HFinite) = (x \<in> HFinite)"
by (blast intro: HFinite_hypreal_sqrt HFinite_hypreal_sqrt_imp_HFinite)

lemma HFinite_sqrt_sum_squares [simp]:
     "(( *f* sqrt)(x*x + y*y) \<in> HFinite) = (x*x + y*y \<in> HFinite)"
apply (rule HFinite_hypreal_sqrt_iff)
apply (rule hypreal_le_add_order)
apply (auto simp add: zero_le_square)
done

lemma Infinitesimal_hypreal_sqrt:
     "[| 0 \<le> x; x \<in> Infinitesimal |] ==> ( *f* sqrt) x \<in> Infinitesimal"
apply (auto simp add: order_le_less)
apply (rule Infinitesimal_square_iff [THEN iffD2])
apply (drule hypreal_sqrt_gt_zero_pow2)
apply (simp add: numeral_2_eq_2)
done

lemma Infinitesimal_hypreal_sqrt_imp_Infinitesimal:
     "[| 0 \<le> x; ( *f* sqrt) x \<in> Infinitesimal |] ==> x \<in> Infinitesimal"
apply (auto simp add: order_le_less)
apply (drule Infinitesimal_square_iff [THEN iffD1])
apply (drule hypreal_sqrt_gt_zero_pow2)
apply (simp add: numeral_2_eq_2 del: Infinitesimal_square_iff [symmetric])
done

lemma Infinitesimal_hypreal_sqrt_iff [simp]:
     "0 \<le> x ==> (( *f* sqrt) x \<in> Infinitesimal) = (x \<in> Infinitesimal)"
by (blast intro: Infinitesimal_hypreal_sqrt_imp_Infinitesimal Infinitesimal_hypreal_sqrt)

lemma Infinitesimal_sqrt_sum_squares [simp]:
     "(( *f* sqrt)(x*x + y*y) \<in> Infinitesimal) = (x*x + y*y \<in> Infinitesimal)"
apply (rule Infinitesimal_hypreal_sqrt_iff)
apply (rule hypreal_le_add_order)
apply (auto simp add: zero_le_square)
done

lemma HInfinite_hypreal_sqrt:
     "[| 0 \<le> x; x \<in> HInfinite |] ==> ( *f* sqrt) x \<in> HInfinite"
apply (auto simp add: order_le_less)
apply (rule HInfinite_square_iff [THEN iffD1])
apply (drule hypreal_sqrt_gt_zero_pow2)
apply (simp add: numeral_2_eq_2)
done

lemma HInfinite_hypreal_sqrt_imp_HInfinite:
     "[| 0 \<le> x; ( *f* sqrt) x \<in> HInfinite |] ==> x \<in> HInfinite"
apply (auto simp add: order_le_less)
apply (drule HInfinite_square_iff [THEN iffD2])
apply (drule hypreal_sqrt_gt_zero_pow2)
apply (simp add: numeral_2_eq_2 del: HInfinite_square_iff)
done

lemma HInfinite_hypreal_sqrt_iff [simp]:
     "0 \<le> x ==> (( *f* sqrt) x \<in> HInfinite) = (x \<in> HInfinite)"
by (blast intro: HInfinite_hypreal_sqrt HInfinite_hypreal_sqrt_imp_HInfinite)

lemma HInfinite_sqrt_sum_squares [simp]:
     "(( *f* sqrt)(x*x + y*y) \<in> HInfinite) = (x*x + y*y \<in> HInfinite)"
apply (rule HInfinite_hypreal_sqrt_iff)
apply (rule hypreal_le_add_order)
apply (auto simp add: zero_le_square)
done

lemma HFinite_exp [simp]:
     "sumhr (0, whn, %n. inverse (real (fact n)) * x ^ n) \<in> HFinite"
by (auto intro!: NSBseq_HFinite_hypreal NSconvergent_NSBseq 
         simp add: starfunNat_sumr [symmetric] starfunNat hypnat_omega_def
                   convergent_NSconvergent_iff [symmetric] 
                   summable_convergent_sumr_iff [symmetric] summable_exp)

lemma exphr_zero [simp]: "exphr 0 = 1"
apply (simp add: exphr_def sumhr_split_add
                   [OF hypnat_one_less_hypnat_omega, symmetric]) 
apply (simp add: sumhr hypnat_zero_def starfunNat hypnat_one_def hypnat_add
                 hypnat_omega_def hypreal_add 
            del: hypnat_add_zero_left)
apply (simp add: hypreal_one_num [symmetric])
done

lemma coshr_zero [simp]: "coshr 0 = 1"
apply (simp add: coshr_def sumhr_split_add
                   [OF hypnat_one_less_hypnat_omega, symmetric]) 
apply (simp add: sumhr hypnat_zero_def starfunNat hypnat_one_def 
         hypnat_add hypnat_omega_def st_add [symmetric] 
         hypreal_one_def [symmetric] hypreal_zero_def [symmetric]
       del: hypnat_add_zero_left)
done

lemma STAR_exp_zero_approx_one [simp]: "( *f* exp) 0 @= 1"
by (simp add: hypreal_zero_def hypreal_one_def starfun hypreal_one_num)

lemma STAR_exp_Infinitesimal: "x \<in> Infinitesimal ==> ( *f* exp) x @= 1"
apply (case_tac "x = 0")
apply (cut_tac [2] x = 0 in DERIV_exp)
apply (auto simp add: NSDERIV_DERIV_iff [symmetric] nsderiv_def)
apply (drule_tac x = x in bspec, auto)
apply (drule_tac c = x in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD] 
            simp add: mult_assoc)
apply (rule approx_add_right_cancel [where d="-1"])
apply (rule approx_sym [THEN [2] approx_trans2])
apply (auto simp add: mem_infmal_iff)
done

lemma STAR_exp_epsilon [simp]: "( *f* exp) epsilon @= 1"
by (auto intro: STAR_exp_Infinitesimal)

lemma STAR_exp_add: "( *f* exp)(x + y) = ( *f* exp) x * ( *f* exp) y"
apply (cases x, cases y)
apply (simp add: starfun hypreal_add hypreal_mult exp_add)
done

lemma exphr_hypreal_of_real_exp_eq: "exphr x = hypreal_of_real (exp x)"
apply (simp add: exphr_def)
apply (rule st_hypreal_of_real [THEN subst])
apply (rule approx_st_eq, auto)
apply (rule approx_minus_iff [THEN iffD2])
apply (auto simp add: mem_infmal_iff [symmetric] hypreal_of_real_def hypnat_zero_def hypnat_omega_def sumhr hypreal_minus hypreal_add)
apply (rule NSLIMSEQ_zero_Infinitesimal_hypreal)
apply (insert exp_converges [of x]) 
apply (simp add: sums_def) 
apply (drule LIMSEQ_const [THEN [2] LIMSEQ_add, where b = "- exp x"])
apply (simp add: LIMSEQ_NSLIMSEQ_iff)
done

lemma starfun_exp_ge_add_one_self [simp]: "0 \<le> x ==> (1 + x) \<le> ( *f* exp) x"
apply (cases x)
apply (simp add: starfun hypreal_add hypreal_le hypreal_zero_num hypreal_one_num, ultra)
done

(* exp (oo) is infinite *)
lemma starfun_exp_HInfinite:
     "[| x \<in> HInfinite; 0 \<le> x |] ==> ( *f* exp) x \<in> HInfinite"
apply (frule starfun_exp_ge_add_one_self)
apply (rule HInfinite_ge_HInfinite, assumption)
apply (rule order_trans [of _ "1+x"], auto) 
done

lemma starfun_exp_minus: "( *f* exp) (-x) = inverse(( *f* exp) x)"
apply (cases x)
apply (simp add: starfun hypreal_inverse hypreal_minus exp_minus)
done

(* exp (-oo) is infinitesimal *)
lemma starfun_exp_Infinitesimal:
     "[| x \<in> HInfinite; x \<le> 0 |] ==> ( *f* exp) x \<in> Infinitesimal"
apply (subgoal_tac "\<exists>y. x = - y")
apply (rule_tac [2] x = "- x" in exI)
apply (auto intro!: HInfinite_inverse_Infinitesimal starfun_exp_HInfinite
            simp add: starfun_exp_minus HInfinite_minus_iff)
done

lemma starfun_exp_gt_one [simp]: "0 < x ==> 1 < ( *f* exp) x"
apply (cases x)
apply (simp add: starfun hypreal_one_num hypreal_zero_num hypreal_less, ultra)
done

(* needs derivative of inverse function
   TRY a NS one today!!!

Goal "x @= 1 ==> ( *f* ln) x @= 1"
by (res_inst_tac [("z","x")] eq_Abs_hypreal 1);
by (auto_tac (claset(),simpset() addsimps [hypreal_one_def]));


Goalw [nsderiv_def] "0r < x ==> NSDERIV ln x :> inverse x";

*)


lemma starfun_ln_exp [simp]: "( *f* ln) (( *f* exp) x) = x"
apply (cases x)
apply (simp add: starfun)
done

lemma starfun_exp_ln_iff [simp]: "(( *f* exp)(( *f* ln) x) = x) = (0 < x)"
apply (cases x)
apply (simp add: starfun hypreal_zero_num hypreal_less)
done

lemma starfun_exp_ln_eq: "( *f* exp) u = x ==> ( *f* ln) x = u"
by (auto simp add: starfun)

lemma starfun_ln_less_self [simp]: "0 < x ==> ( *f* ln) x < x"
apply (cases x)
apply (simp add: starfun hypreal_zero_num hypreal_less, ultra)
done

lemma starfun_ln_ge_zero [simp]: "1 \<le> x ==> 0 \<le> ( *f* ln) x"
apply (cases x)
apply (simp add: starfun hypreal_zero_num hypreal_le hypreal_one_num, ultra)
done

lemma starfun_ln_gt_zero [simp]: "1 < x ==> 0 < ( *f* ln) x"
apply (cases x)
apply (simp add: starfun hypreal_zero_num hypreal_less hypreal_one_num, ultra)
done

lemma starfun_ln_not_eq_zero [simp]: "[| 0 < x; x \<noteq> 1 |] ==> ( *f* ln) x \<noteq> 0"
apply (cases x)
apply (auto simp add: starfun hypreal_zero_num hypreal_less hypreal_one_num, ultra)
apply (auto dest: ln_not_eq_zero) 
done

lemma starfun_ln_HFinite: "[| x \<in> HFinite; 1 \<le> x |] ==> ( *f* ln) x \<in> HFinite"
apply (rule HFinite_bounded)
apply (rule_tac [2] order_less_imp_le)
apply (rule_tac [2] starfun_ln_less_self)
apply (rule_tac [2] order_less_le_trans, auto)
done

lemma starfun_ln_inverse: "0 < x ==> ( *f* ln) (inverse x) = -( *f* ln) x"
apply (cases x)
apply (simp add: starfun hypreal_zero_num hypreal_minus hypreal_inverse hypreal_less, ultra)
apply (simp add: ln_inverse)
done

lemma starfun_exp_HFinite: "x \<in> HFinite ==> ( *f* exp) x \<in> HFinite"
apply (cases x)
apply (auto simp add: starfun HFinite_FreeUltrafilterNat_iff)
apply (rule bexI, rule_tac [2] lemma_hyprel_refl, auto)
apply (rule_tac x = "exp u" in exI)
apply (ultra, arith)
done

lemma starfun_exp_add_HFinite_Infinitesimal_approx:
     "[|x \<in> Infinitesimal; z \<in> HFinite |] ==> ( *f* exp) (z + x) @= ( *f* exp) z"
apply (simp add: STAR_exp_add)
apply (frule STAR_exp_Infinitesimal)
apply (drule approx_mult2)
apply (auto intro: starfun_exp_HFinite)
done

(* using previous result to get to result *)
lemma starfun_ln_HInfinite:
     "[| x \<in> HInfinite; 0 < x |] ==> ( *f* ln) x \<in> HInfinite"
apply (rule ccontr, drule HFinite_HInfinite_iff [THEN iffD2])
apply (drule starfun_exp_HFinite)
apply (simp add: starfun_exp_ln_iff [THEN iffD2] HFinite_HInfinite_iff)
done

lemma starfun_exp_HInfinite_Infinitesimal_disj:
 "x \<in> HInfinite ==> ( *f* exp) x \<in> HInfinite | ( *f* exp) x \<in> Infinitesimal"
apply (insert linorder_linear [of x 0]) 
apply (auto intro: starfun_exp_HInfinite starfun_exp_Infinitesimal)
done

(* check out this proof!!! *)
lemma starfun_ln_HFinite_not_Infinitesimal:
     "[| x \<in> HFinite - Infinitesimal; 0 < x |] ==> ( *f* ln) x \<in> HFinite"
apply (rule ccontr, drule HInfinite_HFinite_iff [THEN iffD2])
apply (drule starfun_exp_HInfinite_Infinitesimal_disj)
apply (simp add: starfun_exp_ln_iff [symmetric] HInfinite_HFinite_iff
            del: starfun_exp_ln_iff)
done

(* we do proof by considering ln of 1/x *)
lemma starfun_ln_Infinitesimal_HInfinite:
     "[| x \<in> Infinitesimal; 0 < x |] ==> ( *f* ln) x \<in> HInfinite"
apply (drule Infinitesimal_inverse_HInfinite)
apply (frule positive_imp_inverse_positive)
apply (drule_tac [2] starfun_ln_HInfinite)
apply (auto simp add: starfun_ln_inverse HInfinite_minus_iff)
done

lemma starfun_ln_less_zero: "[| 0 < x; x < 1 |] ==> ( *f* ln) x < 0"
apply (cases x)
apply (simp add: hypreal_zero_num hypreal_one_num hypreal_less starfun, ultra)
apply (auto intro: ln_less_zero) 
done

lemma starfun_ln_Infinitesimal_less_zero:
     "[| x \<in> Infinitesimal; 0 < x |] ==> ( *f* ln) x < 0"
apply (auto intro!: starfun_ln_less_zero simp add: Infinitesimal_def)
apply (drule bspec [where x = 1])
apply (auto simp add: abs_if)
done

lemma starfun_ln_HInfinite_gt_zero:
     "[| x \<in> HInfinite; 0 < x |] ==> 0 < ( *f* ln) x"
apply (auto intro!: starfun_ln_gt_zero simp add: HInfinite_def)
apply (drule bspec [where x = 1])
apply (auto simp add: abs_if)
done

(*
Goalw [NSLIM_def] "(%h. ((x powr h) - 1) / h) -- 0 --NS> ln x"
*)

lemma HFinite_sin [simp]:
     "sumhr (0, whn, %n. (if even(n) then 0 else  
              ((- 1) ^ ((n - 1) div 2))/(real (fact n))) * x ^ n)  
              \<in> HFinite"
apply (auto intro!: NSBseq_HFinite_hypreal NSconvergent_NSBseq 
            simp add: starfunNat_sumr [symmetric] starfunNat hypnat_omega_def
                      convergent_NSconvergent_iff [symmetric] 
                      summable_convergent_sumr_iff [symmetric])
apply (simp only: One_nat_def summable_sin)
done

lemma STAR_sin_zero [simp]: "( *f* sin) 0 = 0"
by (simp add: starfun hypreal_zero_num)

lemma STAR_sin_Infinitesimal [simp]: "x \<in> Infinitesimal ==> ( *f* sin) x @= x"
apply (case_tac "x = 0")
apply (cut_tac [2] x = 0 in DERIV_sin)
apply (auto simp add: NSDERIV_DERIV_iff [symmetric] nsderiv_def hypreal_of_real_zero)
apply (drule bspec [where x = x], auto)
apply (drule approx_mult1 [where c = x])
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
           simp add: mult_assoc)
done

lemma HFinite_cos [simp]:
     "sumhr (0, whn, %n. (if even(n) then  
            ((- 1) ^ (n div 2))/(real (fact n)) else  
            0) * x ^ n) \<in> HFinite"
by (auto intro!: NSBseq_HFinite_hypreal NSconvergent_NSBseq 
         simp add: starfunNat_sumr [symmetric] starfunNat hypnat_omega_def
                   convergent_NSconvergent_iff [symmetric] 
                   summable_convergent_sumr_iff [symmetric] summable_cos)

lemma STAR_cos_zero [simp]: "( *f* cos) 0 = 1"
by (simp add: starfun hypreal_zero_num hypreal_one_num)

lemma STAR_cos_Infinitesimal [simp]: "x \<in> Infinitesimal ==> ( *f* cos) x @= 1"
apply (case_tac "x = 0")
apply (cut_tac [2] x = 0 in DERIV_cos)
apply (auto simp add: NSDERIV_DERIV_iff [symmetric] nsderiv_def hypreal_of_real_zero)
apply (drule bspec [where x = x])
apply (auto simp add: hypreal_of_real_zero hypreal_of_real_one)
apply (drule approx_mult1 [where c = x])
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc hypreal_of_real_one)
apply (rule approx_add_right_cancel [where d = "-1"], auto)
done

lemma STAR_tan_zero [simp]: "( *f* tan) 0 = 0"
by (simp add: starfun hypreal_zero_num)

lemma STAR_tan_Infinitesimal: "x \<in> Infinitesimal ==> ( *f* tan) x @= x"
apply (case_tac "x = 0")
apply (cut_tac [2] x = 0 in DERIV_tan)
apply (auto simp add: NSDERIV_DERIV_iff [symmetric] nsderiv_def hypreal_of_real_zero)
apply (drule bspec [where x = x], auto)
apply (drule approx_mult1 [where c = x])
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
             simp add: mult_assoc)
done

lemma STAR_sin_cos_Infinitesimal_mult:
     "x \<in> Infinitesimal ==> ( *f* sin) x * ( *f* cos) x @= x"
apply (insert approx_mult_HFinite [of "( *f* sin) x" _ "( *f* cos) x" 1]) 
apply (simp add: Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma HFinite_pi: "hypreal_of_real pi \<in> HFinite"
by simp

(* lemmas *)

lemma lemma_split_hypreal_of_real:
     "N \<in> HNatInfinite  
      ==> hypreal_of_real a =  
          hypreal_of_hypnat N * (inverse(hypreal_of_hypnat N) * hypreal_of_real a)"
by (simp add: mult_assoc [symmetric] HNatInfinite_not_eq_zero)

lemma STAR_sin_Infinitesimal_divide:
     "[|x \<in> Infinitesimal; x \<noteq> 0 |] ==> ( *f* sin) x/x @= 1"
apply (cut_tac x = 0 in DERIV_sin)
apply (simp add: NSDERIV_DERIV_iff [symmetric] nsderiv_def hypreal_of_real_zero hypreal_of_real_one)
done

(*------------------------------------------------------------------------*) 
(* sin* (1/n) * 1/(1/n) @= 1 for n = oo                                   *)
(*------------------------------------------------------------------------*)

lemma lemma_sin_pi:
     "n \<in> HNatInfinite  
      ==> ( *f* sin) (inverse (hypreal_of_hypnat n))/(inverse (hypreal_of_hypnat n)) @= 1"
apply (rule STAR_sin_Infinitesimal_divide)
apply (auto simp add: HNatInfinite_not_eq_zero)
done

lemma STAR_sin_inverse_HNatInfinite:
     "n \<in> HNatInfinite  
      ==> ( *f* sin) (inverse (hypreal_of_hypnat n)) * hypreal_of_hypnat n @= 1"
apply (frule lemma_sin_pi)
apply (simp add: divide_inverse)
done

lemma Infinitesimal_pi_divide_HNatInfinite: 
     "N \<in> HNatInfinite  
      ==> hypreal_of_real pi/(hypreal_of_hypnat N) \<in> Infinitesimal"
apply (simp add: divide_inverse)
apply (auto intro: Infinitesimal_HFinite_mult2)
done

lemma pi_divide_HNatInfinite_not_zero [simp]:
     "N \<in> HNatInfinite ==> hypreal_of_real pi/(hypreal_of_hypnat N) \<noteq> 0"
by (simp add: HNatInfinite_not_eq_zero)

lemma STAR_sin_pi_divide_HNatInfinite_approx_pi:
     "n \<in> HNatInfinite  
      ==> ( *f* sin) (hypreal_of_real pi/(hypreal_of_hypnat n)) * hypreal_of_hypnat n  
          @= hypreal_of_real pi"
apply (frule STAR_sin_Infinitesimal_divide
               [OF Infinitesimal_pi_divide_HNatInfinite 
                   pi_divide_HNatInfinite_not_zero])
apply (auto simp add: inverse_mult_distrib)
apply (rule approx_SReal_mult_cancel [of "inverse (hypreal_of_real pi)"])
apply (auto intro: SReal_inverse simp add: divide_inverse mult_ac)
done

lemma STAR_sin_pi_divide_HNatInfinite_approx_pi2:
     "n \<in> HNatInfinite  
      ==> hypreal_of_hypnat n *  
          ( *f* sin) (hypreal_of_real pi/(hypreal_of_hypnat n))  
          @= hypreal_of_real pi"
apply (rule mult_commute [THEN subst])
apply (erule STAR_sin_pi_divide_HNatInfinite_approx_pi)
done

lemma starfunNat_pi_divide_n_Infinitesimal: 
     "N \<in> HNatInfinite ==> ( *fNat* (%x. pi / real x)) N \<in> Infinitesimal"
by (auto intro!: Infinitesimal_HFinite_mult2 
         simp add: starfunNat_mult [symmetric] divide_inverse
                   starfunNat_inverse [symmetric] starfunNat_real_of_nat)

lemma STAR_sin_pi_divide_n_approx:
     "N \<in> HNatInfinite ==>  
      ( *f* sin) (( *fNat* (%x. pi / real x)) N) @=  
      hypreal_of_real pi/(hypreal_of_hypnat N)"
by (auto intro!: STAR_sin_Infinitesimal Infinitesimal_HFinite_mult2 
         simp add: starfunNat_mult [symmetric] divide_inverse
                   starfunNat_inverse_real_of_nat_eq)

lemma NSLIMSEQ_sin_pi: "(%n. real n * sin (pi / real n)) ----NS> pi"
apply (auto simp add: NSLIMSEQ_def starfunNat_mult [symmetric] starfunNat_real_of_nat)
apply (rule_tac f1 = sin in starfun_stafunNat_o2 [THEN subst])
apply (auto simp add: starfunNat_mult [symmetric] starfunNat_real_of_nat divide_inverse)
apply (rule_tac f1 = inverse in starfun_stafunNat_o2 [THEN subst])
apply (auto dest: STAR_sin_pi_divide_HNatInfinite_approx_pi 
            simp add: starfunNat_real_of_nat mult_commute divide_inverse)
done

lemma NSLIMSEQ_cos_one: "(%n. cos (pi / real n))----NS> 1"
apply (simp add: NSLIMSEQ_def, auto)
apply (rule_tac f1 = cos in starfun_stafunNat_o2 [THEN subst])
apply (rule STAR_cos_Infinitesimal)
apply (auto intro!: Infinitesimal_HFinite_mult2 
            simp add: starfunNat_mult [symmetric] divide_inverse
                      starfunNat_inverse [symmetric] starfunNat_real_of_nat)
done

lemma NSLIMSEQ_sin_cos_pi:
     "(%n. real n * sin (pi / real n) * cos (pi / real n)) ----NS> pi"
by (insert NSLIMSEQ_mult [OF NSLIMSEQ_sin_pi NSLIMSEQ_cos_one], simp)


text{*A familiar approximation to @{term "cos x"} when @{term x} is small*}

lemma STAR_cos_Infinitesimal_approx:
     "x \<in> Infinitesimal ==> ( *f* cos) x @= 1 - x ^ 2"
apply (rule STAR_cos_Infinitesimal [THEN approx_trans])
apply (auto simp add: Infinitesimal_approx_minus [symmetric] 
            diff_minus add_assoc [symmetric] numeral_2_eq_2)
done

lemma STAR_cos_Infinitesimal_approx2:
     "x \<in> Infinitesimal ==> ( *f* cos) x @= 1 - (x ^ 2)/2"
apply (rule STAR_cos_Infinitesimal [THEN approx_trans])
apply (auto intro: Infinitesimal_SReal_divide 
            simp add: Infinitesimal_approx_minus [symmetric] numeral_2_eq_2)
done

ML
{*
val STAR_sqrt_zero = thm "STAR_sqrt_zero";
val STAR_sqrt_one = thm "STAR_sqrt_one";
val hypreal_sqrt_pow2_iff = thm "hypreal_sqrt_pow2_iff";
val hypreal_sqrt_gt_zero_pow2 = thm "hypreal_sqrt_gt_zero_pow2";
val hypreal_sqrt_pow2_gt_zero = thm "hypreal_sqrt_pow2_gt_zero";
val hypreal_sqrt_not_zero = thm "hypreal_sqrt_not_zero";
val hypreal_inverse_sqrt_pow2 = thm "hypreal_inverse_sqrt_pow2";
val hypreal_sqrt_mult_distrib = thm "hypreal_sqrt_mult_distrib";
val hypreal_sqrt_mult_distrib2 = thm "hypreal_sqrt_mult_distrib2";
val hypreal_sqrt_approx_zero = thm "hypreal_sqrt_approx_zero";
val hypreal_sqrt_approx_zero2 = thm "hypreal_sqrt_approx_zero2";
val hypreal_sqrt_sum_squares = thm "hypreal_sqrt_sum_squares";
val hypreal_sqrt_sum_squares2 = thm "hypreal_sqrt_sum_squares2";
val hypreal_sqrt_gt_zero = thm "hypreal_sqrt_gt_zero";
val hypreal_sqrt_ge_zero = thm "hypreal_sqrt_ge_zero";
val hypreal_sqrt_hrabs = thm "hypreal_sqrt_hrabs";
val hypreal_sqrt_hrabs2 = thm "hypreal_sqrt_hrabs2";
val hypreal_sqrt_hyperpow_hrabs = thm "hypreal_sqrt_hyperpow_hrabs";
val star_sqrt_HFinite = thm "star_sqrt_HFinite";
val st_hypreal_sqrt = thm "st_hypreal_sqrt";
val hypreal_sqrt_sum_squares_ge1 = thm "hypreal_sqrt_sum_squares_ge1";
val HFinite_hypreal_sqrt = thm "HFinite_hypreal_sqrt";
val HFinite_hypreal_sqrt_imp_HFinite = thm "HFinite_hypreal_sqrt_imp_HFinite";
val HFinite_hypreal_sqrt_iff = thm "HFinite_hypreal_sqrt_iff";
val HFinite_sqrt_sum_squares = thm "HFinite_sqrt_sum_squares";
val Infinitesimal_hypreal_sqrt = thm "Infinitesimal_hypreal_sqrt";
val Infinitesimal_hypreal_sqrt_imp_Infinitesimal = thm "Infinitesimal_hypreal_sqrt_imp_Infinitesimal";
val Infinitesimal_hypreal_sqrt_iff = thm "Infinitesimal_hypreal_sqrt_iff";
val Infinitesimal_sqrt_sum_squares = thm "Infinitesimal_sqrt_sum_squares";
val HInfinite_hypreal_sqrt = thm "HInfinite_hypreal_sqrt";
val HInfinite_hypreal_sqrt_imp_HInfinite = thm "HInfinite_hypreal_sqrt_imp_HInfinite";
val HInfinite_hypreal_sqrt_iff = thm "HInfinite_hypreal_sqrt_iff";
val HInfinite_sqrt_sum_squares = thm "HInfinite_sqrt_sum_squares";
val HFinite_exp = thm "HFinite_exp";
val exphr_zero = thm "exphr_zero";
val coshr_zero = thm "coshr_zero";
val STAR_exp_zero_approx_one = thm "STAR_exp_zero_approx_one";
val STAR_exp_Infinitesimal = thm "STAR_exp_Infinitesimal";
val STAR_exp_epsilon = thm "STAR_exp_epsilon";
val STAR_exp_add = thm "STAR_exp_add";
val exphr_hypreal_of_real_exp_eq = thm "exphr_hypreal_of_real_exp_eq";
val starfun_exp_ge_add_one_self = thm "starfun_exp_ge_add_one_self";
val starfun_exp_HInfinite = thm "starfun_exp_HInfinite";
val starfun_exp_minus = thm "starfun_exp_minus";
val starfun_exp_Infinitesimal = thm "starfun_exp_Infinitesimal";
val starfun_exp_gt_one = thm "starfun_exp_gt_one";
val starfun_ln_exp = thm "starfun_ln_exp";
val starfun_exp_ln_iff = thm "starfun_exp_ln_iff";
val starfun_exp_ln_eq = thm "starfun_exp_ln_eq";
val starfun_ln_less_self = thm "starfun_ln_less_self";
val starfun_ln_ge_zero = thm "starfun_ln_ge_zero";
val starfun_ln_gt_zero = thm "starfun_ln_gt_zero";
val starfun_ln_not_eq_zero = thm "starfun_ln_not_eq_zero";
val starfun_ln_HFinite = thm "starfun_ln_HFinite";
val starfun_ln_inverse = thm "starfun_ln_inverse";
val starfun_exp_HFinite = thm "starfun_exp_HFinite";
val starfun_exp_add_HFinite_Infinitesimal_approx = thm "starfun_exp_add_HFinite_Infinitesimal_approx";
val starfun_ln_HInfinite = thm "starfun_ln_HInfinite";
val starfun_exp_HInfinite_Infinitesimal_disj = thm "starfun_exp_HInfinite_Infinitesimal_disj";
val starfun_ln_HFinite_not_Infinitesimal = thm "starfun_ln_HFinite_not_Infinitesimal";
val starfun_ln_Infinitesimal_HInfinite = thm "starfun_ln_Infinitesimal_HInfinite";
val starfun_ln_less_zero = thm "starfun_ln_less_zero";
val starfun_ln_Infinitesimal_less_zero = thm "starfun_ln_Infinitesimal_less_zero";
val starfun_ln_HInfinite_gt_zero = thm "starfun_ln_HInfinite_gt_zero";
val HFinite_sin = thm "HFinite_sin";
val STAR_sin_zero = thm "STAR_sin_zero";
val STAR_sin_Infinitesimal = thm "STAR_sin_Infinitesimal";
val HFinite_cos = thm "HFinite_cos";
val STAR_cos_zero = thm "STAR_cos_zero";
val STAR_cos_Infinitesimal = thm "STAR_cos_Infinitesimal";
val STAR_tan_zero = thm "STAR_tan_zero";
val STAR_tan_Infinitesimal = thm "STAR_tan_Infinitesimal";
val STAR_sin_cos_Infinitesimal_mult = thm "STAR_sin_cos_Infinitesimal_mult";
val HFinite_pi = thm "HFinite_pi";
val lemma_split_hypreal_of_real = thm "lemma_split_hypreal_of_real";
val STAR_sin_Infinitesimal_divide = thm "STAR_sin_Infinitesimal_divide";
val lemma_sin_pi = thm "lemma_sin_pi";
val STAR_sin_inverse_HNatInfinite = thm "STAR_sin_inverse_HNatInfinite";
val Infinitesimal_pi_divide_HNatInfinite = thm "Infinitesimal_pi_divide_HNatInfinite";
val pi_divide_HNatInfinite_not_zero = thm "pi_divide_HNatInfinite_not_zero";
val STAR_sin_pi_divide_HNatInfinite_approx_pi = thm "STAR_sin_pi_divide_HNatInfinite_approx_pi";
val STAR_sin_pi_divide_HNatInfinite_approx_pi2 = thm "STAR_sin_pi_divide_HNatInfinite_approx_pi2";
val starfunNat_pi_divide_n_Infinitesimal = thm "starfunNat_pi_divide_n_Infinitesimal";
val STAR_sin_pi_divide_n_approx = thm "STAR_sin_pi_divide_n_approx";
val NSLIMSEQ_sin_pi = thm "NSLIMSEQ_sin_pi";
val NSLIMSEQ_cos_one = thm "NSLIMSEQ_cos_one";
val NSLIMSEQ_sin_cos_pi = thm "NSLIMSEQ_sin_cos_pi";
val STAR_cos_Infinitesimal_approx = thm "STAR_cos_Infinitesimal_approx";
val STAR_cos_Infinitesimal_approx2 = thm "STAR_cos_Infinitesimal_approx2";
*}


end

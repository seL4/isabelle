(*  Title:      HOL/Nonstandard_Analysis/HTranscendental.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2001 University of Edinburgh

Converted to Isar and polished by lcp
*)

section\<open>Nonstandard Extensions of Transcendental Functions\<close>

theory HTranscendental
imports Complex_Main HSeries HDeriv
begin

definition
  exphr :: "real \<Rightarrow> hypreal" where
    \<comment> \<open>define exponential function using standard part\<close>
  "exphr x \<equiv>  st(sumhr (0, whn, \<lambda>n. inverse (fact n) * (x ^ n)))"

definition
  sinhr :: "real \<Rightarrow> hypreal" where
  "sinhr x \<equiv> st(sumhr (0, whn, \<lambda>n. sin_coeff n * x ^ n))"
  
definition
  coshr :: "real \<Rightarrow> hypreal" where
  "coshr x \<equiv> st(sumhr (0, whn, \<lambda>n. cos_coeff n * x ^ n))"


subsection\<open>Nonstandard Extension of Square Root Function\<close>

lemma STAR_sqrt_zero [simp]: "( *f* sqrt) 0 = 0"
  by (simp add: starfun star_n_zero_num)

lemma STAR_sqrt_one [simp]: "( *f* sqrt) 1 = 1"
  by (simp add: starfun star_n_one_num)

lemma hypreal_sqrt_pow2_iff: "(( *f* sqrt)(x) ^ 2 = x) = (0 \<le> x)"
proof (cases x)
  case (star_n X)
  then show ?thesis
    by (simp add: star_n_le star_n_zero_num starfun hrealpow star_n_eq_iff del: hpowr_Suc power_Suc)
qed

lemma hypreal_sqrt_gt_zero_pow2: "\<And>x. 0 < x \<Longrightarrow> ( *f* sqrt) (x) ^ 2 = x"
  by transfer simp

lemma hypreal_sqrt_pow2_gt_zero: "0 < x \<Longrightarrow> 0 < ( *f* sqrt) (x) ^ 2"
  by (frule hypreal_sqrt_gt_zero_pow2, auto)

lemma hypreal_sqrt_not_zero: "0 < x \<Longrightarrow> ( *f* sqrt) (x) \<noteq> 0"
  using hypreal_sqrt_gt_zero_pow2 by fastforce

lemma hypreal_inverse_sqrt_pow2:
     "0 < x \<Longrightarrow> inverse (( *f* sqrt)(x)) ^ 2 = inverse x"
  by (simp add: hypreal_sqrt_gt_zero_pow2 power_inverse)

lemma hypreal_sqrt_mult_distrib: 
    "\<And>x y. \<lbrakk>0 < x; 0 <y\<rbrakk> \<Longrightarrow>
      ( *f* sqrt)(x*y) = ( *f* sqrt)(x) * ( *f* sqrt)(y)"
  by transfer (auto intro: real_sqrt_mult) 

lemma hypreal_sqrt_mult_distrib2:
     "\<lbrakk>0\<le>x; 0\<le>y\<rbrakk> \<Longrightarrow>  ( *f* sqrt)(x*y) = ( *f* sqrt)(x) * ( *f* sqrt)(y)"
by (auto intro: hypreal_sqrt_mult_distrib simp add: order_le_less)

lemma hypreal_sqrt_approx_zero [simp]:
  assumes "0 < x"
  shows "(( *f* sqrt) x \<approx> 0) \<longleftrightarrow> (x \<approx> 0)"
proof -
  have "( *f* sqrt) x \<in> Infinitesimal \<longleftrightarrow> ((*f* sqrt) x)\<^sup>2 \<in> Infinitesimal"
    by (metis Infinitesimal_hrealpow pos2 power2_eq_square Infinitesimal_square_iff)
  also have "... \<longleftrightarrow> x \<in> Infinitesimal"
    by (simp add: assms hypreal_sqrt_gt_zero_pow2)
  finally show ?thesis
    using mem_infmal_iff by blast
qed

lemma hypreal_sqrt_approx_zero2 [simp]:
  "0 \<le> x \<Longrightarrow> (( *f* sqrt)(x) \<approx> 0) = (x \<approx> 0)"
  by (auto simp add: order_le_less)

lemma hypreal_sqrt_gt_zero: "\<And>x. 0 < x \<Longrightarrow> 0 < ( *f* sqrt)(x)"
  by transfer (simp add: real_sqrt_gt_zero)

lemma hypreal_sqrt_ge_zero: "0 \<le> x \<Longrightarrow> 0 \<le> ( *f* sqrt)(x)"
  by (auto intro: hypreal_sqrt_gt_zero simp add: order_le_less)

lemma hypreal_sqrt_lessI:
  "\<And>x u. \<lbrakk>0 < u; x < u\<^sup>2\<rbrakk> \<Longrightarrow> ( *f* sqrt) x < u"
proof transfer
  show "\<And>x u. \<lbrakk>0 < u; x < u\<^sup>2\<rbrakk> \<Longrightarrow> sqrt x < u"
  by (metis less_le real_sqrt_less_iff real_sqrt_pow2 real_sqrt_power) 
qed
 
lemma hypreal_sqrt_hrabs [simp]: "\<And>x. ( *f* sqrt)(x\<^sup>2) = \<bar>x\<bar>"
  by transfer simp

lemma hypreal_sqrt_hrabs2 [simp]: "\<And>x. ( *f* sqrt)(x*x) = \<bar>x\<bar>"
  by transfer simp

lemma hypreal_sqrt_hyperpow_hrabs [simp]:
  "\<And>x. ( *f* sqrt)(x pow (hypnat_of_nat 2)) = \<bar>x\<bar>"
  by transfer simp

lemma star_sqrt_HFinite: "\<lbrakk>x \<in> HFinite; 0 \<le> x\<rbrakk> \<Longrightarrow> ( *f* sqrt) x \<in> HFinite"
  by (metis HFinite_square_iff hypreal_sqrt_pow2_iff power2_eq_square)

lemma st_hypreal_sqrt:
  assumes "x \<in> HFinite" "0 \<le> x"
  shows "st(( *f* sqrt) x) = ( *f* sqrt)(st x)"
proof (rule power_inject_base)
  show "st ((*f* sqrt) x) ^ Suc 1 = (*f* sqrt) (st x) ^ Suc 1"
    using assms hypreal_sqrt_pow2_iff [of x]
    by (metis HFinite_square_iff hypreal_sqrt_hrabs2 power2_eq_square st_hrabs st_mult)
  show "0 \<le> st ((*f* sqrt) x)"
    by (simp add: assms hypreal_sqrt_ge_zero st_zero_le star_sqrt_HFinite)
  show "0 \<le> (*f* sqrt) (st x)"
    by (simp add: assms hypreal_sqrt_ge_zero st_zero_le)
qed

lemma hypreal_sqrt_sum_squares_ge1 [simp]: "\<And>x y. x \<le> ( *f* sqrt)(x\<^sup>2 + y\<^sup>2)"
  by transfer (rule real_sqrt_sum_squares_ge1)

lemma HFinite_hypreal_sqrt_imp_HFinite:
  "\<lbrakk>0 \<le> x; ( *f* sqrt) x \<in> HFinite\<rbrakk> \<Longrightarrow> x \<in> HFinite"
  by (metis HFinite_mult hrealpow_two hypreal_sqrt_pow2_iff numeral_2_eq_2)

lemma HFinite_hypreal_sqrt_iff [simp]:
  "0 \<le> x \<Longrightarrow> (( *f* sqrt) x \<in> HFinite) = (x \<in> HFinite)"
  by (blast intro: star_sqrt_HFinite HFinite_hypreal_sqrt_imp_HFinite)

lemma Infinitesimal_hypreal_sqrt:
     "\<lbrakk>0 \<le> x; x \<in> Infinitesimal\<rbrakk> \<Longrightarrow> ( *f* sqrt) x \<in> Infinitesimal"
  by (simp add: mem_infmal_iff)

lemma Infinitesimal_hypreal_sqrt_imp_Infinitesimal:
     "\<lbrakk>0 \<le> x; ( *f* sqrt) x \<in> Infinitesimal\<rbrakk> \<Longrightarrow> x \<in> Infinitesimal"
  using hypreal_sqrt_approx_zero2 mem_infmal_iff by blast

lemma Infinitesimal_hypreal_sqrt_iff [simp]:
     "0 \<le> x \<Longrightarrow> (( *f* sqrt) x \<in> Infinitesimal) = (x \<in> Infinitesimal)"
by (blast intro: Infinitesimal_hypreal_sqrt_imp_Infinitesimal Infinitesimal_hypreal_sqrt)

lemma HInfinite_hypreal_sqrt:
     "\<lbrakk>0 \<le> x; x \<in> HInfinite\<rbrakk> \<Longrightarrow> ( *f* sqrt) x \<in> HInfinite"
  by (simp add: HInfinite_HFinite_iff)

lemma HInfinite_hypreal_sqrt_imp_HInfinite:
     "\<lbrakk>0 \<le> x; ( *f* sqrt) x \<in> HInfinite\<rbrakk> \<Longrightarrow> x \<in> HInfinite"
  using HFinite_hypreal_sqrt_iff HInfinite_HFinite_iff by blast

lemma HInfinite_hypreal_sqrt_iff [simp]:
     "0 \<le> x \<Longrightarrow> (( *f* sqrt) x \<in> HInfinite) = (x \<in> HInfinite)"
by (blast intro: HInfinite_hypreal_sqrt HInfinite_hypreal_sqrt_imp_HInfinite)

lemma HFinite_exp [simp]:
  "sumhr (0, whn, \<lambda>n. inverse (fact n) * x ^ n) \<in> HFinite"
  unfolding sumhr_app star_zero_def starfun2_star_of atLeast0LessThan
  by (metis NSBseqD2 NSconvergent_NSBseq convergent_NSconvergent_iff summable_iff_convergent summable_exp)

lemma exphr_zero [simp]: "exphr 0 = 1"
proof -
  have "\<forall>x>1. 1 = sumhr (0, 1, \<lambda>n. inverse (fact n) * 0 ^ n) + sumhr (1, x, \<lambda>n. inverse (fact n) * 0 ^ n)"
    unfolding sumhr_app by transfer (simp add: power_0_left)
  then have "sumhr (0, 1, \<lambda>n. inverse (fact n) * 0 ^ n) + sumhr (1, whn, \<lambda>n. inverse (fact n) * 0 ^ n) \<approx> 1"
    by auto
  then show ?thesis
    unfolding exphr_def
    using sumhr_split_add [OF hypnat_one_less_hypnat_omega] st_unique by auto
qed

lemma coshr_zero [simp]: "coshr 0 = 1"
  proof -
  have "\<forall>x>1. 1 = sumhr (0, 1, \<lambda>n. cos_coeff n * 0 ^ n) + sumhr (1, x, \<lambda>n. cos_coeff n * 0 ^ n)"
    unfolding sumhr_app by transfer (simp add: power_0_left)
  then have "sumhr (0, 1, \<lambda>n. cos_coeff n * 0 ^ n) + sumhr (1, whn, \<lambda>n. cos_coeff n * 0 ^ n) \<approx> 1"
    by auto
  then show ?thesis
    unfolding coshr_def
    using sumhr_split_add [OF hypnat_one_less_hypnat_omega] st_unique by auto
qed

lemma STAR_exp_zero_approx_one [simp]: "( *f* exp) (0::hypreal) \<approx> 1"
  proof -
  have "(*f* exp) (0::real star) = 1"
    by transfer simp
  then show ?thesis
    by auto
qed

lemma STAR_exp_Infinitesimal: 
  assumes "x \<in> Infinitesimal" shows "( *f* exp) (x::hypreal) \<approx> 1"
proof (cases "x = 0")
  case False
  have "NSDERIV exp 0 :> 1"
    by (metis DERIV_exp NSDERIV_DERIV_iff exp_zero)
  then have "((*f* exp) x - 1) / x \<approx> 1"
    using nsderiv_def False NSDERIVD2 assms by fastforce
  then have "(*f* exp) x - 1 \<approx> x"
    using NSDERIVD4 \<open>NSDERIV exp 0 :> 1\<close> assms by fastforce
  then show ?thesis
    by (meson Infinitesimal_approx approx_minus_iff approx_trans2 assms not_Infinitesimal_not_zero)
qed auto

lemma STAR_exp_epsilon [simp]: "( *f* exp) \<epsilon> \<approx> 1"
  by (auto intro: STAR_exp_Infinitesimal)

lemma STAR_exp_add:
  "\<And>(x::'a:: {banach,real_normed_field} star) y. ( *f* exp)(x + y) = ( *f* exp) x * ( *f* exp) y"
  by transfer (rule exp_add)

lemma exphr_hypreal_of_real_exp_eq: "exphr x = hypreal_of_real (exp x)"
proof -
  have "(\<lambda>n. inverse (fact n) * x ^ n) sums exp x"
    using exp_converges [of x] by simp
  then have "(\<lambda>n. \<Sum>n<n. inverse (fact n) * x ^ n) \<longlonglongrightarrow>\<^sub>N\<^sub>S exp x"
    using NSsums_def sums_NSsums_iff by blast
  then have "hypreal_of_real (exp x) \<approx> sumhr (0, whn, \<lambda>n. inverse (fact n) * x ^ n)"
    unfolding starfunNat_sumr [symmetric] atLeast0LessThan
    using HNatInfinite_whn NSLIMSEQ_iff approx_sym by blast
  then show ?thesis
    unfolding exphr_def using st_eq_approx_iff by auto
qed

lemma starfun_exp_ge_add_one_self [simp]: "\<And>x::hypreal. 0 \<le> x \<Longrightarrow> (1 + x) \<le> ( *f* exp) x"
  by transfer (rule exp_ge_add_one_self_aux)

text\<open>exp maps infinities to infinities\<close>
lemma starfun_exp_HInfinite:
  fixes x :: hypreal
  assumes "x \<in> HInfinite" "0 \<le> x"
  shows "( *f* exp) x \<in> HInfinite"
proof -
  have "x \<le> 1 + x"
    by simp
  also have "\<dots> \<le> (*f* exp) x"
    by (simp add: \<open>0 \<le> x\<close>)
  finally show ?thesis
    using HInfinite_ge_HInfinite assms by blast
qed

lemma starfun_exp_minus:
  "\<And>x::'a:: {banach,real_normed_field} star. ( *f* exp) (-x) = inverse(( *f* exp) x)"
  by transfer (rule exp_minus)

text\<open>exp maps infinitesimals to infinitesimals\<close>
lemma starfun_exp_Infinitesimal:
  fixes x :: hypreal
  assumes "x \<in> HInfinite" "x \<le> 0"
  shows "( *f* exp) x \<in> Infinitesimal"
proof -
  obtain y where "x = -y" "y \<ge> 0"
    by (metis abs_of_nonpos assms(2) eq_abs_iff')
  then have "( *f* exp) y \<in> HInfinite"
    using HInfinite_minus_iff assms(1) starfun_exp_HInfinite by blast
  then show ?thesis
    by (simp add: HInfinite_inverse_Infinitesimal \<open>x = - y\<close> starfun_exp_minus)
qed

lemma starfun_exp_gt_one [simp]: "\<And>x::hypreal. 0 < x \<Longrightarrow> 1 < ( *f* exp) x"
  by transfer (rule exp_gt_one)

abbreviation real_ln :: "real \<Rightarrow> real" where 
  "real_ln \<equiv> ln"

lemma starfun_ln_exp [simp]: "\<And>x. ( *f* real_ln) (( *f* exp) x) = x"
  by transfer (rule ln_exp)

lemma starfun_exp_ln_iff [simp]: "\<And>x. (( *f* exp)(( *f* real_ln) x) = x) = (0 < x)"
  by transfer (rule exp_ln_iff)

lemma starfun_exp_ln_eq: "\<And>u x. ( *f* exp) u = x \<Longrightarrow> ( *f* real_ln) x = u"
  by transfer (rule ln_unique)

lemma starfun_ln_less_self [simp]: "\<And>x. 0 < x \<Longrightarrow> ( *f* real_ln) x < x"
  by transfer (rule ln_less_self)

lemma starfun_ln_ge_zero [simp]: "\<And>x. 1 \<le> x \<Longrightarrow> 0 \<le> ( *f* real_ln) x"
  by transfer (rule ln_ge_zero)

lemma starfun_ln_gt_zero [simp]: "\<And>x .1 < x \<Longrightarrow> 0 < ( *f* real_ln) x"
  by transfer (rule ln_gt_zero)

lemma starfun_ln_not_eq_zero [simp]: "\<And>x. \<lbrakk>0 < x; x \<noteq> 1\<rbrakk> \<Longrightarrow> ( *f* real_ln) x \<noteq> 0"
  by transfer simp

lemma starfun_ln_HFinite: "\<lbrakk>x \<in> HFinite; 1 \<le> x\<rbrakk> \<Longrightarrow> ( *f* real_ln) x \<in> HFinite"
  by (metis HFinite_HInfinite_iff less_le_trans starfun_exp_HInfinite starfun_exp_ln_iff starfun_ln_ge_zero zero_less_one)

lemma starfun_ln_inverse: "\<And>x. 0 < x \<Longrightarrow> ( *f* real_ln) (inverse x) = -( *f* ln) x"
  by transfer (rule ln_inverse)

lemma starfun_abs_exp_cancel: "\<And>x. \<bar>( *f* exp) (x::hypreal)\<bar> = ( *f* exp) x"
  by transfer (rule abs_exp_cancel)

lemma starfun_exp_less_mono: "\<And>x y::hypreal. x < y \<Longrightarrow> ( *f* exp) x < ( *f* exp) y"
  by transfer (rule exp_less_mono)

lemma starfun_exp_HFinite: 
  fixes x :: hypreal
  assumes "x \<in> HFinite"
  shows "( *f* exp) x \<in> HFinite"
proof -
  obtain u where "u \<in> \<real>" "\<bar>x\<bar> < u"
    using HFiniteD assms by force
  with assms have "\<bar>(*f* exp) x\<bar> < (*f* exp) u" 
    using starfun_abs_exp_cancel starfun_exp_less_mono by auto
  with \<open>u \<in> \<real>\<close> show ?thesis
    by (force simp: HFinite_def Reals_eq_Standard)
qed

lemma starfun_exp_add_HFinite_Infinitesimal_approx:
  fixes x :: hypreal
  shows "\<lbrakk>x \<in> Infinitesimal; z \<in> HFinite\<rbrakk> \<Longrightarrow> ( *f* exp) (z + x::hypreal) \<approx> ( *f* exp) z"
  using STAR_exp_Infinitesimal approx_mult2 starfun_exp_HFinite by (fastforce simp add: STAR_exp_add)

lemma starfun_ln_HInfinite:
  "\<lbrakk>x \<in> HInfinite; 0 < x\<rbrakk> \<Longrightarrow> ( *f* real_ln) x \<in> HInfinite"
  by (metis HInfinite_HFinite_iff starfun_exp_HFinite starfun_exp_ln_iff)

lemma starfun_exp_HInfinite_Infinitesimal_disj:
  fixes x :: hypreal
  shows "x \<in> HInfinite \<Longrightarrow> ( *f* exp) x \<in> HInfinite \<or> ( *f* exp) (x::hypreal) \<in> Infinitesimal"
  by (meson linear starfun_exp_HInfinite starfun_exp_Infinitesimal)

lemma starfun_ln_HFinite_not_Infinitesimal:
     "\<lbrakk>x \<in> HFinite - Infinitesimal; 0 < x\<rbrakk> \<Longrightarrow> ( *f* real_ln) x \<in> HFinite"
  by (metis DiffD1 DiffD2 HInfinite_HFinite_iff starfun_exp_HInfinite_Infinitesimal_disj starfun_exp_ln_iff)

(* we do proof by considering ln of 1/x *)
lemma starfun_ln_Infinitesimal_HInfinite:
  assumes "x \<in> Infinitesimal" "0 < x"
  shows "( *f* real_ln) x \<in> HInfinite"
proof -
  have "inverse x \<in> HInfinite"
    using Infinitesimal_inverse_HInfinite assms by blast
  then show ?thesis
    using HInfinite_minus_iff assms(2) starfun_ln_HInfinite starfun_ln_inverse by fastforce
qed

lemma starfun_ln_less_zero: "\<And>x. \<lbrakk>0 < x; x < 1\<rbrakk> \<Longrightarrow> ( *f* real_ln) x < 0"
  by transfer (rule ln_less_zero)

lemma starfun_ln_Infinitesimal_less_zero:
  "\<lbrakk>x \<in> Infinitesimal; 0 < x\<rbrakk> \<Longrightarrow> ( *f* real_ln) x < 0"
  by (auto intro!: starfun_ln_less_zero simp add: Infinitesimal_def)

lemma starfun_ln_HInfinite_gt_zero:
  "\<lbrakk>x \<in> HInfinite; 0 < x\<rbrakk> \<Longrightarrow> 0 < ( *f* real_ln) x"
  by (auto intro!: starfun_ln_gt_zero simp add: HInfinite_def)


lemma HFinite_sin [simp]: "sumhr (0, whn, \<lambda>n. sin_coeff n * x ^ n) \<in> HFinite"
proof -
  have "summable (\<lambda>i. sin_coeff i * x ^ i)"
    using summable_norm_sin [of x] by (simp add: summable_rabs_cancel)
  then have "(*f* (\<lambda>n. \<Sum>n<n. sin_coeff n * x ^ n)) whn \<in> HFinite"
    unfolding summable_sums_iff sums_NSsums_iff NSsums_def NSLIMSEQ_iff
    using HFinite_star_of HNatInfinite_whn approx_HFinite approx_sym by blast
  then show ?thesis
    unfolding sumhr_app
    by (simp only: star_zero_def starfun2_star_of atLeast0LessThan)
qed

lemma STAR_sin_zero [simp]: "( *f* sin) 0 = 0"
  by transfer (rule sin_zero)

lemma STAR_sin_Infinitesimal [simp]:
  fixes x :: "'a::{real_normed_field,banach} star"
  assumes "x \<in> Infinitesimal"
  shows "( *f* sin) x \<approx> x"
proof (cases "x = 0")
  case False
  have "NSDERIV sin 0 :> 1"
    by (metis DERIV_sin NSDERIV_DERIV_iff cos_zero)
  then have "(*f* sin) x / x \<approx> 1"
    using False NSDERIVD2 assms by fastforce
  with assms show ?thesis
    unfolding star_one_def
    by (metis False Infinitesimal_approx Infinitesimal_ratio approx_star_of_HFinite)
qed auto

lemma HFinite_cos [simp]: "sumhr (0, whn, \<lambda>n. cos_coeff n * x ^ n) \<in> HFinite"
proof -
  have "summable (\<lambda>i. cos_coeff i * x ^ i)"
    using summable_norm_cos [of x] by (simp add: summable_rabs_cancel)
  then have "(*f* (\<lambda>n. \<Sum>n<n. cos_coeff n * x ^ n)) whn \<in> HFinite"
    unfolding summable_sums_iff sums_NSsums_iff NSsums_def NSLIMSEQ_iff
    using HFinite_star_of HNatInfinite_whn approx_HFinite approx_sym by blast
  then show ?thesis
    unfolding sumhr_app
    by (simp only: star_zero_def starfun2_star_of atLeast0LessThan)
qed

lemma STAR_cos_zero [simp]: "( *f* cos) 0 = 1"
  by transfer (rule cos_zero)

lemma STAR_cos_Infinitesimal [simp]:
  fixes x :: "'a::{real_normed_field,banach} star"
  assumes "x \<in> Infinitesimal"
  shows "( *f* cos) x \<approx> 1"
proof (cases "x = 0")
  case False
  have "NSDERIV cos 0 :> 0"
    by (metis DERIV_cos NSDERIV_DERIV_iff add.inverse_neutral sin_zero)
  then have "(*f* cos) x - 1 \<approx> 0"
    using NSDERIV_approx assms by fastforce
  with assms show ?thesis
    using approx_minus_iff by blast
qed auto

lemma STAR_tan_zero [simp]: "( *f* tan) 0 = 0"
  by transfer (rule tan_zero)

lemma STAR_tan_Infinitesimal [simp]:
  assumes "x \<in> Infinitesimal"
  shows "( *f* tan) x \<approx> x"
proof (cases "x = 0")
  case False
  have "NSDERIV tan 0 :> 1"
    using DERIV_tan [of 0] by (simp add: NSDERIV_DERIV_iff)
  then have "(*f* tan) x / x \<approx> 1"
    using False NSDERIVD2 assms by fastforce
  with assms show ?thesis
    unfolding star_one_def
    by (metis False Infinitesimal_approx Infinitesimal_ratio approx_star_of_HFinite)
qed auto

lemma STAR_sin_cos_Infinitesimal_mult:
  fixes x :: "'a::{real_normed_field,banach} star"
  shows "x \<in> Infinitesimal \<Longrightarrow> ( *f* sin) x * ( *f* cos) x \<approx> x"
  using approx_mult_HFinite [of "( *f* sin) x" _ "( *f* cos) x" 1] 
  by (simp add: Infinitesimal_subset_HFinite [THEN subsetD])

lemma HFinite_pi: "hypreal_of_real pi \<in> HFinite"
  by simp


lemma STAR_sin_Infinitesimal_divide:
  fixes x :: "'a::{real_normed_field,banach} star"
  shows "\<lbrakk>x \<in> Infinitesimal; x \<noteq> 0\<rbrakk> \<Longrightarrow> ( *f* sin) x/x \<approx> 1"
  using DERIV_sin [of "0::'a"]
  by (simp add: NSDERIV_DERIV_iff [symmetric] nsderiv_def)

subsection \<open>Proving $\sin* (1/n) \times 1/(1/n) \approx 1$ for $n = \infty$ \<close> 

lemma lemma_sin_pi:
  "n \<in> HNatInfinite  
      \<Longrightarrow> ( *f* sin) (inverse (hypreal_of_hypnat n))/(inverse (hypreal_of_hypnat n)) \<approx> 1"
  by (simp add: STAR_sin_Infinitesimal_divide zero_less_HNatInfinite)

lemma STAR_sin_inverse_HNatInfinite:
     "n \<in> HNatInfinite  
      \<Longrightarrow> ( *f* sin) (inverse (hypreal_of_hypnat n)) * hypreal_of_hypnat n \<approx> 1"
  by (metis field_class.field_divide_inverse inverse_inverse_eq lemma_sin_pi)

lemma Infinitesimal_pi_divide_HNatInfinite: 
     "N \<in> HNatInfinite  
      \<Longrightarrow> hypreal_of_real pi/(hypreal_of_hypnat N) \<in> Infinitesimal"
  by (simp add: Infinitesimal_HFinite_mult2 field_class.field_divide_inverse)

lemma pi_divide_HNatInfinite_not_zero [simp]:
  "N \<in> HNatInfinite \<Longrightarrow> hypreal_of_real pi/(hypreal_of_hypnat N) \<noteq> 0"
  by (simp add: zero_less_HNatInfinite)

lemma STAR_sin_pi_divide_HNatInfinite_approx_pi:
  assumes "n \<in> HNatInfinite"
  shows "(*f* sin) (hypreal_of_real pi / hypreal_of_hypnat n) * hypreal_of_hypnat n \<approx>
         hypreal_of_real pi"
proof -
  have "(*f* sin) (hypreal_of_real pi / hypreal_of_hypnat n) / (hypreal_of_real pi / hypreal_of_hypnat n) \<approx> 1"
    using Infinitesimal_pi_divide_HNatInfinite STAR_sin_Infinitesimal_divide assms pi_divide_HNatInfinite_not_zero by blast
  then have "hypreal_of_hypnat n * star_of sin \<star> (hypreal_of_real pi / hypreal_of_hypnat n) / hypreal_of_real pi \<approx> 1"
    by (simp add: mult.commute starfun_def)
  then show ?thesis
    apply (simp add: starfun_def field_simps)
    by (metis (no_types, lifting) approx_mult_subst_star_of approx_refl mult_cancel_right1 nonzero_eq_divide_eq pi_neq_zero star_of_eq_0)
qed

lemma STAR_sin_pi_divide_HNatInfinite_approx_pi2:
     "n \<in> HNatInfinite  
      \<Longrightarrow> hypreal_of_hypnat n * ( *f* sin) (hypreal_of_real pi/(hypreal_of_hypnat n)) \<approx> hypreal_of_real pi"
  by (metis STAR_sin_pi_divide_HNatInfinite_approx_pi mult.commute)

lemma starfunNat_pi_divide_n_Infinitesimal: 
     "N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>x. pi / real x)) N \<in> Infinitesimal"
  by (simp add: Infinitesimal_HFinite_mult2 divide_inverse starfunNat_real_of_nat)

lemma STAR_sin_pi_divide_n_approx:
  assumes "N \<in> HNatInfinite"
  shows "( *f* sin) (( *f* (\<lambda>x. pi / real x)) N) \<approx> hypreal_of_real pi/(hypreal_of_hypnat N)"
proof -
  have "\<exists>s. (*f* sin) ((*f* (\<lambda>n. pi / real n)) N) \<approx> s \<and> hypreal_of_real pi / hypreal_of_hypnat N \<approx> s"
    by (metis (lifting) Infinitesimal_approx Infinitesimal_pi_divide_HNatInfinite STAR_sin_Infinitesimal assms starfunNat_pi_divide_n_Infinitesimal)
  then show ?thesis
    by (meson approx_trans2)
qed

lemma NSLIMSEQ_sin_pi: "(\<lambda>n. real n * sin (pi / real n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S pi"
proof -
  have *: "hypreal_of_hypnat N * (*f* sin) ((*f* (\<lambda>x. pi / real x)) N) \<approx> hypreal_of_real pi"
    if "N \<in> HNatInfinite"
    for N :: "nat star"
    using that
    by simp (metis STAR_sin_pi_divide_HNatInfinite_approx_pi2 starfunNat_real_of_nat)
  show ?thesis
    by (simp add: NSLIMSEQ_def starfunNat_real_of_nat) (metis * starfun_o2)
qed

lemma NSLIMSEQ_cos_one: "(\<lambda>n. cos (pi / real n))\<longlonglongrightarrow>\<^sub>N\<^sub>S 1"
proof -
  have "(*f* cos) ((*f* (\<lambda>x. pi / real x)) N) \<approx> 1"
    if "N \<in> HNatInfinite" for N 
    using that STAR_cos_Infinitesimal starfunNat_pi_divide_n_Infinitesimal by blast
  then show ?thesis
    by (simp add: NSLIMSEQ_def) (metis STAR_cos_Infinitesimal starfunNat_pi_divide_n_Infinitesimal starfun_o2)
qed

lemma NSLIMSEQ_sin_cos_pi:
  "(\<lambda>n. real n * sin (pi / real n) * cos (pi / real n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S pi"
  using NSLIMSEQ_cos_one NSLIMSEQ_mult NSLIMSEQ_sin_pi by force


text\<open>A familiar approximation to \<^term>\<open>cos x\<close> when \<^term>\<open>x\<close> is small\<close>

lemma STAR_cos_Infinitesimal_approx:
  fixes x :: "'a::{real_normed_field,banach} star"
  shows "x \<in> Infinitesimal \<Longrightarrow> ( *f* cos) x \<approx> 1 - x\<^sup>2"
  by (metis Infinitesimal_square_iff STAR_cos_Infinitesimal approx_diff approx_sym diff_zero mem_infmal_iff power2_eq_square)

lemma STAR_cos_Infinitesimal_approx2:
  fixes x :: hypreal 
  assumes "x \<in> Infinitesimal"
  shows "( *f* cos) x \<approx> 1 - (x\<^sup>2)/2"
proof -
  have "1 \<approx> 1 - x\<^sup>2 / 2"
    using assms
    by (auto intro: Infinitesimal_SReal_divide simp add: Infinitesimal_approx_minus [symmetric] numeral_2_eq_2)
  then show ?thesis
    using STAR_cos_Infinitesimal approx_trans assms by blast
qed

end

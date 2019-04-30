(*  Title:      HOL/Nonstandard_Analysis/NSA.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson, University of Cambridge
*)

section \<open>Infinite Numbers, Infinitesimals, Infinitely Close Relation\<close>

theory NSA
  imports HyperDef "HOL-Library.Lub_Glb" 
begin

definition hnorm :: "'a::real_normed_vector star \<Rightarrow> real star"
  where [transfer_unfold]: "hnorm = *f* norm"

definition Infinitesimal  :: "('a::real_normed_vector) star set"
  where "Infinitesimal = {x. \<forall>r \<in> Reals. 0 < r \<longrightarrow> hnorm x < r}"

definition HFinite :: "('a::real_normed_vector) star set"
  where "HFinite = {x. \<exists>r \<in> Reals. hnorm x < r}"

definition HInfinite :: "('a::real_normed_vector) star set"
  where "HInfinite = {x. \<forall>r \<in> Reals. r < hnorm x}"

definition approx :: "'a::real_normed_vector star \<Rightarrow> 'a star \<Rightarrow> bool"  (infixl "\<approx>" 50)
  where "x \<approx> y \<longleftrightarrow> x - y \<in> Infinitesimal"
    \<comment> \<open>the ``infinitely close'' relation\<close>

definition st :: "hypreal \<Rightarrow> hypreal"
  where "st = (\<lambda>x. SOME r. x \<in> HFinite \<and> r \<in> \<real> \<and> r \<approx> x)"
    \<comment> \<open>the standard part of a hyperreal\<close>

definition monad :: "'a::real_normed_vector star \<Rightarrow> 'a star set"
  where "monad x = {y. x \<approx> y}"

definition galaxy :: "'a::real_normed_vector star \<Rightarrow> 'a star set"
  where "galaxy x = {y. (x + -y) \<in> HFinite}"

lemma SReal_def: "\<real> \<equiv> {x. \<exists>r. x = hypreal_of_real r}"
  by (simp add: Reals_def image_def)


subsection \<open>Nonstandard Extension of the Norm Function\<close>

definition scaleHR :: "real star \<Rightarrow> 'a star \<Rightarrow> 'a::real_normed_vector star"
  where [transfer_unfold]: "scaleHR = starfun2 scaleR"

lemma Standard_hnorm [simp]: "x \<in> Standard \<Longrightarrow> hnorm x \<in> Standard"
  by (simp add: hnorm_def)

lemma star_of_norm [simp]: "star_of (norm x) = hnorm (star_of x)"
  by transfer (rule refl)

lemma hnorm_ge_zero [simp]: "\<And>x::'a::real_normed_vector star. 0 \<le> hnorm x"
  by transfer (rule norm_ge_zero)

lemma hnorm_eq_zero [simp]: "\<And>x::'a::real_normed_vector star. hnorm x = 0 \<longleftrightarrow> x = 0"
  by transfer (rule norm_eq_zero)

lemma hnorm_triangle_ineq: "\<And>x y::'a::real_normed_vector star. hnorm (x + y) \<le> hnorm x + hnorm y"
  by transfer (rule norm_triangle_ineq)

lemma hnorm_triangle_ineq3: "\<And>x y::'a::real_normed_vector star. \<bar>hnorm x - hnorm y\<bar> \<le> hnorm (x - y)"
  by transfer (rule norm_triangle_ineq3)

lemma hnorm_scaleR: "\<And>x::'a::real_normed_vector star. hnorm (a *\<^sub>R x) = \<bar>star_of a\<bar> * hnorm x"
  by transfer (rule norm_scaleR)

lemma hnorm_scaleHR: "\<And>a (x::'a::real_normed_vector star). hnorm (scaleHR a x) = \<bar>a\<bar> * hnorm x"
  by transfer (rule norm_scaleR)

lemma hnorm_mult_ineq: "\<And>x y::'a::real_normed_algebra star. hnorm (x * y) \<le> hnorm x * hnorm y"
  by transfer (rule norm_mult_ineq)

lemma hnorm_mult: "\<And>x y::'a::real_normed_div_algebra star. hnorm (x * y) = hnorm x * hnorm y"
  by transfer (rule norm_mult)

lemma hnorm_hyperpow: "\<And>(x::'a::{real_normed_div_algebra} star) n. hnorm (x pow n) = hnorm x pow n"
  by transfer (rule norm_power)

lemma hnorm_one [simp]: "hnorm (1::'a::real_normed_div_algebra star) = 1"
  by transfer (rule norm_one)

lemma hnorm_zero [simp]: "hnorm (0::'a::real_normed_vector star) = 0"
  by transfer (rule norm_zero)

lemma zero_less_hnorm_iff [simp]: "\<And>x::'a::real_normed_vector star. 0 < hnorm x \<longleftrightarrow> x \<noteq> 0"
  by transfer (rule zero_less_norm_iff)

lemma hnorm_minus_cancel [simp]: "\<And>x::'a::real_normed_vector star. hnorm (- x) = hnorm x"
  by transfer (rule norm_minus_cancel)

lemma hnorm_minus_commute: "\<And>a b::'a::real_normed_vector star. hnorm (a - b) = hnorm (b - a)"
  by transfer (rule norm_minus_commute)

lemma hnorm_triangle_ineq2: "\<And>a b::'a::real_normed_vector star. hnorm a - hnorm b \<le> hnorm (a - b)"
  by transfer (rule norm_triangle_ineq2)

lemma hnorm_triangle_ineq4: "\<And>a b::'a::real_normed_vector star. hnorm (a - b) \<le> hnorm a + hnorm b"
  by transfer (rule norm_triangle_ineq4)

lemma abs_hnorm_cancel [simp]: "\<And>a::'a::real_normed_vector star. \<bar>hnorm a\<bar> = hnorm a"
  by transfer (rule abs_norm_cancel)

lemma hnorm_of_hypreal [simp]: "\<And>r. hnorm (of_hypreal r::'a::real_normed_algebra_1 star) = \<bar>r\<bar>"
  by transfer (rule norm_of_real)

lemma nonzero_hnorm_inverse:
  "\<And>a::'a::real_normed_div_algebra star. a \<noteq> 0 \<Longrightarrow> hnorm (inverse a) = inverse (hnorm a)"
  by transfer (rule nonzero_norm_inverse)

lemma hnorm_inverse:
  "\<And>a::'a::{real_normed_div_algebra, division_ring} star. hnorm (inverse a) = inverse (hnorm a)"
  by transfer (rule norm_inverse)

lemma hnorm_divide: "\<And>a b::'a::{real_normed_field, field} star. hnorm (a / b) = hnorm a / hnorm b"
  by transfer (rule norm_divide)

lemma hypreal_hnorm_def [simp]: "\<And>r::hypreal. hnorm r = \<bar>r\<bar>"
  by transfer (rule real_norm_def)

lemma hnorm_add_less:
  "\<And>(x::'a::real_normed_vector star) y r s. hnorm x < r \<Longrightarrow> hnorm y < s \<Longrightarrow> hnorm (x + y) < r + s"
  by transfer (rule norm_add_less)

lemma hnorm_mult_less:
  "\<And>(x::'a::real_normed_algebra star) y r s. hnorm x < r \<Longrightarrow> hnorm y < s \<Longrightarrow> hnorm (x * y) < r * s"
  by transfer (rule norm_mult_less)

lemma hnorm_scaleHR_less: "\<bar>x\<bar> < r \<Longrightarrow> hnorm y < s \<Longrightarrow> hnorm (scaleHR x y) < r * s"
 by (simp only: hnorm_scaleHR) (simp add: mult_strict_mono')


subsection \<open>Closure Laws for the Standard Reals\<close>

lemma Reals_add_cancel: "x + y \<in> \<real> \<Longrightarrow> y \<in> \<real> \<Longrightarrow> x \<in> \<real>"
  by (drule (1) Reals_diff) simp

lemma SReal_hrabs: "x \<in> \<real> \<Longrightarrow> \<bar>x\<bar> \<in> \<real>"
  for x :: hypreal
  by (simp add: Reals_eq_Standard)

lemma SReal_hypreal_of_real [simp]: "hypreal_of_real x \<in> \<real>"
  by (simp add: Reals_eq_Standard)

lemma SReal_divide_numeral: "r \<in> \<real> \<Longrightarrow> r / (numeral w::hypreal) \<in> \<real>"
  by simp

text \<open>\<open>\<epsilon>\<close> is not in Reals because it is an infinitesimal\<close>
lemma SReal_epsilon_not_mem: "\<epsilon> \<notin> \<real>"
  by (auto simp: SReal_def hypreal_of_real_not_eq_epsilon [symmetric])

lemma SReal_omega_not_mem: "\<omega> \<notin> \<real>"
  by (auto simp: SReal_def hypreal_of_real_not_eq_omega [symmetric])

lemma SReal_UNIV_real: "{x. hypreal_of_real x \<in> \<real>} = (UNIV::real set)"
  by simp

lemma SReal_iff: "x \<in> \<real> \<longleftrightarrow> (\<exists>y. x = hypreal_of_real y)"
  by (simp add: SReal_def)

lemma hypreal_of_real_image: "hypreal_of_real `(UNIV::real set) = \<real>"
  by (simp add: Reals_eq_Standard Standard_def)

lemma inv_hypreal_of_real_image: "inv hypreal_of_real ` \<real> = UNIV"
  by (simp add: Reals_eq_Standard Standard_def inj_star_of)

lemma SReal_dense: "x \<in> \<real> \<Longrightarrow> y \<in> \<real> \<Longrightarrow> x < y \<Longrightarrow> \<exists>r \<in> Reals. x < r \<and> r < y"
  for x y :: hypreal
  using dense by (fastforce simp add: SReal_def)


subsection \<open>Set of Finite Elements is a Subring of the Extended Reals\<close>

lemma HFinite_add: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> x + y \<in> HFinite"
  unfolding HFinite_def by (blast intro!: Reals_add hnorm_add_less)

lemma HFinite_mult: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> x * y \<in> HFinite"
  for x y :: "'a::real_normed_algebra star"
  unfolding HFinite_def by (blast intro!: Reals_mult hnorm_mult_less)

lemma HFinite_scaleHR: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> scaleHR x y \<in> HFinite"
  by (auto simp: HFinite_def intro!: Reals_mult hnorm_scaleHR_less)

lemma HFinite_minus_iff: "- x \<in> HFinite \<longleftrightarrow> x \<in> HFinite"
  by (simp add: HFinite_def)

lemma HFinite_star_of [simp]: "star_of x \<in> HFinite"
  by (simp add: HFinite_def) (metis SReal_hypreal_of_real gt_ex star_of_less star_of_norm)

lemma SReal_subset_HFinite: "(\<real>::hypreal set) \<subseteq> HFinite"
  by (auto simp add: SReal_def)

lemma HFiniteD: "x \<in> HFinite \<Longrightarrow> \<exists>t \<in> Reals. hnorm x < t"
  by (simp add: HFinite_def)

lemma HFinite_hrabs_iff [iff]: "\<bar>x\<bar> \<in> HFinite \<longleftrightarrow> x \<in> HFinite"
  for x :: hypreal
  by (simp add: HFinite_def)

lemma HFinite_hnorm_iff [iff]: "hnorm x \<in> HFinite \<longleftrightarrow> x \<in> HFinite"
  for x :: hypreal
  by (simp add: HFinite_def)

lemma HFinite_numeral [simp]: "numeral w \<in> HFinite"
  unfolding star_numeral_def by (rule HFinite_star_of)

text \<open>As always with numerals, \<open>0\<close> and \<open>1\<close> are special cases.\<close>

lemma HFinite_0 [simp]: "0 \<in> HFinite"
  unfolding star_zero_def by (rule HFinite_star_of)

lemma HFinite_1 [simp]: "1 \<in> HFinite"
  unfolding star_one_def by (rule HFinite_star_of)

lemma hrealpow_HFinite: "x \<in> HFinite \<Longrightarrow> x ^ n \<in> HFinite"
  for x :: "'a::{real_normed_algebra,monoid_mult} star"
  by (induct n) (auto intro: HFinite_mult)

lemma HFinite_bounded: 
  fixes x y :: hypreal
  assumes "x \<in> HFinite" and y: "y \<le> x" "0 \<le> y" shows "y \<in> HFinite"
proof (cases "x \<le> 0")
  case True
  then have "y = 0"
    using y by auto
  then show ?thesis
    by simp
next
  case False
  then show ?thesis
    using assms le_less_trans by (auto simp: HFinite_def)
qed


subsection \<open>Set of Infinitesimals is a Subring of the Hyperreals\<close>

lemma InfinitesimalI: "(\<And>r. r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> hnorm x < r) \<Longrightarrow> x \<in> Infinitesimal"
  by (simp add: Infinitesimal_def)

lemma InfinitesimalD: "x \<in> Infinitesimal \<Longrightarrow> \<forall>r \<in> Reals. 0 < r \<longrightarrow> hnorm x < r"
  by (simp add: Infinitesimal_def)

lemma InfinitesimalI2: "(\<And>r. 0 < r \<Longrightarrow> hnorm x < star_of r) \<Longrightarrow> x \<in> Infinitesimal"
  by (auto simp add: Infinitesimal_def SReal_def)

lemma InfinitesimalD2: "x \<in> Infinitesimal \<Longrightarrow> 0 < r \<Longrightarrow> hnorm x < star_of r"
  by (auto simp add: Infinitesimal_def SReal_def)

lemma Infinitesimal_zero [iff]: "0 \<in> Infinitesimal"
  by (simp add: Infinitesimal_def)

lemma Infinitesimal_add:
  assumes "x \<in> Infinitesimal" "y \<in> Infinitesimal"
  shows "x + y \<in> Infinitesimal"
proof (rule InfinitesimalI)
  show "hnorm (x + y) < r"
    if "r \<in> \<real>" and "0 < r" for r :: "real star"
  proof -
    have "hnorm x < r/2" "hnorm y < r/2"
      using InfinitesimalD SReal_divide_numeral assms half_gt_zero that by blast+
    then show ?thesis
      using hnorm_add_less by fastforce
  qed
qed

lemma Infinitesimal_minus_iff [simp]: "- x \<in> Infinitesimal \<longleftrightarrow> x \<in> Infinitesimal"
  by (simp add: Infinitesimal_def)

lemma Infinitesimal_hnorm_iff: "hnorm x \<in> Infinitesimal \<longleftrightarrow> x \<in> Infinitesimal"
  by (simp add: Infinitesimal_def)

lemma Infinitesimal_hrabs_iff [iff]: "\<bar>x\<bar> \<in> Infinitesimal \<longleftrightarrow> x \<in> Infinitesimal"
  for x :: hypreal
  by (simp add: abs_if)

lemma Infinitesimal_of_hypreal_iff [simp]:
  "(of_hypreal x::'a::real_normed_algebra_1 star) \<in> Infinitesimal \<longleftrightarrow> x \<in> Infinitesimal"
  by (subst Infinitesimal_hnorm_iff [symmetric]) simp

lemma Infinitesimal_diff: "x \<in> Infinitesimal \<Longrightarrow> y \<in> Infinitesimal \<Longrightarrow> x - y \<in> Infinitesimal"
  using Infinitesimal_add [of x "- y"] by simp

lemma Infinitesimal_mult: 
  fixes x y :: "'a::real_normed_algebra star"
  assumes "x \<in> Infinitesimal" "y \<in> Infinitesimal"
  shows "x * y \<in> Infinitesimal"
  proof (rule InfinitesimalI)
  show "hnorm (x * y) < r"
    if "r \<in> \<real>" and "0 < r" for r :: "real star"
  proof -
    have "hnorm x < 1" "hnorm y < r"
      using assms that  by (auto simp add: InfinitesimalD)
    then show ?thesis
      using hnorm_mult_less by fastforce
  qed
qed

lemma Infinitesimal_HFinite_mult:
  fixes x y :: "'a::real_normed_algebra star"
  assumes "x \<in> Infinitesimal" "y \<in> HFinite"
  shows "x * y \<in> Infinitesimal"
proof (rule InfinitesimalI)
  obtain t where "hnorm y < t" "t \<in> Reals"
    using HFiniteD \<open>y \<in> HFinite\<close> by blast
  then have "t > 0"
    using hnorm_ge_zero le_less_trans by blast
  show "hnorm (x * y) < r"
    if "r \<in> \<real>" and "0 < r" for r :: "real star"
  proof -
    have "hnorm x < r/t"
      by (meson InfinitesimalD Reals_divide \<open>hnorm y < t\<close> \<open>t \<in> \<real>\<close> assms(1) divide_pos_pos hnorm_ge_zero le_less_trans that) 
    then have "hnorm (x * y) < (r / t) * t"
      using \<open>hnorm y < t\<close> hnorm_mult_less by blast
    then show ?thesis
      using \<open>0 < t\<close> by auto
  qed
qed

lemma Infinitesimal_HFinite_scaleHR:
  assumes "x \<in> Infinitesimal" "y \<in> HFinite"
  shows "scaleHR x y \<in> Infinitesimal"
proof (rule InfinitesimalI)
  obtain t where "hnorm y < t" "t \<in> Reals"
    using HFiniteD \<open>y \<in> HFinite\<close> by blast
  then have "t > 0"
    using hnorm_ge_zero le_less_trans by blast
  show "hnorm (scaleHR x y) < r"
    if "r \<in> \<real>" and "0 < r" for r :: "real star"
  proof -
    have "\<bar>x\<bar> * hnorm y < (r / t) * t"
      by (metis InfinitesimalD Reals_divide \<open>0 < t\<close> \<open>hnorm y < t\<close> \<open>t \<in> \<real>\<close> assms(1) divide_pos_pos hnorm_ge_zero hypreal_hnorm_def mult_strict_mono' that)
    then show ?thesis
      by (simp add: \<open>0 < t\<close> hnorm_scaleHR less_imp_not_eq2)
  qed
qed

lemma Infinitesimal_HFinite_mult2:
  fixes x y :: "'a::real_normed_algebra star"
  assumes "x \<in> Infinitesimal" "y \<in> HFinite"
  shows  "y * x \<in> Infinitesimal"
proof (rule InfinitesimalI)
  obtain t where "hnorm y < t" "t \<in> Reals"
    using HFiniteD \<open>y \<in> HFinite\<close> by blast
  then have "t > 0"
    using hnorm_ge_zero le_less_trans by blast
  show "hnorm (y * x) < r"
    if "r \<in> \<real>" and "0 < r" for r :: "real star"
  proof -
    have "hnorm x < r/t"
      by (meson InfinitesimalD Reals_divide \<open>hnorm y < t\<close> \<open>t \<in> \<real>\<close> assms(1) divide_pos_pos hnorm_ge_zero le_less_trans that) 
    then have "hnorm (y * x) < t * (r / t)"
      using \<open>hnorm y < t\<close> hnorm_mult_less by blast
    then show ?thesis
      using \<open>0 < t\<close> by auto
  qed
qed

lemma Infinitesimal_scaleR2: 
  assumes "x \<in> Infinitesimal" shows "a *\<^sub>R x \<in> Infinitesimal"
    by (metis HFinite_star_of Infinitesimal_HFinite_mult2 Infinitesimal_hnorm_iff assms hnorm_scaleR hypreal_hnorm_def star_of_norm)

lemma Compl_HFinite: "- HFinite = HInfinite"
  proof -
  have "r < hnorm x" if *: "\<And>s. s \<in> \<real> \<Longrightarrow> s \<le> hnorm x" and "r \<in> \<real>"
    for x :: "'a star" and r :: hypreal
    using * [of "r+1"] \<open>r \<in> \<real>\<close> by auto
  then show ?thesis
    by (auto simp add: HInfinite_def HFinite_def linorder_not_less)
qed

lemma HInfinite_inverse_Infinitesimal:
  "x \<in> HInfinite \<Longrightarrow> inverse x \<in> Infinitesimal"
  for x :: "'a::real_normed_div_algebra star"
  by (simp add: HInfinite_def InfinitesimalI hnorm_inverse inverse_less_imp_less)

lemma inverse_Infinitesimal_iff_HInfinite:
  "x \<noteq> 0 \<Longrightarrow> inverse x \<in> Infinitesimal \<longleftrightarrow> x \<in> HInfinite"
  for x :: "'a::real_normed_div_algebra star"
  by (metis Compl_HFinite Compl_iff HInfinite_inverse_Infinitesimal InfinitesimalD Infinitesimal_HFinite_mult Reals_1 hnorm_one left_inverse less_irrefl zero_less_one)

lemma HInfiniteI: "(\<And>r. r \<in> \<real> \<Longrightarrow> r < hnorm x) \<Longrightarrow> x \<in> HInfinite"
  by (simp add: HInfinite_def)

lemma HInfiniteD: "x \<in> HInfinite \<Longrightarrow> r \<in> \<real> \<Longrightarrow> r < hnorm x"
  by (simp add: HInfinite_def)

lemma HInfinite_mult: 
  fixes x y :: "'a::real_normed_div_algebra star"
  assumes "x \<in> HInfinite" "y \<in> HInfinite" shows "x * y \<in> HInfinite"
proof (rule HInfiniteI, simp only: hnorm_mult)
  have "x \<noteq> 0"
    using Compl_HFinite HFinite_0 assms by blast
  show "r < hnorm x * hnorm y"
    if "r \<in> \<real>" for r :: "real star"
  proof -
    have "r = r * 1"
      by simp
    also have "\<dots> < hnorm x * hnorm y"
      by (meson HInfiniteD Reals_1 \<open>x \<noteq> 0\<close> assms le_numeral_extra(1) mult_strict_mono that zero_less_hnorm_iff)
    finally show ?thesis .
  qed
qed

lemma hypreal_add_zero_less_le_mono: "r < x \<Longrightarrow> 0 \<le> y \<Longrightarrow> r < x + y"
  for r x y :: hypreal
  by simp

lemma HInfinite_add_ge_zero: "x \<in> HInfinite \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> x + y \<in> HInfinite"
  for x y :: hypreal
  by (auto simp: abs_if add.commute HInfinite_def)

lemma HInfinite_add_ge_zero2: "x \<in> HInfinite \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> y + x \<in> HInfinite"
  for x y :: hypreal
  by (auto intro!: HInfinite_add_ge_zero simp add: add.commute)

lemma HInfinite_add_gt_zero: "x \<in> HInfinite \<Longrightarrow> 0 < y \<Longrightarrow> 0 < x \<Longrightarrow> x + y \<in> HInfinite"
  for x y :: hypreal
  by (blast intro: HInfinite_add_ge_zero order_less_imp_le)

lemma HInfinite_minus_iff: "- x \<in> HInfinite \<longleftrightarrow> x \<in> HInfinite"
  by (simp add: HInfinite_def)

lemma HInfinite_add_le_zero: "x \<in> HInfinite \<Longrightarrow> y \<le> 0 \<Longrightarrow> x \<le> 0 \<Longrightarrow> x + y \<in> HInfinite"
  for x y :: hypreal
  by (metis (no_types, lifting) HInfinite_add_ge_zero2 HInfinite_minus_iff add.inverse_distrib_swap neg_0_le_iff_le)

lemma HInfinite_add_lt_zero: "x \<in> HInfinite \<Longrightarrow> y < 0 \<Longrightarrow> x < 0 \<Longrightarrow> x + y \<in> HInfinite"
  for x y :: hypreal
  by (blast intro: HInfinite_add_le_zero order_less_imp_le)

lemma HFinite_sum_squares:
  "a \<in> HFinite \<Longrightarrow> b \<in> HFinite \<Longrightarrow> c \<in> HFinite \<Longrightarrow> a * a + b * b + c * c \<in> HFinite"
  for a b c :: "'a::real_normed_algebra star"
  by (auto intro: HFinite_mult HFinite_add)

lemma not_Infinitesimal_not_zero: "x \<notin> Infinitesimal \<Longrightarrow> x \<noteq> 0"
  by auto

lemma not_Infinitesimal_not_zero2: "x \<in> HFinite - Infinitesimal \<Longrightarrow> x \<noteq> 0"
  by auto

lemma HFinite_diff_Infinitesimal_hrabs:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> \<bar>x\<bar> \<in> HFinite - Infinitesimal"
  for x :: hypreal
  by blast

lemma hnorm_le_Infinitesimal: "e \<in> Infinitesimal \<Longrightarrow> hnorm x \<le> e \<Longrightarrow> x \<in> Infinitesimal"
  by (auto simp: Infinitesimal_def abs_less_iff)

lemma hnorm_less_Infinitesimal: "e \<in> Infinitesimal \<Longrightarrow> hnorm x < e \<Longrightarrow> x \<in> Infinitesimal"
  by (erule hnorm_le_Infinitesimal, erule order_less_imp_le)

lemma hrabs_le_Infinitesimal: "e \<in> Infinitesimal \<Longrightarrow> \<bar>x\<bar> \<le> e \<Longrightarrow> x \<in> Infinitesimal"
  for x :: hypreal
  by (erule hnorm_le_Infinitesimal) simp

lemma hrabs_less_Infinitesimal: "e \<in> Infinitesimal \<Longrightarrow> \<bar>x\<bar> < e \<Longrightarrow> x \<in> Infinitesimal"
  for x :: hypreal
  by (erule hnorm_less_Infinitesimal) simp

lemma Infinitesimal_interval:
  "e \<in> Infinitesimal \<Longrightarrow> e' \<in> Infinitesimal \<Longrightarrow> e' < x \<Longrightarrow> x < e \<Longrightarrow> x \<in> Infinitesimal"
  for x :: hypreal
  by (auto simp add: Infinitesimal_def abs_less_iff)

lemma Infinitesimal_interval2:
  "e \<in> Infinitesimal \<Longrightarrow> e' \<in> Infinitesimal \<Longrightarrow> e' \<le> x \<Longrightarrow> x \<le> e \<Longrightarrow> x \<in> Infinitesimal"
  for x :: hypreal
  by (auto intro: Infinitesimal_interval simp add: order_le_less)


lemma lemma_Infinitesimal_hyperpow: "x \<in> Infinitesimal \<Longrightarrow> 0 < N \<Longrightarrow> \<bar>x pow N\<bar> \<le> \<bar>x\<bar>"
  for x :: hypreal
  apply (clarsimp simp: Infinitesimal_def)
  by (metis Reals_1 abs_ge_zero hyperpow_Suc_le_self2 hyperpow_hrabs hypnat_gt_zero_iff2 zero_less_one)

lemma Infinitesimal_hyperpow: "x \<in> Infinitesimal \<Longrightarrow> 0 < N \<Longrightarrow> x pow N \<in> Infinitesimal"
  for x :: hypreal
  using hrabs_le_Infinitesimal lemma_Infinitesimal_hyperpow by blast

lemma hrealpow_hyperpow_Infinitesimal_iff:
  "(x ^ n \<in> Infinitesimal) \<longleftrightarrow> x pow (hypnat_of_nat n) \<in> Infinitesimal"
  by (simp only: hyperpow_hypnat_of_nat)

lemma Infinitesimal_hrealpow: "x \<in> Infinitesimal \<Longrightarrow> 0 < n \<Longrightarrow> x ^ n \<in> Infinitesimal"
  for x :: hypreal
  by (simp add: hrealpow_hyperpow_Infinitesimal_iff Infinitesimal_hyperpow)

lemma not_Infinitesimal_mult:
  "x \<notin> Infinitesimal \<Longrightarrow> y \<notin> Infinitesimal \<Longrightarrow> x * y \<notin> Infinitesimal"
  for x y :: "'a::real_normed_div_algebra star"
  by (metis (no_types, lifting) inverse_Infinitesimal_iff_HInfinite ComplI Compl_HFinite Infinitesimal_HFinite_mult divide_inverse eq_divide_imp inverse_inverse_eq mult_zero_right)

lemma Infinitesimal_mult_disj: "x * y \<in> Infinitesimal \<Longrightarrow> x \<in> Infinitesimal \<or> y \<in> Infinitesimal"
  for x y :: "'a::real_normed_div_algebra star"
  using not_Infinitesimal_mult by blast

lemma HFinite_Infinitesimal_not_zero: "x \<in> HFinite-Infinitesimal \<Longrightarrow> x \<noteq> 0"
  by blast

lemma HFinite_Infinitesimal_diff_mult:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> y \<in> HFinite - Infinitesimal \<Longrightarrow> x * y \<in> HFinite - Infinitesimal"
  for x y :: "'a::real_normed_div_algebra star"
  by (simp add: HFinite_mult not_Infinitesimal_mult)

lemma Infinitesimal_subset_HFinite: "Infinitesimal \<subseteq> HFinite"
  using HFinite_def InfinitesimalD Reals_1 zero_less_one by blast

lemma Infinitesimal_star_of_mult: "x \<in> Infinitesimal \<Longrightarrow> x * star_of r \<in> Infinitesimal"
  for x :: "'a::real_normed_algebra star"
  by (erule HFinite_star_of [THEN [2] Infinitesimal_HFinite_mult])

lemma Infinitesimal_star_of_mult2: "x \<in> Infinitesimal \<Longrightarrow> star_of r * x \<in> Infinitesimal"
  for x :: "'a::real_normed_algebra star"
  by (erule HFinite_star_of [THEN [2] Infinitesimal_HFinite_mult2])


subsection \<open>The Infinitely Close Relation\<close>

lemma mem_infmal_iff: "x \<in> Infinitesimal \<longleftrightarrow> x \<approx> 0"
  by (simp add: Infinitesimal_def approx_def)

lemma approx_minus_iff: "x \<approx> y \<longleftrightarrow> x - y \<approx> 0"
  by (simp add: approx_def)

lemma approx_minus_iff2: "x \<approx> y \<longleftrightarrow> - y + x \<approx> 0"
  by (simp add: approx_def add.commute)

lemma approx_refl [iff]: "x \<approx> x"
  by (simp add: approx_def Infinitesimal_def)

lemma approx_sym: "x \<approx> y \<Longrightarrow> y \<approx> x"
  by (metis Infinitesimal_minus_iff approx_def minus_diff_eq)

lemma approx_trans:
  assumes "x \<approx> y" "y \<approx> z" shows "x \<approx> z"
proof -
  have "x - y \<in> Infinitesimal" "z - y \<in> Infinitesimal"
    using assms approx_def approx_sym by auto
  then have "x - z \<in> Infinitesimal"
    using Infinitesimal_diff by force
  then show ?thesis
    by (simp add: approx_def)
qed

lemma approx_trans2: "r \<approx> x \<Longrightarrow> s \<approx> x \<Longrightarrow> r \<approx> s"
  by (blast intro: approx_sym approx_trans)

lemma approx_trans3: "x \<approx> r \<Longrightarrow> x \<approx> s \<Longrightarrow> r \<approx> s"
  by (blast intro: approx_sym approx_trans)

lemma approx_reorient: "x \<approx> y \<longleftrightarrow> y \<approx> x"
  by (blast intro: approx_sym)

text \<open>Reorientation simplification procedure: reorients (polymorphic)
  \<open>0 = x\<close>, \<open>1 = x\<close>, \<open>nnn = x\<close> provided \<open>x\<close> isn't \<open>0\<close>, \<open>1\<close> or a numeral.\<close>
simproc_setup approx_reorient_simproc
  ("0 \<approx> x" | "1 \<approx> y" | "numeral w \<approx> z" | "- 1 \<approx> y" | "- numeral w \<approx> r") =
\<open>
  let val rule = @{thm approx_reorient} RS eq_reflection
      fun proc phi ss ct =
        case Thm.term_of ct of
          _ $ t $ u => if can HOLogic.dest_number u then NONE
            else if can HOLogic.dest_number t then SOME rule else NONE
        | _ => NONE
  in proc end
\<close>

lemma Infinitesimal_approx_minus: "x - y \<in> Infinitesimal \<longleftrightarrow> x \<approx> y"
  by (simp add: approx_minus_iff [symmetric] mem_infmal_iff)

lemma approx_monad_iff: "x \<approx> y \<longleftrightarrow> monad x = monad y"
  apply (simp add: monad_def set_eq_iff)
  using approx_reorient approx_trans by blast

lemma Infinitesimal_approx: "x \<in> Infinitesimal \<Longrightarrow> y \<in> Infinitesimal \<Longrightarrow> x \<approx> y"
  by (simp add: Infinitesimal_diff approx_def)

lemma approx_add: "a \<approx> b \<Longrightarrow> c \<approx> d \<Longrightarrow> a + c \<approx> b + d"
proof (unfold approx_def)
  assume inf: "a - b \<in> Infinitesimal" "c - d \<in> Infinitesimal"
  have "a + c - (b + d) = (a - b) + (c - d)" by simp
  also have "... \<in> Infinitesimal"
    using inf by (rule Infinitesimal_add)
  finally show "a + c - (b + d) \<in> Infinitesimal" .
qed

lemma approx_minus: "a \<approx> b \<Longrightarrow> - a \<approx> - b"
  by (metis approx_def approx_sym minus_diff_eq minus_diff_minus)

lemma approx_minus2: "- a \<approx> - b \<Longrightarrow> a \<approx> b"
  by (auto dest: approx_minus)

lemma approx_minus_cancel [simp]: "- a \<approx> - b \<longleftrightarrow> a \<approx> b"
  by (blast intro: approx_minus approx_minus2)

lemma approx_add_minus: "a \<approx> b \<Longrightarrow> c \<approx> d \<Longrightarrow> a + - c \<approx> b + - d"
  by (blast intro!: approx_add approx_minus)

lemma approx_diff: "a \<approx> b \<Longrightarrow> c \<approx> d \<Longrightarrow> a - c \<approx> b - d"
  using approx_add [of a b "- c" "- d"] by simp

lemma approx_mult1: "a \<approx> b \<Longrightarrow> c \<in> HFinite \<Longrightarrow> a * c \<approx> b * c"
  for a b c :: "'a::real_normed_algebra star"
  by (simp add: approx_def Infinitesimal_HFinite_mult left_diff_distrib [symmetric])

lemma approx_mult2: "a \<approx> b \<Longrightarrow> c \<in> HFinite \<Longrightarrow> c * a \<approx> c * b"
  for a b c :: "'a::real_normed_algebra star"
  by (simp add: approx_def Infinitesimal_HFinite_mult2 right_diff_distrib [symmetric])

lemma approx_mult_subst: "u \<approx> v * x \<Longrightarrow> x \<approx> y \<Longrightarrow> v \<in> HFinite \<Longrightarrow> u \<approx> v * y"
  for u v x y :: "'a::real_normed_algebra star"
  by (blast intro: approx_mult2 approx_trans)

lemma approx_mult_subst2: "u \<approx> x * v \<Longrightarrow> x \<approx> y \<Longrightarrow> v \<in> HFinite \<Longrightarrow> u \<approx> y * v"
  for u v x y :: "'a::real_normed_algebra star"
  by (blast intro: approx_mult1 approx_trans)

lemma approx_mult_subst_star_of: "u \<approx> x * star_of v \<Longrightarrow> x \<approx> y \<Longrightarrow> u \<approx> y * star_of v"
  for u x y :: "'a::real_normed_algebra star"
  by (auto intro: approx_mult_subst2)

lemma approx_eq_imp: "a = b \<Longrightarrow> a \<approx> b"
  by (simp add: approx_def)

lemma Infinitesimal_minus_approx: "x \<in> Infinitesimal \<Longrightarrow> - x \<approx> x"
  by (blast intro: Infinitesimal_minus_iff [THEN iffD2] mem_infmal_iff [THEN iffD1] approx_trans2)

lemma bex_Infinitesimal_iff: "(\<exists>y \<in> Infinitesimal. x - z = y) \<longleftrightarrow> x \<approx> z"
  by (simp add: approx_def)

lemma bex_Infinitesimal_iff2: "(\<exists>y \<in> Infinitesimal. x = z + y) \<longleftrightarrow> x \<approx> z"
  by (force simp add: bex_Infinitesimal_iff [symmetric])

lemma Infinitesimal_add_approx: "y \<in> Infinitesimal \<Longrightarrow> x + y = z \<Longrightarrow> x \<approx> z"
  using approx_sym bex_Infinitesimal_iff2 by blast

lemma Infinitesimal_add_approx_self: "y \<in> Infinitesimal \<Longrightarrow> x \<approx> x + y"
  by (simp add: Infinitesimal_add_approx)

lemma Infinitesimal_add_approx_self2: "y \<in> Infinitesimal \<Longrightarrow> x \<approx> y + x"
  by (auto dest: Infinitesimal_add_approx_self simp add: add.commute)

lemma Infinitesimal_add_minus_approx_self: "y \<in> Infinitesimal \<Longrightarrow> x \<approx> x + - y"
  by (blast intro!: Infinitesimal_add_approx_self Infinitesimal_minus_iff [THEN iffD2])

lemma Infinitesimal_add_cancel: "y \<in> Infinitesimal \<Longrightarrow> x + y \<approx> z \<Longrightarrow> x \<approx> z"
  using Infinitesimal_add_approx approx_trans by blast

lemma Infinitesimal_add_right_cancel: "y \<in> Infinitesimal \<Longrightarrow> x \<approx> z + y \<Longrightarrow> x \<approx> z"
  by (metis Infinitesimal_add_approx_self approx_monad_iff)

lemma approx_add_left_cancel: "d + b \<approx> d + c \<Longrightarrow> b \<approx> c"
  by (metis add_diff_cancel_left bex_Infinitesimal_iff)

lemma approx_add_right_cancel: "b + d \<approx> c + d \<Longrightarrow> b \<approx> c"
  by (simp add: approx_def)

lemma approx_add_mono1: "b \<approx> c \<Longrightarrow> d + b \<approx> d + c"
  by (simp add: approx_add)

lemma approx_add_mono2: "b \<approx> c \<Longrightarrow> b + a \<approx> c + a"
  by (simp add: add.commute approx_add_mono1)

lemma approx_add_left_iff [simp]: "a + b \<approx> a + c \<longleftrightarrow> b \<approx> c"
  by (fast elim: approx_add_left_cancel approx_add_mono1)

lemma approx_add_right_iff [simp]: "b + a \<approx> c + a \<longleftrightarrow> b \<approx> c"
  by (simp add: add.commute)

lemma approx_HFinite: "x \<in> HFinite \<Longrightarrow> x \<approx> y \<Longrightarrow> y \<in> HFinite"
  by (metis HFinite_add Infinitesimal_subset_HFinite approx_sym subsetD bex_Infinitesimal_iff2)

lemma approx_star_of_HFinite: "x \<approx> star_of D \<Longrightarrow> x \<in> HFinite"
  by (rule approx_sym [THEN [2] approx_HFinite], auto)

lemma approx_mult_HFinite: "a \<approx> b \<Longrightarrow> c \<approx> d \<Longrightarrow> b \<in> HFinite \<Longrightarrow> d \<in> HFinite \<Longrightarrow> a * c \<approx> b * d"
  for a b c d :: "'a::real_normed_algebra star"
  by (meson approx_HFinite approx_mult2 approx_mult_subst2 approx_sym)

lemma scaleHR_left_diff_distrib: "\<And>a b x. scaleHR (a - b) x = scaleHR a x - scaleHR b x"
  by transfer (rule scaleR_left_diff_distrib)

lemma approx_scaleR1: "a \<approx> star_of b \<Longrightarrow> c \<in> HFinite \<Longrightarrow> scaleHR a c \<approx> b *\<^sub>R c"
  unfolding approx_def
  by (metis Infinitesimal_HFinite_scaleHR scaleHR_def scaleHR_left_diff_distrib star_scaleR_def starfun2_star_of)

lemma approx_scaleR2: "a \<approx> b \<Longrightarrow> c *\<^sub>R a \<approx> c *\<^sub>R b"
  by (simp add: approx_def Infinitesimal_scaleR2 scaleR_right_diff_distrib [symmetric])

lemma approx_scaleR_HFinite: "a \<approx> star_of b \<Longrightarrow> c \<approx> d \<Longrightarrow> d \<in> HFinite \<Longrightarrow> scaleHR a c \<approx> b *\<^sub>R d"
  by (meson approx_HFinite approx_scaleR1 approx_scaleR2 approx_sym approx_trans)

lemma approx_mult_star_of: "a \<approx> star_of b \<Longrightarrow> c \<approx> star_of d \<Longrightarrow> a * c \<approx> star_of b * star_of d"
  for a c :: "'a::real_normed_algebra star"
  by (blast intro!: approx_mult_HFinite approx_star_of_HFinite HFinite_star_of)

lemma approx_SReal_mult_cancel_zero:
  fixes a x :: hypreal
  assumes "a \<in> \<real>" "a \<noteq> 0" "a * x \<approx> 0" shows "x \<approx> 0"
proof -
  have "inverse a \<in> HFinite"
    using Reals_inverse SReal_subset_HFinite assms(1) by blast
  then show ?thesis
    using assms by (auto dest: approx_mult2 simp add: mult.assoc [symmetric])
qed

lemma approx_mult_SReal1: "a \<in> \<real> \<Longrightarrow> x \<approx> 0 \<Longrightarrow> x * a \<approx> 0"
  for a x :: hypreal
  by (auto dest: SReal_subset_HFinite [THEN subsetD] approx_mult1)

lemma approx_mult_SReal2: "a \<in> \<real> \<Longrightarrow> x \<approx> 0 \<Longrightarrow> a * x \<approx> 0"
  for a x :: hypreal
  by (auto dest: SReal_subset_HFinite [THEN subsetD] approx_mult2)

lemma approx_mult_SReal_zero_cancel_iff [simp]: "a \<in> \<real> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> a * x \<approx> 0 \<longleftrightarrow> x \<approx> 0"
  for a x :: hypreal
  by (blast intro: approx_SReal_mult_cancel_zero approx_mult_SReal2)

lemma approx_SReal_mult_cancel:
  fixes a w z :: hypreal
  assumes "a \<in> \<real>" "a \<noteq> 0" "a * w \<approx> a * z" shows "w \<approx> z"
proof -
  have "inverse a \<in> HFinite"
    using Reals_inverse SReal_subset_HFinite assms(1) by blast
  then show ?thesis
    using assms by (auto dest: approx_mult2 simp add: mult.assoc [symmetric])
qed

lemma approx_SReal_mult_cancel_iff1 [simp]: "a \<in> \<real> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> a * w \<approx> a * z \<longleftrightarrow> w \<approx> z"
  for a w z :: hypreal
  by (meson SReal_subset_HFinite approx_SReal_mult_cancel approx_mult2 subsetD)

lemma approx_le_bound:
  fixes z :: hypreal
  assumes "z \<le> f" " f \<approx> g" "g \<le> z" shows "f \<approx> z"
proof -
  obtain y where "z \<le> g + y" and "y \<in> Infinitesimal" "f = g + y"
    using assms bex_Infinitesimal_iff2 by auto
  then have "z - g \<in> Infinitesimal"
    using assms(3) hrabs_le_Infinitesimal by auto 
  then show ?thesis
    by (metis approx_def approx_trans2 assms(2))
qed

lemma approx_hnorm: "x \<approx> y \<Longrightarrow> hnorm x \<approx> hnorm y"
  for x y :: "'a::real_normed_vector star"
proof (unfold approx_def)
  assume "x - y \<in> Infinitesimal"
  then have "hnorm (x - y) \<in> Infinitesimal"
    by (simp only: Infinitesimal_hnorm_iff)
  moreover have "(0::real star) \<in> Infinitesimal"
    by (rule Infinitesimal_zero)
  moreover have "0 \<le> \<bar>hnorm x - hnorm y\<bar>"
    by (rule abs_ge_zero)
  moreover have "\<bar>hnorm x - hnorm y\<bar> \<le> hnorm (x - y)"
    by (rule hnorm_triangle_ineq3)
  ultimately have "\<bar>hnorm x - hnorm y\<bar> \<in> Infinitesimal"
    by (rule Infinitesimal_interval2)
  then show "hnorm x - hnorm y \<in> Infinitesimal"
    by (simp only: Infinitesimal_hrabs_iff)
qed


subsection \<open>Zero is the Only Infinitesimal that is also a Real\<close>

lemma Infinitesimal_less_SReal: "x \<in> \<real> \<Longrightarrow> y \<in> Infinitesimal \<Longrightarrow> 0 < x \<Longrightarrow> y < x"
  for x y :: hypreal
  using InfinitesimalD by fastforce

lemma Infinitesimal_less_SReal2: "y \<in> Infinitesimal \<Longrightarrow> \<forall>r \<in> Reals. 0 < r \<longrightarrow> y < r"
  for y :: hypreal
  by (blast intro: Infinitesimal_less_SReal)

lemma SReal_not_Infinitesimal: "0 < y \<Longrightarrow> y \<in> \<real> ==> y \<notin> Infinitesimal"
  for y :: hypreal
  by (auto simp add: Infinitesimal_def abs_if)

lemma SReal_minus_not_Infinitesimal: "y < 0 \<Longrightarrow> y \<in> \<real> \<Longrightarrow> y \<notin> Infinitesimal"
  for y :: hypreal
  using Infinitesimal_minus_iff Reals_minus SReal_not_Infinitesimal neg_0_less_iff_less by blast

lemma SReal_Int_Infinitesimal_zero: "\<real> Int Infinitesimal = {0::hypreal}"
  proof -
  have "x = 0" if "x \<in> \<real>" "x \<in> Infinitesimal" for x :: "real star"
    using that SReal_minus_not_Infinitesimal SReal_not_Infinitesimal not_less_iff_gr_or_eq by blast
  then show ?thesis
    by auto
qed

lemma SReal_Infinitesimal_zero: "x \<in> \<real> \<Longrightarrow> x \<in> Infinitesimal \<Longrightarrow> x = 0"
  for x :: hypreal
  using SReal_Int_Infinitesimal_zero by blast

lemma SReal_HFinite_diff_Infinitesimal: "x \<in> \<real> \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> x \<in> HFinite - Infinitesimal"
  for x :: hypreal
  by (auto dest: SReal_Infinitesimal_zero SReal_subset_HFinite [THEN subsetD])

lemma hypreal_of_real_HFinite_diff_Infinitesimal:
  "hypreal_of_real x \<noteq> 0 \<Longrightarrow> hypreal_of_real x \<in> HFinite - Infinitesimal"
  by (rule SReal_HFinite_diff_Infinitesimal) auto

lemma star_of_Infinitesimal_iff_0 [iff]: "star_of x \<in> Infinitesimal \<longleftrightarrow> x = 0"
proof
  show "x = 0" if "star_of x \<in> Infinitesimal"
  proof -
    have "hnorm (star_n (\<lambda>n. x)) \<in> Standard"
      by (metis Reals_eq_Standard SReal_iff star_of_def star_of_norm)
    then show ?thesis
      by (metis InfinitesimalD2 less_irrefl star_of_norm that zero_less_norm_iff)
  qed
qed auto

lemma star_of_HFinite_diff_Infinitesimal: "x \<noteq> 0 \<Longrightarrow> star_of x \<in> HFinite - Infinitesimal"
  by simp

lemma numeral_not_Infinitesimal [simp]:
  "numeral w \<noteq> (0::hypreal) \<Longrightarrow> (numeral w :: hypreal) \<notin> Infinitesimal"
  by (fast dest: Reals_numeral [THEN SReal_Infinitesimal_zero])

text \<open>Again: \<open>1\<close> is a special case, but not \<open>0\<close> this time.\<close>
lemma one_not_Infinitesimal [simp]:
  "(1::'a::{real_normed_vector,zero_neq_one} star) \<notin> Infinitesimal"
  by (metis star_of_Infinitesimal_iff_0 star_one_def zero_neq_one)

lemma approx_SReal_not_zero: "y \<in> \<real> \<Longrightarrow> x \<approx> y \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x \<noteq> 0"
  for x y :: hypreal
  using SReal_Infinitesimal_zero approx_sym mem_infmal_iff by auto

lemma HFinite_diff_Infinitesimal_approx:
  "x \<approx> y \<Longrightarrow> y \<in> HFinite - Infinitesimal \<Longrightarrow> x \<in> HFinite - Infinitesimal"
  by (meson Diff_iff approx_HFinite approx_sym approx_trans3 mem_infmal_iff)

text \<open>The premise \<open>y \<noteq> 0\<close> is essential; otherwise \<open>x / y = 0\<close> and we lose the
  \<open>HFinite\<close> premise.\<close>
lemma Infinitesimal_ratio:
  "y \<noteq> 0 \<Longrightarrow> y \<in> Infinitesimal \<Longrightarrow> x / y \<in> HFinite \<Longrightarrow> x \<in> Infinitesimal"
  for x y :: "'a::{real_normed_div_algebra,field} star"
  using Infinitesimal_HFinite_mult by fastforce

lemma Infinitesimal_SReal_divide: "x \<in> Infinitesimal \<Longrightarrow> y \<in> \<real> \<Longrightarrow> x / y \<in> Infinitesimal"
  for x y :: hypreal
  by (metis HFinite_star_of Infinitesimal_HFinite_mult Reals_inverse SReal_iff divide_inverse)


section \<open>Standard Part Theorem\<close>

text \<open>
  Every finite \<open>x \<in> R*\<close> is infinitely close to a unique real number
  (i.e. a member of \<open>Reals\<close>).
\<close>


subsection \<open>Uniqueness: Two Infinitely Close Reals are Equal\<close>

lemma star_of_approx_iff [simp]: "star_of x \<approx> star_of y \<longleftrightarrow> x = y"
  by (metis approx_def right_minus_eq star_of_Infinitesimal_iff_0 star_of_simps(2))

lemma SReal_approx_iff: "x \<in> \<real> \<Longrightarrow> y \<in> \<real> \<Longrightarrow> x \<approx> y \<longleftrightarrow> x = y"
  for x y :: hypreal
  by (meson Reals_diff SReal_Infinitesimal_zero approx_def approx_refl right_minus_eq)

lemma numeral_approx_iff [simp]:
  "(numeral v \<approx> (numeral w :: 'a::{numeral,real_normed_vector} star)) = (numeral v = (numeral w :: 'a))"
  by (metis star_of_approx_iff star_of_numeral)

text \<open>And also for \<open>0 \<approx> #nn\<close> and \<open>1 \<approx> #nn\<close>, \<open>#nn \<approx> 0\<close> and \<open>#nn \<approx> 1\<close>.\<close>
lemma [simp]:
  "(numeral w \<approx> (0::'a::{numeral,real_normed_vector} star)) = (numeral w = (0::'a))"
  "((0::'a::{numeral,real_normed_vector} star) \<approx> numeral w) = (numeral w = (0::'a))"
  "(numeral w \<approx> (1::'b::{numeral,one,real_normed_vector} star)) = (numeral w = (1::'b))"
  "((1::'b::{numeral,one,real_normed_vector} star) \<approx> numeral w) = (numeral w = (1::'b))"
  "\<not> (0 \<approx> (1::'c::{zero_neq_one,real_normed_vector} star))"
  "\<not> (1 \<approx> (0::'c::{zero_neq_one,real_normed_vector} star))"
  unfolding star_numeral_def star_zero_def star_one_def star_of_approx_iff
  by (auto intro: sym)

lemma star_of_approx_numeral_iff [simp]: "star_of k \<approx> numeral w \<longleftrightarrow> k = numeral w"
  by (subst star_of_approx_iff [symmetric]) auto

lemma star_of_approx_zero_iff [simp]: "star_of k \<approx> 0 \<longleftrightarrow> k = 0"
  by (simp_all add: star_of_approx_iff [symmetric])

lemma star_of_approx_one_iff [simp]: "star_of k \<approx> 1 \<longleftrightarrow> k = 1"
  by (simp_all add: star_of_approx_iff [symmetric])

lemma approx_unique_real: "r \<in> \<real> \<Longrightarrow> s \<in> \<real> \<Longrightarrow> r \<approx> x \<Longrightarrow> s \<approx> x \<Longrightarrow> r = s"
  for r s :: hypreal
  by (blast intro: SReal_approx_iff [THEN iffD1] approx_trans2)


subsection \<open>Existence of Unique Real Infinitely Close\<close>

subsubsection \<open>Lifting of the Ub and Lub Properties\<close>

lemma hypreal_of_real_isUb_iff: "isUb \<real> (hypreal_of_real ` Q) (hypreal_of_real Y) = isUb UNIV Q Y"
  for Q :: "real set" and Y :: real
  by (simp add: isUb_def setle_def)

lemma hypreal_of_real_isLub_iff:
  "isLub \<real> (hypreal_of_real ` Q) (hypreal_of_real Y) = isLub (UNIV :: real set) Q Y" (is "?lhs = ?rhs")
  for Q :: "real set" and Y :: real
proof 
  assume ?lhs
  then show ?rhs
    by (simp add: isLub_def leastP_def) (metis hypreal_of_real_isUb_iff mem_Collect_eq setge_def star_of_le)
next
  assume ?rhs
  then show ?lhs
  apply (simp add: isLub_def leastP_def hypreal_of_real_isUb_iff setge_def)
    by (metis SReal_iff hypreal_of_real_isUb_iff isUb_def star_of_le)
qed

lemma lemma_isUb_hypreal_of_real: "isUb \<real> P Y \<Longrightarrow> \<exists>Yo. isUb \<real> P (hypreal_of_real Yo)"
  by (auto simp add: SReal_iff isUb_def)

lemma lemma_isLub_hypreal_of_real: "isLub \<real> P Y \<Longrightarrow> \<exists>Yo. isLub \<real> P (hypreal_of_real Yo)"
  by (auto simp add: isLub_def leastP_def isUb_def SReal_iff)

lemma SReal_complete:
  fixes P :: "hypreal set"
  assumes "isUb \<real> P Y" "P \<subseteq> \<real>" "P \<noteq> {}"
    shows "\<exists>t. isLub \<real> P t"
proof -
  obtain Q where "P = hypreal_of_real ` Q"
    by (metis \<open>P \<subseteq> \<real>\<close> hypreal_of_real_image subset_imageE)
  then show ?thesis
    by (metis assms(1) \<open>P \<noteq> {}\<close> equals0I hypreal_of_real_isLub_iff hypreal_of_real_isUb_iff image_empty lemma_isUb_hypreal_of_real reals_complete)
qed


text \<open>Lemmas about lubs.\<close>

lemma lemma_st_part_lub:
  fixes x :: hypreal
  assumes "x \<in> HFinite"
  shows "\<exists>t. isLub \<real> {s. s \<in> \<real> \<and> s < x} t"
proof -
  obtain t where t: "t \<in> \<real>" "hnorm x < t"
    using HFiniteD assms by blast
  then have "isUb \<real> {s. s \<in> \<real> \<and> s < x} t"
    by (simp add: abs_less_iff isUbI le_less_linear less_imp_not_less setleI)
  moreover have "\<exists>y. y \<in> \<real> \<and> y < x"
    using t by (rule_tac x = "-t" in exI) (auto simp add: abs_less_iff)
  ultimately show ?thesis
    using SReal_complete by fastforce
qed

lemma lemma_st_part_le1:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> x \<le> t + r"
  for x r t :: hypreal
  by (metis (no_types, lifting) Reals_add add.commute isLubD1a isLubD2 less_add_same_cancel2 mem_Collect_eq not_le)

lemma hypreal_setle_less_trans: "S *<= x \<Longrightarrow> x < y \<Longrightarrow> S *<= y"
  for x y :: hypreal
  by (meson le_less_trans less_imp_le setle_def)

lemma hypreal_gt_isUb: "isUb R S x \<Longrightarrow> x < y \<Longrightarrow> y \<in> R \<Longrightarrow> isUb R S y"
  for x y :: hypreal
  using hypreal_setle_less_trans isUb_def by blast

lemma lemma_st_part_gt_ub: "x \<in> HFinite \<Longrightarrow> x < y \<Longrightarrow> y \<in> \<real> \<Longrightarrow> isUb \<real> {s. s \<in> \<real> \<and> s < x} y"
  for x y :: hypreal
  by (auto dest: order_less_trans intro: order_less_imp_le intro!: isUbI setleI)

lemma lemma_minus_le_zero: "t \<le> t + -r \<Longrightarrow> r \<le> 0"
  for r t :: hypreal
  by simp

lemma lemma_st_part_le2:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> t + -r \<le> x"
  for x r t :: hypreal
  apply (frule isLubD1a)
  apply (rule ccontr, drule linorder_not_le [THEN iffD1])
  apply (drule Reals_minus, drule_tac a = t in Reals_add, assumption)
  apply (drule lemma_st_part_gt_ub, assumption+)
  apply (drule isLub_le_isUb, assumption)
  apply (drule lemma_minus_le_zero)
  apply (auto dest: order_less_le_trans)
  done

lemma lemma_st_part1a:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> x + -t \<le> r"
  for x r t :: hypreal
  using lemma_st_part_le1 by fastforce

lemma lemma_st_part2a:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> - (x + -t) \<le> r"
  for x r t :: hypreal
  apply (subgoal_tac "(t + -r \<le> x)")
   apply simp
  apply (rule lemma_st_part_le2)
     apply auto
  done

lemma lemma_SReal_ub: "x \<in> \<real> \<Longrightarrow> isUb \<real> {s. s \<in> \<real> \<and> s < x} x"
  for x :: hypreal
  by (auto intro: isUbI setleI order_less_imp_le)

lemma lemma_SReal_lub: "x \<in> \<real> \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} x"
  for x :: hypreal
  apply (auto intro!: isLubI2 lemma_SReal_ub setgeI)
  apply (frule isUbD2a)
  apply (rule_tac x = x and y = y in linorder_cases)
    apply (auto intro!: order_less_imp_le)
  apply (drule SReal_dense, assumption, assumption, safe)
  apply (drule_tac y = r in isUbD)
   apply (auto dest: order_less_le_trans)
  done

lemma lemma_st_part_not_eq1:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> x + - t \<noteq> r"
  for x r t :: hypreal
  apply auto
  apply (frule isLubD1a [THEN Reals_minus])
  using Reals_add_cancel [of x "- t"] apply simp
  apply (drule_tac x = x in lemma_SReal_lub)
  apply (drule isLub_unique, assumption, auto)
  done

lemma lemma_st_part_not_eq2:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> - (x + -t) \<noteq> r"
  for x r t :: hypreal
  apply (auto)
  apply (frule isLubD1a)
  using Reals_add_cancel [of "- x" t] apply simp
  apply (drule_tac x = x in lemma_SReal_lub)
  apply (drule isLub_unique, assumption, auto)
  done

lemma lemma_st_part_major:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> r \<in> \<real> \<Longrightarrow> 0 < r \<Longrightarrow> \<bar>x - t\<bar> < r"
  for x r t :: hypreal
  apply (frule lemma_st_part1a)
     apply (frule_tac [4] lemma_st_part2a, auto)
  apply (drule order_le_imp_less_or_eq)+
  apply auto
  using lemma_st_part_not_eq2 apply fastforce
  using lemma_st_part_not_eq1 apply fastforce
  done

lemma lemma_st_part_major2:
  "x \<in> HFinite \<Longrightarrow> isLub \<real> {s. s \<in> \<real> \<and> s < x} t \<Longrightarrow> \<forall>r \<in> Reals. 0 < r \<longrightarrow> \<bar>x - t\<bar> < r"
  for x t :: hypreal
  by (blast dest!: lemma_st_part_major)


text\<open>Existence of real and Standard Part Theorem.\<close>

lemma lemma_st_part_Ex: "x \<in> HFinite \<Longrightarrow> \<exists>t\<in>Reals. \<forall>r \<in> Reals. 0 < r \<longrightarrow> \<bar>x - t\<bar> < r"
  for x :: hypreal
  by (meson isLubD1a lemma_st_part_lub lemma_st_part_major2)

lemma st_part_Ex: "x \<in> HFinite \<Longrightarrow> \<exists>t\<in>Reals. x \<approx> t"
  for x :: hypreal
  by (metis InfinitesimalI approx_def hypreal_hnorm_def lemma_st_part_Ex)

text \<open>There is a unique real infinitely close.\<close>
lemma st_part_Ex1: "x \<in> HFinite \<Longrightarrow> \<exists>!t::hypreal. t \<in> \<real> \<and> x \<approx> t"
  by (meson SReal_approx_iff approx_trans2 st_part_Ex)


subsection \<open>Finite, Infinite and Infinitesimal\<close>

lemma HFinite_Int_HInfinite_empty [simp]: "HFinite Int HInfinite = {}"
  using Compl_HFinite by blast

lemma HFinite_not_HInfinite:
  assumes x: "x \<in> HFinite" shows "x \<notin> HInfinite"
  using Compl_HFinite x by blast

lemma not_HFinite_HInfinite: "x \<notin> HFinite \<Longrightarrow> x \<in> HInfinite"
  using Compl_HFinite by blast

lemma HInfinite_HFinite_disj: "x \<in> HInfinite \<or> x \<in> HFinite"
  by (blast intro: not_HFinite_HInfinite)

lemma HInfinite_HFinite_iff: "x \<in> HInfinite \<longleftrightarrow> x \<notin> HFinite"
  by (blast dest: HFinite_not_HInfinite not_HFinite_HInfinite)

lemma HFinite_HInfinite_iff: "x \<in> HFinite \<longleftrightarrow> x \<notin> HInfinite"
  by (simp add: HInfinite_HFinite_iff)

lemma HInfinite_diff_HFinite_Infinitesimal_disj:
  "x \<notin> Infinitesimal \<Longrightarrow> x \<in> HInfinite \<or> x \<in> HFinite - Infinitesimal"
  by (fast intro: not_HFinite_HInfinite)

lemma HFinite_inverse: "x \<in> HFinite \<Longrightarrow> x \<notin> Infinitesimal \<Longrightarrow> inverse x \<in> HFinite"
  for x :: "'a::real_normed_div_algebra star"
  using HInfinite_inverse_Infinitesimal not_HFinite_HInfinite by force

lemma HFinite_inverse2: "x \<in> HFinite - Infinitesimal \<Longrightarrow> inverse x \<in> HFinite"
  for x :: "'a::real_normed_div_algebra star"
  by (blast intro: HFinite_inverse)

text \<open>Stronger statement possible in fact.\<close>
lemma Infinitesimal_inverse_HFinite: "x \<notin> Infinitesimal \<Longrightarrow> inverse x \<in> HFinite"
  for x :: "'a::real_normed_div_algebra star"
  using HFinite_HInfinite_iff HInfinite_inverse_Infinitesimal by fastforce

lemma HFinite_not_Infinitesimal_inverse:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> inverse x \<in> HFinite - Infinitesimal"
  for x :: "'a::real_normed_div_algebra star"
  using HFinite_Infinitesimal_not_zero HFinite_inverse2 Infinitesimal_HFinite_mult2 by fastforce

lemma approx_inverse: "x \<approx> y \<Longrightarrow> y \<in> HFinite - Infinitesimal \<Longrightarrow> inverse x \<approx> inverse y"
  for x y :: "'a::real_normed_div_algebra star"
  apply (frule HFinite_diff_Infinitesimal_approx, assumption)
  apply (frule not_Infinitesimal_not_zero2)
  apply (frule_tac x = x in not_Infinitesimal_not_zero2)
  apply (drule HFinite_inverse2)+
  apply (drule approx_mult2, assumption, auto)
  apply (drule_tac c = "inverse x" in approx_mult1, assumption)
  apply (auto intro: approx_sym simp add: mult.assoc)
  done

(*Used for NSLIM_inverse, NSLIMSEQ_inverse*)
lemmas star_of_approx_inverse = star_of_HFinite_diff_Infinitesimal [THEN [2] approx_inverse]
lemmas hypreal_of_real_approx_inverse =  hypreal_of_real_HFinite_diff_Infinitesimal [THEN [2] approx_inverse]

lemma inverse_add_Infinitesimal_approx:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> h \<in> Infinitesimal \<Longrightarrow> inverse (x + h) \<approx> inverse x"
  for x h :: "'a::real_normed_div_algebra star"
  by (auto intro: approx_inverse approx_sym Infinitesimal_add_approx_self)

lemma inverse_add_Infinitesimal_approx2:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> h \<in> Infinitesimal \<Longrightarrow> inverse (h + x) \<approx> inverse x"
  for x h :: "'a::real_normed_div_algebra star"
  by (metis add.commute inverse_add_Infinitesimal_approx)

lemma inverse_add_Infinitesimal_approx_Infinitesimal:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> h \<in> Infinitesimal \<Longrightarrow> inverse (x + h) - inverse x \<approx> h"
  for x h :: "'a::real_normed_div_algebra star"
  by (meson Infinitesimal_approx bex_Infinitesimal_iff inverse_add_Infinitesimal_approx)

lemma Infinitesimal_square_iff: "x \<in> Infinitesimal \<longleftrightarrow> x * x \<in> Infinitesimal"
  for x :: "'a::real_normed_div_algebra star"
  using Infinitesimal_mult Infinitesimal_mult_disj by auto
declare Infinitesimal_square_iff [symmetric, simp]

lemma HFinite_square_iff [simp]: "x * x \<in> HFinite \<longleftrightarrow> x \<in> HFinite"
  for x :: "'a::real_normed_div_algebra star"
  using HFinite_HInfinite_iff HFinite_mult HInfinite_mult by blast

lemma HInfinite_square_iff [simp]: "x * x \<in> HInfinite \<longleftrightarrow> x \<in> HInfinite"
  for x :: "'a::real_normed_div_algebra star"
  by (auto simp add: HInfinite_HFinite_iff)

lemma approx_HFinite_mult_cancel: "a \<in> HFinite - Infinitesimal \<Longrightarrow> a * w \<approx> a * z \<Longrightarrow> w \<approx> z"
  for a w z :: "'a::real_normed_div_algebra star"
  by (metis DiffD2 Infinitesimal_mult_disj bex_Infinitesimal_iff right_diff_distrib)

lemma approx_HFinite_mult_cancel_iff1: "a \<in> HFinite - Infinitesimal \<Longrightarrow> a * w \<approx> a * z \<longleftrightarrow> w \<approx> z"
  for a w z :: "'a::real_normed_div_algebra star"
  by (auto intro: approx_mult2 approx_HFinite_mult_cancel)

lemma HInfinite_HFinite_add_cancel: "x + y \<in> HInfinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> x \<in> HInfinite"
  using HFinite_add HInfinite_HFinite_iff by blast

lemma HInfinite_HFinite_add: "x \<in> HInfinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> x + y \<in> HInfinite"
  by (metis (no_types, hide_lams) HFinite_HInfinite_iff HFinite_add HFinite_minus_iff add.commute add_minus_cancel)

lemma HInfinite_ge_HInfinite: "x \<in> HInfinite \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> x \<Longrightarrow> y \<in> HInfinite"
  for x y :: hypreal
  by (auto intro: HFinite_bounded simp add: HInfinite_HFinite_iff)

lemma Infinitesimal_inverse_HInfinite: "x \<in> Infinitesimal \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse x \<in> HInfinite"
  for x :: "'a::real_normed_div_algebra star"
  by (metis Infinitesimal_HFinite_mult not_HFinite_HInfinite one_not_Infinitesimal right_inverse)

lemma HInfinite_HFinite_not_Infinitesimal_mult:
  "x \<in> HInfinite \<Longrightarrow> y \<in> HFinite - Infinitesimal \<Longrightarrow> x * y \<in> HInfinite"
  for x y :: "'a::real_normed_div_algebra star"
  by (metis (no_types, hide_lams) HFinite_HInfinite_iff HFinite_Infinitesimal_not_zero HFinite_inverse2 HFinite_mult mult.assoc mult.right_neutral right_inverse)

lemma HInfinite_HFinite_not_Infinitesimal_mult2:
  "x \<in> HInfinite \<Longrightarrow> y \<in> HFinite - Infinitesimal \<Longrightarrow> y * x \<in> HInfinite"
  for x y :: "'a::real_normed_div_algebra star"
  by (metis Diff_iff HInfinite_HFinite_iff HInfinite_inverse_Infinitesimal Infinitesimal_HFinite_mult2 divide_inverse mult_zero_right nonzero_eq_divide_eq)

lemma HInfinite_gt_SReal: "x \<in> HInfinite \<Longrightarrow> 0 < x \<Longrightarrow> y \<in> \<real> \<Longrightarrow> y < x"
  for x y :: hypreal
  by (auto dest!: bspec simp add: HInfinite_def abs_if order_less_imp_le)

lemma HInfinite_gt_zero_gt_one: "x \<in> HInfinite \<Longrightarrow> 0 < x \<Longrightarrow> 1 < x"
  for x :: hypreal
  by (auto intro: HInfinite_gt_SReal)

lemma not_HInfinite_one [simp]: "1 \<notin> HInfinite"
  by (simp add: HInfinite_HFinite_iff)

lemma approx_hrabs_disj: "\<bar>x\<bar> \<approx> x \<or> \<bar>x\<bar> \<approx> -x"
  for x :: hypreal
  using hrabs_disj [of x] by auto


subsection \<open>Theorems about Monads\<close>

lemma monad_hrabs_Un_subset: "monad \<bar>x\<bar> \<le> monad x \<union> monad (- x)"
  for x :: hypreal
  by (rule hrabs_disj [of x, THEN disjE]) auto

lemma Infinitesimal_monad_eq: "e \<in> Infinitesimal \<Longrightarrow> monad (x + e) = monad x"
  by (fast intro!: Infinitesimal_add_approx_self [THEN approx_sym] approx_monad_iff [THEN iffD1])

lemma mem_monad_iff: "u \<in> monad x \<longleftrightarrow> - u \<in> monad (- x)"
  by (simp add: monad_def)

lemma Infinitesimal_monad_zero_iff: "x \<in> Infinitesimal \<longleftrightarrow> x \<in> monad 0"
  by (auto intro: approx_sym simp add: monad_def mem_infmal_iff)

lemma monad_zero_minus_iff: "x \<in> monad 0 \<longleftrightarrow> - x \<in> monad 0"
  by (simp add: Infinitesimal_monad_zero_iff [symmetric])

lemma monad_zero_hrabs_iff: "x \<in> monad 0 \<longleftrightarrow> \<bar>x\<bar> \<in> monad 0"
  for x :: hypreal
  by (rule hrabs_disj [of x, THEN disjE]) (auto simp: monad_zero_minus_iff [symmetric])

lemma mem_monad_self [simp]: "x \<in> monad x"
  by (simp add: monad_def)


subsection \<open>Proof that \<^term>\<open>x \<approx> y\<close> implies \<^term>\<open>\<bar>x\<bar> \<approx> \<bar>y\<bar>\<close>\<close>

lemma approx_subset_monad: "x \<approx> y \<Longrightarrow> {x, y} \<le> monad x"
  by (simp (no_asm)) (simp add: approx_monad_iff)

lemma approx_subset_monad2: "x \<approx> y \<Longrightarrow> {x, y} \<le> monad y"
  using approx_subset_monad approx_sym by auto

lemma mem_monad_approx: "u \<in> monad x \<Longrightarrow> x \<approx> u"
  by (simp add: monad_def)

lemma approx_mem_monad: "x \<approx> u \<Longrightarrow> u \<in> monad x"
  by (simp add: monad_def)

lemma approx_mem_monad2: "x \<approx> u \<Longrightarrow> x \<in> monad u"
  using approx_mem_monad approx_sym by blast

lemma approx_mem_monad_zero: "x \<approx> y \<Longrightarrow> x \<in> monad 0 \<Longrightarrow> y \<in> monad 0"
  using approx_trans monad_def by blast

lemma Infinitesimal_approx_hrabs: "x \<approx> y \<Longrightarrow> x \<in> Infinitesimal \<Longrightarrow> \<bar>x\<bar> \<approx> \<bar>y\<bar>"
  for x y :: hypreal
  using approx_hnorm by fastforce

lemma less_Infinitesimal_less: "0 < x \<Longrightarrow> x \<notin> Infinitesimal \<Longrightarrow> e \<in> Infinitesimal \<Longrightarrow> e < x"
  for x :: hypreal
  using Infinitesimal_interval less_linear by blast

lemma Ball_mem_monad_gt_zero: "0 < x \<Longrightarrow> x \<notin> Infinitesimal \<Longrightarrow> u \<in> monad x \<Longrightarrow> 0 < u"
  for u x :: hypreal
  apply (drule mem_monad_approx [THEN approx_sym])
  apply (erule bex_Infinitesimal_iff2 [THEN iffD2, THEN bexE])
  apply (drule_tac e = "-xa" in less_Infinitesimal_less, auto)
  done

lemma Ball_mem_monad_less_zero: "x < 0 \<Longrightarrow> x \<notin> Infinitesimal \<Longrightarrow> u \<in> monad x \<Longrightarrow> u < 0"
  for u x :: hypreal
  apply (drule mem_monad_approx [THEN approx_sym])
  apply (erule bex_Infinitesimal_iff [THEN iffD2, THEN bexE])
  apply (cut_tac x = "-x" and e = xa in less_Infinitesimal_less, auto)
  done

lemma lemma_approx_gt_zero: "0 < x \<Longrightarrow> x \<notin> Infinitesimal \<Longrightarrow> x \<approx> y \<Longrightarrow> 0 < y"
  for x y :: hypreal
  by (blast dest: Ball_mem_monad_gt_zero approx_subset_monad)

lemma lemma_approx_less_zero: "x < 0 \<Longrightarrow> x \<notin> Infinitesimal \<Longrightarrow> x \<approx> y \<Longrightarrow> y < 0"
  for x y :: hypreal
  by (blast dest: Ball_mem_monad_less_zero approx_subset_monad)

lemma approx_hrabs: "x \<approx> y \<Longrightarrow> \<bar>x\<bar> \<approx> \<bar>y\<bar>"
  for x y :: hypreal
  by (drule approx_hnorm) simp

lemma approx_hrabs_zero_cancel: "\<bar>x\<bar> \<approx> 0 \<Longrightarrow> x \<approx> 0"
  for x :: hypreal
  using hrabs_disj [of x] by (auto dest: approx_minus)

lemma approx_hrabs_add_Infinitesimal: "e \<in> Infinitesimal \<Longrightarrow> \<bar>x\<bar> \<approx> \<bar>x + e\<bar>"
  for e x :: hypreal
  by (fast intro: approx_hrabs Infinitesimal_add_approx_self)

lemma approx_hrabs_add_minus_Infinitesimal: "e \<in> Infinitesimal ==> \<bar>x\<bar> \<approx> \<bar>x + -e\<bar>"
  for e x :: hypreal
  by (fast intro: approx_hrabs Infinitesimal_add_minus_approx_self)

lemma hrabs_add_Infinitesimal_cancel:
  "e \<in> Infinitesimal \<Longrightarrow> e' \<in> Infinitesimal \<Longrightarrow> \<bar>x + e\<bar> = \<bar>y + e'\<bar> \<Longrightarrow> \<bar>x\<bar> \<approx> \<bar>y\<bar>"
  for e e' x y :: hypreal
  by (metis approx_hrabs_add_Infinitesimal approx_trans2)

lemma hrabs_add_minus_Infinitesimal_cancel:
  "e \<in> Infinitesimal \<Longrightarrow> e' \<in> Infinitesimal \<Longrightarrow> \<bar>x + -e\<bar> = \<bar>y + -e'\<bar> \<Longrightarrow> \<bar>x\<bar> \<approx> \<bar>y\<bar>"
  for e e' x y :: hypreal
  by (meson Infinitesimal_minus_iff hrabs_add_Infinitesimal_cancel)


subsection \<open>More \<^term>\<open>HFinite\<close> and \<^term>\<open>Infinitesimal\<close> Theorems\<close>

text \<open>
  Interesting slightly counterintuitive theorem: necessary
  for proving that an open interval is an NS open set.
\<close>
lemma Infinitesimal_add_hypreal_of_real_less:
  "x < y \<Longrightarrow> u \<in> Infinitesimal \<Longrightarrow> hypreal_of_real x + u < hypreal_of_real y"
  apply (simp add: Infinitesimal_def)
  apply (drule_tac x = "hypreal_of_real y + -hypreal_of_real x" in bspec, simp)
  apply (simp add: abs_less_iff)
  done

lemma Infinitesimal_add_hrabs_hypreal_of_real_less:
  "x \<in> Infinitesimal \<Longrightarrow> \<bar>hypreal_of_real r\<bar> < hypreal_of_real y \<Longrightarrow>
    \<bar>hypreal_of_real r + x\<bar> < hypreal_of_real y"
  apply (drule_tac x = "hypreal_of_real r" in approx_hrabs_add_Infinitesimal)
  apply (drule approx_sym [THEN bex_Infinitesimal_iff2 [THEN iffD2]])
  apply (auto intro!: Infinitesimal_add_hypreal_of_real_less
      simp del: star_of_abs simp add: star_of_abs [symmetric])
  done

lemma Infinitesimal_add_hrabs_hypreal_of_real_less2:
  "x \<in> Infinitesimal \<Longrightarrow> \<bar>hypreal_of_real r\<bar> < hypreal_of_real y \<Longrightarrow>
    \<bar>x + hypreal_of_real r\<bar> < hypreal_of_real y"
  using Infinitesimal_add_hrabs_hypreal_of_real_less by fastforce

lemma hypreal_of_real_le_add_Infininitesimal_cancel:
  "u \<in> Infinitesimal \<Longrightarrow> v \<in> Infinitesimal \<Longrightarrow>
    hypreal_of_real x + u \<le> hypreal_of_real y + v \<Longrightarrow>
    hypreal_of_real x \<le> hypreal_of_real y"
  apply (simp add: linorder_not_less [symmetric], auto)
  apply (drule_tac u = "v-u" in Infinitesimal_add_hypreal_of_real_less)
   apply (auto simp add: Infinitesimal_diff)
  done

lemma hypreal_of_real_le_add_Infininitesimal_cancel2:
  "u \<in> Infinitesimal \<Longrightarrow> v \<in> Infinitesimal \<Longrightarrow>
    hypreal_of_real x + u \<le> hypreal_of_real y + v \<Longrightarrow> x \<le> y"
  by (blast intro: star_of_le [THEN iffD1] intro!: hypreal_of_real_le_add_Infininitesimal_cancel)

lemma hypreal_of_real_less_Infinitesimal_le_zero:
  "hypreal_of_real x < e \<Longrightarrow> e \<in> Infinitesimal \<Longrightarrow> hypreal_of_real x \<le> 0"
  by (metis Infinitesimal_interval eq_iff le_less_linear star_of_Infinitesimal_iff_0 star_of_eq_0)

(*used once, in Lim/NSDERIV_inverse*)
lemma Infinitesimal_add_not_zero: "h \<in> Infinitesimal \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> star_of x + h \<noteq> 0"
  apply auto
  apply (subgoal_tac "h = - star_of x")
   apply (auto intro: minus_unique [symmetric])
  done

lemma Infinitesimal_square_cancel [simp]: "x * x + y * y \<in> Infinitesimal \<Longrightarrow> x * x \<in> Infinitesimal"
  for x y :: hypreal
  by (meson Infinitesimal_interval2 le_add_same_cancel1 not_Infinitesimal_not_zero zero_le_square)

lemma HFinite_square_cancel [simp]: "x * x + y * y \<in> HFinite \<Longrightarrow> x * x \<in> HFinite"
  for x y :: hypreal
  using HFinite_bounded le_add_same_cancel1 zero_le_square by blast

lemma Infinitesimal_square_cancel2 [simp]: "x * x + y * y \<in> Infinitesimal \<Longrightarrow> y * y \<in> Infinitesimal"
  for x y :: hypreal
  apply (rule Infinitesimal_square_cancel)
  apply (rule add.commute [THEN subst])
  apply simp
  done

lemma HFinite_square_cancel2 [simp]: "x * x + y * y \<in> HFinite \<Longrightarrow> y * y \<in> HFinite"
  for x y :: hypreal
  apply (rule HFinite_square_cancel)
  apply (rule add.commute [THEN subst])
  apply simp
  done

lemma Infinitesimal_sum_square_cancel [simp]:
  "x * x + y * y + z * z \<in> Infinitesimal \<Longrightarrow> x * x \<in> Infinitesimal"
  for x y z :: hypreal
  apply (rule Infinitesimal_interval2, assumption)
    apply (rule_tac [2] zero_le_square, simp)
  apply (insert zero_le_square [of y])
  apply (insert zero_le_square [of z], simp del:zero_le_square)
  done

lemma HFinite_sum_square_cancel [simp]: "x * x + y * y + z * z \<in> HFinite \<Longrightarrow> x * x \<in> HFinite"
  for x y z :: hypreal
  apply (rule HFinite_bounded, assumption)
   apply (rule_tac [2] zero_le_square)
  apply (insert zero_le_square [of y])
  apply (insert zero_le_square [of z], simp del:zero_le_square)
  done

lemma Infinitesimal_sum_square_cancel2 [simp]:
  "y * y + x * x + z * z \<in> Infinitesimal \<Longrightarrow> x * x \<in> Infinitesimal"
  for x y z :: hypreal
  apply (rule Infinitesimal_sum_square_cancel)
  apply (simp add: ac_simps)
  done

lemma HFinite_sum_square_cancel2 [simp]: "y * y + x * x + z * z \<in> HFinite \<Longrightarrow> x * x \<in> HFinite"
  for x y z :: hypreal
  apply (rule HFinite_sum_square_cancel)
  apply (simp add: ac_simps)
  done

lemma Infinitesimal_sum_square_cancel3 [simp]:
  "z * z + y * y + x * x \<in> Infinitesimal \<Longrightarrow> x * x \<in> Infinitesimal"
  for x y z :: hypreal
  apply (rule Infinitesimal_sum_square_cancel)
  apply (simp add: ac_simps)
  done

lemma HFinite_sum_square_cancel3 [simp]: "z * z + y * y + x * x \<in> HFinite \<Longrightarrow> x * x \<in> HFinite"
  for x y z :: hypreal
  apply (rule HFinite_sum_square_cancel)
  apply (simp add: ac_simps)
  done

lemma monad_hrabs_less: "y \<in> monad x \<Longrightarrow> 0 < hypreal_of_real e \<Longrightarrow> \<bar>y - x\<bar> < hypreal_of_real e"
  by (simp add: Infinitesimal_approx_minus approx_sym less_Infinitesimal_less mem_monad_approx)

lemma mem_monad_SReal_HFinite: "x \<in> monad (hypreal_of_real  a) \<Longrightarrow> x \<in> HFinite"
  using HFinite_star_of approx_HFinite mem_monad_approx by blast


subsection \<open>Theorems about Standard Part\<close>

lemma st_approx_self: "x \<in> HFinite \<Longrightarrow> st x \<approx> x"
  by (metis (no_types, lifting) approx_refl approx_trans3 someI_ex st_def st_part_Ex st_part_Ex1)

lemma st_SReal: "x \<in> HFinite \<Longrightarrow> st x \<in> \<real>"
  apply (simp add: st_def)
  apply (frule st_part_Ex, safe)
  apply (rule someI2)
   apply (auto intro: approx_sym)
  done

lemma st_HFinite: "x \<in> HFinite \<Longrightarrow> st x \<in> HFinite"
  by (erule st_SReal [THEN SReal_subset_HFinite [THEN subsetD]])

lemma st_unique: "r \<in> \<real> \<Longrightarrow> r \<approx> x \<Longrightarrow> st x = r"
  apply (frule SReal_subset_HFinite [THEN subsetD])
  apply (drule (1) approx_HFinite)
  apply (unfold st_def)
  apply (rule some_equality)
   apply (auto intro: approx_unique_real)
  done

lemma st_SReal_eq: "x \<in> \<real> \<Longrightarrow> st x = x"
  by (metis approx_refl st_unique)

lemma st_hypreal_of_real [simp]: "st (hypreal_of_real x) = hypreal_of_real x"
  by (rule SReal_hypreal_of_real [THEN st_SReal_eq])

lemma st_eq_approx: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> st x = st y \<Longrightarrow> x \<approx> y"
  by (auto dest!: st_approx_self elim!: approx_trans3)

lemma approx_st_eq:
  assumes x: "x \<in> HFinite" and y: "y \<in> HFinite" and xy: "x \<approx> y"
  shows "st x = st y"
proof -
  have "st x \<approx> x" "st y \<approx> y" "st x \<in> \<real>" "st y \<in> \<real>"
    by (simp_all add: st_approx_self st_SReal x y)
  with xy show ?thesis
    by (fast elim: approx_trans approx_trans2 SReal_approx_iff [THEN iffD1])
qed

lemma st_eq_approx_iff: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> x \<approx> y \<longleftrightarrow> st x = st y"
  by (blast intro: approx_st_eq st_eq_approx)

lemma st_Infinitesimal_add_SReal: "x \<in> \<real> \<Longrightarrow> e \<in> Infinitesimal \<Longrightarrow> st (x + e) = x"
  apply (erule st_unique)
  apply (erule Infinitesimal_add_approx_self)
  done

lemma st_Infinitesimal_add_SReal2: "x \<in> \<real> \<Longrightarrow> e \<in> Infinitesimal \<Longrightarrow> st (e + x) = x"
  apply (erule st_unique)
  apply (erule Infinitesimal_add_approx_self2)
  done

lemma HFinite_st_Infinitesimal_add: "x \<in> HFinite \<Longrightarrow> \<exists>e \<in> Infinitesimal. x = st(x) + e"
  by (blast dest!: st_approx_self [THEN approx_sym] bex_Infinitesimal_iff2 [THEN iffD2])

lemma st_add: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> st (x + y) = st x + st y"
  by (simp add: st_unique st_SReal st_approx_self approx_add)

lemma st_numeral [simp]: "st (numeral w) = numeral w"
  by (rule Reals_numeral [THEN st_SReal_eq])

lemma st_neg_numeral [simp]: "st (- numeral w) = - numeral w"
proof -
  from Reals_numeral have "numeral w \<in> \<real>" .
  then have "- numeral w \<in> \<real>" by simp
  with st_SReal_eq show ?thesis .
qed

lemma st_0 [simp]: "st 0 = 0"
  by (simp add: st_SReal_eq)

lemma st_1 [simp]: "st 1 = 1"
  by (simp add: st_SReal_eq)

lemma st_neg_1 [simp]: "st (- 1) = - 1"
  by (simp add: st_SReal_eq)

lemma st_minus: "x \<in> HFinite \<Longrightarrow> st (- x) = - st x"
  by (simp add: st_unique st_SReal st_approx_self approx_minus)

lemma st_diff: "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> st (x - y) = st x - st y"
  by (simp add: st_unique st_SReal st_approx_self approx_diff)

lemma st_mult: "\<lbrakk>x \<in> HFinite; y \<in> HFinite\<rbrakk> \<Longrightarrow> st (x * y) = st x * st y"
  by (simp add: st_unique st_SReal st_approx_self approx_mult_HFinite)

lemma st_Infinitesimal: "x \<in> Infinitesimal \<Longrightarrow> st x = 0"
  by (simp add: st_unique mem_infmal_iff)

lemma st_not_Infinitesimal: "st(x) \<noteq> 0 \<Longrightarrow> x \<notin> Infinitesimal"
by (fast intro: st_Infinitesimal)

lemma st_inverse: "x \<in> HFinite \<Longrightarrow> st x \<noteq> 0 \<Longrightarrow> st (inverse x) = inverse (st x)"
  apply (rule_tac c1 = "st x" in mult_left_cancel [THEN iffD1])
   apply (auto simp add: st_mult [symmetric] st_not_Infinitesimal HFinite_inverse)
  apply (subst right_inverse, auto)
  done

lemma st_divide [simp]: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> st y \<noteq> 0 \<Longrightarrow> st (x / y) = st x / st y"
  by (simp add: divide_inverse st_mult st_not_Infinitesimal HFinite_inverse st_inverse)

lemma st_idempotent [simp]: "x \<in> HFinite \<Longrightarrow> st (st x) = st x"
  by (blast intro: st_HFinite st_approx_self approx_st_eq)

lemma Infinitesimal_add_st_less:
  "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> u \<in> Infinitesimal \<Longrightarrow> st x < st y \<Longrightarrow> st x + u < st y"
  apply (drule st_SReal)+
  apply (auto intro!: Infinitesimal_add_hypreal_of_real_less simp add: SReal_iff)
  done

lemma Infinitesimal_add_st_le_cancel:
  "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> u \<in> Infinitesimal \<Longrightarrow>
    st x \<le> st y + u \<Longrightarrow> st x \<le> st y"
  apply (simp add: linorder_not_less [symmetric])
  apply (auto dest: Infinitesimal_add_st_less)
  done

lemma st_le: "x \<in> HFinite \<Longrightarrow> y \<in> HFinite \<Longrightarrow> x \<le> y \<Longrightarrow> st x \<le> st y"
  by (metis approx_le_bound approx_sym linear st_SReal st_approx_self st_part_Ex1)

lemma st_zero_le: "0 \<le> x \<Longrightarrow> x \<in> HFinite \<Longrightarrow> 0 \<le> st x"
  apply (subst st_0 [symmetric])
  apply (rule st_le, auto)
  done

lemma st_zero_ge: "x \<le> 0 \<Longrightarrow> x \<in> HFinite \<Longrightarrow> st x \<le> 0"
  apply (subst st_0 [symmetric])
  apply (rule st_le, auto)
  done

lemma st_hrabs: "x \<in> HFinite \<Longrightarrow> \<bar>st x\<bar> = st \<bar>x\<bar>"
  apply (simp add: linorder_not_le st_zero_le abs_if st_minus linorder_not_less)
  apply (auto dest!: st_zero_ge [OF order_less_imp_le])
  done


subsection \<open>Alternative Definitions using Free Ultrafilter\<close>

subsubsection \<open>\<^term>\<open>HFinite\<close>\<close>

lemma HFinite_FreeUltrafilterNat:
  "star_n X \<in> HFinite \<Longrightarrow> \<exists>u. eventually (\<lambda>n. norm (X n) < u) \<U>"
  apply (auto simp add: HFinite_def SReal_def)
  apply (rule_tac x=r in exI)
  apply (simp add: hnorm_def star_of_def starfun_star_n)
  apply (simp add: star_less_def starP2_star_n)
  done

lemma FreeUltrafilterNat_HFinite:
  "\<exists>u. eventually (\<lambda>n. norm (X n) < u) \<U> \<Longrightarrow> star_n X \<in> HFinite"
  apply (auto simp add: HFinite_def mem_Rep_star_iff)
  apply (rule_tac x="star_of u" in bexI)
   apply (simp add: hnorm_def starfun_star_n star_of_def)
   apply (simp add: star_less_def starP2_star_n)
  apply (simp add: SReal_def)
  done

lemma HFinite_FreeUltrafilterNat_iff:
  "star_n X \<in> HFinite \<longleftrightarrow> (\<exists>u. eventually (\<lambda>n. norm (X n) < u) \<U>)"
  by (blast intro!: HFinite_FreeUltrafilterNat FreeUltrafilterNat_HFinite)


subsubsection \<open>\<^term>\<open>HInfinite\<close>\<close>

lemma lemma_Compl_eq: "- {n. u < norm (f n)} = {n. norm (f n) \<le> u}"
  by auto

lemma lemma_Compl_eq2: "- {n. norm (f n) < u} = {n. u \<le> norm (f n)}"
  by auto

lemma lemma_Int_eq1: "{n. norm (f n) \<le> u} Int {n. u \<le> norm (f n)} = {n. norm(f n) = u}"
  by auto

lemma lemma_FreeUltrafilterNat_one: "{n. norm (f n) = u} \<le> {n. norm (f n) < u + (1::real)}"
  by auto

text \<open>Exclude this type of sets from free ultrafilter for Infinite numbers!\<close>
lemma FreeUltrafilterNat_const_Finite:
  "eventually (\<lambda>n. norm (X n) = u) \<U> \<Longrightarrow> star_n X \<in> HFinite"
  apply (rule FreeUltrafilterNat_HFinite)
  apply (rule_tac x = "u + 1" in exI)
  apply (auto elim: eventually_mono)
  done

lemma HInfinite_FreeUltrafilterNat:
  "star_n X \<in> HInfinite \<Longrightarrow> \<forall>u. eventually (\<lambda>n. u < norm (X n)) \<U>"
  apply (drule HInfinite_HFinite_iff [THEN iffD1])
  apply (simp add: HFinite_FreeUltrafilterNat_iff)
  apply (rule allI, drule_tac x="u + 1" in spec)
  apply (simp add: FreeUltrafilterNat.eventually_not_iff[symmetric])
  apply (auto elim: eventually_mono)
  done

lemma lemma_Int_HI: "{n. norm (Xa n) < u} \<inter> {n. X n = Xa n} \<subseteq> {n. norm (X n) < u}"
  for u :: real
  by auto

lemma FreeUltrafilterNat_HInfinite:
  "\<forall>u. eventually (\<lambda>n. u < norm (X n)) \<U> \<Longrightarrow> star_n X \<in> HInfinite"
  apply (rule HInfinite_HFinite_iff [THEN iffD2])
  apply (safe, drule HFinite_FreeUltrafilterNat, safe)
  apply (drule_tac x = u in spec)
proof -
  fix u
  assume "\<forall>\<^sub>Fn in \<U>. norm (X n) < u" "\<forall>\<^sub>Fn in \<U>. u < norm (X n)"
  then have "\<forall>\<^sub>F x in \<U>. False"
    by eventually_elim auto
  then show False
    by (simp add: eventually_False FreeUltrafilterNat.proper)
qed

lemma HInfinite_FreeUltrafilterNat_iff:
  "star_n X \<in> HInfinite \<longleftrightarrow> (\<forall>u. eventually (\<lambda>n. u < norm (X n)) \<U>)"
  by (blast intro!: HInfinite_FreeUltrafilterNat FreeUltrafilterNat_HInfinite)


subsubsection \<open>\<^term>\<open>Infinitesimal\<close>\<close>

lemma ball_SReal_eq: "(\<forall>x::hypreal \<in> Reals. P x) \<longleftrightarrow> (\<forall>x::real. P (star_of x))"
  by (auto simp: SReal_def)

lemma Infinitesimal_FreeUltrafilterNat:
  "star_n X \<in> Infinitesimal \<Longrightarrow> \<forall>u>0. eventually (\<lambda>n. norm (X n) < u) \<U>"
  apply (simp add: Infinitesimal_def ball_SReal_eq)
  apply (simp add: hnorm_def starfun_star_n star_of_def)
  apply (simp add: star_less_def starP2_star_n)
  done

lemma FreeUltrafilterNat_Infinitesimal:
  "\<forall>u>0. eventually (\<lambda>n. norm (X n) < u) \<U> \<Longrightarrow> star_n X \<in> Infinitesimal"
  apply (simp add: Infinitesimal_def ball_SReal_eq)
  apply (simp add: hnorm_def starfun_star_n star_of_def)
  apply (simp add: star_less_def starP2_star_n)
  done

lemma Infinitesimal_FreeUltrafilterNat_iff:
  "(star_n X \<in> Infinitesimal) = (\<forall>u>0. eventually (\<lambda>n. norm (X n) < u) \<U>)"
  by (blast intro!: Infinitesimal_FreeUltrafilterNat FreeUltrafilterNat_Infinitesimal)


text \<open>Infinitesimals as smaller than \<open>1/n\<close> for all \<open>n::nat (> 0)\<close>.\<close>

lemma lemma_Infinitesimal: "(\<forall>r. 0 < r \<longrightarrow> x < r) \<longleftrightarrow> (\<forall>n. x < inverse (real (Suc n)))"
  by (meson inverse_positive_iff_positive less_trans of_nat_0_less_iff reals_Archimedean zero_less_Suc)

lemma lemma_Infinitesimal2:
  "(\<forall>r \<in> Reals. 0 < r \<longrightarrow> x < r) \<longleftrightarrow> (\<forall>n. x < inverse(hypreal_of_nat (Suc n)))"
  apply safe
   apply (drule_tac x = "inverse (hypreal_of_real (real (Suc n))) " in bspec)
    apply simp_all
  using less_imp_of_nat_less apply fastforce
  apply (auto dest!: reals_Archimedean simp add: SReal_iff simp del: of_nat_Suc)
  apply (drule star_of_less [THEN iffD2])
  apply simp
  apply (blast intro: order_less_trans)
  done


lemma Infinitesimal_hypreal_of_nat_iff:
  "Infinitesimal = {x. \<forall>n. hnorm x < inverse (hypreal_of_nat (Suc n))}"
  using Infinitesimal_def lemma_Infinitesimal2 by auto


subsection \<open>Proof that \<open>\<omega>\<close> is an infinite number\<close>

text \<open>It will follow that \<open>\<epsilon>\<close> is an infinitesimal number.\<close>

lemma Suc_Un_eq: "{n. n < Suc m} = {n. n < m} Un {n. n = m}"
  by (auto simp add: less_Suc_eq)


text \<open>Prove that any segment is finite and hence cannot belong to \<open>\<U>\<close>.\<close>

lemma finite_real_of_nat_segment: "finite {n::nat. real n < real (m::nat)}"
  by auto

lemma finite_real_of_nat_less_real: "finite {n::nat. real n < u}"
  apply (cut_tac x = u in reals_Archimedean2, safe)
  apply (rule finite_real_of_nat_segment [THEN [2] finite_subset])
  apply (auto dest: order_less_trans)
  done

lemma finite_real_of_nat_le_real: "finite {n::nat. real n \<le> u}"
  by (metis infinite_nat_iff_unbounded leD le_nat_floor mem_Collect_eq)

lemma finite_rabs_real_of_nat_le_real: "finite {n::nat. \<bar>real n\<bar> \<le> u}"
  by (simp add: finite_real_of_nat_le_real)

lemma rabs_real_of_nat_le_real_FreeUltrafilterNat:
  "\<not> eventually (\<lambda>n. \<bar>real n\<bar> \<le> u) \<U>"
  by (blast intro!: FreeUltrafilterNat.finite finite_rabs_real_of_nat_le_real)

lemma FreeUltrafilterNat_nat_gt_real: "eventually (\<lambda>n. u < real n) \<U>"
  apply (rule FreeUltrafilterNat.finite')
  apply (subgoal_tac "{n::nat. \<not> u < real n} = {n. real n \<le> u}")
   apply (auto simp add: finite_real_of_nat_le_real)
  done

text \<open>The complement of \<open>{n. \<bar>real n\<bar> \<le> u} = {n. u < \<bar>real n\<bar>}\<close> is in
  \<open>\<U>\<close> by property of (free) ultrafilters.\<close>

text \<open>\<^term>\<open>\<omega>\<close> is a member of \<^term>\<open>HInfinite\<close>.\<close>
theorem HInfinite_omega [simp]: "\<omega> \<in> HInfinite"
  apply (simp add: omega_def)
  apply (rule FreeUltrafilterNat_HInfinite)
  apply clarify
  apply (rule_tac u1 = "u-1" in eventually_mono [OF FreeUltrafilterNat_nat_gt_real])
  apply auto
  done


text \<open>Epsilon is a member of Infinitesimal.\<close>

lemma Infinitesimal_epsilon [simp]: "\<epsilon> \<in> Infinitesimal"
  by (auto intro!: HInfinite_inverse_Infinitesimal HInfinite_omega
      simp add: hypreal_epsilon_inverse_omega)

lemma HFinite_epsilon [simp]: "\<epsilon> \<in> HFinite"
  by (auto intro: Infinitesimal_subset_HFinite [THEN subsetD])

lemma epsilon_approx_zero [simp]: "\<epsilon> \<approx> 0"
  by (simp add: mem_infmal_iff [symmetric])

text \<open>Needed for proof that we define a hyperreal \<open>[<X(n)] \<approx> hypreal_of_real a\<close> given
  that \<open>\<forall>n. |X n - a| < 1/n\<close>. Used in proof of \<open>NSLIM \<Rightarrow> LIM\<close>.\<close>
lemma real_of_nat_less_inverse_iff: "0 < u \<Longrightarrow> u < inverse (real(Suc n)) \<longleftrightarrow> real(Suc n) < inverse u"
  using less_imp_inverse_less by force

lemma finite_inverse_real_of_posnat_gt_real: "0 < u \<Longrightarrow> finite {n. u < inverse (real (Suc n))}"
proof (simp only: real_of_nat_less_inverse_iff)
  have "{n. 1 + real n < inverse u} = {n. real n < inverse u - 1}"
    by fastforce
  then show "finite {n. real (Suc n) < inverse u}"
    using finite_real_of_nat_less_real [of "inverse u - 1"]
    by auto
qed

lemma lemma_real_le_Un_eq2:
  "{n. u \<le> inverse(real(Suc n))} =
    {n. u < inverse(real(Suc n))} \<union> {n. u = inverse(real(Suc n))}"
  by (auto dest: order_le_imp_less_or_eq simp add: order_less_imp_le)

lemma finite_inverse_real_of_posnat_ge_real: "0 < u \<Longrightarrow> finite {n. u \<le> inverse (real (Suc n))}"
  by (auto simp add: lemma_real_le_Un_eq2 lemma_finite_epsilon_set finite_inverse_real_of_posnat_gt_real
      simp del: of_nat_Suc)

lemma inverse_real_of_posnat_ge_real_FreeUltrafilterNat:
  "0 < u \<Longrightarrow> \<not> eventually (\<lambda>n. u \<le> inverse(real(Suc n))) \<U>"
  by (blast intro!: FreeUltrafilterNat.finite finite_inverse_real_of_posnat_ge_real)

text \<open>The complement of \<open>{n. u \<le> inverse(real(Suc n))} = {n. inverse (real (Suc n)) < u}\<close>
  is in \<open>\<U>\<close> by property of (free) ultrafilters.\<close>
lemma Compl_le_inverse_eq: "- {n. u \<le> inverse(real(Suc n))} = {n. inverse(real(Suc n)) < u}"
  by (auto dest!: order_le_less_trans simp add: linorder_not_le)


lemma FreeUltrafilterNat_inverse_real_of_posnat:
  "0 < u \<Longrightarrow> eventually (\<lambda>n. inverse(real(Suc n)) < u) \<U>"
  by (drule inverse_real_of_posnat_ge_real_FreeUltrafilterNat)
    (simp add: FreeUltrafilterNat.eventually_not_iff not_le[symmetric])

text \<open>Example of an hypersequence (i.e. an extended standard sequence)
  whose term with an hypernatural suffix is an infinitesimal i.e.
  the whn'nth term of the hypersequence is a member of Infinitesimal\<close>

lemma SEQ_Infinitesimal: "( *f* (\<lambda>n::nat. inverse(real(Suc n)))) whn \<in> Infinitesimal"
  by (simp add: hypnat_omega_def starfun_star_n star_n_inverse Infinitesimal_FreeUltrafilterNat_iff
      FreeUltrafilterNat_inverse_real_of_posnat del: of_nat_Suc)

text \<open>Example where we get a hyperreal from a real sequence
  for which a particular property holds. The theorem is
  used in proofs about equivalence of nonstandard and
  standard neighbourhoods. Also used for equivalence of
  nonstandard ans standard definitions of pointwise
  limit.\<close>

text \<open>\<open>|X(n) - x| < 1/n \<Longrightarrow> [<X n>] - hypreal_of_real x| \<in> Infinitesimal\<close>\<close>
lemma real_seq_to_hypreal_Infinitesimal:
  "\<forall>n. norm (X n - x) < inverse (real (Suc n)) \<Longrightarrow> star_n X - star_of x \<in> Infinitesimal"
  unfolding star_n_diff star_of_def Infinitesimal_FreeUltrafilterNat_iff star_n_inverse
  by (auto dest!: FreeUltrafilterNat_inverse_real_of_posnat
      intro: order_less_trans elim!: eventually_mono)

lemma real_seq_to_hypreal_approx:
  "\<forall>n. norm (X n - x) < inverse (real (Suc n)) \<Longrightarrow> star_n X \<approx> star_of x"
  by (metis bex_Infinitesimal_iff real_seq_to_hypreal_Infinitesimal)

lemma real_seq_to_hypreal_approx2:
  "\<forall>n. norm (x - X n) < inverse(real(Suc n)) \<Longrightarrow> star_n X \<approx> star_of x"
  by (metis norm_minus_commute real_seq_to_hypreal_approx)

lemma real_seq_to_hypreal_Infinitesimal2:
  "\<forall>n. norm(X n - Y n) < inverse(real(Suc n)) \<Longrightarrow> star_n X - star_n Y \<in> Infinitesimal"
  unfolding Infinitesimal_FreeUltrafilterNat_iff star_n_diff
  by (auto dest!: FreeUltrafilterNat_inverse_real_of_posnat
      intro: order_less_trans elim!: eventually_mono)

end

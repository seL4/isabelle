(*  Title:      HOL/Nonstandard_Analysis/HyperDef.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

section \<open>Construction of Hyperreals Using Ultrafilters\<close>

theory HyperDef
  imports Complex_Main HyperNat
begin

type_synonym hypreal = "real star"

abbreviation hypreal_of_real :: "real \<Rightarrow> real star"
  where "hypreal_of_real \<equiv> star_of"

abbreviation hypreal_of_hypnat :: "hypnat \<Rightarrow> hypreal"
  where "hypreal_of_hypnat \<equiv> of_hypnat"

definition omega :: hypreal  (\<open>\<omega>\<close>)
  where "\<omega> = star_n (\<lambda>n. real (Suc n))"
    \<comment> \<open>an infinite number \<open>= [<1, 2, 3, \<dots>>]\<close>\<close>

definition epsilon :: hypreal  (\<open>\<epsilon>\<close>)
  where "\<epsilon> = star_n (\<lambda>n. inverse (real (Suc n)))"
    \<comment> \<open>an infinitesimal number \<open>= [<1, 1/2, 1/3, \<dots>>]\<close>\<close>


subsection \<open>Real vector class instances\<close>

instantiation star :: (scaleR) scaleR
begin
  definition star_scaleR_def [transfer_unfold]: "scaleR r \<equiv> *f* (scaleR r)"
  instance ..
end

lemma Standard_scaleR [simp]: "x \<in> Standard \<Longrightarrow> scaleR r x \<in> Standard"
  by (simp add: star_scaleR_def)

lemma star_of_scaleR [simp]: "star_of (scaleR r x) = scaleR r (star_of x)"
  by transfer (rule refl)

instance star :: (real_vector) real_vector
proof
  fix a b :: real
  show "\<And>x y::'a star. scaleR a (x + y) = scaleR a x + scaleR a y"
    by transfer (rule scaleR_right_distrib)
  show "\<And>x::'a star. scaleR (a + b) x = scaleR a x + scaleR b x"
    by transfer (rule scaleR_left_distrib)
  show "\<And>x::'a star. scaleR a (scaleR b x) = scaleR (a * b) x"
    by transfer (rule scaleR_scaleR)
  show "\<And>x::'a star. scaleR 1 x = x"
    by transfer (rule scaleR_one)
qed

instance star :: (real_algebra) real_algebra
proof
  fix a :: real
  show "\<And>x y::'a star. scaleR a x * y = scaleR a (x * y)"
    by transfer (rule mult_scaleR_left)
  show "\<And>x y::'a star. x * scaleR a y = scaleR a (x * y)"
    by transfer (rule mult_scaleR_right)
qed

instance star :: (real_algebra_1) real_algebra_1 ..

instance star :: (real_div_algebra) real_div_algebra ..

instance star :: (field_char_0) field_char_0 ..

instance star :: (real_field) real_field ..

lemma star_of_real_def [transfer_unfold]: "of_real r = star_of (of_real r)"
  by (unfold of_real_def, transfer, rule refl)

lemma Standard_of_real [simp]: "of_real r \<in> Standard"
  by (simp add: star_of_real_def)

lemma star_of_of_real [simp]: "star_of (of_real r) = of_real r"
  by transfer (rule refl)

lemma of_real_eq_star_of [simp]: "of_real = star_of"
proof
  show "of_real r = star_of r" for r :: real
    by transfer simp
qed

lemma Reals_eq_Standard: "(\<real> :: hypreal set) = Standard"
  by (simp add: Reals_def Standard_def)


subsection \<open>Injection from \<^typ>\<open>hypreal\<close>\<close>

definition of_hypreal :: "hypreal \<Rightarrow> 'a::real_algebra_1 star"
  where [transfer_unfold]: "of_hypreal = *f* of_real"

lemma Standard_of_hypreal [simp]: "r \<in> Standard \<Longrightarrow> of_hypreal r \<in> Standard"
  by (simp add: of_hypreal_def)

lemma of_hypreal_0 [simp]: "of_hypreal 0 = 0"
  by transfer (rule of_real_0)

lemma of_hypreal_1 [simp]: "of_hypreal 1 = 1"
  by transfer (rule of_real_1)

lemma of_hypreal_add [simp]: "\<And>x y. of_hypreal (x + y) = of_hypreal x + of_hypreal y"
  by transfer (rule of_real_add)

lemma of_hypreal_minus [simp]: "\<And>x. of_hypreal (- x) = - of_hypreal x"
  by transfer (rule of_real_minus)

lemma of_hypreal_diff [simp]: "\<And>x y. of_hypreal (x - y) = of_hypreal x - of_hypreal y"
  by transfer (rule of_real_diff)

lemma of_hypreal_mult [simp]: "\<And>x y. of_hypreal (x * y) = of_hypreal x * of_hypreal y"
  by transfer (rule of_real_mult)

lemma of_hypreal_inverse [simp]:
  "\<And>x. of_hypreal (inverse x) =
    inverse (of_hypreal x :: 'a::{real_div_algebra, division_ring} star)"
  by transfer (rule of_real_inverse)

lemma of_hypreal_divide [simp]:
  "\<And>x y. of_hypreal (x / y) =
    (of_hypreal x / of_hypreal y :: 'a::{real_field, field} star)"
  by transfer (rule of_real_divide)

lemma of_hypreal_eq_iff [simp]: "\<And>x y. (of_hypreal x = of_hypreal y) = (x = y)"
  by transfer (rule of_real_eq_iff)

lemma of_hypreal_eq_0_iff [simp]: "\<And>x. (of_hypreal x = 0) = (x = 0)"
  by transfer (rule of_real_eq_0_iff)


subsection \<open>Properties of \<^term>\<open>starrel\<close>\<close>

lemma lemma_starrel_refl [simp]: "x \<in> starrel `` {x}"
  by (simp add: starrel_def)

lemma starrel_in_hypreal [simp]: "starrel``{x}\<in>star"
  by (simp add: star_def starrel_def quotient_def, blast)

declare Abs_star_inject [simp] Abs_star_inverse [simp]
declare equiv_starrel [THEN eq_equiv_class_iff, simp]


subsection \<open>\<^term>\<open>hypreal_of_real\<close>: the Injection from \<^typ>\<open>real\<close> to \<^typ>\<open>hypreal\<close>\<close>

lemma inj_star_of: "inj star_of"
  by (rule inj_onI) simp

lemma mem_Rep_star_iff: "X \<in> Rep_star x \<longleftrightarrow> x = star_n X"
  by (cases x) (simp add: star_n_def)

lemma Rep_star_star_n_iff [simp]: "X \<in> Rep_star (star_n Y) \<longleftrightarrow> eventually (\<lambda>n. Y n = X n) \<U>"
  by (simp add: star_n_def)

lemma Rep_star_star_n: "X \<in> Rep_star (star_n X)"
  by simp


subsection \<open>Properties of \<^term>\<open>star_n\<close>\<close>

lemma star_n_add: "star_n X + star_n Y = star_n (\<lambda>n. X n + Y n)"
  by (simp only: star_add_def starfun2_star_n)

lemma star_n_minus: "- star_n X = star_n (\<lambda>n. -(X n))"
  by (simp only: star_minus_def starfun_star_n)

lemma star_n_diff: "star_n X - star_n Y = star_n (\<lambda>n. X n - Y n)"
  by (simp only: star_diff_def starfun2_star_n)

lemma star_n_mult: "star_n X * star_n Y = star_n (\<lambda>n. X n * Y n)"
  by (simp only: star_mult_def starfun2_star_n)

lemma star_n_inverse: "inverse (star_n X) = star_n (\<lambda>n. inverse (X n))"
  by (simp only: star_inverse_def starfun_star_n)

lemma star_n_le: "star_n X \<le> star_n Y = eventually (\<lambda>n. X n \<le> Y n) \<U>"
  by (simp only: star_le_def starP2_star_n)

lemma star_n_less: "star_n X < star_n Y = eventually (\<lambda>n. X n < Y n) \<U>"
  by (simp only: star_less_def starP2_star_n)

lemma star_n_zero_num: "0 = star_n (\<lambda>n. 0)"
  by (simp only: star_zero_def star_of_def)

lemma star_n_one_num: "1 = star_n (\<lambda>n. 1)"
  by (simp only: star_one_def star_of_def)

lemma star_n_abs: "\<bar>star_n X\<bar> = star_n (\<lambda>n. \<bar>X n\<bar>)"
  by (simp only: star_abs_def starfun_star_n)

lemma hypreal_omega_gt_zero [simp]: "0 < \<omega>"
  by (simp add: omega_def star_n_zero_num star_n_less)


subsection \<open>Existence of Infinite Hyperreal Number\<close>

text \<open>Existence of infinite number not corresponding to any real number.
  Use assumption that member \<^term>\<open>\<U>\<close> is not finite.\<close>

lemma hypreal_of_real_not_eq_omega: "hypreal_of_real x \<noteq> \<omega>"
proof -
  have False if "\<forall>\<^sub>F n in \<U>. x = 1 + real n" for x
  proof -
    have "finite {n::nat. x = 1 + real n}"
      by (simp add: finite_nat_set_iff_bounded_le) (metis add.commute nat_le_linear nat_le_real_less)
    then show False
      using FreeUltrafilterNat.finite that by blast
  qed
  then show ?thesis
    by (auto simp add: omega_def star_of_def star_n_eq_iff)
qed

text \<open>Existence of infinitesimal number also not corresponding to any real number.\<close>

lemma hypreal_of_real_not_eq_epsilon: "hypreal_of_real x \<noteq> \<epsilon>"
proof -
  have False if "\<forall>\<^sub>F n in \<U>. x = inverse (1 + real n)" for x
  proof -
    have "finite {n::nat. x = inverse (1 + real n)}"
      by (simp add: finite_nat_set_iff_bounded_le) (metis add.commute inverse_inverse_eq linear nat_le_real_less of_nat_Suc) 
    then show False
      using FreeUltrafilterNat.finite that by blast
  qed
  then show ?thesis
    by (auto simp: epsilon_def star_of_def star_n_eq_iff)
qed

lemma epsilon_ge_zero [simp]: "0 \<le> \<epsilon>"
  by (simp add: epsilon_def star_n_zero_num star_n_le)

lemma epsilon_not_zero: "\<epsilon> \<noteq> 0"
  using hypreal_of_real_not_eq_epsilon by force

lemma epsilon_inverse_omega: "\<epsilon> = inverse \<omega>"
  by (simp add: epsilon_def omega_def star_n_inverse)

lemma epsilon_gt_zero: "0 < \<epsilon>"
  by (simp add: epsilon_inverse_omega)


subsection \<open>Embedding the Naturals into the Hyperreals\<close>

abbreviation hypreal_of_nat :: "nat \<Rightarrow> hypreal"
  where "hypreal_of_nat \<equiv> of_nat"

lemma SNat_eq: "Nats = {n. \<exists>N. n = hypreal_of_nat N}"
  by (simp add: Nats_def image_def)

text \<open>Naturals embedded in hyperreals: is a hyperreal c.f. NS extension.\<close>

lemma hypreal_of_nat: "hypreal_of_nat m = star_n (\<lambda>n. real m)"
  by (simp add: star_of_def [symmetric])

declaration \<open>
  K (Lin_Arith.add_simps @{thms star_of_zero star_of_one
      star_of_numeral star_of_add
      star_of_minus star_of_diff star_of_mult}
  #> Lin_Arith.add_inj_thms @{thms star_of_le [THEN iffD2]
      star_of_less [THEN iffD2] star_of_eq [THEN iffD2]}
  #> Lin_Arith.add_inj_const (\<^const_name>\<open>StarDef.star_of\<close>, \<^typ>\<open>real \<Rightarrow> hypreal\<close>))
\<close>

simproc_setup fast_arith_hypreal ("(m::hypreal) < n" | "(m::hypreal) \<le> n" | "(m::hypreal) = n") =
  \<open>K Lin_Arith.simproc\<close>


subsection \<open>Exponentials on the Hyperreals\<close>

lemma hpowr_0 [simp]: "r ^ 0 = (1::hypreal)"
  for r :: hypreal
  by (rule power_0)

lemma hpowr_Suc [simp]: "r ^ (Suc n) = r * (r ^ n)"
  for r :: hypreal
  by (rule power_Suc)

lemma hrealpow: "star_n X ^ m = star_n (\<lambda>n. (X n::real) ^ m)"
  by (induct m) (auto simp: star_n_one_num star_n_mult)

lemma hrealpow_sum_square_expand:
  "(x + y) ^ Suc (Suc 0) =
    x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + (hypreal_of_nat (Suc (Suc 0))) * x * y"
  for x y :: hypreal
  by (simp add: distrib_left distrib_right)

lemma power_hypreal_of_real_numeral:
  "(numeral v :: hypreal) ^ n = hypreal_of_real ((numeral v) ^ n)"
  by simp
declare power_hypreal_of_real_numeral [of _ "numeral w", simp] for w

lemma power_hypreal_of_real_neg_numeral:
  "(- numeral v :: hypreal) ^ n = hypreal_of_real ((- numeral v) ^ n)"
  by simp
declare power_hypreal_of_real_neg_numeral [of _ "numeral w", simp] for w


subsection \<open>Powers with Hypernatural Exponents\<close>

text \<open>Hypernatural powers of hyperreals.\<close>
definition pow :: "'a::power star \<Rightarrow> nat star \<Rightarrow> 'a star"  (infixr \<open>pow\<close> 80)
  where hyperpow_def [transfer_unfold]: "R pow N = ( *f2* (^)) R N"

lemma Standard_hyperpow [simp]: "r \<in> Standard \<Longrightarrow> n \<in> Standard \<Longrightarrow> r pow n \<in> Standard"
  by (simp add: hyperpow_def)

lemma hyperpow: "star_n X pow star_n Y = star_n (\<lambda>n. X n ^ Y n)"
  by (simp add: hyperpow_def starfun2_star_n)

lemma hyperpow_zero [simp]: "\<And>n. (0::'a::{power,semiring_0} star) pow (n + (1::hypnat)) = 0"
  by transfer simp

lemma hyperpow_not_zero: "\<And>r n. r \<noteq> (0::'a::{field} star) \<Longrightarrow> r pow n \<noteq> 0"
  by transfer (rule power_not_zero)

lemma hyperpow_inverse: "\<And>r n. r \<noteq> (0::'a::field star) \<Longrightarrow> inverse (r pow n) = (inverse r) pow n"
  by transfer (rule power_inverse [symmetric])

lemma hyperpow_hrabs: "\<And>r n. \<bar>r::'a::{linordered_idom} star\<bar> pow n = \<bar>r pow n\<bar>"
  by transfer (rule power_abs [symmetric])

lemma hyperpow_add: "\<And>r n m. (r::'a::monoid_mult star) pow (n + m) = (r pow n) * (r pow m)"
  by transfer (rule power_add)

lemma hyperpow_one [simp]: "\<And>r. (r::'a::monoid_mult star) pow (1::hypnat) = r"
  by transfer (rule power_one_right)

lemma hyperpow_two: "\<And>r. (r::'a::monoid_mult star) pow (2::hypnat) = r * r"
  by transfer (rule power2_eq_square)

lemma hyperpow_gt_zero: "\<And>r n. (0::'a::{linordered_semidom} star) < r \<Longrightarrow> 0 < r pow n"
  by transfer (rule zero_less_power)

lemma hyperpow_ge_zero: "\<And>r n. (0::'a::{linordered_semidom} star) \<le> r \<Longrightarrow> 0 \<le> r pow n"
  by transfer (rule zero_le_power)

lemma hyperpow_le: "\<And>x y n. (0::'a::{linordered_semidom} star) < x \<Longrightarrow> x \<le> y \<Longrightarrow> x pow n \<le> y pow n"
  by transfer (rule power_mono [OF _ order_less_imp_le])

lemma hyperpow_eq_one [simp]: "\<And>n. 1 pow n = (1::'a::monoid_mult star)"
  by transfer (rule power_one)

lemma hrabs_hyperpow_minus [simp]: "\<And>(a::'a::linordered_idom star) n. \<bar>(-a) pow n\<bar> = \<bar>a pow n\<bar>"
  by transfer (rule abs_power_minus)

lemma hyperpow_mult: "\<And>r s n. (r * s::'a::comm_monoid_mult star) pow n = (r pow n) * (s pow n)"
  by transfer (rule power_mult_distrib)

lemma hyperpow_two_le [simp]: "\<And>r. (0::'a::{monoid_mult,linordered_ring_strict} star) \<le> r pow 2"
  by (auto simp add: hyperpow_two zero_le_mult_iff)

lemma hyperpow_two_hrabs [simp]: "\<bar>x::'a::linordered_idom star\<bar> pow 2 = x pow 2"
  by (simp add: hyperpow_hrabs)

lemma hyperpow_two_gt_one: "\<And>r::'a::linordered_semidom star. 1 < r \<Longrightarrow> 1 < r pow 2"
  by transfer simp

lemma hyperpow_two_ge_one: "\<And>r::'a::linordered_semidom star. 1 \<le> r \<Longrightarrow> 1 \<le> r pow 2"
  by transfer (rule one_le_power)

lemma two_hyperpow_ge_one [simp]: "(1::hypreal) \<le> 2 pow n"
  by (metis hyperpow_eq_one hyperpow_le one_le_numeral zero_less_one)

lemma hyperpow_minus_one2 [simp]: "\<And>n. (- 1) pow (2 * n) = (1::hypreal)"
  by transfer (rule power_minus1_even)

lemma hyperpow_less_le: "\<And>r n N. (0::hypreal) \<le> r \<Longrightarrow> r \<le> 1 \<Longrightarrow> n < N \<Longrightarrow> r pow N \<le> r pow n"
  by transfer (rule power_decreasing [OF order_less_imp_le])

lemma hyperpow_SHNat_le:
  "0 \<le> r \<Longrightarrow> r \<le> (1::hypreal) \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> \<forall>n\<in>Nats. r pow N \<le> r pow n"
  by (auto intro!: hyperpow_less_le simp: HNatInfinite_iff)

lemma hyperpow_realpow: "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)"
  by transfer (rule refl)

lemma hyperpow_SReal [simp]: "(hypreal_of_real r) pow (hypnat_of_nat n) \<in> \<real>"
  by (simp add: Reals_eq_Standard)

lemma hyperpow_zero_HNatInfinite [simp]: "N \<in> HNatInfinite \<Longrightarrow> (0::hypreal) pow N = 0"
  by (drule HNatInfinite_is_Suc, auto)

lemma hyperpow_le_le: "(0::hypreal) \<le> r \<Longrightarrow> r \<le> 1 \<Longrightarrow> n \<le> N \<Longrightarrow> r pow N \<le> r pow n"
  by (metis hyperpow_less_le le_less)

lemma hyperpow_Suc_le_self2: "(0::hypreal) \<le> r \<Longrightarrow> r < 1 \<Longrightarrow> r pow (n + (1::hypnat)) \<le> r"
  by (metis hyperpow_less_le hyperpow_one hypnat_add_self_le le_less)

lemma hyperpow_hypnat_of_nat: "\<And>x. x pow hypnat_of_nat n = x ^ n"
  by transfer (rule refl)

lemma of_hypreal_hyperpow:
  "\<And>x n. of_hypreal (x pow n) = (of_hypreal x::'a::{real_algebra_1} star) pow n"
  by transfer (rule of_real_power)

end

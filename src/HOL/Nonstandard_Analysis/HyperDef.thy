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

definition omega :: hypreal  ("\<omega>")
  where "\<omega> = star_n (\<lambda>n. real (Suc n))"
    \<comment> \<open>an infinite number \<open>= [<1, 2, 3, \<dots>>]\<close>\<close>

definition epsilon :: hypreal  ("\<epsilon>")
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


subsection \<open>Injection from @{typ hypreal}\<close>

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


subsection \<open>Properties of @{term starrel}\<close>

lemma lemma_starrel_refl [simp]: "x \<in> starrel `` {x}"
  by (simp add: starrel_def)

lemma starrel_in_hypreal [simp]: "starrel``{x}\<in>star"
  by (simp add: star_def starrel_def quotient_def, blast)

declare Abs_star_inject [simp] Abs_star_inverse [simp]
declare equiv_starrel [THEN eq_equiv_class_iff, simp]


subsection \<open>@{term hypreal_of_real}: the Injection from @{typ real} to @{typ hypreal}\<close>

lemma inj_star_of: "inj star_of"
  by (rule inj_onI) simp

lemma mem_Rep_star_iff: "X \<in> Rep_star x \<longleftrightarrow> x = star_n X"
  by (cases x) (simp add: star_n_def)

lemma Rep_star_star_n_iff [simp]: "X \<in> Rep_star (star_n Y) \<longleftrightarrow> eventually (\<lambda>n. Y n = X n) \<U>"
  by (simp add: star_n_def)

lemma Rep_star_star_n: "X \<in> Rep_star (star_n X)"
  by simp


subsection \<open>Properties of @{term star_n}\<close>

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
  Use assumption that member @{term \<U>} is not finite.\<close>

text \<open>A few lemmas first.\<close>

lemma lemma_omega_empty_singleton_disj:
  "{n::nat. x = real n} = {} \<or> (\<exists>y. {n::nat. x = real n} = {y})"
  by force

lemma lemma_finite_omega_set: "finite {n::nat. x = real n}"
  using lemma_omega_empty_singleton_disj [of x] by auto

lemma not_ex_hypreal_of_real_eq_omega: "\<nexists>x. hypreal_of_real x = \<omega>"
  apply (simp add: omega_def star_of_def star_n_eq_iff)
  apply clarify
  apply (rule_tac x2="x-1" in lemma_finite_omega_set [THEN FreeUltrafilterNat.finite, THEN notE])
  apply (erule eventually_mono)
  apply auto
  done

lemma hypreal_of_real_not_eq_omega: "hypreal_of_real x \<noteq> \<omega>"
  using not_ex_hypreal_of_real_eq_omega by auto

text \<open>Existence of infinitesimal number also not corresponding to any real number.\<close>

lemma lemma_epsilon_empty_singleton_disj:
  "{n::nat. x = inverse(real(Suc n))} = {} \<or> (\<exists>y. {n::nat. x = inverse(real(Suc n))} = {y})"
  by auto

lemma lemma_finite_epsilon_set: "finite {n. x = inverse (real (Suc n))}"
  using lemma_epsilon_empty_singleton_disj [of x] by auto

lemma not_ex_hypreal_of_real_eq_epsilon: "\<nexists>x. hypreal_of_real x = \<epsilon>"
  by (auto simp: epsilon_def star_of_def star_n_eq_iff
      lemma_finite_epsilon_set [THEN FreeUltrafilterNat.finite] simp del: of_nat_Suc)

lemma hypreal_of_real_not_eq_epsilon: "hypreal_of_real x \<noteq> \<epsilon>"
  using not_ex_hypreal_of_real_eq_epsilon by auto

lemma hypreal_epsilon_not_zero: "\<epsilon> \<noteq> 0"
  by (simp add: epsilon_def star_zero_def star_of_def star_n_eq_iff FreeUltrafilterNat.proper
      del: star_of_zero)

lemma hypreal_epsilon_inverse_omega: "\<epsilon> = inverse \<omega>"
  by (simp add: epsilon_def omega_def star_n_inverse)

lemma hypreal_epsilon_gt_zero: "0 < \<epsilon>"
  by (simp add: hypreal_epsilon_inverse_omega)


subsection \<open>Absolute Value Function for the Hyperreals\<close>

lemma hrabs_add_less: "\<bar>x\<bar> < r \<Longrightarrow> \<bar>y\<bar> < s \<Longrightarrow> \<bar>x + y\<bar> < r + s"
  for x y r s :: hypreal
  by (simp add: abs_if split: if_split_asm)

lemma hrabs_less_gt_zero: "\<bar>x\<bar> < r \<Longrightarrow> 0 < r"
  for x r :: hypreal
  by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "\<bar>x\<bar> = x \<or> \<bar>x\<bar> = -x"
  for x :: "'a::abs_if"
  by (simp add: abs_if)

lemma hrabs_add_lemma_disj: "y + - x + (y + - z) = \<bar>x + - z\<bar> \<Longrightarrow> y = z \<or> x = y"
  for x y z :: hypreal
  by (simp add: abs_if split: if_split_asm)


subsection \<open>Embedding the Naturals into the Hyperreals\<close>

abbreviation hypreal_of_nat :: "nat \<Rightarrow> hypreal"
  where "hypreal_of_nat \<equiv> of_nat"

lemma SNat_eq: "Nats = {n. \<exists>N. n = hypreal_of_nat N}"
  by (simp add: Nats_def image_def)

text \<open>Naturals embedded in hyperreals: is a hyperreal c.f. NS extension.\<close>

lemma hypreal_of_nat: "hypreal_of_nat m = star_n (\<lambda>n. real m)"
  by (simp add: star_of_def [symmetric])

declaration \<open>
  K (Lin_Arith.add_inj_thms [@{thm star_of_le} RS iffD2,
    @{thm star_of_less} RS iffD2, @{thm star_of_eq} RS iffD2]
  #> Lin_Arith.add_simps [@{thm star_of_zero}, @{thm star_of_one},
      @{thm star_of_numeral}, @{thm star_of_add},
      @{thm star_of_minus}, @{thm star_of_diff}, @{thm star_of_mult}]
  #> Lin_Arith.add_inj_const (@{const_name "StarDef.star_of"}, @{typ "real \<Rightarrow> hypreal"}))
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

lemma hrealpow_two: "r ^ Suc (Suc 0) = r * r"
  for r :: hypreal
  by simp

lemma hrealpow_two_le [simp]: "0 \<le> r ^ Suc (Suc 0)"
  for r :: hypreal
  by (auto simp add: zero_le_mult_iff)

lemma hrealpow_two_le_add_order [simp]: "0 \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0)"
  for u v :: hypreal
  by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hrealpow_two_le_add_order2 [simp]: "0 \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0) + w ^ Suc (Suc 0)"
  for u v w :: hypreal
  by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hypreal_add_nonneg_eq_0_iff: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  for x y :: hypreal
  by arith


(* FIXME: DELETE THESE *)
lemma hypreal_three_squares_add_zero_iff: "x * x + y * y + z * z = 0 \<longleftrightarrow> x = 0 \<and> y = 0 \<and> z = 0"
  for x y z :: hypreal
  by (simp only: zero_le_square add_nonneg_nonneg hypreal_add_nonneg_eq_0_iff) auto

lemma hrealpow_three_squares_add_zero_iff [simp]:
  "x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + z ^ Suc (Suc 0) = 0 \<longleftrightarrow> x = 0 \<and> y = 0 \<and> z = 0"
  for x y z :: hypreal
  by (simp only: hypreal_three_squares_add_zero_iff hrealpow_two)

(*FIXME: This and RealPow.abs_realpow_two should be replaced by an abstract
  result proved in Rings or Fields*)
lemma hrabs_hrealpow_two [simp]: "\<bar>x ^ Suc (Suc 0)\<bar> = x ^ Suc (Suc 0)"
  for x :: hypreal
  by (simp add: abs_mult)

lemma two_hrealpow_ge_one [simp]: "(1::hypreal) \<le> 2 ^ n"
  using power_increasing [of 0 n "2::hypreal"] by simp

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
(*
lemma hrealpow_HFinite:
  fixes x :: "'a::{real_normed_algebra,power} star"
  shows "x \<in> HFinite ==> x ^ n \<in> HFinite"
apply (induct_tac "n")
apply (auto simp add: power_Suc intro: HFinite_mult)
done
*)


subsection \<open>Powers with Hypernatural Exponents\<close>

text \<open>Hypernatural powers of hyperreals.\<close>
definition pow :: "'a::power star \<Rightarrow> nat star \<Rightarrow> 'a star"  (infixr "pow" 80)
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

lemma hrabs_hyperpow_two [simp]:
  "\<bar>x pow 2\<bar> = (x::'a::{monoid_mult,linordered_ring_strict} star) pow 2"
  by (simp only: abs_of_nonneg hyperpow_two_le)

lemma hyperpow_two_hrabs [simp]: "\<bar>x::'a::linordered_idom star\<bar> pow 2 = x pow 2"
  by (simp add: hyperpow_hrabs)

text \<open>The precondition could be weakened to @{term "0\<le>x"}.\<close>
lemma hypreal_mult_less_mono: "u < v \<Longrightarrow> x < y \<Longrightarrow> 0 < v \<Longrightarrow> 0 < x \<Longrightarrow> u * x < v * y"
  for u v x y :: hypreal
  by (simp add: mult_strict_mono order_less_imp_le)

lemma hyperpow_two_gt_one: "\<And>r::'a::linordered_semidom star. 1 < r \<Longrightarrow> 1 < r pow 2"
  by transfer simp

lemma hyperpow_two_ge_one: "\<And>r::'a::linordered_semidom star. 1 \<le> r \<Longrightarrow> 1 \<le> r pow 2"
  by transfer (rule one_le_power)

lemma two_hyperpow_ge_one [simp]: "(1::hypreal) \<le> 2 pow n"
  apply (rule_tac y = "1 pow n" in order_trans)
   apply (rule_tac [2] hyperpow_le)
    apply auto
  done

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
  apply (drule order_le_less [of n, THEN iffD1])
  apply (auto intro: hyperpow_less_le)
  done

lemma hyperpow_Suc_le_self2: "(0::hypreal) \<le> r \<Longrightarrow> r < 1 \<Longrightarrow> r pow (n + (1::hypnat)) \<le> r"
  apply (drule_tac n = " (1::hypnat) " in hyperpow_le_le)
    apply auto
  done

lemma hyperpow_hypnat_of_nat: "\<And>x. x pow hypnat_of_nat n = x ^ n"
  by transfer (rule refl)

lemma of_hypreal_hyperpow:
  "\<And>x n. of_hypreal (x pow n) = (of_hypreal x::'a::{real_algebra_1} star) pow n"
  by transfer (rule of_real_power)

end

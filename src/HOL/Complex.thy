(*  Title:       HOL/Complex.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2001 University of Edinburgh
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

section {* Complex Numbers: Rectangular and Polar Representations *}

theory Complex
imports Transcendental
begin

text {*
We use the @{text codatatype} command to define the type of complex numbers. This allows us to use
@{text primcorec} to define complex functions by defining their real and imaginary result
separately.
*}

codatatype complex = Complex (Re: real) (Im: real)

lemma complex_surj: "Complex (Re z) (Im z) = z"
  by (rule complex.collapse)

lemma complex_eqI [intro?]: "\<lbrakk>Re x = Re y; Im x = Im y\<rbrakk> \<Longrightarrow> x = y"
  by (rule complex.expand) simp

lemma complex_eq_iff: "x = y \<longleftrightarrow> Re x = Re y \<and> Im x = Im y"
  by (auto intro: complex.expand)

subsection {* Addition and Subtraction *}

instantiation complex :: ab_group_add
begin

primcorec zero_complex where
  "Re 0 = 0"
| "Im 0 = 0"

primcorec plus_complex where
  "Re (x + y) = Re x + Re y"
| "Im (x + y) = Im x + Im y"

primcorec uminus_complex where
  "Re (- x) = - Re x"
| "Im (- x) = - Im x"

primcorec minus_complex where
  "Re (x - y) = Re x - Re y"
| "Im (x - y) = Im x - Im y"

instance
  by intro_classes (simp_all add: complex_eq_iff)

end

subsection {* Multiplication and Division *}

instantiation complex :: field_inverse_zero
begin

primcorec one_complex where
  "Re 1 = 1"
| "Im 1 = 0"

primcorec times_complex where
  "Re (x * y) = Re x * Re y - Im x * Im y"
| "Im (x * y) = Re x * Im y + Im x * Re y"

primcorec inverse_complex where
  "Re (inverse x) = Re x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)"
| "Im (inverse x) = - Im x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)"

definition "x / (y\<Colon>complex) = x * inverse y"

instance
  by intro_classes
     (simp_all add: complex_eq_iff divide_complex_def
      distrib_left distrib_right right_diff_distrib left_diff_distrib
      power2_eq_square add_divide_distrib [symmetric])

end

lemma Re_divide: "Re (x / y) = (Re x * Re y + Im x * Im y) / ((Re y)\<^sup>2 + (Im y)\<^sup>2)"
  unfolding divide_complex_def by (simp add: add_divide_distrib)

lemma Im_divide: "Im (x / y) = (Im x * Re y - Re x * Im y) / ((Re y)\<^sup>2 + (Im y)\<^sup>2)"
  unfolding divide_complex_def times_complex.sel inverse_complex.sel
  by (simp_all add: divide_simps)

lemma Re_power2: "Re (x ^ 2) = (Re x)^2 - (Im x)^2"
  by (simp add: power2_eq_square)

lemma Im_power2: "Im (x ^ 2) = 2 * Re x * Im x"
  by (simp add: power2_eq_square)

lemma Re_power_real: "Im x = 0 \<Longrightarrow> Re (x ^ n) = Re x ^ n "
  by (induct n) simp_all

lemma Im_power_real: "Im x = 0 \<Longrightarrow> Im (x ^ n) = 0"
  by (induct n) simp_all

subsection {* Scalar Multiplication *}

instantiation complex :: real_field
begin

primcorec scaleR_complex where
  "Re (scaleR r x) = r * Re x"
| "Im (scaleR r x) = r * Im x"

instance
proof
  fix a b :: real and x y :: complex
  show "scaleR a (x + y) = scaleR a x + scaleR a y"
    by (simp add: complex_eq_iff distrib_left)
  show "scaleR (a + b) x = scaleR a x + scaleR b x"
    by (simp add: complex_eq_iff distrib_right)
  show "scaleR a (scaleR b x) = scaleR (a * b) x"
    by (simp add: complex_eq_iff mult.assoc)
  show "scaleR 1 x = x"
    by (simp add: complex_eq_iff)
  show "scaleR a x * y = scaleR a (x * y)"
    by (simp add: complex_eq_iff algebra_simps)
  show "x * scaleR a y = scaleR a (x * y)"
    by (simp add: complex_eq_iff algebra_simps)
qed

end

subsection {* Numerals, Arithmetic, and Embedding from Reals *}

abbreviation complex_of_real :: "real \<Rightarrow> complex"
  where "complex_of_real \<equiv> of_real"

declare [[coercion "of_real :: real \<Rightarrow> complex"]]
declare [[coercion "of_rat :: rat \<Rightarrow> complex"]]
declare [[coercion "of_int :: int \<Rightarrow> complex"]]
declare [[coercion "of_nat :: nat \<Rightarrow> complex"]]

lemma complex_Re_of_nat [simp]: "Re (of_nat n) = of_nat n"
  by (induct n) simp_all

lemma complex_Im_of_nat [simp]: "Im (of_nat n) = 0"
  by (induct n) simp_all

lemma complex_Re_of_int [simp]: "Re (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma complex_Im_of_int [simp]: "Im (of_int z) = 0"
  by (cases z rule: int_diff_cases) simp

lemma complex_Re_numeral [simp]: "Re (numeral v) = numeral v"
  using complex_Re_of_int [of "numeral v"] by simp

lemma complex_Im_numeral [simp]: "Im (numeral v) = 0"
  using complex_Im_of_int [of "numeral v"] by simp

lemma Re_complex_of_real [simp]: "Re (complex_of_real z) = z"
  by (simp add: of_real_def)

lemma Im_complex_of_real [simp]: "Im (complex_of_real z) = 0"
  by (simp add: of_real_def)

lemma Re_divide_numeral [simp]: "Re (z / numeral w) = Re z / numeral w"
  by (simp add: Re_divide sqr_conv_mult)

lemma Im_divide_numeral [simp]: "Im (z / numeral w) = Im z / numeral w"
  by (simp add: Im_divide sqr_conv_mult)

subsection {* The Complex Number $i$ *}

primcorec "ii" :: complex  ("\<i>") where
  "Re ii = 0"
| "Im ii = 1"

lemma Complex_eq[simp]: "Complex a b = a + \<i> * b"
  by (simp add: complex_eq_iff)

lemma complex_eq: "a = Re a + \<i> * Im a"
  by (simp add: complex_eq_iff)

lemma fun_complex_eq: "f = (\<lambda>x. Re (f x) + \<i> * Im (f x))"
  by (simp add: fun_eq_iff complex_eq)

lemma i_squared [simp]: "ii * ii = -1"
  by (simp add: complex_eq_iff)

lemma power2_i [simp]: "ii\<^sup>2 = -1"
  by (simp add: power2_eq_square)

lemma inverse_i [simp]: "inverse ii = - ii"
  by (rule inverse_unique) simp

lemma divide_i [simp]: "x / ii = - ii * x"
  by (simp add: divide_complex_def)

lemma complex_i_mult_minus [simp]: "ii * (ii * x) = - x"
  by (simp add: mult.assoc [symmetric])

lemma complex_i_not_zero [simp]: "ii \<noteq> 0"
  by (simp add: complex_eq_iff)

lemma complex_i_not_one [simp]: "ii \<noteq> 1"
  by (simp add: complex_eq_iff)

lemma complex_i_not_numeral [simp]: "ii \<noteq> numeral w"
  by (simp add: complex_eq_iff)

lemma complex_i_not_neg_numeral [simp]: "ii \<noteq> - numeral w"
  by (simp add: complex_eq_iff)

lemma complex_split_polar: "\<exists>r a. z = complex_of_real r * (cos a + \<i> * sin a)"
  by (simp add: complex_eq_iff polar_Ex)

lemma i_even_power [simp]: "\<i> ^ (n * 2) = (-1) ^ n"
  by (metis mult.commute power2_i power_mult)

subsection {* Vector Norm *}

instantiation complex :: real_normed_field
begin

definition "norm z = sqrt ((Re z)\<^sup>2 + (Im z)\<^sup>2)"

abbreviation cmod :: "complex \<Rightarrow> real"
  where "cmod \<equiv> norm"

definition complex_sgn_def:
  "sgn x = x /\<^sub>R cmod x"

definition dist_complex_def:
  "dist x y = cmod (x - y)"

definition open_complex_def:
  "open (S :: complex set) \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

instance proof
  fix r :: real and x y :: complex and S :: "complex set"
  show "(norm x = 0) = (x = 0)"
    by (simp add: norm_complex_def complex_eq_iff)
  show "norm (x + y) \<le> norm x + norm y"
    by (simp add: norm_complex_def complex_eq_iff real_sqrt_sum_squares_triangle_ineq)
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    by (simp add: norm_complex_def complex_eq_iff power_mult_distrib distrib_left [symmetric] real_sqrt_mult)
  show "norm (x * y) = norm x * norm y"
    by (simp add: norm_complex_def complex_eq_iff real_sqrt_mult [symmetric] power2_eq_square algebra_simps)
qed (rule complex_sgn_def dist_complex_def open_complex_def)+

end

lemma norm_ii [simp]: "norm ii = 1"
  by (simp add: norm_complex_def)

lemma cmod_unit_one: "cmod (cos a + \<i> * sin a) = 1"
  by (simp add: norm_complex_def)

lemma cmod_complex_polar: "cmod (r * (cos a + \<i> * sin a)) = \<bar>r\<bar>"
  by (simp add: norm_mult cmod_unit_one)

lemma complex_Re_le_cmod: "Re x \<le> cmod x"
  unfolding norm_complex_def
  by (rule real_sqrt_sum_squares_ge1)

lemma complex_mod_minus_le_complex_mod: "- cmod x \<le> cmod x"
  by (rule order_trans [OF _ norm_ge_zero]) simp

lemma complex_mod_triangle_ineq2: "cmod (b + a) - cmod b \<le> cmod a"
  by (rule ord_le_eq_trans [OF norm_triangle_ineq2]) simp

lemma abs_Re_le_cmod: "\<bar>Re x\<bar> \<le> cmod x"
  by (simp add: norm_complex_def)

lemma abs_Im_le_cmod: "\<bar>Im x\<bar> \<le> cmod x"
  by (simp add: norm_complex_def)

lemma cmod_le: "cmod z \<le> \<bar>Re z\<bar> + \<bar>Im z\<bar>"
  apply (subst complex_eq)
  apply (rule order_trans)
  apply (rule norm_triangle_ineq)
  apply (simp add: norm_mult)
  done

lemma cmod_eq_Re: "Im z = 0 \<Longrightarrow> cmod z = \<bar>Re z\<bar>"
  by (simp add: norm_complex_def)

lemma cmod_eq_Im: "Re z = 0 \<Longrightarrow> cmod z = \<bar>Im z\<bar>"
  by (simp add: norm_complex_def)

lemma cmod_power2: "cmod z ^ 2 = (Re z)^2 + (Im z)^2"
  by (simp add: norm_complex_def)

lemma cmod_plus_Re_le_0_iff: "cmod z + Re z \<le> 0 \<longleftrightarrow> Re z = - cmod z"
  using abs_Re_le_cmod[of z] by auto

lemma Im_eq_0: "\<bar>Re z\<bar> = cmod z \<Longrightarrow> Im z = 0"
  by (subst (asm) power_eq_iff_eq_base[symmetric, where n=2])
     (auto simp add: norm_complex_def)

lemma abs_sqrt_wlog:
  fixes x::"'a::linordered_idom"
  assumes "\<And>x::'a. x \<ge> 0 \<Longrightarrow> P x (x\<^sup>2)" shows "P \<bar>x\<bar> (x\<^sup>2)"
by (metis abs_ge_zero assms power2_abs)

lemma complex_abs_le_norm: "\<bar>Re z\<bar> + \<bar>Im z\<bar> \<le> sqrt 2 * norm z"
  unfolding norm_complex_def
  apply (rule abs_sqrt_wlog [where x="Re z"])
  apply (rule abs_sqrt_wlog [where x="Im z"])
  apply (rule power2_le_imp_le)
  apply (simp_all add: power2_sum add.commute sum_squares_bound real_sqrt_mult [symmetric])
  done


text {* Properties of complex signum. *}

lemma sgn_eq: "sgn z = z / complex_of_real (cmod z)"
  by (simp add: sgn_div_norm divide_inverse scaleR_conv_of_real mult.commute)

lemma Re_sgn [simp]: "Re(sgn z) = Re(z)/cmod z"
  by (simp add: complex_sgn_def divide_inverse)

lemma Im_sgn [simp]: "Im(sgn z) = Im(z)/cmod z"
  by (simp add: complex_sgn_def divide_inverse)


subsection {* Completeness of the Complexes *}

lemma bounded_linear_Re: "bounded_linear Re"
  by (rule bounded_linear_intro [where K=1], simp_all add: norm_complex_def)

lemma bounded_linear_Im: "bounded_linear Im"
  by (rule bounded_linear_intro [where K=1], simp_all add: norm_complex_def)

lemmas Cauchy_Re = bounded_linear.Cauchy [OF bounded_linear_Re]
lemmas Cauchy_Im = bounded_linear.Cauchy [OF bounded_linear_Im]
lemmas tendsto_Re [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Re]
lemmas tendsto_Im [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_Im]
lemmas isCont_Re [simp] = bounded_linear.isCont [OF bounded_linear_Re]
lemmas isCont_Im [simp] = bounded_linear.isCont [OF bounded_linear_Im]
lemmas continuous_Re [simp] = bounded_linear.continuous [OF bounded_linear_Re]
lemmas continuous_Im [simp] = bounded_linear.continuous [OF bounded_linear_Im]
lemmas continuous_on_Re [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Re]
lemmas continuous_on_Im [continuous_intros] = bounded_linear.continuous_on[OF bounded_linear_Im]
lemmas has_derivative_Re [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Re]
lemmas has_derivative_Im [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_Im]
lemmas sums_Re = bounded_linear.sums [OF bounded_linear_Re]
lemmas sums_Im = bounded_linear.sums [OF bounded_linear_Im]

lemma tendsto_Complex [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> (g ---> b) F \<Longrightarrow> ((\<lambda>x. Complex (f x) (g x)) ---> Complex a b) F"
  by (auto intro!: tendsto_intros)

lemma tendsto_complex_iff:
  "(f ---> x) F \<longleftrightarrow> (((\<lambda>x. Re (f x)) ---> Re x) F \<and> ((\<lambda>x. Im (f x)) ---> Im x) F)"
proof safe
  assume "((\<lambda>x. Re (f x)) ---> Re x) F" "((\<lambda>x. Im (f x)) ---> Im x) F"
  from tendsto_Complex[OF this] show "(f ---> x) F"
    unfolding complex.collapse .
qed (auto intro: tendsto_intros)

lemma continuous_complex_iff: "continuous F f \<longleftrightarrow>
    continuous F (\<lambda>x. Re (f x)) \<and> continuous F (\<lambda>x. Im (f x))"
  unfolding continuous_def tendsto_complex_iff ..

lemma has_vector_derivative_complex_iff: "(f has_vector_derivative x) F \<longleftrightarrow>
    ((\<lambda>x. Re (f x)) has_field_derivative (Re x)) F \<and>
    ((\<lambda>x. Im (f x)) has_field_derivative (Im x)) F"
  unfolding has_vector_derivative_def has_field_derivative_def has_derivative_def tendsto_complex_iff
  by (simp add: field_simps bounded_linear_scaleR_left bounded_linear_mult_right)

lemma has_field_derivative_Re[derivative_intros]:
  "(f has_vector_derivative D) F \<Longrightarrow> ((\<lambda>x. Re (f x)) has_field_derivative (Re D)) F"
  unfolding has_vector_derivative_complex_iff by safe

lemma has_field_derivative_Im[derivative_intros]:
  "(f has_vector_derivative D) F \<Longrightarrow> ((\<lambda>x. Im (f x)) has_field_derivative (Im D)) F"
  unfolding has_vector_derivative_complex_iff by safe

instance complex :: banach
proof
  fix X :: "nat \<Rightarrow> complex"
  assume X: "Cauchy X"
  then have "(\<lambda>n. Complex (Re (X n)) (Im (X n))) ----> Complex (lim (\<lambda>n. Re (X n))) (lim (\<lambda>n. Im (X n)))"
    by (intro tendsto_Complex convergent_LIMSEQ_iff[THEN iffD1] Cauchy_convergent_iff[THEN iffD1] Cauchy_Re Cauchy_Im)
  then show "convergent X"
    unfolding complex.collapse by (rule convergentI)
qed

declare
  DERIV_power[where 'a=complex, unfolded of_nat_def[symmetric], derivative_intros]

subsection {* Complex Conjugation *}

primcorec cnj :: "complex \<Rightarrow> complex" where
  "Re (cnj z) = Re z"
| "Im (cnj z) = - Im z"

lemma complex_cnj_cancel_iff [simp]: "(cnj x = cnj y) = (x = y)"
  by (simp add: complex_eq_iff)

lemma complex_cnj_cnj [simp]: "cnj (cnj z) = z"
  by (simp add: complex_eq_iff)

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
  by (simp add: complex_eq_iff)

lemma complex_cnj_zero_iff [iff]: "(cnj z = 0) = (z = 0)"
  by (simp add: complex_eq_iff)

lemma complex_cnj_add [simp]: "cnj (x + y) = cnj x + cnj y"
  by (simp add: complex_eq_iff)

lemma cnj_setsum [simp]: "cnj (setsum f s) = (\<Sum>x\<in>s. cnj (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma complex_cnj_diff [simp]: "cnj (x - y) = cnj x - cnj y"
  by (simp add: complex_eq_iff)

lemma complex_cnj_minus [simp]: "cnj (- x) = - cnj x"
  by (simp add: complex_eq_iff)

lemma complex_cnj_one [simp]: "cnj 1 = 1"
  by (simp add: complex_eq_iff)

lemma complex_cnj_mult [simp]: "cnj (x * y) = cnj x * cnj y"
  by (simp add: complex_eq_iff)

lemma cnj_setprod [simp]: "cnj (setprod f s) = (\<Prod>x\<in>s. cnj (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma complex_cnj_inverse [simp]: "cnj (inverse x) = inverse (cnj x)"
  by (simp add: complex_eq_iff)

lemma complex_cnj_divide [simp]: "cnj (x / y) = cnj x / cnj y"
  by (simp add: divide_complex_def)

lemma complex_cnj_power [simp]: "cnj (x ^ n) = cnj x ^ n"
  by (induct n) simp_all

lemma complex_cnj_of_nat [simp]: "cnj (of_nat n) = of_nat n"
  by (simp add: complex_eq_iff)

lemma complex_cnj_of_int [simp]: "cnj (of_int z) = of_int z"
  by (simp add: complex_eq_iff)

lemma complex_cnj_numeral [simp]: "cnj (numeral w) = numeral w"
  by (simp add: complex_eq_iff)

lemma complex_cnj_neg_numeral [simp]: "cnj (- numeral w) = - numeral w"
  by (simp add: complex_eq_iff)

lemma complex_cnj_scaleR [simp]: "cnj (scaleR r x) = scaleR r (cnj x)"
  by (simp add: complex_eq_iff)

lemma complex_mod_cnj [simp]: "cmod (cnj z) = cmod z"
  by (simp add: norm_complex_def)

lemma complex_cnj_complex_of_real [simp]: "cnj (of_real x) = of_real x"
  by (simp add: complex_eq_iff)

lemma complex_cnj_i [simp]: "cnj ii = - ii"
  by (simp add: complex_eq_iff)

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re z)"
  by (simp add: complex_eq_iff)

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im z) * ii"
  by (simp add: complex_eq_iff)

lemma complex_mult_cnj: "z * cnj z = complex_of_real ((Re z)\<^sup>2 + (Im z)\<^sup>2)"
  by (simp add: complex_eq_iff power2_eq_square)

lemma complex_mod_mult_cnj: "cmod (z * cnj z) = (cmod z)\<^sup>2"
  by (simp add: norm_mult power2_eq_square)

lemma complex_mod_sqrt_Re_mult_cnj: "cmod z = sqrt (Re (z * cnj z))"
  by (simp add: norm_complex_def power2_eq_square)

lemma complex_In_mult_cnj_zero [simp]: "Im (z * cnj z) = 0"
  by simp

lemma bounded_linear_cnj: "bounded_linear cnj"
  using complex_cnj_add complex_cnj_scaleR
  by (rule bounded_linear_intro [where K=1], simp)

lemmas tendsto_cnj [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_cnj]
lemmas isCont_cnj [simp] = bounded_linear.isCont [OF bounded_linear_cnj]
lemmas continuous_cnj [simp, continuous_intros] = bounded_linear.continuous [OF bounded_linear_cnj]
lemmas continuous_on_cnj [simp, continuous_intros] = bounded_linear.continuous_on [OF bounded_linear_cnj]
lemmas has_derivative_cnj [simp, derivative_intros] = bounded_linear.has_derivative [OF bounded_linear_cnj]

lemma lim_cnj: "((\<lambda>x. cnj(f x)) ---> cnj l) F \<longleftrightarrow> (f ---> l) F"
  by (simp add: tendsto_iff dist_complex_def complex_cnj_diff [symmetric] del: complex_cnj_diff)

lemma sums_cnj: "((\<lambda>x. cnj(f x)) sums cnj l) \<longleftrightarrow> (f sums l)"
  by (simp add: sums_def lim_cnj cnj_setsum [symmetric] del: cnj_setsum)


subsection{*Basic Lemmas*}

lemma complex_eq_0: "z=0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 = 0"
  by (metis zero_complex.sel complex_eqI sum_power2_eq_zero_iff)

lemma complex_neq_0: "z\<noteq>0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 > 0"
  by (metis complex_eq_0 less_numeral_extra(3) sum_power2_gt_zero_iff)

lemma complex_norm_square: "of_real ((norm z)\<^sup>2) = z * cnj z"
by (cases z)
   (auto simp: complex_eq_iff norm_complex_def power2_eq_square[symmetric] of_real_power[symmetric]
         simp del: of_real_power)

lemma re_complex_div_eq_0: "Re (a / b) = 0 \<longleftrightarrow> Re (a * cnj b) = 0"
  by (auto simp add: Re_divide)

lemma im_complex_div_eq_0: "Im (a / b) = 0 \<longleftrightarrow> Im (a * cnj b) = 0"
  by (auto simp add: Im_divide)

lemma complex_div_gt_0:
  "(Re (a / b) > 0 \<longleftrightarrow> Re (a * cnj b) > 0) \<and> (Im (a / b) > 0 \<longleftrightarrow> Im (a * cnj b) > 0)"
proof cases
  assume "b = 0" then show ?thesis by auto
next
  assume "b \<noteq> 0"
  then have "0 < (Re b)\<^sup>2 + (Im b)\<^sup>2"
    by (simp add: complex_eq_iff sum_power2_gt_zero_iff)
  then show ?thesis
    by (simp add: Re_divide Im_divide zero_less_divide_iff)
qed

lemma re_complex_div_gt_0: "Re (a / b) > 0 \<longleftrightarrow> Re (a * cnj b) > 0"
  and im_complex_div_gt_0: "Im (a / b) > 0 \<longleftrightarrow> Im (a * cnj b) > 0"
  using complex_div_gt_0 by auto

lemma re_complex_div_ge_0: "Re(a / b) \<ge> 0 \<longleftrightarrow> Re(a * cnj b) \<ge> 0"
  by (metis le_less re_complex_div_eq_0 re_complex_div_gt_0)

lemma im_complex_div_ge_0: "Im(a / b) \<ge> 0 \<longleftrightarrow> Im(a * cnj b) \<ge> 0"
  by (metis im_complex_div_eq_0 im_complex_div_gt_0 le_less)

lemma re_complex_div_lt_0: "Re(a / b) < 0 \<longleftrightarrow> Re(a * cnj b) < 0"
  by (metis less_asym neq_iff re_complex_div_eq_0 re_complex_div_gt_0)

lemma im_complex_div_lt_0: "Im(a / b) < 0 \<longleftrightarrow> Im(a * cnj b) < 0"
  by (metis im_complex_div_eq_0 im_complex_div_gt_0 less_asym neq_iff)

lemma re_complex_div_le_0: "Re(a / b) \<le> 0 \<longleftrightarrow> Re(a * cnj b) \<le> 0"
  by (metis not_le re_complex_div_gt_0)

lemma im_complex_div_le_0: "Im(a / b) \<le> 0 \<longleftrightarrow> Im(a * cnj b) \<le> 0"
  by (metis im_complex_div_gt_0 not_le)

lemma Re_setsum[simp]: "Re (setsum f s) = (\<Sum>x\<in>s. Re (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma Im_setsum[simp]: "Im (setsum f s) = (\<Sum>x\<in>s. Im(f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma sums_complex_iff: "f sums x \<longleftrightarrow> ((\<lambda>x. Re (f x)) sums Re x) \<and> ((\<lambda>x. Im (f x)) sums Im x)"
  unfolding sums_def tendsto_complex_iff Im_setsum Re_setsum ..

lemma summable_complex_iff: "summable f \<longleftrightarrow> summable (\<lambda>x. Re (f x)) \<and>  summable (\<lambda>x. Im (f x))"
  unfolding summable_def sums_complex_iff[abs_def] by (metis complex.sel)

lemma summable_complex_of_real [simp]: "summable (\<lambda>n. complex_of_real (f n)) \<longleftrightarrow> summable f"
  unfolding summable_complex_iff by simp

lemma summable_Re: "summable f \<Longrightarrow> summable (\<lambda>x. Re (f x))"
  unfolding summable_complex_iff by blast

lemma summable_Im: "summable f \<Longrightarrow> summable (\<lambda>x. Im (f x))"
  unfolding summable_complex_iff by blast

lemma complex_is_Real_iff: "z \<in> \<real> \<longleftrightarrow> Im z = 0"
  by (auto simp: Reals_def complex_eq_iff)

lemma Reals_cnj_iff: "z \<in> \<real> \<longleftrightarrow> cnj z = z"
  by (auto simp: complex_is_Real_iff complex_eq_iff)

lemma in_Reals_norm: "z \<in> \<real> \<Longrightarrow> norm(z) = abs(Re z)"
  by (simp add: complex_is_Real_iff norm_complex_def)

lemma series_comparison_complex:
  fixes f:: "nat \<Rightarrow> 'a::banach"
  assumes sg: "summable g"
     and "\<And>n. g n \<in> \<real>" "\<And>n. Re (g n) \<ge> 0"
     and fg: "\<And>n. n \<ge> N \<Longrightarrow> norm(f n) \<le> norm(g n)"
  shows "summable f"
proof -
  have g: "\<And>n. cmod (g n) = Re (g n)" using assms
    by (metis abs_of_nonneg in_Reals_norm)
  show ?thesis
    apply (rule summable_comparison_test' [where g = "\<lambda>n. norm (g n)" and N=N])
    using sg
    apply (auto simp: summable_def)
    apply (rule_tac x="Re s" in exI)
    apply (auto simp: g sums_Re)
    apply (metis fg g)
    done
qed

subsection{*Finally! Polar Form for Complex Numbers*}

subsubsection {* $\cos \theta + i \sin \theta$ *}

primcorec cis :: "real \<Rightarrow> complex" where
  "Re (cis a) = cos a"
| "Im (cis a) = sin a"

lemma cis_zero [simp]: "cis 0 = 1"
  by (simp add: complex_eq_iff)

lemma norm_cis [simp]: "norm (cis a) = 1"
  by (simp add: norm_complex_def)

lemma sgn_cis [simp]: "sgn (cis a) = cis a"
  by (simp add: sgn_div_norm)

lemma cis_neq_zero [simp]: "cis a \<noteq> 0"
  by (metis norm_cis norm_zero zero_neq_one)

lemma cis_mult: "cis a * cis b = cis (a + b)"
  by (simp add: complex_eq_iff cos_add sin_add)

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
  by (induct n, simp_all add: real_of_nat_Suc algebra_simps cis_mult)

lemma cis_inverse [simp]: "inverse(cis a) = cis (-a)"
  by (simp add: complex_eq_iff)

lemma cis_divide: "cis a / cis b = cis (a - b)"
  by (simp add: divide_complex_def cis_mult)

lemma cos_n_Re_cis_pow_n: "cos (real n * a) = Re(cis a ^ n)"
  by (auto simp add: DeMoivre)

lemma sin_n_Im_cis_pow_n: "sin (real n * a) = Im(cis a ^ n)"
  by (auto simp add: DeMoivre)

lemma cis_pi: "cis pi = -1"
  by (simp add: complex_eq_iff)

subsubsection {* $r(\cos \theta + i \sin \theta)$ *}

definition rcis :: "real \<Rightarrow> real \<Rightarrow> complex" where
  "rcis r a = complex_of_real r * cis a"

lemma Re_rcis [simp]: "Re(rcis r a) = r * cos a"
  by (simp add: rcis_def)

lemma Im_rcis [simp]: "Im(rcis r a) = r * sin a"
  by (simp add: rcis_def)

lemma rcis_Ex: "\<exists>r a. z = rcis r a"
  by (simp add: complex_eq_iff polar_Ex)

lemma complex_mod_rcis [simp]: "cmod(rcis r a) = abs r"
  by (simp add: rcis_def norm_mult)

lemma cis_rcis_eq: "cis a = rcis 1 a"
  by (simp add: rcis_def)

lemma rcis_mult: "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)"
  by (simp add: rcis_def cis_mult)

lemma rcis_zero_mod [simp]: "rcis 0 a = 0"
  by (simp add: rcis_def)

lemma rcis_zero_arg [simp]: "rcis r 0 = complex_of_real r"
  by (simp add: rcis_def)

lemma rcis_eq_zero_iff [simp]: "rcis r a = 0 \<longleftrightarrow> r = 0"
  by (simp add: rcis_def)

lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
  by (simp add: rcis_def power_mult_distrib DeMoivre)

lemma rcis_inverse: "inverse(rcis r a) = rcis (1/r) (-a)"
  by (simp add: divide_inverse rcis_def)

lemma rcis_divide: "rcis r1 a / rcis r2 b = rcis (r1/r2) (a - b)"
  by (simp add: rcis_def cis_divide [symmetric])

subsubsection {* Complex exponential *}

abbreviation expi :: "complex \<Rightarrow> complex"
  where "expi \<equiv> exp"

lemma cis_conv_exp: "cis b = exp (\<i> * b)"
proof -
  { fix n :: nat
    have "\<i> ^ n = fact n *\<^sub>R (cos_coeff n + \<i> * sin_coeff n)"
      by (induct n)
         (simp_all add: sin_coeff_Suc cos_coeff_Suc complex_eq_iff Re_divide Im_divide field_simps
                        power2_eq_square real_of_nat_Suc add_nonneg_eq_0_iff
                        real_of_nat_def[symmetric])
    then have "(\<i> * complex_of_real b) ^ n /\<^sub>R fact n =
        of_real (cos_coeff n * b^n) + \<i> * of_real (sin_coeff n * b^n)"
      by (simp add: field_simps) }
  then show ?thesis
    by (auto simp add: cis.ctr exp_def simp del: of_real_mult
             intro!: sums_unique sums_add sums_mult sums_of_real sin_converges cos_converges)
qed

lemma expi_def: "expi z = exp (Re z) * cis (Im z)"
  unfolding cis_conv_exp exp_of_real [symmetric] mult_exp_exp by (cases z) simp

lemma Re_exp: "Re (exp z) = exp (Re z) * cos (Im z)"
  unfolding expi_def by simp

lemma Im_exp: "Im (exp z) = exp (Re z) * sin (Im z)"
  unfolding expi_def by simp

lemma complex_expi_Ex: "\<exists>a r. z = complex_of_real r * expi a"
apply (insert rcis_Ex [of z])
apply (auto simp add: expi_def rcis_def mult.assoc [symmetric])
apply (rule_tac x = "ii * complex_of_real a" in exI, auto)
done

lemma expi_two_pi_i [simp]: "expi((2::complex) * complex_of_real pi * ii) = 1"
  by (simp add: expi_def complex_eq_iff)

subsubsection {* Complex argument *}

definition arg :: "complex \<Rightarrow> real" where
  "arg z = (if z = 0 then 0 else (SOME a. sgn z = cis a \<and> -pi < a \<and> a \<le> pi))"

lemma arg_zero: "arg 0 = 0"
  by (simp add: arg_def)

lemma arg_unique:
  assumes "sgn z = cis x" and "-pi < x" and "x \<le> pi"
  shows "arg z = x"
proof -
  from assms have "z \<noteq> 0" by auto
  have "(SOME a. sgn z = cis a \<and> -pi < a \<and> a \<le> pi) = x"
  proof
    fix a def d \<equiv> "a - x"
    assume a: "sgn z = cis a \<and> - pi < a \<and> a \<le> pi"
    from a assms have "- (2*pi) < d \<and> d < 2*pi"
      unfolding d_def by simp
    moreover from a assms have "cos a = cos x" and "sin a = sin x"
      by (simp_all add: complex_eq_iff)
    hence cos: "cos d = 1" unfolding d_def cos_diff by simp
    moreover from cos have "sin d = 0" by (rule cos_one_sin_zero)
    ultimately have "d = 0"
      unfolding sin_zero_iff
      by (auto elim!: evenE dest!: less_2_cases)
    thus "a = x" unfolding d_def by simp
  qed (simp add: assms del: Re_sgn Im_sgn)
  with `z \<noteq> 0` show "arg z = x"
    unfolding arg_def by simp
qed

lemma arg_correct:
  assumes "z \<noteq> 0" shows "sgn z = cis (arg z) \<and> -pi < arg z \<and> arg z \<le> pi"
proof (simp add: arg_def assms, rule someI_ex)
  obtain r a where z: "z = rcis r a" using rcis_Ex by fast
  with assms have "r \<noteq> 0" by auto
  def b \<equiv> "if 0 < r then a else a + pi"
  have b: "sgn z = cis b"
    unfolding z b_def rcis_def using `r \<noteq> 0`
    by (simp add: of_real_def sgn_scaleR sgn_if complex_eq_iff)
  have cis_2pi_nat: "\<And>n. cis (2 * pi * real_of_nat n) = 1"
    by (induct_tac n) (simp_all add: distrib_left cis_mult [symmetric] complex_eq_iff)
  have cis_2pi_int: "\<And>x. cis (2 * pi * real_of_int x) = 1"
    by (case_tac x rule: int_diff_cases)
       (simp add: right_diff_distrib cis_divide [symmetric] cis_2pi_nat)
  def c \<equiv> "b - 2*pi * of_int \<lceil>(b - pi) / (2*pi)\<rceil>"
  have "sgn z = cis c"
    unfolding b c_def
    by (simp add: cis_divide [symmetric] cis_2pi_int)
  moreover have "- pi < c \<and> c \<le> pi"
    using ceiling_correct [of "(b - pi) / (2*pi)"]
    by (simp add: c_def less_divide_eq divide_le_eq algebra_simps)
  ultimately show "\<exists>a. sgn z = cis a \<and> -pi < a \<and> a \<le> pi" by fast
qed

lemma arg_bounded: "- pi < arg z \<and> arg z \<le> pi"
  by (cases "z = 0") (simp_all add: arg_zero arg_correct)

lemma cis_arg: "z \<noteq> 0 \<Longrightarrow> cis (arg z) = sgn z"
  by (simp add: arg_correct)

lemma rcis_cmod_arg: "rcis (cmod z) (arg z) = z"
  by (cases "z = 0") (simp_all add: rcis_def cis_arg sgn_div_norm of_real_def)

lemma cos_arg_i_mult_zero [simp]: "y \<noteq> 0 \<Longrightarrow> Re y = 0 \<Longrightarrow> cos (arg y) = 0"
  using cis_arg [of y] by (simp add: complex_eq_iff)

subsection {* Square root of complex numbers *}

primcorec csqrt :: "complex \<Rightarrow> complex" where
  "Re (csqrt z) = sqrt ((cmod z + Re z) / 2)"
| "Im (csqrt z) = (if Im z = 0 then 1 else sgn (Im z)) * sqrt ((cmod z - Re z) / 2)"

lemma csqrt_of_real_nonneg [simp]: "Im x = 0 \<Longrightarrow> Re x \<ge> 0 \<Longrightarrow> csqrt x = sqrt (Re x)"
  by (simp add: complex_eq_iff norm_complex_def)

lemma csqrt_of_real_nonpos [simp]: "Im x = 0 \<Longrightarrow> Re x \<le> 0 \<Longrightarrow> csqrt x = \<i> * sqrt \<bar>Re x\<bar>"
  by (simp add: complex_eq_iff norm_complex_def)

lemma csqrt_0 [simp]: "csqrt 0 = 0"
  by simp

lemma csqrt_1 [simp]: "csqrt 1 = 1"
  by simp

lemma csqrt_ii [simp]: "csqrt \<i> = (1 + \<i>) / sqrt 2"
  by (simp add: complex_eq_iff Re_divide Im_divide real_sqrt_divide real_div_sqrt)

lemma power2_csqrt[algebra]: "(csqrt z)\<^sup>2 = z"
proof cases
  assume "Im z = 0" then show ?thesis
    using real_sqrt_pow2[of "Re z"] real_sqrt_pow2[of "- Re z"]
    by (cases "0::real" "Re z" rule: linorder_cases)
       (simp_all add: complex_eq_iff Re_power2 Im_power2 power2_eq_square cmod_eq_Re)
next
  assume "Im z \<noteq> 0"
  moreover
  have "cmod z * cmod z - Re z * Re z = Im z * Im z"
    by (simp add: norm_complex_def power2_eq_square)
  moreover
  have "\<bar>Re z\<bar> \<le> cmod z"
    by (simp add: norm_complex_def)
  ultimately show ?thesis
    by (simp add: Re_power2 Im_power2 complex_eq_iff real_sgn_eq
                  field_simps real_sqrt_mult[symmetric] real_sqrt_divide)
qed

lemma csqrt_eq_0 [simp]: "csqrt z = 0 \<longleftrightarrow> z = 0"
  by auto (metis power2_csqrt power_eq_0_iff)

lemma csqrt_eq_1 [simp]: "csqrt z = 1 \<longleftrightarrow> z = 1"
  by auto (metis power2_csqrt power2_eq_1_iff)

lemma csqrt_principal: "0 < Re (csqrt z) \<or> Re (csqrt z) = 0 \<and> 0 \<le> Im (csqrt z)"
  by (auto simp add: not_less cmod_plus_Re_le_0_iff Im_eq_0)

lemma Re_csqrt: "0 \<le> Re (csqrt z)"
  by (metis csqrt_principal le_less)

lemma csqrt_square:
  assumes "0 < Re b \<or> (Re b = 0 \<and> 0 \<le> Im b)"
  shows "csqrt (b^2) = b"
proof -
  have "csqrt (b^2) = b \<or> csqrt (b^2) = - b"
    unfolding power2_eq_iff[symmetric] by (simp add: power2_csqrt)
  moreover have "csqrt (b^2) \<noteq> -b \<or> b = 0"
    using csqrt_principal[of "b ^ 2"] assms by (intro disjCI notI) (auto simp: complex_eq_iff)
  ultimately show ?thesis
    by auto
qed

lemma csqrt_minus [simp]:
  assumes "Im x < 0 \<or> (Im x = 0 \<and> 0 \<le> Re x)"
  shows "csqrt (- x) = \<i> * csqrt x"
proof -
  have "csqrt ((\<i> * csqrt x)^2) = \<i> * csqrt x"
  proof (rule csqrt_square)
    have "Im (csqrt x) \<le> 0"
      using assms by (auto simp add: cmod_eq_Re mult_le_0_iff field_simps complex_Re_le_cmod)
    then show "0 < Re (\<i> * csqrt x) \<or> Re (\<i> * csqrt x) = 0 \<and> 0 \<le> Im (\<i> * csqrt x)"
      by (auto simp add: Re_csqrt simp del: csqrt.simps)
  qed
  also have "(\<i> * csqrt x)^2 = - x"
    by (simp add: power2_csqrt power_mult_distrib)
  finally show ?thesis .
qed

text {* Legacy theorem names *}

lemmas expand_complex_eq = complex_eq_iff
lemmas complex_Re_Im_cancel_iff = complex_eq_iff
lemmas complex_equality = complex_eqI
lemmas cmod_def = norm_complex_def
lemmas complex_norm_def = norm_complex_def
lemmas complex_divide_def = divide_complex_def

lemma legacy_Complex_simps:
  shows Complex_eq_0: "Complex a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
    and complex_add: "Complex a b + Complex c d = Complex (a + c) (b + d)"
    and complex_minus: "- (Complex a b) = Complex (- a) (- b)"
    and complex_diff: "Complex a b - Complex c d = Complex (a - c) (b - d)"
    and Complex_eq_1: "Complex a b = 1 \<longleftrightarrow> a = 1 \<and> b = 0"
    and Complex_eq_neg_1: "Complex a b = - 1 \<longleftrightarrow> a = - 1 \<and> b = 0"
    and complex_mult: "Complex a b * Complex c d = Complex (a * c - b * d) (a * d + b * c)"
    and complex_inverse: "inverse (Complex a b) = Complex (a / (a\<^sup>2 + b\<^sup>2)) (- b / (a\<^sup>2 + b\<^sup>2))"
    and Complex_eq_numeral: "Complex a b = numeral w \<longleftrightarrow> a = numeral w \<and> b = 0"
    and Complex_eq_neg_numeral: "Complex a b = - numeral w \<longleftrightarrow> a = - numeral w \<and> b = 0"
    and complex_scaleR: "scaleR r (Complex a b) = Complex (r * a) (r * b)"
    and Complex_eq_i: "(Complex x y = ii) = (x = 0 \<and> y = 1)"
    and i_mult_Complex: "ii * Complex a b = Complex (- b) a"
    and Complex_mult_i: "Complex a b * ii = Complex (- b) a"
    and i_complex_of_real: "ii * complex_of_real r = Complex 0 r"
    and complex_of_real_i: "complex_of_real r * ii = Complex 0 r"
    and Complex_add_complex_of_real: "Complex x y + complex_of_real r = Complex (x+r) y"
    and complex_of_real_add_Complex: "complex_of_real r + Complex x y = Complex (r+x) y"
    and Complex_mult_complex_of_real: "Complex x y * complex_of_real r = Complex (x*r) (y*r)"
    and complex_of_real_mult_Complex: "complex_of_real r * Complex x y = Complex (r*x) (r*y)"
    and complex_eq_cancel_iff2: "(Complex x y = complex_of_real xa) = (x = xa & y = 0)"
    and complex_cn: "cnj (Complex a b) = Complex a (- b)"
    and Complex_setsum': "setsum (%x. Complex (f x) 0) s = Complex (setsum f s) 0"
    and Complex_setsum: "Complex (setsum f s) 0 = setsum (%x. Complex (f x) 0) s"
    and complex_of_real_def: "complex_of_real r = Complex r 0"
    and complex_norm: "cmod (Complex x y) = sqrt (x\<^sup>2 + y\<^sup>2)"
  by (simp_all add: norm_complex_def field_simps complex_eq_iff Re_divide Im_divide del: Complex_eq)

lemma Complex_in_Reals: "Complex x 0 \<in> \<real>"
  by (metis Reals_of_real complex_of_real_def)

end

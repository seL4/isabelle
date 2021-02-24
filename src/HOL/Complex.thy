(*  Title:       HOL/Complex.thy
    Author:      Jacques D. Fleuriot, 2001 University of Edinburgh
    Author:      Lawrence C Paulson, 2003/4
*)

section \<open>Complex Numbers: Rectangular and Polar Representations\<close>

theory Complex
imports Transcendental
begin

text \<open>
  We use the \<^theory_text>\<open>codatatype\<close> command to define the type of complex numbers. This
  allows us to use \<^theory_text>\<open>primcorec\<close> to define complex functions by defining their
  real and imaginary result separately.
\<close>

codatatype complex = Complex (Re: real) (Im: real)

lemma complex_surj: "Complex (Re z) (Im z) = z"
  by (rule complex.collapse)

lemma complex_eqI [intro?]: "Re x = Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x = y"
  by (rule complex.expand) simp

lemma complex_eq_iff: "x = y \<longleftrightarrow> Re x = Re y \<and> Im x = Im y"
  by (auto intro: complex.expand)


subsection \<open>Addition and Subtraction\<close>

instantiation complex :: ab_group_add
begin

primcorec zero_complex
  where
    "Re 0 = 0"
  | "Im 0 = 0"

primcorec plus_complex
  where
    "Re (x + y) = Re x + Re y"
  | "Im (x + y) = Im x + Im y"

primcorec uminus_complex
  where
    "Re (- x) = - Re x"
  | "Im (- x) = - Im x"

primcorec minus_complex
  where
    "Re (x - y) = Re x - Re y"
  | "Im (x - y) = Im x - Im y"

instance
  by standard (simp_all add: complex_eq_iff)

end


subsection \<open>Multiplication and Division\<close>

instantiation complex :: field
begin

primcorec one_complex
  where
    "Re 1 = 1"
  | "Im 1 = 0"

primcorec times_complex
  where
    "Re (x * y) = Re x * Re y - Im x * Im y"
  | "Im (x * y) = Re x * Im y + Im x * Re y"

primcorec inverse_complex
  where
    "Re (inverse x) = Re x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)"
  | "Im (inverse x) = - Im x / ((Re x)\<^sup>2 + (Im x)\<^sup>2)"

definition "x div y = x * inverse y" for x y :: complex

instance
  by standard
     (simp_all add: complex_eq_iff divide_complex_def
      distrib_left distrib_right right_diff_distrib left_diff_distrib
      power2_eq_square add_divide_distrib [symmetric])

end

lemma Re_divide: "Re (x / y) = (Re x * Re y + Im x * Im y) / ((Re y)\<^sup>2 + (Im y)\<^sup>2)"
  by (simp add: divide_complex_def add_divide_distrib)

lemma Im_divide: "Im (x / y) = (Im x * Re y - Re x * Im y) / ((Re y)\<^sup>2 + (Im y)\<^sup>2)"
  by (simp add: divide_complex_def diff_divide_distrib)

lemma Complex_divide:
    "(x / y) = Complex ((Re x * Re y + Im x * Im y) / ((Re y)\<^sup>2 + (Im y)\<^sup>2))
                       ((Im x * Re y - Re x * Im y) / ((Re y)\<^sup>2 + (Im y)\<^sup>2))"
  by (metis Im_divide Re_divide complex_surj)

lemma Re_power2: "Re (x ^ 2) = (Re x)^2 - (Im x)^2"
  by (simp add: power2_eq_square)

lemma Im_power2: "Im (x ^ 2) = 2 * Re x * Im x"
  by (simp add: power2_eq_square)

lemma Re_power_real [simp]: "Im x = 0 \<Longrightarrow> Re (x ^ n) = Re x ^ n "
  by (induct n) simp_all

lemma Im_power_real [simp]: "Im x = 0 \<Longrightarrow> Im (x ^ n) = 0"
  by (induct n) simp_all


subsection \<open>Scalar Multiplication\<close>

instantiation complex :: real_field
begin

primcorec scaleR_complex
  where
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


subsection \<open>Numerals, Arithmetic, and Embedding from R\<close>

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

lemma Re_divide_of_nat [simp]: "Re (z / of_nat n) = Re z / of_nat n"
  by (cases n) (simp_all add: Re_divide field_split_simps power2_eq_square del: of_nat_Suc)

lemma Im_divide_of_nat [simp]: "Im (z / of_nat n) = Im z / of_nat n"
  by (cases n) (simp_all add: Im_divide field_split_simps power2_eq_square del: of_nat_Suc)

lemma of_real_Re [simp]: "z \<in> \<real> \<Longrightarrow> of_real (Re z) = z"
  by (auto simp: Reals_def)

lemma complex_Re_fact [simp]: "Re (fact n) = fact n"
proof -
  have "(fact n :: complex) = of_real (fact n)"
    by simp
  also have "Re \<dots> = fact n"
    by (subst Re_complex_of_real) simp_all
  finally show ?thesis .
qed

lemma complex_Im_fact [simp]: "Im (fact n) = 0"
  by (subst of_nat_fact [symmetric]) (simp only: complex_Im_of_nat)

lemma Re_prod_Reals: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<real>) \<Longrightarrow> Re (prod f A) = prod (\<lambda>x. Re (f x)) A"
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  hence "Re (prod f (insert x A)) = Re (f x) * Re (prod f A) - Im (f x) * Im (prod f A)"
    by simp
  also from insert.prems have "f x \<in> \<real>" by simp
  hence "Im (f x) = 0" by (auto elim!: Reals_cases)
  also have "Re (prod f A) = (\<Prod>x\<in>A. Re (f x))"
    by (intro insert.IH insert.prems) auto
  finally show ?case using insert.hyps by simp
qed auto


subsection \<open>The Complex Number $i$\<close>

primcorec imaginary_unit :: complex  ("\<i>")
  where
    "Re \<i> = 0"
  | "Im \<i> = 1"

lemma Complex_eq: "Complex a b = a + \<i> * b"
  by (simp add: complex_eq_iff)

lemma complex_eq: "a = Re a + \<i> * Im a"
  by (simp add: complex_eq_iff)

lemma fun_complex_eq: "f = (\<lambda>x. Re (f x) + \<i> * Im (f x))"
  by (simp add: fun_eq_iff complex_eq)

lemma i_squared [simp]: "\<i> * \<i> = -1"
  by (simp add: complex_eq_iff)

lemma power2_i [simp]: "\<i>\<^sup>2 = -1"
  by (simp add: power2_eq_square)

lemma inverse_i [simp]: "inverse \<i> = - \<i>"
  by (rule inverse_unique) simp

lemma divide_i [simp]: "x / \<i> = - \<i> * x"
  by (simp add: divide_complex_def)

lemma complex_i_mult_minus [simp]: "\<i> * (\<i> * x) = - x"
  by (simp add: mult.assoc [symmetric])

lemma complex_i_not_zero [simp]: "\<i> \<noteq> 0"
  by (simp add: complex_eq_iff)

lemma complex_i_not_one [simp]: "\<i> \<noteq> 1"
  by (simp add: complex_eq_iff)

lemma complex_i_not_numeral [simp]: "\<i> \<noteq> numeral w"
  by (simp add: complex_eq_iff)

lemma complex_i_not_neg_numeral [simp]: "\<i> \<noteq> - numeral w"
  by (simp add: complex_eq_iff)

lemma complex_split_polar: "\<exists>r a. z = complex_of_real r * (cos a + \<i> * sin a)"
  by (simp add: complex_eq_iff polar_Ex)

lemma i_even_power [simp]: "\<i> ^ (n * 2) = (-1) ^ n"
  by (metis mult.commute power2_i power_mult)

lemma Re_i_times [simp]: "Re (\<i> * z) = - Im z"
  by simp

lemma Im_i_times [simp]: "Im (\<i> * z) = Re z"
  by simp

lemma i_times_eq_iff: "\<i> * w = z \<longleftrightarrow> w = - (\<i> * z)"
  by auto

lemma divide_numeral_i [simp]: "z / (numeral n * \<i>) = - (\<i> * z) / numeral n"
  by (metis divide_divide_eq_left divide_i mult.commute mult_minus_right)

lemma imaginary_eq_real_iff [simp]:
  assumes "y \<in> Reals" "x \<in> Reals"
  shows "\<i> * y = x \<longleftrightarrow> x=0 \<and> y=0"
    using assms
    unfolding Reals_def
    apply clarify
      apply (rule iffI)
    apply (metis Im_complex_of_real Im_i_times Re_complex_of_real mult_eq_0_iff of_real_0)
    by simp

lemma real_eq_imaginary_iff [simp]:
  assumes "y \<in> Reals" "x \<in> Reals"
  shows "x = \<i> * y  \<longleftrightarrow> x=0 \<and> y=0"
    using assms imaginary_eq_real_iff by fastforce

subsection \<open>Vector Norm\<close>

instantiation complex :: real_normed_field
begin

definition "norm z = sqrt ((Re z)\<^sup>2 + (Im z)\<^sup>2)"

abbreviation cmod :: "complex \<Rightarrow> real"
  where "cmod \<equiv> norm"

definition complex_sgn_def: "sgn x = x /\<^sub>R cmod x"

definition dist_complex_def: "dist x y = cmod (x - y)"

definition uniformity_complex_def [code del]:
  "(uniformity :: (complex \<times> complex) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_complex_def [code del]:
  "open (U :: complex set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance
proof
  fix r :: real and x y :: complex and S :: "complex set"
  show "(norm x = 0) = (x = 0)"
    by (simp add: norm_complex_def complex_eq_iff)
  show "norm (x + y) \<le> norm x + norm y"
    by (simp add: norm_complex_def complex_eq_iff real_sqrt_sum_squares_triangle_ineq)
  show "norm (scaleR r x) = \<bar>r\<bar> * norm x"
    by (simp add: norm_complex_def complex_eq_iff power_mult_distrib distrib_left [symmetric]
        real_sqrt_mult)
  show "norm (x * y) = norm x * norm y"
    by (simp add: norm_complex_def complex_eq_iff real_sqrt_mult [symmetric]
        power2_eq_square algebra_simps)
qed (rule complex_sgn_def dist_complex_def open_complex_def uniformity_complex_def)+

end

declare uniformity_Abort[where 'a = complex, code]

lemma norm_ii [simp]: "norm \<i> = 1"
  by (simp add: norm_complex_def)

lemma cmod_unit_one: "cmod (cos a + \<i> * sin a) = 1"
  by (simp add: norm_complex_def)

lemma cmod_complex_polar: "cmod (r * (cos a + \<i> * sin a)) = \<bar>r\<bar>"
  by (simp add: norm_mult cmod_unit_one)

lemma complex_Re_le_cmod: "Re x \<le> cmod x"
  unfolding norm_complex_def by (rule real_sqrt_sum_squares_ge1)

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

lemma cmod_power2: "(cmod z)\<^sup>2 = (Re z)\<^sup>2 + (Im z)\<^sup>2"
  by (simp add: norm_complex_def)

lemma cmod_plus_Re_le_0_iff: "cmod z + Re z \<le> 0 \<longleftrightarrow> Re z = - cmod z"
  using abs_Re_le_cmod[of z] by auto

lemma cmod_Re_le_iff: "Im x = Im y \<Longrightarrow> cmod x \<le> cmod y \<longleftrightarrow> \<bar>Re x\<bar> \<le> \<bar>Re y\<bar>"
  by (metis add.commute add_le_cancel_left norm_complex_def real_sqrt_abs real_sqrt_le_iff)

lemma cmod_Im_le_iff: "Re x = Re y \<Longrightarrow> cmod x \<le> cmod y \<longleftrightarrow> \<bar>Im x\<bar> \<le> \<bar>Im y\<bar>"
  by (metis add_le_cancel_left norm_complex_def real_sqrt_abs real_sqrt_le_iff)

lemma Im_eq_0: "\<bar>Re z\<bar> = cmod z \<Longrightarrow> Im z = 0"
  by (subst (asm) power_eq_iff_eq_base[symmetric, where n=2]) (auto simp add: norm_complex_def)

lemma abs_sqrt_wlog: "(\<And>x. x \<ge> 0 \<Longrightarrow> P x (x\<^sup>2)) \<Longrightarrow> P \<bar>x\<bar> (x\<^sup>2)"
  for x::"'a::linordered_idom"
  by (metis abs_ge_zero power2_abs)

lemma complex_abs_le_norm: "\<bar>Re z\<bar> + \<bar>Im z\<bar> \<le> sqrt 2 * norm z"
  unfolding norm_complex_def
  apply (rule abs_sqrt_wlog [where x="Re z"])
  apply (rule abs_sqrt_wlog [where x="Im z"])
  apply (rule power2_le_imp_le)
   apply (simp_all add: power2_sum add.commute sum_squares_bound real_sqrt_mult [symmetric])
  done

lemma complex_unit_circle: "z \<noteq> 0 \<Longrightarrow> (Re z / cmod z)\<^sup>2 + (Im z / cmod z)\<^sup>2 = 1"
  by (simp add: norm_complex_def complex_eq_iff power2_eq_square add_divide_distrib [symmetric])


text \<open>Properties of complex signum.\<close>

lemma sgn_eq: "sgn z = z / complex_of_real (cmod z)"
  by (simp add: sgn_div_norm divide_inverse scaleR_conv_of_real mult.commute)

lemma Re_sgn [simp]: "Re(sgn z) = Re(z)/cmod z"
  by (simp add: complex_sgn_def divide_inverse)

lemma Im_sgn [simp]: "Im(sgn z) = Im(z)/cmod z"
  by (simp add: complex_sgn_def divide_inverse)


subsection \<open>Absolute value\<close>

instantiation complex :: field_abs_sgn
begin

definition abs_complex :: "complex \<Rightarrow> complex"
  where "abs_complex = of_real \<circ> norm"

instance
  apply standard
         apply (auto simp add: abs_complex_def complex_sgn_def norm_mult)
  apply (auto simp add: scaleR_conv_of_real field_simps)
  done

end


subsection \<open>Completeness of the Complexes\<close>

lemma bounded_linear_Re: "bounded_linear Re"
  by (rule bounded_linear_intro [where K=1]) (simp_all add: norm_complex_def)

lemma bounded_linear_Im: "bounded_linear Im"
  by (rule bounded_linear_intro [where K=1]) (simp_all add: norm_complex_def)

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
  "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. Complex (f x) (g x)) \<longlongrightarrow> Complex a b) F"
  unfolding Complex_eq by (auto intro!: tendsto_intros)

lemma tendsto_complex_iff:
  "(f \<longlongrightarrow> x) F \<longleftrightarrow> (((\<lambda>x. Re (f x)) \<longlongrightarrow> Re x) F \<and> ((\<lambda>x. Im (f x)) \<longlongrightarrow> Im x) F)"
proof safe
  assume "((\<lambda>x. Re (f x)) \<longlongrightarrow> Re x) F" "((\<lambda>x. Im (f x)) \<longlongrightarrow> Im x) F"
  from tendsto_Complex[OF this] show "(f \<longlongrightarrow> x) F"
    unfolding complex.collapse .
qed (auto intro: tendsto_intros)

lemma continuous_complex_iff:
  "continuous F f \<longleftrightarrow> continuous F (\<lambda>x. Re (f x)) \<and> continuous F (\<lambda>x. Im (f x))"
  by (simp only: continuous_def tendsto_complex_iff)

lemma continuous_on_of_real_o_iff [simp]:
     "continuous_on S (\<lambda>x. complex_of_real (g x)) = continuous_on S g"
  using continuous_on_Re continuous_on_of_real  by fastforce

lemma continuous_on_of_real_id [simp]:
     "continuous_on S (of_real :: real \<Rightarrow> 'a::real_normed_algebra_1)"
  by (rule continuous_on_of_real [OF continuous_on_id])

lemma has_vector_derivative_complex_iff: "(f has_vector_derivative x) F \<longleftrightarrow>
    ((\<lambda>x. Re (f x)) has_field_derivative (Re x)) F \<and>
    ((\<lambda>x. Im (f x)) has_field_derivative (Im x)) F"
  by (simp add: has_vector_derivative_def has_field_derivative_def has_derivative_def
      tendsto_complex_iff algebra_simps bounded_linear_scaleR_left bounded_linear_mult_right)

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
  then have "(\<lambda>n. Complex (Re (X n)) (Im (X n))) \<longlonglongrightarrow>
    Complex (lim (\<lambda>n. Re (X n))) (lim (\<lambda>n. Im (X n)))"
    by (intro tendsto_Complex convergent_LIMSEQ_iff[THEN iffD1]
        Cauchy_convergent_iff[THEN iffD1] Cauchy_Re Cauchy_Im)
  then show "convergent X"
    unfolding complex.collapse by (rule convergentI)
qed

declare DERIV_power[where 'a=complex, unfolded of_nat_def[symmetric], derivative_intros]


subsection \<open>Complex Conjugation\<close>

primcorec cnj :: "complex \<Rightarrow> complex"
  where
    "Re (cnj z) = Re z"
  | "Im (cnj z) = - Im z"

lemma complex_cnj_cancel_iff [simp]: "cnj x = cnj y \<longleftrightarrow> x = y"
  by (simp add: complex_eq_iff)

lemma complex_cnj_cnj [simp]: "cnj (cnj z) = z"
  by (simp add: complex_eq_iff)

lemma complex_cnj_zero [simp]: "cnj 0 = 0"
  by (simp add: complex_eq_iff)

lemma complex_cnj_zero_iff [iff]: "cnj z = 0 \<longleftrightarrow> z = 0"
  by (simp add: complex_eq_iff)

lemma complex_cnj_one_iff [simp]: "cnj z = 1 \<longleftrightarrow> z = 1"
  by (simp add: complex_eq_iff)

lemma complex_cnj_add [simp]: "cnj (x + y) = cnj x + cnj y"
  by (simp add: complex_eq_iff)

lemma cnj_sum [simp]: "cnj (sum f s) = (\<Sum>x\<in>s. cnj (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma complex_cnj_diff [simp]: "cnj (x - y) = cnj x - cnj y"
  by (simp add: complex_eq_iff)

lemma complex_cnj_minus [simp]: "cnj (- x) = - cnj x"
  by (simp add: complex_eq_iff)

lemma complex_cnj_one [simp]: "cnj 1 = 1"
  by (simp add: complex_eq_iff)

lemma complex_cnj_mult [simp]: "cnj (x * y) = cnj x * cnj y"
  by (simp add: complex_eq_iff)

lemma cnj_prod [simp]: "cnj (prod f s) = (\<Prod>x\<in>s. cnj (f x))"
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

lemma complex_cnj_i [simp]: "cnj \<i> = - \<i>"
  by (simp add: complex_eq_iff)

lemma complex_add_cnj: "z + cnj z = complex_of_real (2 * Re z)"
  by (simp add: complex_eq_iff)

lemma complex_diff_cnj: "z - cnj z = complex_of_real (2 * Im z) * \<i>"
  by (simp add: complex_eq_iff)

lemma Ints_cnj [intro]: "x \<in> \<int> \<Longrightarrow> cnj x \<in> \<int>"
  by (auto elim!: Ints_cases)

lemma cnj_in_Ints_iff [simp]: "cnj x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  using Ints_cnj[of x] Ints_cnj[of "cnj x"] by auto

lemma complex_mult_cnj: "z * cnj z = complex_of_real ((Re z)\<^sup>2 + (Im z)\<^sup>2)"
  by (simp add: complex_eq_iff power2_eq_square)

lemma cnj_add_mult_eq_Re: "z * cnj w + cnj z * w = 2 * Re (z * cnj w)"
  by (rule complex_eqI) auto

lemma complex_mod_mult_cnj: "cmod (z * cnj z) = (cmod z)\<^sup>2"
  by (simp add: norm_mult power2_eq_square)

lemma complex_mod_sqrt_Re_mult_cnj: "cmod z = sqrt (Re (z * cnj z))"
  by (simp add: norm_complex_def power2_eq_square)

lemma complex_In_mult_cnj_zero [simp]: "Im (z * cnj z) = 0"
  by simp

lemma complex_cnj_fact [simp]: "cnj (fact n) = fact n"
  by (subst of_nat_fact [symmetric], subst complex_cnj_of_nat) simp

lemma complex_cnj_pochhammer [simp]: "cnj (pochhammer z n) = pochhammer (cnj z) n"
  by (induct n arbitrary: z) (simp_all add: pochhammer_rec)

lemma bounded_linear_cnj: "bounded_linear cnj"
  using complex_cnj_add complex_cnj_scaleR by (rule bounded_linear_intro [where K=1]) simp

lemma linear_cnj: "linear cnj"
  using bounded_linear.linear[OF bounded_linear_cnj] .

lemmas tendsto_cnj [tendsto_intros] = bounded_linear.tendsto [OF bounded_linear_cnj]
  and isCont_cnj [simp] = bounded_linear.isCont [OF bounded_linear_cnj]
  and continuous_cnj [simp, continuous_intros] = bounded_linear.continuous [OF bounded_linear_cnj]
  and continuous_on_cnj [simp, continuous_intros] = bounded_linear.continuous_on [OF bounded_linear_cnj]
  and has_derivative_cnj [simp, derivative_intros] = bounded_linear.has_derivative [OF bounded_linear_cnj]

lemma lim_cnj: "((\<lambda>x. cnj(f x)) \<longlongrightarrow> cnj l) F \<longleftrightarrow> (f \<longlongrightarrow> l) F"
  by (simp add: tendsto_iff dist_complex_def complex_cnj_diff [symmetric] del: complex_cnj_diff)

lemma sums_cnj: "((\<lambda>x. cnj(f x)) sums cnj l) \<longleftrightarrow> (f sums l)"
  by (simp add: sums_def lim_cnj cnj_sum [symmetric] del: cnj_sum)

lemma differentiable_cnj_iff:
  "(\<lambda>z. cnj (f z)) differentiable at x within A \<longleftrightarrow> f differentiable at x within A"
proof
  assume "(\<lambda>z. cnj (f z)) differentiable at x within A"
  then obtain D where "((\<lambda>z. cnj (f z)) has_derivative D) (at x within A)"
    by (auto simp: differentiable_def)
  from has_derivative_cnj[OF this] show "f differentiable at x within A"
    by (auto simp: differentiable_def)
next
  assume "f differentiable at x within A"
  then obtain D where "(f has_derivative D) (at x within A)"
    by (auto simp: differentiable_def)
  from has_derivative_cnj[OF this] show "(\<lambda>z. cnj (f z)) differentiable at x within A"
    by (auto simp: differentiable_def)
qed

lemma has_vector_derivative_cnj [derivative_intros]:
  assumes "(f has_vector_derivative f') (at z within A)"
  shows   "((\<lambda>z. cnj (f z)) has_vector_derivative cnj f') (at z within A)"
  using assms by (auto simp: has_vector_derivative_complex_iff intro: derivative_intros)


subsection \<open>Basic Lemmas\<close>

lemma complex_eq_0: "z=0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 = 0"
  by (metis zero_complex.sel complex_eqI sum_power2_eq_zero_iff)

lemma complex_neq_0: "z\<noteq>0 \<longleftrightarrow> (Re z)\<^sup>2 + (Im z)\<^sup>2 > 0"
  by (metis complex_eq_0 less_numeral_extra(3) sum_power2_gt_zero_iff)

lemma complex_norm_square: "of_real ((norm z)\<^sup>2) = z * cnj z"
  by (cases z)
    (auto simp: complex_eq_iff norm_complex_def power2_eq_square[symmetric] of_real_power[symmetric]
      simp del: of_real_power)

lemma complex_div_cnj: "a / b = (a * cnj b) / (norm b)\<^sup>2"
  using complex_norm_square by auto

lemma Re_complex_div_eq_0: "Re (a / b) = 0 \<longleftrightarrow> Re (a * cnj b) = 0"
  by (auto simp add: Re_divide)

lemma Im_complex_div_eq_0: "Im (a / b) = 0 \<longleftrightarrow> Im (a * cnj b) = 0"
  by (auto simp add: Im_divide)

lemma complex_div_gt_0: "(Re (a / b) > 0 \<longleftrightarrow> Re (a * cnj b) > 0) \<and> (Im (a / b) > 0 \<longleftrightarrow> Im (a * cnj b) > 0)"
proof (cases "b = 0")
  case True
  then show ?thesis by auto
next
  case False
  then have "0 < (Re b)\<^sup>2 + (Im b)\<^sup>2"
    by (simp add: complex_eq_iff sum_power2_gt_zero_iff)
  then show ?thesis
    by (simp add: Re_divide Im_divide zero_less_divide_iff)
qed

lemma Re_complex_div_gt_0: "Re (a / b) > 0 \<longleftrightarrow> Re (a * cnj b) > 0"
  and Im_complex_div_gt_0: "Im (a / b) > 0 \<longleftrightarrow> Im (a * cnj b) > 0"
  using complex_div_gt_0 by auto

lemma Re_complex_div_ge_0: "Re (a / b) \<ge> 0 \<longleftrightarrow> Re (a * cnj b) \<ge> 0"
  by (metis le_less Re_complex_div_eq_0 Re_complex_div_gt_0)

lemma Im_complex_div_ge_0: "Im (a / b) \<ge> 0 \<longleftrightarrow> Im (a * cnj b) \<ge> 0"
  by (metis Im_complex_div_eq_0 Im_complex_div_gt_0 le_less)

lemma Re_complex_div_lt_0: "Re (a / b) < 0 \<longleftrightarrow> Re (a * cnj b) < 0"
  by (metis less_asym neq_iff Re_complex_div_eq_0 Re_complex_div_gt_0)

lemma Im_complex_div_lt_0: "Im (a / b) < 0 \<longleftrightarrow> Im (a * cnj b) < 0"
  by (metis Im_complex_div_eq_0 Im_complex_div_gt_0 less_asym neq_iff)

lemma Re_complex_div_le_0: "Re (a / b) \<le> 0 \<longleftrightarrow> Re (a * cnj b) \<le> 0"
  by (metis not_le Re_complex_div_gt_0)

lemma Im_complex_div_le_0: "Im (a / b) \<le> 0 \<longleftrightarrow> Im (a * cnj b) \<le> 0"
  by (metis Im_complex_div_gt_0 not_le)

lemma Re_divide_of_real [simp]: "Re (z / of_real r) = Re z / r"
  by (simp add: Re_divide power2_eq_square)

lemma Im_divide_of_real [simp]: "Im (z / of_real r) = Im z / r"
  by (simp add: Im_divide power2_eq_square)

lemma Re_divide_Reals [simp]: "r \<in> \<real> \<Longrightarrow> Re (z / r) = Re z / Re r"
  by (metis Re_divide_of_real of_real_Re)

lemma Im_divide_Reals [simp]: "r \<in> \<real> \<Longrightarrow> Im (z / r) = Im z / Re r"
  by (metis Im_divide_of_real of_real_Re)

lemma Re_sum[simp]: "Re (sum f s) = (\<Sum>x\<in>s. Re (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma Im_sum[simp]: "Im (sum f s) = (\<Sum>x\<in>s. Im(f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma sums_complex_iff: "f sums x \<longleftrightarrow> ((\<lambda>x. Re (f x)) sums Re x) \<and> ((\<lambda>x. Im (f x)) sums Im x)"
  unfolding sums_def tendsto_complex_iff Im_sum Re_sum ..

lemma summable_complex_iff: "summable f \<longleftrightarrow> summable (\<lambda>x. Re (f x)) \<and>  summable (\<lambda>x. Im (f x))"
  unfolding summable_def sums_complex_iff[abs_def] by (metis complex.sel)

lemma summable_complex_of_real [simp]: "summable (\<lambda>n. complex_of_real (f n)) \<longleftrightarrow> summable f"
  unfolding summable_complex_iff by simp

lemma summable_Re: "summable f \<Longrightarrow> summable (\<lambda>x. Re (f x))"
  unfolding summable_complex_iff by blast

lemma summable_Im: "summable f \<Longrightarrow> summable (\<lambda>x. Im (f x))"
  unfolding summable_complex_iff by blast

lemma complex_is_Nat_iff: "z \<in> \<nat> \<longleftrightarrow> Im z = 0 \<and> (\<exists>i. Re z = of_nat i)"
  by (auto simp: Nats_def complex_eq_iff)

lemma complex_is_Int_iff: "z \<in> \<int> \<longleftrightarrow> Im z = 0 \<and> (\<exists>i. Re z = of_int i)"
  by (auto simp: Ints_def complex_eq_iff)

lemma complex_is_Real_iff: "z \<in> \<real> \<longleftrightarrow> Im z = 0"
  by (auto simp: Reals_def complex_eq_iff)

lemma Reals_cnj_iff: "z \<in> \<real> \<longleftrightarrow> cnj z = z"
  by (auto simp: complex_is_Real_iff complex_eq_iff)

lemma in_Reals_norm: "z \<in> \<real> \<Longrightarrow> norm z = \<bar>Re z\<bar>"
  by (simp add: complex_is_Real_iff norm_complex_def)

lemma Re_Reals_divide: "r \<in> \<real> \<Longrightarrow> Re (r / z) = Re r * Re z / (norm z)\<^sup>2"
  by (simp add: Re_divide complex_is_Real_iff cmod_power2)

lemma Im_Reals_divide: "r \<in> \<real> \<Longrightarrow> Im (r / z) = -Re r * Im z / (norm z)\<^sup>2"
  by (simp add: Im_divide complex_is_Real_iff cmod_power2)

lemma series_comparison_complex:
  fixes f:: "nat \<Rightarrow> 'a::banach"
  assumes sg: "summable g"
    and "\<And>n. g n \<in> \<real>" "\<And>n. Re (g n) \<ge> 0"
    and fg: "\<And>n. n \<ge> N \<Longrightarrow> norm(f n) \<le> norm(g n)"
  shows "summable f"
proof -
  have g: "\<And>n. cmod (g n) = Re (g n)"
    using assms by (metis abs_of_nonneg in_Reals_norm)
  show ?thesis
    apply (rule summable_comparison_test' [where g = "\<lambda>n. norm (g n)" and N=N])
    using sg
     apply (auto simp: summable_def)
     apply (rule_tac x = "Re s" in exI)
     apply (auto simp: g sums_Re)
    apply (metis fg g)
    done
qed


subsection \<open>Polar Form for Complex Numbers\<close>

lemma complex_unimodular_polar:
  assumes "norm z = 1"
  obtains t where "0 \<le> t" "t < 2 * pi" "z = Complex (cos t) (sin t)"
  by (metis cmod_power2 one_power2 complex_surj sincos_total_2pi [of "Re z" "Im z"] assms)


subsubsection \<open>$\cos \theta + i \sin \theta$\<close>

primcorec cis :: "real \<Rightarrow> complex"
  where
    "Re (cis a) = cos a"
  | "Im (cis a) = sin a"

lemma cis_zero [simp]: "cis 0 = 1"
  by (simp add: complex_eq_iff)

lemma norm_cis [simp]: "norm (cis a) = 1"
  by (simp add: norm_complex_def)

lemma sgn_cis [simp]: "sgn (cis a) = cis a"
  by (simp add: sgn_div_norm)

lemma cis_2pi [simp]: "cis (2 * pi) = 1"
  by (simp add: cis.ctr complex_eq_iff)

lemma cis_neq_zero [simp]: "cis a \<noteq> 0"
  by (metis norm_cis norm_zero zero_neq_one)

lemma cis_cnj: "cnj (cis t) = cis (-t)"
  by (simp add: complex_eq_iff)

lemma cis_mult: "cis a * cis b = cis (a + b)"
  by (simp add: complex_eq_iff cos_add sin_add)

lemma DeMoivre: "(cis a) ^ n = cis (real n * a)"
  by (induct n) (simp_all add: algebra_simps cis_mult)

lemma cis_inverse [simp]: "inverse (cis a) = cis (- a)"
  by (simp add: complex_eq_iff)

lemma cis_divide: "cis a / cis b = cis (a - b)"
  by (simp add: divide_complex_def cis_mult)

lemma cos_n_Re_cis_pow_n: "cos (real n * a) = Re (cis a ^ n)"
  by (auto simp add: DeMoivre)

lemma sin_n_Im_cis_pow_n: "sin (real n * a) = Im (cis a ^ n)"
  by (auto simp add: DeMoivre)

lemma cis_pi [simp]: "cis pi = -1"
  by (simp add: complex_eq_iff)

lemma cis_pi_half[simp]: "cis (pi / 2) = \<i>"
  by (simp add: cis.ctr complex_eq_iff)

lemma cis_minus_pi_half[simp]: "cis (-(pi / 2)) = -\<i>"
  by (simp add: cis.ctr complex_eq_iff)

lemma cis_multiple_2pi[simp]: "n \<in> \<int> \<Longrightarrow> cis (2 * pi * n) = 1"
  by (auto elim!: Ints_cases simp: cis.ctr one_complex.ctr)


subsubsection \<open>$r(\cos \theta + i \sin \theta)$\<close>

definition rcis :: "real \<Rightarrow> real \<Rightarrow> complex"
  where "rcis r a = complex_of_real r * cis a"

lemma Re_rcis [simp]: "Re(rcis r a) = r * cos a"
  by (simp add: rcis_def)

lemma Im_rcis [simp]: "Im(rcis r a) = r * sin a"
  by (simp add: rcis_def)

lemma rcis_Ex: "\<exists>r a. z = rcis r a"
  by (simp add: complex_eq_iff polar_Ex)

lemma complex_mod_rcis [simp]: "cmod (rcis r a) = \<bar>r\<bar>"
  by (simp add: rcis_def norm_mult)

lemma cis_rcis_eq: "cis a = rcis 1 a"
  by (simp add: rcis_def)

lemma rcis_mult: "rcis r1 a * rcis r2 b = rcis (r1 * r2) (a + b)"
  by (simp add: rcis_def cis_mult)

lemma rcis_zero_mod [simp]: "rcis 0 a = 0"
  by (simp add: rcis_def)

lemma rcis_zero_arg [simp]: "rcis r 0 = complex_of_real r"
  by (simp add: rcis_def)

lemma rcis_eq_zero_iff [simp]: "rcis r a = 0 \<longleftrightarrow> r = 0"
  by (simp add: rcis_def)

lemma DeMoivre2: "(rcis r a) ^ n = rcis (r ^ n) (real n * a)"
  by (simp add: rcis_def power_mult_distrib DeMoivre)

lemma rcis_inverse: "inverse(rcis r a) = rcis (1 / r) (- a)"
  by (simp add: divide_inverse rcis_def)

lemma rcis_divide: "rcis r1 a / rcis r2 b = rcis (r1 / r2) (a - b)"
  by (simp add: rcis_def cis_divide [symmetric])


subsubsection \<open>Complex exponential\<close>

lemma exp_Reals_eq:
  assumes "z \<in> \<real>"
  shows   "exp z = of_real (exp (Re z))"
  using assms by (auto elim!: Reals_cases simp: exp_of_real)

lemma cis_conv_exp: "cis b = exp (\<i> * b)"
proof -
  have "(\<i> * complex_of_real b) ^ n /\<^sub>R fact n =
      of_real (cos_coeff n * b^n) + \<i> * of_real (sin_coeff n * b^n)"
    for n :: nat
  proof -
    have "\<i> ^ n = fact n *\<^sub>R (cos_coeff n + \<i> * sin_coeff n)"
      by (induct n)
        (simp_all add: sin_coeff_Suc cos_coeff_Suc complex_eq_iff Re_divide Im_divide field_simps
          power2_eq_square add_nonneg_eq_0_iff)
    then show ?thesis
      by (simp add: field_simps)
  qed
  then show ?thesis
    using sin_converges [of b] cos_converges [of b]
    by (auto simp add: Complex_eq cis.ctr exp_def simp del: of_real_mult
        intro!: sums_unique sums_add sums_mult sums_of_real)
qed

lemma exp_eq_polar: "exp z = exp (Re z) * cis (Im z)"
  unfolding cis_conv_exp exp_of_real [symmetric] mult_exp_exp
  by (cases z) (simp add: Complex_eq)

lemma Re_exp: "Re (exp z) = exp (Re z) * cos (Im z)"
  unfolding exp_eq_polar by simp

lemma Im_exp: "Im (exp z) = exp (Re z) * sin (Im z)"
  unfolding exp_eq_polar by simp

lemma norm_cos_sin [simp]: "norm (Complex (cos t) (sin t)) = 1"
  by (simp add: norm_complex_def)

lemma norm_exp_eq_Re [simp]: "norm (exp z) = exp (Re z)"
  by (simp add: cis.code cmod_complex_polar exp_eq_polar Complex_eq)

lemma complex_exp_exists: "\<exists>a r. z = complex_of_real r * exp a"
  apply (insert rcis_Ex [of z])
  apply (auto simp add: exp_eq_polar rcis_def mult.assoc [symmetric])
  apply (rule_tac x = "\<i> * complex_of_real a" in exI)
  apply auto
  done

lemma exp_pi_i [simp]: "exp (of_real pi * \<i>) = -1"
  by (metis cis_conv_exp cis_pi mult.commute)

lemma exp_pi_i' [simp]: "exp (\<i> * of_real pi) = -1"
  using cis_conv_exp cis_pi by auto

lemma exp_two_pi_i [simp]: "exp (2 * of_real pi * \<i>) = 1"
  by (simp add: exp_eq_polar complex_eq_iff)

lemma exp_two_pi_i' [simp]: "exp (\<i> * (of_real pi * 2)) = 1"
  by (metis exp_two_pi_i mult.commute)

lemma continuous_on_cis [continuous_intros]:
  "continuous_on A f \<Longrightarrow> continuous_on A (\<lambda>x. cis (f x))"
  by (auto simp: cis_conv_exp intro!: continuous_intros)


subsubsection \<open>Complex argument\<close>

definition arg :: "complex \<Rightarrow> real"
  where "arg z = (if z = 0 then 0 else (SOME a. sgn z = cis a \<and> - pi < a \<and> a \<le> pi))"

lemma arg_zero: "arg 0 = 0"
  by (simp add: arg_def)

lemma arg_unique:
  assumes "sgn z = cis x" and "-pi < x" and "x \<le> pi"
  shows "arg z = x"
proof -
  from assms have "z \<noteq> 0" by auto
  have "(SOME a. sgn z = cis a \<and> -pi < a \<and> a \<le> pi) = x"
  proof
    fix a
    define d where "d = a - x"
    assume a: "sgn z = cis a \<and> - pi < a \<and> a \<le> pi"
    from a assms have "- (2*pi) < d \<and> d < 2*pi"
      unfolding d_def by simp
    moreover
    from a assms have "cos a = cos x" and "sin a = sin x"
      by (simp_all add: complex_eq_iff)
    then have cos: "cos d = 1"
      by (simp add: d_def cos_diff)
    moreover from cos have "sin d = 0"
      by (rule cos_one_sin_zero)
    ultimately have "d = 0"
      by (auto simp: sin_zero_iff elim!: evenE dest!: less_2_cases)
    then show "a = x"
      by (simp add: d_def)
  qed (simp add: assms del: Re_sgn Im_sgn)
  with \<open>z \<noteq> 0\<close> show "arg z = x"
    by (simp add: arg_def)
qed

lemma arg_correct:
  assumes "z \<noteq> 0"
  shows "sgn z = cis (arg z) \<and> -pi < arg z \<and> arg z \<le> pi"
proof (simp add: arg_def assms, rule someI_ex)
  obtain r a where z: "z = rcis r a"
    using rcis_Ex by fast
  with assms have "r \<noteq> 0" by auto
  define b where "b = (if 0 < r then a else a + pi)"
  have b: "sgn z = cis b"
    using \<open>r \<noteq> 0\<close> by (simp add: z b_def rcis_def of_real_def sgn_scaleR sgn_if complex_eq_iff)
  have cis_2pi_nat: "cis (2 * pi * real_of_nat n) = 1" for n
    by (induct n) (simp_all add: distrib_left cis_mult [symmetric] complex_eq_iff)
  have cis_2pi_int: "cis (2 * pi * real_of_int x) = 1" for x
    by (cases x rule: int_diff_cases)
      (simp add: right_diff_distrib cis_divide [symmetric] cis_2pi_nat)
  define c where "c = b - 2 * pi * of_int \<lceil>(b - pi) / (2 * pi)\<rceil>"
  have "sgn z = cis c"
    by (simp add: b c_def cis_divide [symmetric] cis_2pi_int)
  moreover have "- pi < c \<and> c \<le> pi"
    using ceiling_correct [of "(b - pi) / (2*pi)"]
    by (simp add: c_def less_divide_eq divide_le_eq algebra_simps del: le_of_int_ceiling)
  ultimately show "\<exists>a. sgn z = cis a \<and> -pi < a \<and> a \<le> pi"
    by fast
qed

lemma arg_bounded: "- pi < arg z \<and> arg z \<le> pi"
  by (cases "z = 0") (simp_all add: arg_zero arg_correct)

lemma cis_arg: "z \<noteq> 0 \<Longrightarrow> cis (arg z) = sgn z"
  by (simp add: arg_correct)

lemma rcis_cmod_arg: "rcis (cmod z) (arg z) = z"
  by (cases "z = 0") (simp_all add: rcis_def cis_arg sgn_div_norm of_real_def)

lemma cos_arg_i_mult_zero [simp]: "y \<noteq> 0 \<Longrightarrow> Re y = 0 \<Longrightarrow> cos (arg y) = 0"
  using cis_arg [of y] by (simp add: complex_eq_iff)

lemma arg_ii [simp]: "arg \<i> = pi/2"
  by (rule arg_unique; simp add: sgn_eq)

lemma arg_minus_ii [simp]: "arg (-\<i>) = -pi/2"
proof (rule arg_unique)
  show "sgn (- \<i>) = cis (- pi / 2)"
    by (simp add: sgn_eq)
  show "- pi / 2 \<le> pi"
    using pi_not_less_zero by linarith
qed auto

subsection \<open>Complex n-th roots\<close>

lemma bij_betw_roots_unity:
  assumes "n > 0"
  shows   "bij_betw (\<lambda>k. cis (2 * pi * real k / real n)) {..<n} {z. z ^ n = 1}"
    (is "bij_betw ?f _ _")
  unfolding bij_betw_def
proof (intro conjI)
  show inj: "inj_on ?f {..<n}" unfolding inj_on_def
  proof (safe, goal_cases)
    case (1 k l)
    hence kl: "k < n" "l < n" by simp_all
    from 1 have "1 = ?f k / ?f l" by simp
    also have "\<dots> = cis (2*pi*(real k - real l)/n)"
      using assms by (simp add: field_simps cis_divide)
    finally have "cos (2*pi*(real k - real l) / n) = 1"
      by (simp add: complex_eq_iff)
    then obtain m :: int where "2 * pi * (real k - real l) / real n = real_of_int m * 2 * pi"
      by (subst (asm) cos_one_2pi_int) blast
    hence "real_of_int (int k - int l) = real_of_int (m * int n)"
      unfolding of_int_diff of_int_mult using assms
      by (simp add: nonzero_divide_eq_eq)
    also note of_int_eq_iff
    finally have *: "abs m * n = abs (int k - int l)" by (simp add: abs_mult)
    also have "\<dots> < int n" using kl by linarith
    finally have "m = 0" using assms by simp
    with * show "k = l" by simp
  qed

  have subset: "?f ` {..<n} \<subseteq> {z. z ^ n = 1}"
  proof safe
    fix k :: nat
    have "cis (2 * pi * real k / real n) ^ n = cis (2 * pi) ^ k"
      using assms by (simp add: DeMoivre mult_ac)
    also have "cis (2 * pi) = 1" by (simp add: complex_eq_iff)
    finally show "?f k ^ n = 1" by simp
  qed

  have "n = card {..<n}" by simp
  also from assms and subset have "\<dots> \<le> card {z::complex. z ^ n = 1}"
    by (intro card_inj_on_le[OF inj]) (auto simp: finite_roots_unity)
  finally have card: "card {z::complex. z ^ n = 1} = n"
    using assms by (intro antisym card_roots_unity) auto

  have "card (?f ` {..<n}) = card {z::complex. z ^ n = 1}"
    using card inj by (subst card_image) auto
  with subset and assms show "?f ` {..<n} = {z::complex. z ^ n = 1}"
    by (intro card_subset_eq finite_roots_unity) auto
qed

lemma card_roots_unity_eq:
  assumes "n > 0"
  shows   "card {z::complex. z ^ n = 1} = n"
  using bij_betw_same_card [OF bij_betw_roots_unity [OF assms]] by simp

lemma bij_betw_nth_root_unity:
  fixes c :: complex and n :: nat
  assumes c: "c \<noteq> 0" and n: "n > 0"
  defines "c' \<equiv> root n (norm c) * cis (arg c / n)"
  shows "bij_betw (\<lambda>z. c' * z) {z. z ^ n = 1} {z. z ^ n = c}"
proof -
  have "c' ^ n = of_real (root n (norm c) ^ n) * cis (arg c)"
    unfolding of_real_power using n by (simp add: c'_def power_mult_distrib DeMoivre)
  also from n have "root n (norm c) ^ n = norm c" by simp
  also from c have "of_real \<dots> * cis (arg c) = c" by (simp add: cis_arg Complex.sgn_eq)
  finally have [simp]: "c' ^ n = c" .

  show ?thesis unfolding bij_betw_def inj_on_def
  proof safe
    fix z :: complex assume "z ^ n = 1"
    hence "(c' * z) ^ n = c' ^ n" by (simp add: power_mult_distrib)
    also have "c' ^ n = of_real (root n (norm c) ^ n) * cis (arg c)"
      unfolding of_real_power using n by (simp add: c'_def power_mult_distrib DeMoivre)
    also from n have "root n (norm c) ^ n = norm c" by simp
    also from c have "\<dots> * cis (arg c) = c" by (simp add: cis_arg Complex.sgn_eq)
    finally show "(c' * z) ^ n = c" .
  next
    fix z assume z: "c = z ^ n"
    define z' where "z' = z / c'"
    from c and n have "c' \<noteq> 0" by (auto simp: c'_def)
    with n c have "z = c' * z'" and "z' ^ n = 1"
      by (auto simp: z'_def power_divide z)
    thus "z \<in> (\<lambda>z. c' * z) ` {z. z ^ n = 1}" by blast
  qed (insert c n, auto simp: c'_def)
qed

lemma finite_nth_roots [intro]:
  assumes "n > 0"
  shows   "finite {z::complex. z ^ n = c}"
proof (cases "c = 0")
  case True
  with assms have "{z::complex. z ^ n = c} = {0}" by auto
  thus ?thesis by simp
next
  case False
  from assms have "finite {z::complex. z ^ n = 1}" by (intro finite_roots_unity) simp_all
  also have "?this \<longleftrightarrow> ?thesis"
    by (rule bij_betw_finite, rule bij_betw_nth_root_unity) fact+
  finally show ?thesis .
qed

lemma card_nth_roots:
  assumes "c \<noteq> 0" "n > 0"
  shows   "card {z::complex. z ^ n = c} = n"
proof -
  have "card {z. z ^ n = c} = card {z::complex. z ^ n = 1}"
    by (rule sym, rule bij_betw_same_card, rule bij_betw_nth_root_unity) fact+
  also have "\<dots> = n" by (rule card_roots_unity_eq) fact+
  finally show ?thesis .
qed

lemma sum_roots_unity:
  assumes "n > 1"
  shows   "\<Sum>{z::complex. z ^ n = 1} = 0"
proof -
  define \<omega> where "\<omega> = cis (2 * pi / real n)"
  have [simp]: "\<omega> \<noteq> 1"
  proof
    assume "\<omega> = 1"
    with assms obtain k :: int where "2 * pi / real n = 2 * pi * of_int k"
      by (auto simp: \<omega>_def complex_eq_iff cos_one_2pi_int)
    with assms have "real n * of_int k = 1" by (simp add: field_simps)
    also have "real n * of_int k = of_int (int n * k)" by simp
    also have "1 = (of_int 1 :: real)" by simp
    also note of_int_eq_iff
    finally show False using assms by (auto simp: zmult_eq_1_iff)
  qed

  have "(\<Sum>z | z ^ n = 1. z :: complex) = (\<Sum>k<n. cis (2 * pi * real k / real n))"
    using assms by (intro sum.reindex_bij_betw [symmetric] bij_betw_roots_unity) auto
  also have "\<dots> = (\<Sum>k<n. \<omega> ^ k)"
    by (intro sum.cong refl) (auto simp: \<omega>_def DeMoivre mult_ac)
  also have "\<dots> = (\<omega> ^ n - 1) / (\<omega> - 1)"
    by (subst geometric_sum) auto
  also have "\<omega> ^ n - 1 = cis (2 * pi) - 1" using assms by (auto simp: \<omega>_def DeMoivre)
  also have "\<dots> = 0" by (simp add: complex_eq_iff)
  finally show ?thesis by simp
qed

lemma sum_nth_roots:
  assumes "n > 1"
  shows   "\<Sum>{z::complex. z ^ n = c} = 0"
proof (cases "c = 0")
  case True
  with assms have "{z::complex. z ^ n = c} = {0}" by auto
  also have "\<Sum>\<dots> = 0" by simp
  finally show ?thesis .
next
  case False
  define c' where "c' = root n (norm c) * cis (arg c / n)"
  from False and assms have "(\<Sum>{z. z ^ n = c}) = (\<Sum>z | z ^ n = 1. c' * z)"
    by (subst sum.reindex_bij_betw [OF bij_betw_nth_root_unity, symmetric])
       (auto simp: sum_distrib_left finite_roots_unity c'_def)
  also from assms have "\<dots> = 0"
    by (simp add: sum_distrib_left [symmetric] sum_roots_unity)
  finally show ?thesis .
qed

subsection \<open>Square root of complex numbers\<close>

primcorec csqrt :: "complex \<Rightarrow> complex"
  where
    "Re (csqrt z) = sqrt ((cmod z + Re z) / 2)"
  | "Im (csqrt z) = (if Im z = 0 then 1 else sgn (Im z)) * sqrt ((cmod z - Re z) / 2)"

lemma csqrt_of_real_nonneg [simp]: "Im x = 0 \<Longrightarrow> Re x \<ge> 0 \<Longrightarrow> csqrt x = sqrt (Re x)"
  by (simp add: complex_eq_iff norm_complex_def)

lemma csqrt_of_real_nonpos [simp]: "Im x = 0 \<Longrightarrow> Re x \<le> 0 \<Longrightarrow> csqrt x = \<i> * sqrt \<bar>Re x\<bar>"
  by (simp add: complex_eq_iff norm_complex_def)

lemma of_real_sqrt: "x \<ge> 0 \<Longrightarrow> of_real (sqrt x) = csqrt (of_real x)"
  by (simp add: complex_eq_iff norm_complex_def)

lemma csqrt_0 [simp]: "csqrt 0 = 0"
  by simp

lemma csqrt_1 [simp]: "csqrt 1 = 1"
  by simp

lemma csqrt_ii [simp]: "csqrt \<i> = (1 + \<i>) / sqrt 2"
  by (simp add: complex_eq_iff Re_divide Im_divide real_sqrt_divide real_div_sqrt)

lemma power2_csqrt[simp,algebra]: "(csqrt z)\<^sup>2 = z"
proof (cases "Im z = 0")
  case True
  then show ?thesis
    using real_sqrt_pow2[of "Re z"] real_sqrt_pow2[of "- Re z"]
    by (cases "0::real" "Re z" rule: linorder_cases)
      (simp_all add: complex_eq_iff Re_power2 Im_power2 power2_eq_square cmod_eq_Re)
next
  case False
  moreover have "cmod z * cmod z - Re z * Re z = Im z * Im z"
    by (simp add: norm_complex_def power2_eq_square)
  moreover have "\<bar>Re z\<bar> \<le> cmod z"
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
    by (simp add: power2_eq_iff[symmetric])
  moreover have "csqrt (b^2) \<noteq> -b \<or> b = 0"
    using csqrt_principal[of "b ^ 2"] assms
    by (intro disjCI notI) (auto simp: complex_eq_iff)
  ultimately show ?thesis
    by auto
qed

lemma csqrt_unique: "w\<^sup>2 = z \<Longrightarrow> 0 < Re w \<or> Re w = 0 \<and> 0 \<le> Im w \<Longrightarrow> csqrt z = w"
  by (auto simp: csqrt_square)

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
    by (simp add: power_mult_distrib)
  finally show ?thesis .
qed


text \<open>Legacy theorem names\<close>

lemmas cmod_def = norm_complex_def

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
    and Complex_eq_i: "Complex x y = \<i> \<longleftrightarrow> x = 0 \<and> y = 1"
    and i_mult_Complex: "\<i> * Complex a b = Complex (- b) a"
    and Complex_mult_i: "Complex a b * \<i> = Complex (- b) a"
    and i_complex_of_real: "\<i> * complex_of_real r = Complex 0 r"
    and complex_of_real_i: "complex_of_real r * \<i> = Complex 0 r"
    and Complex_add_complex_of_real: "Complex x y + complex_of_real r = Complex (x+r) y"
    and complex_of_real_add_Complex: "complex_of_real r + Complex x y = Complex (r+x) y"
    and Complex_mult_complex_of_real: "Complex x y * complex_of_real r = Complex (x*r) (y*r)"
    and complex_of_real_mult_Complex: "complex_of_real r * Complex x y = Complex (r*x) (r*y)"
    and complex_eq_cancel_iff2: "(Complex x y = complex_of_real xa) = (x = xa \<and> y = 0)"
    and complex_cnj: "cnj (Complex a b) = Complex a (- b)"
    and Complex_sum': "sum (\<lambda>x. Complex (f x) 0) s = Complex (sum f s) 0"
    and Complex_sum: "Complex (sum f s) 0 = sum (\<lambda>x. Complex (f x) 0) s"
    and complex_of_real_def: "complex_of_real r = Complex r 0"
    and complex_norm: "cmod (Complex x y) = sqrt (x\<^sup>2 + y\<^sup>2)"
  by (simp_all add: norm_complex_def field_simps complex_eq_iff Re_divide Im_divide)

lemma Complex_in_Reals: "Complex x 0 \<in> \<real>"
  by (metis Reals_of_real complex_of_real_def)

end

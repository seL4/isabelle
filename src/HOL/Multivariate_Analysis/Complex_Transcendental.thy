(*  Author: John Harrison, Marco Maggesi, Graziano Gentili, Gianni Ciolli, Valentina Bruno
    Ported from "hol_light/Multivariate/transcendentals.ml" by L C Paulson (2015)
*)

section {* Complex Transcendental Functions *}

theory Complex_Transcendental
imports  "~~/src/HOL/Multivariate_Analysis/Complex_Analysis_Basics"
begin


lemma complex_differentiable_at_exp: "exp complex_differentiable at z"
  using DERIV_exp complex_differentiable_def by blast

lemma complex_differentiable_within_exp: "exp complex_differentiable (at z within s)"
  by (simp add: complex_differentiable_at_exp complex_differentiable_at_within)

lemma continuous_within_exp:
  fixes z::"'a::{real_normed_field,banach}"
  shows "continuous (at z within s) exp"
by (simp add: continuous_at_imp_continuous_within)

lemma continuous_on_exp:
  fixes s::"'a::{real_normed_field,banach} set"
  shows "continuous_on s exp"
by (simp add: continuous_on_exp continuous_on_id)

lemma holomorphic_on_exp: "exp holomorphic_on s"
  by (simp add: complex_differentiable_within_exp holomorphic_on_def)



subsection{*Euler and de Moivre formulas.*}

text{*The sine series times @{term i}*}
lemma sin_ii_eq: "(\<lambda>n. (ii * sin_coeff n) * z^n) sums (ii * sin z)"
proof -
  have "(\<lambda>n. ii * sin_coeff n *\<^sub>R z^n) sums (ii * sin z)"
    using sin_converges sums_mult by blast
  then show ?thesis
    by (simp add: scaleR_conv_of_real field_simps)
qed

theorem exp_Euler: "exp(ii * z) = cos(z) + ii * sin(z)"
proof -
  have "(\<lambda>n. (cos_coeff n + ii * sin_coeff n) * z^n) 
        = (\<lambda>n. (ii * z) ^ n /\<^sub>R (fact n))"
  proof
    fix n
    show "(cos_coeff n + ii * sin_coeff n) * z^n = (ii * z) ^ n /\<^sub>R (fact n)"
      by (auto simp: cos_coeff_def sin_coeff_def scaleR_conv_of_real field_simps elim!: evenE oddE)
  qed
  also have "... sums (exp (ii * z))"
    by (rule exp_converges)
  finally have "(\<lambda>n. (cos_coeff n + ii * sin_coeff n) * z^n) sums (exp (ii * z))" .
  moreover have "(\<lambda>n. (cos_coeff n + ii * sin_coeff n) * z^n) sums (cos z + ii * sin z)"
    using sums_add [OF cos_converges [of z] sin_ii_eq [of z]]
    by (simp add: field_simps scaleR_conv_of_real)
  ultimately show ?thesis
    using sums_unique2 by blast
qed

corollary exp_minus_Euler: "exp(-(ii * z)) = cos(z) - ii * sin(z)"
  using exp_Euler [of "-z"]
  by simp

lemma sin_exp_eq: "sin z = (exp(ii * z) - exp(-(ii * z))) / (2*ii)"
  by (simp add: exp_Euler exp_minus_Euler)

lemma sin_exp_eq': "sin z = ii * (exp(-(ii * z)) - exp(ii * z)) / 2"
  by (simp add: exp_Euler exp_minus_Euler)

lemma cos_exp_eq:  "cos z = (exp(ii * z) + exp(-(ii * z))) / 2"
  by (simp add: exp_Euler exp_minus_Euler)

subsection{*Relationships between real and complex trig functions*}

declare sin_of_real [simp] cos_of_real [simp]

lemma real_sin_eq [simp]:
  fixes x::real
  shows "Re(sin(of_real x)) = sin x"
  by (simp add: sin_of_real)
  
lemma real_cos_eq [simp]:
  fixes x::real
  shows "Re(cos(of_real x)) = cos x"
  by (simp add: cos_of_real)

lemma DeMoivre: "(cos z + ii * sin z) ^ n = cos(n * z) + ii * sin(n * z)"
  apply (simp add: exp_Euler [symmetric])
  by (metis exp_of_nat_mult mult.left_commute)

lemma exp_cnj:
  fixes z::complex
  shows "cnj (exp z) = exp (cnj z)"
proof -
  have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) = (\<lambda>n. (cnj z)^n /\<^sub>R (fact n))"
    by auto
  also have "... sums (exp (cnj z))"
    by (rule exp_converges)
  finally have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) sums (exp (cnj z))" .
  moreover have "(\<lambda>n. cnj (z ^ n /\<^sub>R (fact n))) sums (cnj (exp z))"
    by (metis exp_converges sums_cnj) 
  ultimately show ?thesis
    using sums_unique2
    by blast 
qed

lemma cnj_sin: "cnj(sin z) = sin(cnj z)"
  by (simp add: sin_exp_eq exp_cnj field_simps)

lemma cnj_cos: "cnj(cos z) = cos(cnj z)"
  by (simp add: cos_exp_eq exp_cnj field_simps)

lemma exp_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> exp z \<in> \<real>"
  by (metis Reals_cases Reals_of_real exp_of_real)

lemma sin_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> sin z \<in> \<real>"
  by (metis Reals_cases Reals_of_real sin_of_real)

lemma cos_in_Reals [simp]: "z \<in> \<real> \<Longrightarrow> cos z \<in> \<real>"
  by (metis Reals_cases Reals_of_real cos_of_real)

lemma complex_differentiable_at_sin: "sin complex_differentiable at z"
  using DERIV_sin complex_differentiable_def by blast

lemma complex_differentiable_within_sin: "sin complex_differentiable (at z within s)"
  by (simp add: complex_differentiable_at_sin complex_differentiable_at_within)

lemma complex_differentiable_at_cos: "cos complex_differentiable at z"
  using DERIV_cos complex_differentiable_def by blast

lemma complex_differentiable_within_cos: "cos complex_differentiable (at z within s)"
  by (simp add: complex_differentiable_at_cos complex_differentiable_at_within)

lemma holomorphic_on_sin: "sin holomorphic_on s"
  by (simp add: complex_differentiable_within_sin holomorphic_on_def)

lemma holomorphic_on_cos: "cos holomorphic_on s"
  by (simp add: complex_differentiable_within_cos holomorphic_on_def)

subsection{* Get a nice real/imaginary separation in Euler's formula.*}

lemma Euler: "exp(z) = of_real(exp(Re z)) * 
              (of_real(cos(Im z)) + ii * of_real(sin(Im z)))"
by (cases z) (simp add: exp_add exp_Euler cos_of_real exp_of_real sin_of_real)

lemma Re_sin: "Re(sin z) = sin(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by (simp add: sin_exp_eq field_simps Re_divide Im_exp)

lemma Im_sin: "Im(sin z) = cos(Re z) * (exp(Im z) - exp(-(Im z))) / 2"
  by (simp add: sin_exp_eq field_simps Im_divide Re_exp)

lemma Re_cos: "Re(cos z) = cos(Re z) * (exp(Im z) + exp(-(Im z))) / 2"
  by (simp add: cos_exp_eq field_simps Re_divide Re_exp)

lemma Im_cos: "Im(cos z) = sin(Re z) * (exp(-(Im z)) - exp(Im z)) / 2"
  by (simp add: cos_exp_eq field_simps Im_divide Im_exp)

(* Now more relatively easy consequences.*)

lemma sin_times_pi_eq_0: "sin(x * pi) = 0 \<longleftrightarrow> x \<in> Ints"
  by (simp add: sin_zero_iff_int2) (metis Ints_cases Ints_real_of_int real_of_int_def)

lemma cos_one_2pi: 
    "cos(x) = 1 \<longleftrightarrow> (\<exists>n::nat. x = n * 2*pi) | (\<exists>n::nat. x = -(n * 2*pi))"
    (is "?lhs = ?rhs")
proof
  assume "cos(x) = 1"
  then have "sin x = 0"
    by (simp add: cos_one_sin_zero)
  then show ?rhs
  proof (simp only: sin_zero_iff, elim exE disjE conjE)
    fix n::nat
    assume n: "even n" "x = real n * (pi/2)"
    then obtain m where m: "n = 2 * m"
      using dvdE by blast
    then have me: "even m" using `?lhs` n
      by (auto simp: field_simps) (metis one_neq_neg_one  power_minus_odd power_one)
    show ?rhs
      using m me n
      by (auto simp: field_simps elim!: evenE)
  next    
    fix n::nat
    assume n: "even n" "x = - (real n * (pi/2))"
    then obtain m where m: "n = 2 * m"
      using dvdE by blast
    then have me: "even m" using `?lhs` n
      by (auto simp: field_simps) (metis one_neq_neg_one  power_minus_odd power_one)
    show ?rhs
      using m me n
      by (auto simp: field_simps elim!: evenE)
  qed
next
  assume "?rhs"
  then show "cos x = 1"
    by (metis cos_2npi cos_minus mult.assoc mult.left_commute)
qed

lemma cos_one_2pi_int: "cos(x) = 1 \<longleftrightarrow> (\<exists>n::int. x = n * 2*pi)"
  apply auto  --{*FIXME simproc bug*}
  apply (auto simp: cos_one_2pi)
  apply (metis real_of_int_of_nat_eq)
  apply (metis mult_minus_right real_of_int_minus real_of_int_of_nat_eq)
  by (metis mult_minus_right of_int_of_nat real_of_int_def real_of_nat_def)

lemma sin_cos_sqrt: "0 \<le> sin(x) \<Longrightarrow> (sin(x) = sqrt(1 - (cos(x) ^ 2)))"
  using sin_squared_eq real_sqrt_unique by fastforce

lemma sin_eq_0_pi: "-pi < x \<Longrightarrow> x < pi \<Longrightarrow> sin(x) = 0 \<Longrightarrow> x = 0"
  by (metis sin_gt_zero sin_minus minus_less_iff neg_0_less_iff_less not_less_iff_gr_or_eq)

lemma cos_treble_cos: 
  fixes x :: "'a::{real_normed_field,banach}"
  shows "cos(3 * x) = 4 * cos(x) ^ 3 - 3 * cos x"
proof -
  have *: "(sin x * (sin x * 3)) = 3 - (cos x * (cos x * 3))"
    by (simp add: mult.assoc [symmetric] sin_squared_eq [unfolded power2_eq_square])
  have "cos(3 * x) = cos(2*x + x)"
    by simp
  also have "... = 4 * cos(x) ^ 3 - 3 * cos x"
    apply (simp only: cos_add cos_double sin_double)
    apply (simp add: * field_simps power2_eq_square power3_eq_cube)
    done
  finally show ?thesis .
qed

end

section {* Binary Approximations to Constants *}

theory Approximations
imports "~~/src/HOL/Multivariate_Analysis/Complex_Transcendental"
begin

declare of_real_numeral [simp]

subsection{*Approximation to pi*}

lemma sin_pi6_straddle:
  assumes "0 \<le> a" "a \<le> b" "b \<le> 4" "sin(a/6) \<le> 1/2" "1/2 \<le> sin(b/6)"
    shows "a \<le> pi \<and> pi \<le> b"
proof -
  have *: "\<And>x::real. 0 < x & x < 7/5 \<Longrightarrow> 0 < sin x"
    using pi_ge_two
    by (auto intro: sin_gt_zero)
  have ab: "(b \<le> pi * 3 \<Longrightarrow> pi \<le> b)" "(a \<le> pi * 3 \<Longrightarrow> a \<le> pi)"
    using sin_mono_le_eq [of "pi/6" "b/6"] sin_mono_le_eq [of "a/6" "pi/6"] assms
    by (simp_all add: sin_30 power.power_Suc norm_divide)
  show ?thesis
    using assms Taylor_sin [of "a/6" 0] pi_ge_two
    by (auto simp: sin_30 power.power_Suc norm_divide intro: ab)
qed

(*32-bit approximation. SLOW simplification steps: big calculations with the rewriting engine*)
lemma pi_approx_32: "abs(pi - 13493037705/4294967296) \<le> inverse(2 ^ 32)"
  apply (simp only: abs_diff_le_iff)
  apply (rule sin_pi6_straddle, simp_all)
  using Taylor_sin [of "1686629713/3221225472" 11]
  apply (simp add: in_Reals_norm sin_coeff_def Re_sin atMost_nat_numeral fact_numeral)
  apply (simp only: pos_le_divide_eq [symmetric])
  using Taylor_sin [of "6746518853/12884901888" 11]
  apply (simp add: in_Reals_norm sin_coeff_def Re_sin atMost_nat_numeral fact_numeral)
  apply (simp only: pos_le_divide_eq [symmetric] pos_divide_le_eq [symmetric])
  done

end

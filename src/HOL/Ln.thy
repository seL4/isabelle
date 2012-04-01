(*  Title:      HOL/Ln.thy
    Author:     Jeremy Avigad
*)

header {* Properties of ln *}

theory Ln
imports Transcendental
begin

lemma exp_first_two_terms: "exp x = 1 + x + suminf (%n. 
  inverse(fact (n+2)) * (x ^ (n+2)))"
proof -
  have "exp x = suminf (%n. inverse(fact n) * (x ^ n))"
    by (simp add: exp_def)
  also from summable_exp have "... = (SUM n::nat : {0..<2}. 
      inverse(fact n) * (x ^ n)) + suminf (%n.
      inverse(fact(n+2)) * (x ^ (n+2)))" (is "_ = ?a + _")
    by (rule suminf_split_initial_segment)
  also have "?a = 1 + x"
    by (simp add: numeral_2_eq_2)
  finally show ?thesis .
qed

lemma exp_bound: "0 <= (x::real) ==> x <= 1 ==> exp x <= 1 + x + x^2"
proof -
  assume a: "0 <= x"
  assume b: "x <= 1"
  { fix n :: nat
    have "2 * 2 ^ n \<le> fact (n + 2)"
      by (induct n, simp, simp)
    hence "real ((2::nat) * 2 ^ n) \<le> real (fact (n + 2))"
      by (simp only: real_of_nat_le_iff)
    hence "2 * 2 ^ n \<le> real (fact (n + 2))"
      by simp
    hence "inverse (fact (n + 2)) \<le> inverse (2 * 2 ^ n)"
      by (rule le_imp_inverse_le) simp
    hence "inverse (fact (n + 2)) \<le> 1/2 * (1/2)^n"
      by (simp add: inverse_mult_distrib power_inverse)
    hence "inverse (fact (n + 2)) * (x^n * x\<twosuperior>) \<le> 1/2 * (1/2)^n * (1 * x\<twosuperior>)"
      by (rule mult_mono)
        (rule mult_mono, simp_all add: power_le_one a b mult_nonneg_nonneg)
    hence "inverse (fact (n + 2)) * x ^ (n + 2) \<le> (x\<twosuperior>/2) * ((1/2)^n)"
      unfolding power_add by (simp add: mult_ac del: fact_Suc) }
  note aux1 = this
  have "(\<lambda>n. x\<twosuperior> / 2 * (1 / 2) ^ n) sums (x\<twosuperior> / 2 * (1 / (1 - 1 / 2)))"
    by (intro sums_mult geometric_sums, simp)
  hence aux2: "(\<lambda>n. (x::real) ^ 2 / 2 * (1 / 2) ^ n) sums x^2"
    by simp
  have "suminf (%n. inverse(fact (n+2)) * (x ^ (n+2))) <= x^2"
  proof -
    have "suminf (%n. inverse(fact (n+2)) * (x ^ (n+2))) <=
        suminf (%n. (x^2/2) * ((1/2)^n))"
      apply (rule summable_le)
      apply (rule allI, rule aux1)
      apply (rule summable_exp [THEN summable_ignore_initial_segment])
      by (rule sums_summable, rule aux2)
    also have "... = x^2"
      by (rule sums_unique [THEN sym], rule aux2)
    finally show ?thesis .
  qed
  thus ?thesis unfolding exp_first_two_terms by auto
qed

lemma ln_one_plus_pos_lower_bound: "0 <= x ==> x <= 1 ==> 
    x - x^2 <= ln (1 + x)"
proof -
  assume a: "0 <= x" and b: "x <= 1"
  have "exp (x - x^2) = exp x / exp (x^2)"
    by (rule exp_diff)
  also have "... <= (1 + x + x^2) / exp (x ^2)"
    apply (rule divide_right_mono) 
    apply (rule exp_bound)
    apply (rule a, rule b)
    apply simp
    done
  also have "... <= (1 + x + x^2) / (1 + x^2)"
    apply (rule divide_left_mono)
    apply (simp add: exp_ge_add_one_self_aux)
    apply (simp add: a)
    apply (simp add: mult_pos_pos add_pos_nonneg)
    done
  also from a have "... <= 1 + x"
    by (simp add: field_simps add_strict_increasing zero_le_mult_iff)
  finally have "exp (x - x^2) <= 1 + x" .
  also have "... = exp (ln (1 + x))"
  proof -
    from a have "0 < 1 + x" by auto
    thus ?thesis
      by (auto simp only: exp_ln_iff [THEN sym])
  qed
  finally have "exp (x - x ^ 2) <= exp (ln (1 + x))" .
  thus ?thesis by (auto simp only: exp_le_cancel_iff)
qed

lemma ln_one_minus_pos_upper_bound: "0 <= x ==> x < 1 ==> ln (1 - x) <= - x"
proof -
  assume a: "0 <= (x::real)" and b: "x < 1"
  have "(1 - x) * (1 + x + x^2) = (1 - x^3)"
    by (simp add: algebra_simps power2_eq_square power3_eq_cube)
  also have "... <= 1"
    by (auto simp add: a)
  finally have "(1 - x) * (1 + x + x ^ 2) <= 1" .
  moreover have c: "0 < 1 + x + x\<twosuperior>"
    by (simp add: add_pos_nonneg a)
  ultimately have "1 - x <= 1 / (1 + x + x^2)"
    by (elim mult_imp_le_div_pos)
  also have "... <= 1 / exp x"
    apply (rule divide_left_mono)
    apply (rule exp_bound, rule a)
    apply (rule b [THEN less_imp_le])
    apply simp
    apply (rule mult_pos_pos)
    apply (rule c)
    apply simp
    done
  also have "... = exp (-x)"
    by (auto simp add: exp_minus divide_inverse)
  finally have "1 - x <= exp (- x)" .
  also have "1 - x = exp (ln (1 - x))"
  proof -
    have "0 < 1 - x"
      by (insert b, auto)
    thus ?thesis
      by (auto simp only: exp_ln_iff [THEN sym])
  qed
  finally have "exp (ln (1 - x)) <= exp (- x)" .
  thus ?thesis by (auto simp only: exp_le_cancel_iff)
qed

lemma aux5: "x < 1 ==> ln(1 - x) = - ln(1 + x / (1 - x))"
proof -
  assume a: "x < 1"
  have "ln(1 - x) = - ln(1 / (1 - x))"
  proof -
    have "ln(1 - x) = - (- ln (1 - x))"
      by auto
    also have "- ln(1 - x) = ln 1 - ln(1 - x)"
      by simp
    also have "... = ln(1 / (1 - x))"
      apply (rule ln_div [THEN sym])
      by (insert a, auto)
    finally show ?thesis .
  qed
  also have " 1 / (1 - x) = 1 + x / (1 - x)" using a by(simp add:field_simps)
  finally show ?thesis .
qed

lemma ln_one_minus_pos_lower_bound: "0 <= x ==> x <= (1 / 2) ==> 
    - x - 2 * x^2 <= ln (1 - x)"
proof -
  assume a: "0 <= x" and b: "x <= (1 / 2)"
  from b have c: "x < 1"
    by auto
  then have "ln (1 - x) = - ln (1 + x / (1 - x))"
    by (rule aux5)
  also have "- (x / (1 - x)) <= ..."
  proof - 
    have "ln (1 + x / (1 - x)) <= x / (1 - x)"
      apply (rule ln_add_one_self_le_self)
      apply (rule divide_nonneg_pos)
      by (insert a c, auto) 
    thus ?thesis
      by auto
  qed
  also have "- (x / (1 - x)) = -x / (1 - x)"
    by auto
  finally have d: "- x / (1 - x) <= ln (1 - x)" .
  have "0 < 1 - x" using a b by simp
  hence e: "-x - 2 * x^2 <= - x / (1 - x)"
    using mult_right_le_one_le[of "x*x" "2*x"] a b
    by (simp add:field_simps power2_eq_square)
  from e d show "- x - 2 * x^2 <= ln (1 - x)"
    by (rule order_trans)
qed

lemma exp_ge_add_one_self [simp]: "1 + (x::real) <= exp x"
  apply (case_tac "0 <= x")
  apply (erule exp_ge_add_one_self_aux)
  apply (case_tac "x <= -1")
  apply (subgoal_tac "1 + x <= 0")
  apply (erule order_trans)
  apply simp
  apply simp
  apply (subgoal_tac "1 + x = exp(ln (1 + x))")
  apply (erule ssubst)
  apply (subst exp_le_cancel_iff)
  apply (subgoal_tac "ln (1 - (- x)) <= - (- x)")
  apply simp
  apply (rule ln_one_minus_pos_upper_bound) 
  apply auto
done

lemma ln_add_one_self_le_self2: "-1 < x ==> ln(1 + x) <= x"
  apply (subgoal_tac "ln (1 + x) \<le> ln (exp x)", simp)
  apply (subst ln_le_cancel_iff)
  apply auto
done

lemma abs_ln_one_plus_x_minus_x_bound_nonneg:
    "0 <= x ==> x <= 1 ==> abs(ln (1 + x) - x) <= x^2"
proof -
  assume x: "0 <= x"
  assume x1: "x <= 1"
  from x have "ln (1 + x) <= x"
    by (rule ln_add_one_self_le_self)
  then have "ln (1 + x) - x <= 0" 
    by simp
  then have "abs(ln(1 + x) - x) = - (ln(1 + x) - x)"
    by (rule abs_of_nonpos)
  also have "... = x - ln (1 + x)" 
    by simp
  also have "... <= x^2"
  proof -
    from x x1 have "x - x^2 <= ln (1 + x)"
      by (intro ln_one_plus_pos_lower_bound)
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound_nonpos:
    "-(1 / 2) <= x ==> x <= 0 ==> abs(ln (1 + x) - x) <= 2 * x^2"
proof -
  assume a: "-(1 / 2) <= x"
  assume b: "x <= 0"
  have "abs(ln (1 + x) - x) = x - ln(1 - (-x))" 
    apply (subst abs_of_nonpos)
    apply simp
    apply (rule ln_add_one_self_le_self2)
    using a apply auto
    done
  also have "... <= 2 * x^2"
    apply (subgoal_tac "- (-x) - 2 * (-x)^2 <= ln (1 - (-x))")
    apply (simp add: algebra_simps)
    apply (rule ln_one_minus_pos_lower_bound)
    using a b apply auto
    done
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound:
    "abs x <= 1 / 2 ==> abs(ln (1 + x) - x) <= 2 * x^2"
  apply (case_tac "0 <= x")
  apply (rule order_trans)
  apply (rule abs_ln_one_plus_x_minus_x_bound_nonneg)
  apply auto
  apply (rule abs_ln_one_plus_x_minus_x_bound_nonpos)
  apply auto
done

lemma ln_x_over_x_mono: "exp 1 <= x ==> x <= y ==> (ln y / y) <= (ln x / x)"  
proof -
  assume x: "exp 1 <= x" "x <= y"
  moreover have "0 < exp (1::real)" by simp
  ultimately have a: "0 < x" and b: "0 < y"
    by (fast intro: less_le_trans order_trans)+
  have "x * ln y - x * ln x = x * (ln y - ln x)"
    by (simp add: algebra_simps)
  also have "... = x * ln(y / x)"
    by (simp only: ln_div a b)
  also have "y / x = (x + (y - x)) / x"
    by simp
  also have "... = 1 + (y - x) / x"
    using x a by (simp add: field_simps)
  also have "x * ln(1 + (y - x) / x) <= x * ((y - x) / x)"
    apply (rule mult_left_mono)
    apply (rule ln_add_one_self_le_self)
    apply (rule divide_nonneg_pos)
    using x a apply simp_all
    done
  also have "... = y - x" using a by simp
  also have "... = (y - x) * ln (exp 1)" by simp
  also have "... <= (y - x) * ln x"
    apply (rule mult_left_mono)
    apply (subst ln_le_cancel_iff)
    apply fact
    apply (rule a)
    apply (rule x)
    using x apply simp
    done
  also have "... = y * ln x - x * ln x"
    by (rule left_diff_distrib)
  finally have "x * ln y <= y * ln x"
    by arith
  then have "ln y <= (y * ln x) / x" using a by (simp add: field_simps)
  also have "... = y * (ln x / x)" by simp
  finally show ?thesis using b by (simp add: field_simps)
qed

lemma ln_le_minus_one:
  "0 < x \<Longrightarrow> ln x \<le> x - 1"
  using exp_ge_add_one_self[of "ln x"] by simp

lemma ln_eq_minus_one:
  assumes "0 < x" "ln x = x - 1" shows "x = 1"
proof -
  let "?l y" = "ln y - y + 1"
  have D: "\<And>x. 0 < x \<Longrightarrow> DERIV ?l x :> (1 / x - 1)"
    by (auto intro!: DERIV_intros)

  show ?thesis
  proof (cases rule: linorder_cases)
    assume "x < 1"
    from dense[OF `x < 1`] obtain a where "x < a" "a < 1" by blast
    from `x < a` have "?l x < ?l a"
    proof (rule DERIV_pos_imp_increasing, safe)
      fix y assume "x \<le> y" "y \<le> a"
      with `0 < x` `a < 1` have "0 < 1 / y - 1" "0 < y"
        by (auto simp: field_simps)
      with D show "\<exists>z. DERIV ?l y :> z \<and> 0 < z"
        by auto
    qed
    also have "\<dots> \<le> 0"
      using ln_le_minus_one `0 < x` `x < a` by (auto simp: field_simps)
    finally show "x = 1" using assms by auto
  next
    assume "1 < x"
    from dense[OF `1 < x`] obtain a where "1 < a" "a < x" by blast
    from `a < x` have "?l x < ?l a"
    proof (rule DERIV_neg_imp_decreasing, safe)
      fix y assume "a \<le> y" "y \<le> x"
      with `1 < a` have "1 / y - 1 < 0" "0 < y"
        by (auto simp: field_simps)
      with D show "\<exists>z. DERIV ?l y :> z \<and> z < 0"
        by blast
    qed
    also have "\<dots> \<le> 0"
      using ln_le_minus_one `1 < a` by (auto simp: field_simps)
    finally show "x = 1" using assms by auto
  qed simp
qed

end

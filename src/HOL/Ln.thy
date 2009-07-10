(*  Title:      Ln.thy
    Author:     Jeremy Avigad
*)

header {* Properties of ln *}

theory Ln
imports Transcendental
begin

lemma exp_first_two_terms: "exp x = 1 + x + suminf (%n. 
  inverse(real (fact (n+2))) * (x ^ (n+2)))"
proof -
  have "exp x = suminf (%n. inverse(real (fact n)) * (x ^ n))"
    by (simp add: exp_def)
  also from summable_exp have "... = (SUM n : {0..<2}. 
      inverse(real (fact n)) * (x ^ n)) + suminf (%n.
      inverse(real (fact (n+2))) * (x ^ (n+2)))" (is "_ = ?a + _")
    by (rule suminf_split_initial_segment)
  also have "?a = 1 + x"
    by (simp add: numerals)
  finally show ?thesis .
qed

lemma exp_tail_after_first_two_terms_summable: 
  "summable (%n. inverse(real (fact (n+2))) * (x ^ (n+2)))"
proof -
  note summable_exp
  thus ?thesis
    by (frule summable_ignore_initial_segment)
qed

lemma aux1: assumes a: "0 <= x" and b: "x <= 1"
    shows "inverse (real (fact ((n::nat) + 2))) * x ^ (n + 2) <= (x^2/2) * ((1/2)^n)"
proof (induct n)
  show "inverse (real (fact ((0::nat) + 2))) * x ^ (0 + 2) <= 
      x ^ 2 / 2 * (1 / 2) ^ 0"
    by (simp add: real_of_nat_Suc power2_eq_square)
next
  fix n :: nat
  assume c: "inverse (real (fact (n + 2))) * x ^ (n + 2)
       <= x ^ 2 / 2 * (1 / 2) ^ n"
  show "inverse (real (fact (Suc n + 2))) * x ^ (Suc n + 2)
           <= x ^ 2 / 2 * (1 / 2) ^ Suc n"
  proof -
    have "inverse(real (fact (Suc n + 2))) <= 
        (1 / 2) *inverse (real (fact (n+2)))"
    proof -
      have "Suc n + 2 = Suc (n + 2)" by simp
      then have "fact (Suc n + 2) = Suc (n + 2) * fact (n + 2)" 
        by simp
      then have "real(fact (Suc n + 2)) = real(Suc (n + 2) * fact (n + 2))" 
        apply (rule subst)
        apply (rule refl)
        done
      also have "... = real(Suc (n + 2)) * real(fact (n + 2))"
        by (rule real_of_nat_mult)
      finally have "real (fact (Suc n + 2)) = 
         real (Suc (n + 2)) * real (fact (n + 2))" .
      then have "inverse(real (fact (Suc n + 2))) = 
         inverse(real (Suc (n + 2))) * inverse(real (fact (n + 2)))"
        apply (rule ssubst)
        apply (rule inverse_mult_distrib)
        done
      also have "... <= (1/2) * inverse(real (fact (n + 2)))"
        apply (rule mult_right_mono)
        apply (subst inverse_eq_divide)
        apply simp
        apply (rule inv_real_of_nat_fact_ge_zero)
        done
      finally show ?thesis .
    qed
    moreover have "x ^ (Suc n + 2) <= x ^ (n + 2)"
      apply (simp add: mult_compare_simps)
      apply (simp add: prems)
      apply (subgoal_tac "0 <= x * (x * x^n)")
      apply force
      apply (rule mult_nonneg_nonneg, rule a)+
      apply (rule zero_le_power, rule a)
      done
    ultimately have "inverse (real (fact (Suc n + 2))) *  x ^ (Suc n + 2) <=
        (1 / 2 * inverse (real (fact (n + 2)))) * x ^ (n + 2)"
      apply (rule mult_mono)
      apply (rule mult_nonneg_nonneg)
      apply simp
      apply (subst inverse_nonnegative_iff_nonnegative)
      apply (rule real_of_nat_ge_zero)
      apply (rule zero_le_power)
      apply (rule a)
      done
    also have "... = 1 / 2 * (inverse (real (fact (n + 2))) * x ^ (n + 2))"
      by simp
    also have "... <= 1 / 2 * (x ^ 2 / 2 * (1 / 2) ^ n)"
      apply (rule mult_left_mono)
      apply (rule prems)
      apply simp
      done
    also have "... = x ^ 2 / 2 * (1 / 2 * (1 / 2) ^ n)"
      by auto
    also have "(1::real) / 2 * (1 / 2) ^ n = (1 / 2) ^ (Suc n)"
      by (rule power_Suc [THEN sym])
    finally show ?thesis .
  qed
qed

lemma aux2: "(%n. (x::real) ^ 2 / 2 * (1 / 2) ^ n) sums x^2"
proof -
  have "(%n. (1 / 2::real)^n) sums (1 / (1 - (1/2)))"
    apply (rule geometric_sums)
    by (simp add: abs_less_iff)
  also have "(1::real) / (1 - 1/2) = 2"
    by simp
  finally have "(%n. (1 / 2::real)^n) sums 2" .
  then have "(%n. x ^ 2 / 2 * (1 / 2) ^ n) sums (x^2 / 2 * 2)"
    by (rule sums_mult)
  also have "x^2 / 2 * 2 = x^2"
    by simp
  finally show ?thesis .
qed

lemma exp_bound: "0 <= (x::real) ==> x <= 1 ==> exp x <= 1 + x + x^2"
proof -
  assume a: "0 <= x"
  assume b: "x <= 1"
  have c: "exp x = 1 + x + suminf (%n. inverse(real (fact (n+2))) * 
      (x ^ (n+2)))"
    by (rule exp_first_two_terms)
  moreover have "suminf (%n. inverse(real (fact (n+2))) * (x ^ (n+2))) <= x^2"
  proof -
    have "suminf (%n. inverse(real (fact (n+2))) * (x ^ (n+2))) <=
        suminf (%n. (x^2/2) * ((1/2)^n))"
      apply (rule summable_le)
      apply (auto simp only: aux1 prems)
      apply (rule exp_tail_after_first_two_terms_summable)
      by (rule sums_summable, rule aux2)  
    also have "... = x^2"
      by (rule sums_unique [THEN sym], rule aux2)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by auto
qed

lemma aux4: "0 <= (x::real) ==> x <= 1 ==> exp (x - x^2) <= 1 + x" 
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
    apply (auto simp add: exp_ge_add_one_self_aux)
    apply (rule add_nonneg_nonneg)
    apply (insert prems, auto)
    apply (rule mult_pos_pos)
    apply auto
    apply (rule add_pos_nonneg)
    apply auto
    done
  also from a have "... <= 1 + x"
    by(simp add:field_simps zero_compare_simps)
  finally show ?thesis .
qed

lemma ln_one_plus_pos_lower_bound: "0 <= x ==> x <= 1 ==> 
    x - x^2 <= ln (1 + x)"
proof -
  assume a: "0 <= x" and b: "x <= 1"
  then have "exp (x - x^2) <= 1 + x"
    by (rule aux4)
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
  moreover have "0 < 1 + x + x^2"
    apply (rule add_pos_nonneg)
    apply (insert a, auto)
    done
  ultimately have "1 - x <= 1 / (1 + x + x^2)"
    by (elim mult_imp_le_div_pos)
  also have "... <= 1 / exp x"
    apply (rule divide_left_mono)
    apply (rule exp_bound, rule a)
    apply (insert prems, auto)
    apply (rule mult_pos_pos)
    apply (rule add_pos_nonneg)
    apply auto
    done
  also have "... = exp (-x)"
    by (auto simp add: exp_minus real_divide_def)
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
  have "0 < 1 - x" using prems by simp
  hence e: "-x - 2 * x^2 <= - x / (1 - x)"
    using mult_right_le_one_le[of "x*x" "2*x"] prems
    by(simp add:field_simps power2_eq_square)
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
  apply (subgoal_tac "x = ln (exp x)")
  apply (erule ssubst)back
  apply (subst ln_le_cancel_iff)
  apply auto
done

lemma abs_ln_one_plus_x_minus_x_bound_nonneg:
    "0 <= x ==> x <= 1 ==> abs(ln (1 + x) - x) <= x^2"
proof -
  assume x: "0 <= x"
  assume "x <= 1"
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
    from prems have "x - x^2 <= ln (1 + x)"
      by (intro ln_one_plus_pos_lower_bound)
    thus ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma abs_ln_one_plus_x_minus_x_bound_nonpos:
    "-(1 / 2) <= x ==> x <= 0 ==> abs(ln (1 + x) - x) <= 2 * x^2"
proof -
  assume "-(1 / 2) <= x"
  assume "x <= 0"
  have "abs(ln (1 + x) - x) = x - ln(1 - (-x))" 
    apply (subst abs_of_nonpos)
    apply simp
    apply (rule ln_add_one_self_le_self2)
    apply (insert prems, auto)
    done
  also have "... <= 2 * x^2"
    apply (subgoal_tac "- (-x) - 2 * (-x)^2 <= ln (1 - (-x))")
    apply (simp add: algebra_simps)
    apply (rule ln_one_minus_pos_lower_bound)
    apply (insert prems, auto)
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

lemma DERIV_ln: "0 < x ==> DERIV ln x :> 1 / x"
  by (rule DERIV_ln[THEN DERIV_cong], simp, simp add: divide_inverse)

lemma ln_x_over_x_mono: "exp 1 <= x ==> x <= y ==> (ln y / y) <= (ln x / x)"  
proof -
  assume "exp 1 <= x" and "x <= y"
  have a: "0 < x" and b: "0 < y"
    apply (insert prems)
    apply (subgoal_tac "0 < exp (1::real)")
    apply arith
    apply auto
    apply (subgoal_tac "0 < exp (1::real)")
    apply arith
    apply auto
    done
  have "x * ln y - x * ln x = x * (ln y - ln x)"
    by (simp add: algebra_simps)
  also have "... = x * ln(y / x)"
    apply (subst ln_div)
    apply (rule b, rule a, rule refl)
    done
  also have "y / x = (x + (y - x)) / x"
    by simp
  also have "... = 1 + (y - x) / x" using a prems by(simp add:field_simps)
  also have "x * ln(1 + (y - x) / x) <= x * ((y - x) / x)"
    apply (rule mult_left_mono)
    apply (rule ln_add_one_self_le_self)
    apply (rule divide_nonneg_pos)
    apply (insert prems a, simp_all) 
    done
  also have "... = y - x" using a by simp
  also have "... = (y - x) * ln (exp 1)" by simp
  also have "... <= (y - x) * ln x"
    apply (rule mult_left_mono)
    apply (subst ln_le_cancel_iff)
    apply force
    apply (rule a)
    apply (rule prems)
    apply (insert prems, simp)
    done
  also have "... = y * ln x - x * ln x"
    by (rule left_diff_distrib)
  finally have "x * ln y <= y * ln x"
    by arith
  then have "ln y <= (y * ln x) / x" using a by(simp add:field_simps)
  also have "... = y * (ln x / x)"  by simp
  finally show ?thesis using b by(simp add:field_simps)
qed

end

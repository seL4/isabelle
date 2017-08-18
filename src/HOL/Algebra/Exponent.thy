(*  Title:      HOL/Algebra/Exponent.thy
    Author:     Florian Kammueller
    Author:     L C Paulson

exponent p s   yields the greatest power of p that divides s.
*)

theory Exponent
imports Main "HOL-Computational_Algebra.Primes"
begin

section \<open>Sylow's Theorem\<close>

text \<open>The Combinatorial Argument Underlying the First Sylow Theorem\<close>

text\<open>needed in this form to prove Sylow's theorem\<close>
corollary (in algebraic_semidom) div_combine: 
  "\<lbrakk>prime_elem p; \<not> p ^ Suc r dvd n; p ^ (a + r) dvd n * k\<rbrakk> \<Longrightarrow> p ^ a dvd k"
  by (metis add_Suc_right mult.commute prime_elem_power_dvd_cases)

lemma exponent_p_a_m_k_equation: 
  fixes p :: nat
  assumes "0 < m" "0 < k" "p \<noteq> 0" "k < p^a" 
    shows "multiplicity p (p^a * m - k) = multiplicity p (p^a - k)"
proof (rule multiplicity_cong [OF iffI])
  fix r
  assume *: "p ^ r dvd p ^ a * m - k" 
  show "p ^ r dvd p ^ a - k"
  proof -
    have "k \<le> p ^ a * m" using assms
      by (meson nat_dvd_not_less dvd_triv_left leI mult_pos_pos order.strict_trans)
    then have "r \<le> a"
      by (meson "*" \<open>0 < k\<close> \<open>k < p^a\<close> dvd_diffD1 dvd_triv_left leI less_imp_le_nat nat_dvd_not_less power_le_dvd)
    then have "p^r dvd p^a * m" by (simp add: le_imp_power_dvd)
    thus ?thesis
      by (meson \<open>k \<le> p ^ a * m\<close> \<open>r \<le> a\<close> * dvd_diffD1 dvd_diff_nat le_imp_power_dvd)
  qed
next
  fix r
  assume *: "p ^ r dvd p ^ a - k" 
  with assms have "r \<le> a"
    by (metis diff_diff_cancel less_imp_le_nat nat_dvd_not_less nat_le_linear power_le_dvd zero_less_diff)
  show "p ^ r dvd p ^ a * m - k"
  proof -
    have "p^r dvd p^a*m"
      by (simp add: \<open>r \<le> a\<close> le_imp_power_dvd)
    then show ?thesis
      by (meson assms * dvd_diffD1 dvd_diff_nat le_imp_power_dvd less_imp_le_nat \<open>r \<le> a\<close>)
  qed
qed

lemma p_not_div_choose_lemma: 
  fixes p :: nat
  assumes eeq: "\<And>i. Suc i < K \<Longrightarrow> multiplicity p (Suc i) = multiplicity p (Suc (j + i))"
      and "k < K" and p: "prime p"
    shows "multiplicity p (j + k choose k) = 0"
  using \<open>k < K\<close>
proof (induction k)
  case 0 then show ?case by simp
next
  case (Suc k)
  then have *: "(Suc (j+k) choose Suc k) > 0" by simp
  then have "multiplicity p ((Suc (j+k) choose Suc k) * Suc k) = multiplicity p (Suc k)"
    by (subst Suc_times_binomial_eq [symmetric], subst prime_elem_multiplicity_mult_distrib)
       (insert p Suc.prems, simp_all add: eeq [symmetric] Suc.IH)
  with p * show ?case
    by (subst (asm) prime_elem_multiplicity_mult_distrib) simp_all
qed

text\<open>The lemma above, with two changes of variables\<close>
lemma p_not_div_choose:
  assumes "k < K" and "k \<le> n" 
      and eeq: "\<And>j. \<lbrakk>0<j; j<K\<rbrakk> \<Longrightarrow> multiplicity p (n - k + (K - j)) = multiplicity p (K - j)" "prime p"
    shows "multiplicity p (n choose k) = 0"
apply (rule p_not_div_choose_lemma [of K p "n-k" k, simplified assms nat_minus_add_max max_absorb1])
apply (metis add_Suc_right eeq diff_diff_cancel order_less_imp_le zero_less_Suc zero_less_diff)
apply (rule TrueI)+
done

proposition const_p_fac:
  assumes "m>0" and prime: "prime p"
  shows "multiplicity p (p^a * m choose p^a) = multiplicity p m"
proof-
  from assms have p: "0 < p ^ a" "0 < p^a * m" "p^a \<le> p^a * m"
    by (auto simp: prime_gt_0_nat) 
  have *: "multiplicity p ((p^a * m - 1) choose (p^a - 1)) = 0"
    apply (rule p_not_div_choose [where K = "p^a"])
    using p exponent_p_a_m_k_equation by (auto simp: diff_le_mono prime)
  have "multiplicity p ((p ^ a * m choose p ^ a) * p ^ a) = a + multiplicity p m"
  proof -
    have "(p ^ a * m choose p ^ a) * p ^ a = p ^ a * m * (p ^ a * m - 1 choose (p ^ a - 1))" 
      (is "_ = ?rhs") using prime 
      by (subst times_binomial_minus1_eq [symmetric]) (auto simp: prime_gt_0_nat)
    also from p have "p ^ a - Suc 0 \<le> p ^ a * m - Suc 0" by linarith
    with prime * p have "multiplicity p ?rhs = multiplicity p (p ^ a * m)"
      by (subst prime_elem_multiplicity_mult_distrib) auto
    also have "\<dots> = a + multiplicity p m" 
      using prime p by (subst prime_elem_multiplicity_mult_distrib) simp_all
    finally show ?thesis .
  qed
  then show ?thesis
    using prime p by (subst (asm) prime_elem_multiplicity_mult_distrib) simp_all
qed

end

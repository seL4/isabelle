(*  Title:      HOL/Algebra/Exponent.thy
    Author:     Florian Kammueller
    Author:     L C Paulson

exponent p s   yields the greatest power of p that divides s.
*)

theory Exponent
imports Main "~~/src/HOL/Number_Theory/Primes"
begin

section \<open>Sylow's Theorem\<close>

text \<open>The Combinatorial Argument Underlying the First Sylow Theorem\<close>


subsection\<open>Prime Theorems\<close>

lemma prime_dvd_cases:
  assumes pk: "p*k dvd m*n" and p: "prime p"
  shows "(\<exists>x. k dvd x*n \<and> m = p*x) \<or> (\<exists>y. k dvd m*y \<and> n = p*y)"
proof -
  have "p dvd m*n" using dvd_mult_left pk by blast
  then consider "p dvd m" | "p dvd n"
    using p is_prime_dvd_mult_iff by blast
  then show ?thesis
  proof cases
    case 1 then obtain a where "m = p * a" by (metis dvd_mult_div_cancel) 
      then have "\<exists>x. k dvd x * n \<and> m = p * x"
        using p pk by (auto simp: mult.assoc)
    then show ?thesis ..
  next
    case 2 then obtain b where "n = p * b" by (metis dvd_mult_div_cancel) 
    with p pk have "\<exists>y. k dvd m*y \<and> n = p*y" 
      by (metis dvd_mult_right dvd_times_left_cancel_iff mult.left_commute mult_zero_left)
    then show ?thesis ..
  qed
qed

lemma prime_power_dvd_prod:
  assumes pc: "p^c dvd m*n" and p: "prime p"
  shows "\<exists>a b. a+b = c \<and> p^a dvd m \<and> p^b dvd n"
using pc
proof (induct c arbitrary: m n)
  case 0 show ?case by simp
next
  case (Suc c)
  consider x where "p^c dvd x*n" "m = p*x" | y where "p^c dvd m*y" "n = p*y"
    using prime_dvd_cases [of _ "p^c", OF _ p] Suc.prems by force
  then show ?case
  proof cases
    case (1 x) 
    with Suc.hyps[of x n] obtain a b where "a + b = c \<and> p ^ a dvd x \<and> p ^ b dvd n" by blast
    with 1 have "Suc a + b = Suc c \<and> p ^ Suc a dvd m \<and> p ^ b dvd n"
      by (auto intro: mult_dvd_mono)
    thus ?thesis by blast
  next
    case (2 y) 
    with Suc.hyps[of m y] obtain a b where "a + b = c \<and> p ^ a dvd m \<and> p ^ b dvd y" by blast
    with 2 have "a + Suc b = Suc c \<and> p ^ a dvd m \<and> p ^ Suc b dvd n"
      by (auto intro: mult_dvd_mono)
    with Suc.hyps [of m y] show "\<exists>a b. a + b = Suc c \<and> p ^ a dvd m \<and> p ^ b dvd n"
      by force
  qed
qed

lemma add_eq_Suc_lem: "a+b = Suc (x+y) \<Longrightarrow> a \<le> x \<or> b \<le> y"
  by arith

lemma prime_power_dvd_cases:
     "\<lbrakk>p^c dvd m * n; a + b = Suc c; prime p\<rbrakk> \<Longrightarrow> p ^ a dvd m \<or> p ^ b dvd n"
  using power_le_dvd prime_power_dvd_prod by (blast dest: prime_power_dvd_prod add_eq_Suc_lem)

text\<open>needed in this form to prove Sylow's theorem\<close>
corollary div_combine: "\<lbrakk>prime p; \<not> p ^ Suc r dvd n; p ^ (a + r) dvd n * k\<rbrakk> \<Longrightarrow> p ^ a dvd k"
  by (metis add_Suc_right mult.commute prime_power_dvd_cases)


subsection\<open>The Exponent Function\<close>

abbreviation (input) "exponent \<equiv> multiplicity"

(*
definition
  exponent :: "nat => nat => nat"
  where "exponent p s = (if prime p then (GREATEST r. p^r dvd s) else 0)"
*)

(*lemma exponent_eq_0 [simp]: "\<not> prime p \<Longrightarrow> exponent p s = 0"
  by (simp add: exponent_def)*)

lemma Suc_le_power: "Suc 0 < p \<Longrightarrow> Suc n \<le> p ^ n"
  by (induct n) (auto simp: Suc_le_eq le_less_trans)

(*
text\<open>An upper bound for the @{term n} such that @{term"p^n dvd a"}: needed for GREATEST to exist\<close>
lemma power_dvd_bound: "\<lbrakk>p ^ n dvd a; Suc 0 < p; 0 < a\<rbrakk> \<Longrightarrow> n < a"
  by (meson Suc_le_lessD Suc_le_power dvd_imp_le le_trans)
*)

(*
lemma exponent_ge:
  assumes "p ^ k dvd n" "prime p" "0 < n"
    shows "k \<le> exponent p n"
proof -
  have "Suc 0 < p"
    using \<open>prime p\<close> by (simp add: prime_def)
  with assms show ?thesis
    by (simp add: \<open>prime p\<close> exponent_def) (meson Greatest_le power_dvd_bound)
qed
*)

(*
lemma power_exponent_dvd: "p ^ exponent p s dvd s"
proof (cases "s = 0")
  case True then show ?thesis by simp
next
  case False then show ?thesis 
    apply (simp add: exponent_def, clarify)
    apply (rule GreatestI [where k = 0])
    apply (auto dest: prime_gt_Suc_0_nat power_dvd_bound)
    done
qed
*)

(*lemma power_Suc_exponent_Not_dvd:
    "\<lbrakk>p * p ^ exponent p s dvd s; prime p\<rbrakk> \<Longrightarrow> s = 0"
  by (metis exponent_ge neq0_conv not_less_eq_eq order_refl power_Suc)
*)


(*
lemma exponent_power_eq [simp]: "prime p \<Longrightarrow> exponent p (p ^ a) = a"
  apply (simp add: exponent_def)
  apply (rule Greatest_equality, simp)
  apply (simp add: prime_gt_Suc_0_nat power_dvd_imp_le)
  done
*)

(*
lemma exponent_1_eq_0 [simp]: "exponent p (Suc 0) = 0"
  apply (case_tac "prime p")
  apply (metis exponent_power_eq nat_power_eq_Suc_0_iff)
  apply simp
  done
*)

lemma exponent_equalityI:
  "(\<And>r. p ^ r dvd a \<longleftrightarrow> p ^ r dvd b) \<Longrightarrow> exponent p a = exponent p b"
  by (simp add: multiplicity_def)

(*
lemma exponent_mult_add: 
  assumes "a > 0" "b > 0"
    shows "exponent p (a * b) = (exponent p a) + (exponent p b)"
proof (cases "prime p")
  case False then show ?thesis by simp
next
  case True show ?thesis
  proof (rule order_antisym)
    show "exponent p a + exponent p b \<le> exponent p (a * b)"
      by (rule exponent_ge) (auto simp: mult_dvd_mono power_add power_exponent_dvd \<open>prime p\<close> assms)
  next
    { assume "exponent p a + exponent p b < exponent p (a * b)"
      then have "p ^ (Suc (exponent p a + exponent p b)) dvd a * b"
        by (meson Suc_le_eq power_exponent_dvd power_le_dvd)
      with prime_power_dvd_cases [where  a = "Suc (exponent p a)" and b = "Suc (exponent p b)"] 
      have False 
        by (metis Suc_n_not_le_n True add_Suc add_Suc_right assms exponent_ge)
    } 
  then show "exponent p (a * b) \<le> exponent p a + exponent p b" by (blast intro: leI)
  qed
qed
*)

lemma not_dvd_imp_multiplicity_0: 
  assumes "\<not>p dvd x"
  shows   "multiplicity p x = 0"
proof -
  from assms have "multiplicity p x < 1"
    by (intro multiplicity_lessI) auto
  thus ?thesis by simp
qed


subsection\<open>The Main Combinatorial Argument\<close>

lemma exponent_p_a_m_k_equation: 
  fixes p :: nat
  assumes "0 < m" "0 < k" "p \<noteq> 0" "k < p^a" 
    shows "exponent p (p^a * m - k) = exponent p (p^a - k)"
proof (rule exponent_equalityI [OF iffI])
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
  assumes eeq: "\<And>i. Suc i < K \<Longrightarrow> exponent p (Suc i) = exponent p (Suc (j + i))"
      and "k < K" and p: "prime p"
    shows "exponent p (j + k choose k) = 0"
  using \<open>k < K\<close>
proof (induction k)
  case 0 then show ?case by simp
next
  case (Suc k)
  then have *: "(Suc (j+k) choose Suc k) > 0" by simp
  then have "exponent p ((Suc (j+k) choose Suc k) * Suc k) = exponent p (Suc k)"
    by (subst Suc_times_binomial_eq [symmetric], subst prime_multiplicity_mult_distrib)
       (insert p Suc.prems, simp_all add: eeq [symmetric] Suc.IH)
  with p * show ?case
    by (subst (asm) prime_multiplicity_mult_distrib) simp_all
qed

text\<open>The lemma above, with two changes of variables\<close>
lemma p_not_div_choose:
  assumes "k < K" and "k \<le> n" 
      and eeq: "\<And>j. \<lbrakk>0<j; j<K\<rbrakk> \<Longrightarrow> exponent p (n - k + (K - j)) = exponent p (K - j)" "is_prime p"
    shows "exponent p (n choose k) = 0"
apply (rule p_not_div_choose_lemma [of K p "n-k" k, simplified assms nat_minus_add_max max_absorb1])
apply (metis add_Suc_right eeq diff_diff_cancel order_less_imp_le zero_less_Suc zero_less_diff)
apply (rule TrueI)+
done

proposition const_p_fac:
  assumes "m>0" and prime: "is_prime p"
  shows "exponent p (p^a * m choose p^a) = exponent p m"
proof-
  from assms have p: "0 < p ^ a" "0 < p^a * m" "p^a \<le> p^a * m"
    by (auto simp: prime_gt_0_nat) 
  have *: "exponent p ((p^a * m - 1) choose (p^a - 1)) = 0"
    apply (rule p_not_div_choose [where K = "p^a"])
    using p exponent_p_a_m_k_equation by (auto simp: diff_le_mono prime)
  have "exponent p ((p ^ a * m choose p ^ a) * p ^ a) = a + exponent p m"
  proof -
    have "(p ^ a * m choose p ^ a) * p ^ a = p ^ a * m * (p ^ a * m - 1 choose (p ^ a - 1))" 
      (is "_ = ?rhs") using prime 
      by (subst times_binomial_minus1_eq [symmetric]) (auto simp: prime_gt_0_nat)
    also from p have "p ^ a - Suc 0 \<le> p ^ a * m - Suc 0" by linarith
    with prime * p have "multiplicity p ?rhs = multiplicity p (p ^ a * m)"
      by (subst prime_multiplicity_mult_distrib) auto
    also have "\<dots> = a + multiplicity p m" 
      using prime p by (subst prime_multiplicity_mult_distrib) simp_all
    finally show ?thesis .
  qed
  then show ?thesis
    using prime p by (subst (asm) prime_multiplicity_mult_distrib) simp_all
qed

end

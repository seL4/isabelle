(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Common discrete functions\<close>

theory Discrete
imports Main
begin

subsection \<open>Discrete logarithm\<close>

context
begin

qualified fun log :: "nat \<Rightarrow> nat"
  where [simp del]: "log n = (if n < 2 then 0 else Suc (log (n div 2)))"

lemma log_induct [consumes 1, case_names one double]:
  fixes n :: nat
  assumes "n > 0"
  assumes one: "P 1"
  assumes double: "\<And>n. n \<ge> 2 \<Longrightarrow> P (n div 2) \<Longrightarrow> P n"
  shows "P n"
using \<open>n > 0\<close> proof (induct n rule: log.induct)
  fix n
  assume "\<not> n < 2 \<Longrightarrow>
          0 < n div 2 \<Longrightarrow> P (n div 2)"
  then have *: "n \<ge> 2 \<Longrightarrow> P (n div 2)" by simp
  assume "n > 0"
  show "P n"
  proof (cases "n = 1")
    case True with one show ?thesis by simp
  next
    case False with \<open>n > 0\<close> have "n \<ge> 2" by auto
    moreover with * have "P (n div 2)" .
    ultimately show ?thesis by (rule double)
  qed
qed
  
lemma log_zero [simp]: "log 0 = 0"
  by (simp add: log.simps)

lemma log_one [simp]: "log 1 = 0"
  by (simp add: log.simps)

lemma log_Suc_zero [simp]: "log (Suc 0) = 0"
  using log_one by simp

lemma log_rec: "n \<ge> 2 \<Longrightarrow> log n = Suc (log (n div 2))"
  by (simp add: log.simps)

lemma log_twice [simp]: "n \<noteq> 0 \<Longrightarrow> log (2 * n) = Suc (log n)"
  by (simp add: log_rec)

lemma log_half [simp]: "log (n div 2) = log n - 1"
proof (cases "n < 2")
  case True
  then have "n = 0 \<or> n = 1" by arith
  then show ?thesis by (auto simp del: One_nat_def)
next
  case False
  then show ?thesis by (simp add: log_rec)
qed

lemma log_exp [simp]: "log (2 ^ n) = n"
  by (induct n) simp_all

lemma log_mono: "mono log"
proof
  fix m n :: nat
  assume "m \<le> n"
  then show "log m \<le> log n"
  proof (induct m arbitrary: n rule: log.induct)
    case (1 m)
    then have mn2: "m div 2 \<le> n div 2" by arith
    show "log m \<le> log n"
    proof (cases "m \<ge> 2")
      case False
      then have "m = 0 \<or> m = 1" by arith
      then show ?thesis by (auto simp del: One_nat_def)
    next
      case True then have "\<not> m < 2" by simp
      with mn2 have "n \<ge> 2" by arith
      from True have m2_0: "m div 2 \<noteq> 0" by arith
      with mn2 have n2_0: "n div 2 \<noteq> 0" by arith
      from \<open>\<not> m < 2\<close> "1.hyps" mn2 have "log (m div 2) \<le> log (n div 2)" by blast
      with m2_0 n2_0 have "log (2 * (m div 2)) \<le> log (2 * (n div 2))" by simp
      with m2_0 n2_0 \<open>m \<ge> 2\<close> \<open>n \<ge> 2\<close> show ?thesis by (simp only: log_rec [of m] log_rec [of n]) simp
    qed
  qed
qed

lemma log_exp2_le:
  assumes "n > 0"
  shows "2 ^ log n \<le> n"
using assms proof (induct n rule: log_induct)
  show "2 ^ log 1 \<le> (1 :: nat)" by simp
next
  fix n :: nat
  assume "n \<ge> 2"
  with log_mono have "log n \<ge> Suc 0"
    by (simp add: log.simps)
  assume "2 ^ log (n div 2) \<le> n div 2"
  with \<open>n \<ge> 2\<close> have "2 ^ (log n - Suc 0) \<le> n div 2" by simp
  then have "2 ^ (log n - Suc 0) * 2 ^ 1 \<le> n div 2 * 2" by simp
  with \<open>log n \<ge> Suc 0\<close> have "2 ^ log n \<le> n div 2 * 2"
    unfolding power_add [symmetric] by simp
  also have "n div 2 * 2 \<le> n" by (cases "even n") simp_all
  finally show "2 ^ log n \<le> n" .
qed


subsection \<open>Discrete square root\<close>

qualified definition sqrt :: "nat \<Rightarrow> nat"
  where "sqrt n = Max {m. m\<^sup>2 \<le> n}"

lemma sqrt_aux:
  fixes n :: nat
  shows "finite {m. m\<^sup>2 \<le> n}" and "{m. m\<^sup>2 \<le> n} \<noteq> {}"
proof -
  { fix m
    assume "m\<^sup>2 \<le> n"
    then have "m \<le> n"
      by (cases m) (simp_all add: power2_eq_square)
  } note ** = this
  then have "{m. m\<^sup>2 \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then show "finite {m. m\<^sup>2 \<le> n}" by (rule finite_subset) rule
  have "0\<^sup>2 \<le> n" by simp
  then show *: "{m. m\<^sup>2 \<le> n} \<noteq> {}" by blast
qed

lemma [code]: "sqrt n = Max (Set.filter (\<lambda>m. m\<^sup>2 \<le> n) {0..n})"
proof -
  from power2_nat_le_imp_le [of _ n] have "{m. m \<le> n \<and> m\<^sup>2 \<le> n} = {m. m\<^sup>2 \<le> n}" by auto
  then show ?thesis by (simp add: sqrt_def Set.filter_def)
qed

lemma sqrt_inverse_power2 [simp]: "sqrt (n\<^sup>2) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: sqrt_def power2_nat_le_eq_le intro: antisym)
qed

lemma sqrt_zero [simp]: "sqrt 0 = 0"
  using sqrt_inverse_power2 [of 0] by simp

lemma sqrt_one [simp]: "sqrt 1 = 1"
  using sqrt_inverse_power2 [of 1] by simp

lemma mono_sqrt: "mono sqrt"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "sqrt m \<le> sqrt n"
    by (auto intro!: Max_mono \<open>0 * 0 \<le> m\<close> finite_less_ub simp add: power2_eq_square sqrt_def)
qed

lemma sqrt_greater_zero_iff [simp]: "sqrt n > 0 \<longleftrightarrow> n > 0"
proof -
  have *: "0 < Max {m. m\<^sup>2 \<le> n} \<longleftrightarrow> (\<exists>a\<in>{m. m\<^sup>2 \<le> n}. 0 < a)"
    by (rule Max_gr_iff) (fact sqrt_aux)+
  show ?thesis
  proof
    assume "0 < sqrt n"
    then have "0 < Max {m. m\<^sup>2 \<le> n}" by (simp add: sqrt_def)
    with * show "0 < n" by (auto dest: power2_nat_le_imp_le)
  next
    assume "0 < n"
    then have "1\<^sup>2 \<le> n \<and> 0 < (1::nat)" by simp
    then have "\<exists>q. q\<^sup>2 \<le> n \<and> 0 < q" ..
    with * have "0 < Max {m. m\<^sup>2 \<le> n}" by blast
    then show "0 < sqrt n" by  (simp add: sqrt_def)
  qed
qed

lemma sqrt_power2_le [simp]: "(sqrt n)\<^sup>2 \<le> n" (* FIXME tune proof *)
proof (cases "n > 0")
  case False then show ?thesis by simp
next
  case True then have "sqrt n > 0" by simp
  then have "mono (times (Max {m. m\<^sup>2 \<le> n}))" by (auto intro: mono_times_nat simp add: sqrt_def)
  then have *: "Max {m. m\<^sup>2 \<le> n} * Max {m. m\<^sup>2 \<le> n} = Max (times (Max {m. m\<^sup>2 \<le> n}) ` {m. m\<^sup>2 \<le> n})"
    using sqrt_aux [of n] by (rule mono_Max_commute)
  have "Max (op * (Max {m. m * m \<le> n}) ` {m. m * m \<le> n}) \<le> n"
    apply (subst Max_le_iff)
    apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
    apply simp
    apply (metis le0 mult_0_right)
    apply auto
    proof -
      fix q
      assume "q * q \<le> n"
      show "Max {m. m * m \<le> n} * q \<le> n"
      proof (cases "q > 0")
        case False then show ?thesis by simp
      next
        case True then have "mono (times q)" by (rule mono_times_nat)
        then have "q * Max {m. m * m \<le> n} = Max (times q ` {m. m * m \<le> n})"
          using sqrt_aux [of n] by (auto simp add: power2_eq_square intro: mono_Max_commute)
        then have "Max {m. m * m \<le> n} * q = Max (times q ` {m. m * m \<le> n})" by (simp add: ac_simps)
        then show ?thesis
          apply simp
          apply (subst Max_le_iff)
          apply auto
          apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
          apply (metis \<open>q * q \<le> n\<close>)
          apply (metis \<open>q * q \<le> n\<close> le_cases mult_le_mono1 mult_le_mono2 order_trans)
          done
      qed
    qed
  with * show ?thesis by (simp add: sqrt_def power2_eq_square)
qed

lemma sqrt_le: "sqrt n \<le> n"
  using sqrt_aux [of n] by (auto simp add: sqrt_def intro: power2_nat_le_imp_le)

end

end
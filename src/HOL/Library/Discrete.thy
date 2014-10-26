(* Author: Florian Haftmann, TU Muenchen *)  

header {* Common discrete functions *}

theory Discrete
imports Main
begin

subsection {* Discrete logarithm *}

fun log :: "nat \<Rightarrow> nat" where
  [simp del]: "log n = (if n < 2 then 0 else Suc (log (n div 2)))"

lemma log_zero [simp]:
  "log 0 = 0"
  by (simp add: log.simps)

lemma log_one [simp]:
  "log 1 = 0"
  by (simp add: log.simps)

lemma log_Suc_zero [simp]:
  "log (Suc 0) = 0"
  using log_one by simp

lemma log_rec:
  "n \<ge> 2 \<Longrightarrow> log n = Suc (log (n div 2))"
  by (simp add: log.simps)

lemma log_twice [simp]:
  "n \<noteq> 0 \<Longrightarrow> log (2 * n) = Suc (log n)"
  by (simp add: log_rec)

lemma log_half [simp]:
  "log (n div 2) = log n - 1"
proof (cases "n < 2")
  case True
  then have "n = 0 \<or> n = 1" by arith
  then show ?thesis by (auto simp del: One_nat_def)
next
  case False then show ?thesis by (simp add: log_rec)
qed

lemma log_exp [simp]:
  "log (2 ^ n) = n"
  by (induct n) simp_all

lemma log_mono:
  "mono log"
proof
  fix m n :: nat
  assume "m \<le> n"
  then show "log m \<le> log n"
  proof (induct m arbitrary: n rule: log.induct)
    case (1 m)
    then have mn2: "m div 2 \<le> n div 2" by arith
    show "log m \<le> log n"
    proof (cases "m < 2")
      case True
      then have "m = 0 \<or> m = 1" by arith
      then show ?thesis by (auto simp del: One_nat_def)
    next
      case False
      with mn2 have "m \<ge> 2" and "n \<ge> 2" by auto arith
      from False have m2_0: "m div 2 \<noteq> 0" by arith
      with mn2 have n2_0: "n div 2 \<noteq> 0" by arith
      from False "1.hyps" mn2 have "log (m div 2) \<le> log (n div 2)" by blast
      with m2_0 n2_0 have "log (2 * (m div 2)) \<le> log (2 * (n div 2))" by simp
      with m2_0 n2_0 `m \<ge> 2` `n \<ge> 2` show ?thesis by (simp only: log_rec [of m] log_rec [of n]) simp
    qed
  qed
qed


subsection {* Discrete square root *}

definition sqrt :: "nat \<Rightarrow> nat"
where
  "sqrt n = Max {m. m\<^sup>2 \<le> n}"

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

lemma [code]:
  "sqrt n = Max (Set.filter (\<lambda>m. m\<^sup>2 \<le> n) {0..n})"
proof -
  from power2_nat_le_imp_le [of _ n] have "{m. m \<le> n \<and> m\<^sup>2 \<le> n} = {m. m\<^sup>2 \<le> n}" by auto
  then show ?thesis by (simp add: sqrt_def Set.filter_def)
qed

lemma sqrt_inverse_power2 [simp]:
  "sqrt (n\<^sup>2) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: sqrt_def power2_nat_le_eq_le intro: antisym)
qed

lemma sqrt_zero [simp]:
  "sqrt 0 = 0"
  using sqrt_inverse_power2 [of 0] by simp

lemma sqrt_one [simp]:
  "sqrt 1 = 1"
  using sqrt_inverse_power2 [of 1] by simp

lemma mono_sqrt:
  "mono sqrt"
proof
  fix m n :: nat
  have *: "0 * 0 \<le> m" by simp
  assume "m \<le> n"
  then show "sqrt m \<le> sqrt n"
    by (auto intro!: Max_mono `0 * 0 \<le> m` finite_less_ub simp add: power2_eq_square sqrt_def)
qed

lemma sqrt_greater_zero_iff [simp]:
  "sqrt n > 0 \<longleftrightarrow> n > 0"
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

lemma sqrt_power2_le [simp]: (* FIXME tune proof *)
  "(sqrt n)\<^sup>2 \<le> n"
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
        then show ?thesis apply simp
          apply (subst Max_le_iff)
          apply auto
          apply (metis (mono_tags) finite_imageI finite_less_ub le_square)
          apply (metis `q * q \<le> n`)
          using `q * q \<le> n` by (metis le_cases mult_le_mono1 mult_le_mono2 order_trans)
      qed
    qed
  with * show ?thesis by (simp add: sqrt_def power2_eq_square)
qed

lemma sqrt_le:
  "sqrt n \<le> n"
  using sqrt_aux [of n] by (auto simp add: sqrt_def intro: power2_nat_le_imp_le)

hide_const (open) log sqrt

end


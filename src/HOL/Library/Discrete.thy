(* Author: Florian Haftmann, TU Muenchen *)  

header {* Common discrete functions *}

theory Discrete
imports Main
begin

lemma power2_nat_le_eq_le:
  fixes m n :: nat
  shows "m ^ 2 \<le> n ^ 2 \<longleftrightarrow> m \<le> n"
  by (auto intro: power2_le_imp_le power_mono)

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
  "sqrt n = Max {m. m ^ 2 \<le> n}"

lemma sqrt_inverse_power2 [simp]:
  "sqrt (n ^ 2) = n"
proof -
  have "{m. m \<le> n} \<noteq> {}" by auto
  then have "Max {m. m \<le> n} \<le> n" by auto
  then show ?thesis
    by (auto simp add: sqrt_def power2_nat_le_eq_le intro: antisym)
qed

lemma [code]:
  "sqrt n = Max (Set.filter (\<lambda>m. m ^ 2 \<le> n) {0..n})"
proof -
  { fix m
    assume "m\<twosuperior> \<le> n"
    then have "m \<le> n"
      by (cases m) (simp_all add: power2_eq_square)
  }
  then have "{m. m \<le> n \<and> m\<twosuperior> \<le> n} = {m. m\<twosuperior> \<le> n}" by auto
  then show ?thesis by (simp add: sqrt_def Set.filter_def)
qed

lemma sqrt_le:
  "sqrt n \<le> n"
proof -
  have "0\<twosuperior> \<le> n" by simp
  then have *: "{m. m\<twosuperior> \<le> n} \<noteq> {}" by blast
  { fix m
    assume "m\<twosuperior> \<le> n"
    then have "m \<le> n"
      by (cases m) (simp_all add: power2_eq_square)
  } note ** = this
  then have "{m. m\<twosuperior> \<le> n} \<subseteq> {m. m \<le> n}" by auto
  then have "finite {m. m\<twosuperior> \<le> n}" by (rule finite_subset) rule
  with * show ?thesis by (auto simp add: sqrt_def intro: **)
qed

hide_const (open) log sqrt

end


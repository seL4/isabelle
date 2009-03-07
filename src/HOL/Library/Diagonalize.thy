(* Author: Florian Haftmann, TU Muenchen *)

header {* A constructive version of Cantor's first diagonalization argument. *}

theory Diagonalize
imports Main
begin

subsection {* Summation from @{text "0"} to @{text "n"} *}

definition sum :: "nat \<Rightarrow> nat" where
  "sum n = n * Suc n div 2"

lemma sum_0:
  "sum 0 = 0"
  unfolding sum_def by simp

lemma sum_Suc:
  "sum (Suc n) = Suc n + sum n"
  unfolding sum_def by simp

lemma sum2:
  "2 * sum n = n * Suc n"
proof -
  have "2 dvd n * Suc n"
  proof (cases "2 dvd n")
    case True then show ?thesis by simp
  next
    case False then have "2 dvd Suc n" by arith
    then show ?thesis by (simp del: mult_Suc_right)
  qed
  then have "n * Suc n div 2 * 2 = n * Suc n"
    by (rule dvd_div_mult_self [of "2::nat"])
  then show ?thesis by (simp add: sum_def)
qed

lemma sum_strict_mono:
  "strict_mono sum"
proof (rule strict_monoI)
  fix m n :: nat
  assume "m < n"
  then have "m * Suc m < n * Suc n" by (intro mult_strict_mono) simp_all
  then have "2 * sum m < 2 * sum n" by (simp add: sum2)
  then show "sum m < sum n" by auto
qed

lemma sum_not_less_self:
  "n \<le> sum n"
proof -
  have "2 * n \<le> n * Suc n" by auto
  with sum2 have "2 * n \<le> 2 * sum n" by simp
  then show ?thesis by simp
qed

lemma sum_rest_aux:
  assumes "q \<le> n"
  assumes "sum m \<le> sum n + q"
  shows "m \<le> n"
proof (rule ccontr)
  assume "\<not> m \<le> n"
  then have "n < m" by simp
  then have "m \<ge> Suc n" by simp
  then have "m = m - Suc n + Suc n" by simp
  then have "m = Suc (n + (m - Suc n))" by simp
  then obtain r where "m = Suc (n + r)" by auto
  with `sum m \<le> sum n + q` have "sum (Suc (n + r)) \<le> sum n + q" by simp
  then have "sum (n + r) + Suc (n + r) \<le> sum n + q" unfolding sum_Suc by simp
  with `m = Suc (n + r)` have "sum (n + r) + m \<le> sum n + q" by simp
  have "sum n \<le> sum (n + r)" unfolding strict_mono_less_eq [OF sum_strict_mono] by simp
  moreover from `q \<le> n` `n < m` have "q < m" by simp
  ultimately have "sum n + q < sum (n + r) + m" by auto
  with `sum (n + r) + m \<le> sum n + q` show False
    by auto
qed

lemma sum_rest:
  assumes "q \<le> n"
  shows "sum m \<le> sum n + q \<longleftrightarrow> m \<le> n"
using assms apply (auto intro: sum_rest_aux)
apply (simp add: strict_mono_less_eq [OF sum_strict_mono, symmetric, of m n])
done


subsection {* Diagonalization: an injective embedding of two @{typ "nat"}s to one @{typ "nat"} *}

definition diagonalize :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "diagonalize m n = sum (m + n) + m"

lemma diagonalize_inject:
  assumes "diagonalize a b = diagonalize c d"
  shows "a = c" and "b = d"
proof -
  from assms have diageq: "sum (a + b) + a = sum (c + d) + c"
    by (simp add: diagonalize_def)
  have "a + b = c + d \<or> a + b \<ge> Suc (c + d) \<or> c + d \<ge> Suc (a + b)" by arith
  then have "a = c \<and> b = d"
  proof (elim disjE)
    assume sumeq: "a + b = c + d"
    then have "a = c" using diageq by auto
    moreover from sumeq this have "b = d" by auto
    ultimately show ?thesis ..
  next
    assume "a + b \<ge> Suc (c + d)"
    with strict_mono_less_eq [OF sum_strict_mono]
      have "sum (a + b) \<ge> sum (Suc (c + d))" by simp
    with diageq show ?thesis by (simp add: sum_Suc)
  next
    assume "c + d \<ge> Suc (a + b)"
    with strict_mono_less_eq [OF sum_strict_mono]
      have "sum (c + d) \<ge> sum (Suc (a + b))" by simp
    with diageq show ?thesis by (simp add: sum_Suc)
  qed
  then show "a = c" and "b = d" by auto
qed


subsection {* The reverse diagonalization: reconstruction a pair of @{typ nat}s from one @{typ nat} *}

text {* The inverse of the @{const sum} function *}

definition tupelize :: "nat \<Rightarrow> nat \<times> nat" where
  "tupelize q = (let d = Max {d. sum d \<le> q}; m = q - sum d
     in (m, d - m))"
  
lemma tupelize_diagonalize:
  "tupelize (diagonalize m n) = (m, n)"
proof -
  from sum_rest
    have "\<And>r. sum r \<le> sum (m + n) + m \<longleftrightarrow> r \<le> m + n" by simp
  then have "Max {d. sum d \<le> (sum (m + n) + m)} = m + n"
    by (auto intro: Max_eqI)
  then show ?thesis
    by (simp add: tupelize_def diagonalize_def)
qed

lemma snd_tupelize:
  "snd (tupelize n) \<le> n"
proof -
  have "sum 0 \<le> n" by (simp add: sum_0)
  then have "Max {m \<Colon> nat. sum m \<le> n} \<le> Max {m \<Colon> nat. m \<le> n}"
    by (intro Max_mono [of "{m. sum m \<le> n}" "{m. m \<le> n}"])
      (auto intro: Max_mono order_trans sum_not_less_self)
  also have "Max {m \<Colon> nat. m \<le> n} \<le> n"
    by (subst Max_le_iff) auto
  finally have "Max {m. sum m \<le> n} \<le> n" .
  then show ?thesis by (simp add: tupelize_def Let_def)
qed

end

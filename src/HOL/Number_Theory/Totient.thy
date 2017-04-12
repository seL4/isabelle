(*  Title:      HOL/Number_Theory/Totient.thy
    Author:     Jeremy Avigad
    Author:     Florian Haftmann
*)

section \<open>Fundamental facts about Euler's totient function\<close>

theory Totient
imports
  "~~/src/HOL/Computational_Algebra/Primes"
begin

definition totatives :: "nat \<Rightarrow> nat set"
  where "totatives n = {m. 0 < m \<and> m < n \<and> coprime m n}"

lemma in_totatives_iff [simp]:
  "m \<in> totatives n \<longleftrightarrow> 0 < m \<and> m < n \<and> coprime m n"
  by (simp add: totatives_def)

lemma finite_totatives [simp]:
  "finite (totatives n)"
  by (simp add: totatives_def)

lemma totatives_subset:
  "totatives n \<subseteq> {1..<n}"
  by auto

lemma totatives_subset_Suc_0 [simp]:
  "totatives n \<subseteq> {Suc 0..<n}"
  using totatives_subset [of n] by simp

lemma totatives_0 [simp]:
  "totatives 0 = {}"
  using totatives_subset [of 0] by simp

lemma totatives_1 [simp]:
  "totatives 1 = {}"
  using totatives_subset [of 1] by simp

lemma totatives_Suc_0 [simp]:
  "totatives (Suc 0) = {}"
  using totatives_1 by simp

lemma one_in_totatives:
  assumes "n \<ge> 2"
  shows "1 \<in> totatives n"
  using assms by simp

lemma minus_one_in_totatives:
  assumes "n \<ge> 2"
  shows "n - 1 \<in> totatives n"
  using assms coprime_minus_one_nat [of n] by simp

lemma totatives_eq_empty_iff [simp]:
  "totatives n = {} \<longleftrightarrow> n \<in> {0, 1}"
proof
  assume "totatives n = {}"
  show "n \<in> {0, 1}"
  proof (rule ccontr)
    assume "n \<notin> {0, 1}"
    then have "n \<ge> 2"
      by simp
    then have "1 \<in> totatives n"
      by (rule one_in_totatives)
    with \<open>totatives n = {}\<close> show False
      by simp
  qed
qed auto

lemma prime_totatives:
  assumes "prime p"
  shows "totatives p = {1..<p}"
proof
  show "{1..<p} \<subseteq> totatives p"
  proof
    fix n
    assume "n \<in> {1..<p}"
    with nat_dvd_not_less have "\<not> p dvd n"
      by auto
    with assms prime_imp_coprime [of p n] have "coprime p n"
      by simp
    with \<open>n \<in> {1..<p}\<close> show "n \<in> totatives p"
      by (auto simp add: totatives_def ac_simps)
  qed
qed auto

lemma totatives_prime:
  assumes "p \<ge> 2" and "totatives p = {1..<p}"
  shows "prime p"
proof (rule ccontr)
  from \<open>2 \<le> p\<close> have "1 < p"
    by simp
  moreover assume "\<not> prime p"
  ultimately obtain n where "1 < n" "n < p" "n dvd p"
    by (auto simp add: prime_nat_iff)
      (metis Suc_lessD Suc_lessI dvd_imp_le dvd_pos_nat le_neq_implies_less)
  then have "n \<in> {1..<p}"
    by simp
  with assms have "n \<in> totatives p"
    by simp
  then have "coprime n p"
    by simp
  with \<open>1 < n\<close> \<open>n dvd p\<close> show False
    by simp
qed

definition totient :: "nat \<Rightarrow> nat"
  where "totient = card \<circ> totatives"

lemma card_totatives [simp]:
  "card (totatives n) = totient n"
  by (simp add: totient_def)

lemma totient_0 [simp]:
  "totient 0 = 0"
  by (simp add: totient_def)

lemma totient_1 [simp]:
  "totient 1 = 0"
  by (simp add: totient_def)

lemma totient_Suc_0 [simp]:
  "totient (Suc 0) = 0"
  using totient_1 by simp
  
lemma prime_totient:
  assumes "prime p"
  shows "totient p = p - 1"
  using assms prime_totatives
  by (simp add: totient_def)

lemma totient_eq_0_iff [simp]:
  "totient n = 0 \<longleftrightarrow> n \<in> {0, 1}"
  by (simp only: totient_def comp_def card_eq_0_iff) auto

lemma totient_noneq_0_iff [simp]:
  "totient n > 0 \<longleftrightarrow> 2 \<le> n"
proof -
  have "totient n > 0 \<longleftrightarrow> totient n \<noteq> 0"
    by blast
  also have "\<dots> \<longleftrightarrow> 2 \<le> n"
    by auto
  finally show ?thesis .
qed

lemma totient_less_eq:
  "totient n \<le> n - 1"
  using card_mono [of "{1..<n}" "totatives n"] by auto

lemma totient_less_eq_Suc_0 [simp]:
  "totient n \<le> n - Suc 0"
  using totient_less_eq [of n] by simp

lemma totient_prime:
  assumes "2 \<le> p" "totient p = p - 1"
  shows "prime p"
proof -
  have "totatives p = {1..<p}"
    by (rule card_subset_eq) (simp_all add: assms)
  with assms show ?thesis
    by (auto intro: totatives_prime)
qed

end

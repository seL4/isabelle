(* Author: Tobias Nipkow *)

theory Tree_Real
imports
  Complex_Main
  Tree
begin

text \<open>This theory is separate from @{theory Tree} because the former is discrete and builds on
@{theory Main} whereas this theory builds on @{theory Complex_Main}.\<close>


lemma size1_height_log: "log 2 (size1 t) \<le> height t"
by (simp add: log2_of_power_le size1_height)

lemma min_height_size1_log: "min_height t \<le> log 2 (size1 t)"
by (simp add: le_log2_of_power min_height_size1)

lemma size1_log_if_complete: "complete t \<Longrightarrow> height t = log 2 (size1 t)"
by (simp add: log2_of_power_eq size1_if_complete)

lemma min_height_size1_log_if_incomplete:
  "\<not> complete t \<Longrightarrow> min_height t < log 2 (size1 t)"
by (simp add: less_log2_of_power min_height_size1_if_incomplete)


lemma min_height_balanced: assumes "balanced t"
shows "min_height t = nat(floor(log 2 (size1 t)))"
proof cases
  assume *: "complete t"
  hence "size1 t = 2 ^ min_height t"
    by (simp add: complete_iff_height size1_if_complete)
  from log2_of_power_eq[OF this] show ?thesis by linarith
next
  assume *: "\<not> complete t"
  hence "height t = min_height t + 1"
    using assms min_height_le_height[of t]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size1 t < 2 ^ (min_height t + 1)"
    by (metis * size1_height_if_incomplete)
  hence "log 2 (size1 t) < min_height t + 1"
    using log2_of_power_less size1_ge0 by blast
  thus ?thesis using min_height_size1_log[of t] by linarith
qed

lemma height_balanced: assumes "balanced t"
shows "height t = nat(ceiling(log 2 (size1 t)))"
proof cases
  assume *: "complete t"
  hence "size1 t = 2 ^ height t"
    by (simp add: size1_if_complete)
  from log2_of_power_eq[OF this] show ?thesis
    by linarith
next
  assume *: "\<not> complete t"
  hence **: "height t = min_height t + 1"
    using assms min_height_le_height[of t]
    by(auto simp add: balanced_def complete_iff_height)
  hence "size1 t \<le> 2 ^ (min_height t + 1)" by (metis size1_height)
  from  log2_of_power_le[OF this size1_ge0] min_height_size1_log_if_incomplete[OF *] **
  show ?thesis by linarith
qed

end
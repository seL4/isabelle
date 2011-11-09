(*  Title:      HOL/Library/Indicator_Function.thy
    Author:     Johannes Hoelzl (TU Muenchen)
*)

header {* Indicator Function *}

theory Indicator_Function
imports Main
begin

definition "indicator S x = (if x \<in> S then 1 else 0)"

lemma indicator_simps[simp]:
  "x \<in> S \<Longrightarrow> indicator S x = 1"
  "x \<notin> S \<Longrightarrow> indicator S x = 0"
  unfolding indicator_def by auto

lemma indicator_pos_le[intro, simp]: "(0::'a::linordered_semidom) \<le> indicator S x"
  and indicator_le_1[intro, simp]: "indicator S x \<le> (1::'a::linordered_semidom)"
  unfolding indicator_def by auto

lemma indicator_abs_le_1: "\<bar>indicator S x\<bar> \<le> (1::'a::linordered_idom)"
  unfolding indicator_def by auto

lemma split_indicator:
  "P (indicator S x) \<longleftrightarrow> ((x \<in> S \<longrightarrow> P 1) \<and> (x \<notin> S \<longrightarrow> P 0))"
  unfolding indicator_def by auto

lemma indicator_inter_arith: "indicator (A \<inter> B) x = indicator A x * (indicator B x::'a::semiring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_union_arith: "indicator (A \<union> B) x =  indicator A x + indicator B x - indicator A x * (indicator B x::'a::ring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_inter_min: "indicator (A \<inter> B) x = min (indicator A x) (indicator B x::'a::linordered_semidom)"
  and indicator_union_max: "indicator (A \<union> B) x = max (indicator A x) (indicator B x::'a::linordered_semidom)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_compl: "indicator (- A) x = 1 - (indicator A x::'a::ring_1)"
  and indicator_diff: "indicator (A - B) x = indicator A x * (1 - indicator B x::'a::ring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_times: "indicator (A \<times> B) x = indicator A (fst x) * (indicator B (snd x)::'a::semiring_1)"
  unfolding indicator_def by (cases x) auto

lemma indicator_sum: "indicator (A <+> B) x = (case x of Inl x \<Rightarrow> indicator A x | Inr x \<Rightarrow> indicator B x)"
  unfolding indicator_def by (cases x) auto

lemma
  fixes f :: "'a \<Rightarrow> 'b::semiring_1" assumes "finite A"
  shows setsum_mult_indicator[simp]: "(\<Sum>x \<in> A. f x * indicator B x) = (\<Sum>x \<in> A \<inter> B. f x)"
  and setsum_indicator_mult[simp]: "(\<Sum>x \<in> A. indicator B x * f x) = (\<Sum>x \<in> A \<inter> B. f x)"
  unfolding indicator_def
  using assms by (auto intro!: setsum_mono_zero_cong_right split: split_if_asm)

lemma setsum_indicator_eq_card:
  assumes "finite A"
  shows "(SUM x : A. indicator B x) = card (A Int B)"
  using setsum_mult_indicator[OF assms, of "%x. 1::nat"]
  unfolding card_eq_setsum by simp

end
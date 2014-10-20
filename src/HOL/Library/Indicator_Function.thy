(*  Title:      HOL/Library/Indicator_Function.thy
    Author:     Johannes Hoelzl (TU Muenchen)
*)

header {* Indicator Function *}

theory Indicator_Function
imports Complex_Main
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

lemma indicator_eq_0_iff: "indicator A x = (0::_::zero_neq_one) \<longleftrightarrow> x \<notin> A"
  by (auto simp: indicator_def)

lemma indicator_eq_1_iff: "indicator A x = (1::_::zero_neq_one) \<longleftrightarrow> x \<in> A"
  by (auto simp: indicator_def)

lemma split_indicator: "P (indicator S x) \<longleftrightarrow> ((x \<in> S \<longrightarrow> P 1) \<and> (x \<notin> S \<longrightarrow> P 0))"
  unfolding indicator_def by auto

lemma split_indicator_asm: "P (indicator S x) \<longleftrightarrow> (\<not> (x \<in> S \<and> \<not> P 1 \<or> x \<notin> S \<and> \<not> P 0))"
  unfolding indicator_def by auto

lemma indicator_inter_arith: "indicator (A \<inter> B) x = indicator A x * (indicator B x::'a::semiring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_union_arith: "indicator (A \<union> B) x = indicator A x + indicator B x - indicator A x * (indicator B x::'a::ring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_inter_min: "indicator (A \<inter> B) x = min (indicator A x) (indicator B x::'a::linordered_semidom)"
  and indicator_union_max: "indicator (A \<union> B) x = max (indicator A x) (indicator B x::'a::linordered_semidom)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_disj_union: "A \<inter> B = {} \<Longrightarrow>  indicator (A \<union> B) x = (indicator A x + indicator B x::'a::linordered_semidom)"
  by (auto split: split_indicator)

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
  using assms by (auto intro!: setsum.mono_neutral_cong_right split: split_if_asm)

lemma setsum_indicator_eq_card:
  assumes "finite A"
  shows "(SUM x : A. indicator B x) = card (A Int B)"
  using setsum_mult_indicator[OF assms, of "%x. 1::nat"]
  unfolding card_eq_setsum by simp

lemma setsum_indicator_scaleR[simp]:
  "finite A \<Longrightarrow>
    (\<Sum>x \<in> A. indicator (B x) (g x) *\<^sub>R f x) = (\<Sum>x \<in> {x\<in>A. g x \<in> B x}. f x::'a::real_vector)"
  using assms by (auto intro!: setsum.mono_neutral_cong_right split: split_if_asm simp: indicator_def)

lemma LIMSEQ_indicator_incseq:
  assumes "incseq A"
  shows "(\<lambda>i. indicator (A i) x :: 'a :: {topological_space, one, zero}) ----> indicator (\<Union>i. A i) x"
proof cases
  assume "\<exists>i. x \<in> A i"
  then obtain i where "x \<in> A i"
    by auto
  then have 
    "\<And>n. (indicator (A (n + i)) x :: 'a) = 1"
    "(indicator (\<Union> i. A i) x :: 'a) = 1"
    using incseqD[OF `incseq A`, of i "n + i" for n] `x \<in> A i` by (auto simp: indicator_def)
  then show ?thesis
    by (rule_tac LIMSEQ_offset[of _ i]) simp
qed (auto simp: indicator_def)

lemma LIMSEQ_indicator_UN:
  "(\<lambda>k. indicator (\<Union> i<k. A i) x :: 'a :: {topological_space, one, zero}) ----> indicator (\<Union>i. A i) x"
proof -
  have "(\<lambda>k. indicator (\<Union> i<k. A i) x::'a) ----> indicator (\<Union>k. \<Union> i<k. A i) x"
    by (intro LIMSEQ_indicator_incseq) (auto simp: incseq_def intro: less_le_trans)
  also have "(\<Union>k. \<Union> i<k. A i) = (\<Union>i. A i)"
    by auto
  finally show ?thesis .
qed

lemma LIMSEQ_indicator_decseq:
  assumes "decseq A"
  shows "(\<lambda>i. indicator (A i) x :: 'a :: {topological_space, one, zero}) ----> indicator (\<Inter>i. A i) x"
proof cases
  assume "\<exists>i. x \<notin> A i"
  then obtain i where "x \<notin> A i"
    by auto
  then have 
    "\<And>n. (indicator (A (n + i)) x :: 'a) = 0"
    "(indicator (\<Inter>i. A i) x :: 'a) = 0"
    using decseqD[OF `decseq A`, of i "n + i" for n] `x \<notin> A i` by (auto simp: indicator_def)
  then show ?thesis
    by (rule_tac LIMSEQ_offset[of _ i]) simp
qed (auto simp: indicator_def)

lemma LIMSEQ_indicator_INT:
  "(\<lambda>k. indicator (\<Inter>i<k. A i) x :: 'a :: {topological_space, one, zero}) ----> indicator (\<Inter>i. A i) x"
proof -
  have "(\<lambda>k. indicator (\<Inter>i<k. A i) x::'a) ----> indicator (\<Inter>k. \<Inter>i<k. A i) x"
    by (intro LIMSEQ_indicator_decseq) (auto simp: decseq_def intro: less_le_trans)
  also have "(\<Inter>k. \<Inter> i<k. A i) = (\<Inter>i. A i)"
    by auto
  finally show ?thesis .
qed

lemma indicator_add:
  "A \<inter> B = {} \<Longrightarrow> (indicator A x::_::monoid_add) + indicator B x = indicator (A \<union> B) x"
  unfolding indicator_def by auto

lemma of_real_indicator: "of_real (indicator A x) = indicator A x"
  by (simp split: split_indicator)

lemma real_of_nat_indicator: "real (indicator A x :: nat) = indicator A x"
  by (simp split: split_indicator)

lemma abs_indicator: "\<bar>indicator A x :: 'a::linordered_idom\<bar> = indicator A x"
  by (simp split: split_indicator)

lemma mult_indicator_subset:
  "A \<subseteq> B \<Longrightarrow> indicator A x * indicator B x = (indicator A x :: 'a::{comm_semiring_1})"
  by (auto split: split_indicator simp: fun_eq_iff)

lemma indicator_sums: 
  assumes "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  shows "(\<lambda>i. indicator (A i) x::real) sums indicator (\<Union>i. A i) x"
proof cases
  assume "\<exists>i. x \<in> A i"
  then obtain i where i: "x \<in> A i" ..
  with assms have "(\<lambda>i. indicator (A i) x::real) sums (\<Sum>i\<in>{i}. indicator (A i) x)"
    by (intro sums_finite) (auto split: split_indicator)
  also have "(\<Sum>i\<in>{i}. indicator (A i) x) = indicator (\<Union>i. A i) x"
    using i by (auto split: split_indicator)
  finally show ?thesis .
qed simp

end

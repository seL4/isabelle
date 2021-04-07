(*  Title:      HOL/Library/Indicator_Function.thy
    Author:     Johannes Hoelzl (TU Muenchen)
*)

section \<open>Indicator Function\<close>

theory Indicator_Function
imports Complex_Main Disjoint_Sets
begin

definition "indicator S x = of_bool (x \<in> S)"

text\<open>Type constrained version\<close>
abbreviation indicat_real :: "'a set \<Rightarrow> 'a \<Rightarrow> real" where "indicat_real S \<equiv> indicator S"

lemma indicator_simps[simp]:
  "x \<in> S \<Longrightarrow> indicator S x = 1"
  "x \<notin> S \<Longrightarrow> indicator S x = 0"
  unfolding indicator_def by auto

lemma indicator_pos_le[intro, simp]: "(0::'a::linordered_semidom) \<le> indicator S x"
  and indicator_le_1[intro, simp]: "indicator S x \<le> (1::'a::linordered_semidom)"
  unfolding indicator_def by auto

lemma indicator_abs_le_1: "\<bar>indicator S x\<bar> \<le> (1::'a::linordered_idom)"
  unfolding indicator_def by auto

lemma indicator_eq_0_iff: "indicator A x = (0::'a::zero_neq_one) \<longleftrightarrow> x \<notin> A"
  by (auto simp: indicator_def)

lemma indicator_eq_1_iff: "indicator A x = (1::'a::zero_neq_one) \<longleftrightarrow> x \<in> A"
  by (auto simp: indicator_def)

lemma indicator_UNIV [simp]: "indicator UNIV = (\<lambda>x. 1)"
  by auto

lemma indicator_leI:
  "(x \<in> A \<Longrightarrow> y \<in> B) \<Longrightarrow> (indicator A x :: 'a::linordered_nonzero_semiring) \<le> indicator B y"
  by (auto simp: indicator_def)

lemma split_indicator: "P (indicator S x) \<longleftrightarrow> ((x \<in> S \<longrightarrow> P 1) \<and> (x \<notin> S \<longrightarrow> P 0))"
  unfolding indicator_def by auto

lemma split_indicator_asm: "P (indicator S x) \<longleftrightarrow> (\<not> (x \<in> S \<and> \<not> P 1 \<or> x \<notin> S \<and> \<not> P 0))"
  unfolding indicator_def by auto

lemma indicator_inter_arith: "indicator (A \<inter> B) x = indicator A x * (indicator B x::'a::semiring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_union_arith:
  "indicator (A \<union> B) x = indicator A x + indicator B x - indicator A x * (indicator B x :: 'a::ring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_inter_min: "indicator (A \<inter> B) x = min (indicator A x) (indicator B x::'a::linordered_semidom)"
  and indicator_union_max: "indicator (A \<union> B) x = max (indicator A x) (indicator B x::'a::linordered_semidom)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_disj_union:
  "A \<inter> B = {} \<Longrightarrow> indicator (A \<union> B) x = (indicator A x + indicator B x :: 'a::linordered_semidom)"
  by (auto split: split_indicator)

lemma indicator_compl: "indicator (- A) x = 1 - (indicator A x :: 'a::ring_1)"
  and indicator_diff: "indicator (A - B) x = indicator A x * (1 - indicator B x ::'a::ring_1)"
  unfolding indicator_def by (auto simp: min_def max_def)

lemma indicator_times:
  "indicator (A \<times> B) x = indicator A (fst x) * (indicator B (snd x) :: 'a::semiring_1)"
  unfolding indicator_def by (cases x) auto

lemma indicator_sum:
  "indicator (A <+> B) x = (case x of Inl x \<Rightarrow> indicator A x | Inr x \<Rightarrow> indicator B x)"
  unfolding indicator_def by (cases x) auto

lemma indicator_image: "inj f \<Longrightarrow> indicator (f ` X) (f x) = (indicator X x::_::zero_neq_one)"
  by (auto simp: indicator_def inj_def)

lemma indicator_vimage: "indicator (f -` A) x = indicator A (f x)"
  by (auto split: split_indicator)

lemma  (* FIXME unnamed!? *)
  fixes f :: "'a \<Rightarrow> 'b::semiring_1"
  assumes "finite A"
  shows sum_mult_indicator[simp]: "(\<Sum>x \<in> A. f x * indicator B x) = (\<Sum>x \<in> A \<inter> B. f x)"
    and sum_indicator_mult[simp]: "(\<Sum>x \<in> A. indicator B x * f x) = (\<Sum>x \<in> A \<inter> B. f x)"
  unfolding indicator_def
  using assms by (auto intro!: sum.mono_neutral_cong_right split: if_split_asm)

lemma sum_indicator_eq_card:
  assumes "finite A"
  shows "(\<Sum>x \<in> A. indicator B x) = card (A Int B)"
  using sum_mult_indicator [OF assms, of "\<lambda>x. 1::nat"]
  unfolding card_eq_sum by simp

lemma sum_indicator_scaleR[simp]:
  "finite A \<Longrightarrow>
    (\<Sum>x \<in> A. indicator (B x) (g x) *\<^sub>R f x) = (\<Sum>x \<in> {x\<in>A. g x \<in> B x}. f x :: 'a::real_vector)"
  by (auto intro!: sum.mono_neutral_cong_right split: if_split_asm simp: indicator_def)

lemma LIMSEQ_indicator_incseq:
  assumes "incseq A"
  shows "(\<lambda>i. indicator (A i) x :: 'a::{topological_space,zero_neq_one}) \<longlonglongrightarrow> indicator (\<Union>i. A i) x"
proof (cases "\<exists>i. x \<in> A i")
  case True
  then obtain i where "x \<in> A i"
    by auto
  then have *:
    "\<And>n. (indicator (A (n + i)) x :: 'a) = 1"
    "(indicator (\<Union>i. A i) x :: 'a) = 1"
    using incseqD[OF \<open>incseq A\<close>, of i "n + i" for n] \<open>x \<in> A i\<close> by (auto simp: indicator_def)
  show ?thesis
    by (rule LIMSEQ_offset[of _ i]) (use * in simp)
next
  case False
  then show ?thesis by (simp add: indicator_def)
qed

lemma LIMSEQ_indicator_UN:
  "(\<lambda>k. indicator (\<Union>i<k. A i) x :: 'a::{topological_space,zero_neq_one}) \<longlonglongrightarrow> indicator (\<Union>i. A i) x"
proof -
  have "(\<lambda>k. indicator (\<Union>i<k. A i) x::'a) \<longlonglongrightarrow> indicator (\<Union>k. \<Union>i<k. A i) x"
    by (intro LIMSEQ_indicator_incseq) (auto simp: incseq_def intro: less_le_trans)
  also have "(\<Union>k. \<Union>i<k. A i) = (\<Union>i. A i)"
    by auto
  finally show ?thesis .
qed

lemma LIMSEQ_indicator_decseq:
  assumes "decseq A"
  shows "(\<lambda>i. indicator (A i) x :: 'a::{topological_space,zero_neq_one}) \<longlonglongrightarrow> indicator (\<Inter>i. A i) x"
proof (cases "\<exists>i. x \<notin> A i")
  case True
  then obtain i where "x \<notin> A i"
    by auto
  then have *:
    "\<And>n. (indicator (A (n + i)) x :: 'a) = 0"
    "(indicator (\<Inter>i. A i) x :: 'a) = 0"
    using decseqD[OF \<open>decseq A\<close>, of i "n + i" for n] \<open>x \<notin> A i\<close> by (auto simp: indicator_def)
  show ?thesis
    by (rule LIMSEQ_offset[of _ i]) (use * in simp)
next
  case False
  then show ?thesis by (simp add: indicator_def)
qed

lemma LIMSEQ_indicator_INT:
  "(\<lambda>k. indicator (\<Inter>i<k. A i) x :: 'a::{topological_space,zero_neq_one}) \<longlonglongrightarrow> indicator (\<Inter>i. A i) x"
proof -
  have "(\<lambda>k. indicator (\<Inter>i<k. A i) x::'a) \<longlonglongrightarrow> indicator (\<Inter>k. \<Inter>i<k. A i) x"
    by (intro LIMSEQ_indicator_decseq) (auto simp: decseq_def intro: less_le_trans)
  also have "(\<Inter>k. \<Inter>i<k. A i) = (\<Inter>i. A i)"
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
  "A \<subseteq> B \<Longrightarrow> indicator A x * indicator B x = (indicator A x :: 'a::comm_semiring_1)"
  by (auto split: split_indicator simp: fun_eq_iff)

lemma indicator_times_eq_if:
  fixes f :: "'a \<Rightarrow> 'b::comm_ring_1"
  shows "indicator S x * f x = (if x \<in> S then f x else 0)" "f x * indicator S x = (if x \<in> S then f x else 0)"
  by auto

lemma indicator_scaleR_eq_if:
  fixes f :: "'a \<Rightarrow> 'b::real_vector"
  shows "indicator S x *\<^sub>R f x = (if x \<in> S then f x else 0)"
  by simp

lemma indicator_sums:
  assumes "\<And>i j. i \<noteq> j \<Longrightarrow> A i \<inter> A j = {}"
  shows "(\<lambda>i. indicator (A i) x::real) sums indicator (\<Union>i. A i) x"
proof (cases "\<exists>i. x \<in> A i")
  case True
  then obtain i where i: "x \<in> A i" ..
  with assms have "(\<lambda>i. indicator (A i) x::real) sums (\<Sum>i\<in>{i}. indicator (A i) x)"
    by (intro sums_finite) (auto split: split_indicator)
  also have "(\<Sum>i\<in>{i}. indicator (A i) x) = indicator (\<Union>i. A i) x"
    using i by (auto split: split_indicator)
  finally show ?thesis .
next
  case False
  then show ?thesis by simp
qed

text \<open>
  The indicator function of the union of a disjoint family of sets is the
  sum over all the individual indicators.
\<close>

lemma indicator_UN_disjoint:
  "finite A \<Longrightarrow> disjoint_family_on f A \<Longrightarrow> indicator (\<Union>(f ` A)) x = (\<Sum>y\<in>A. indicator (f y) x)"
  by (induct A rule: finite_induct)
    (auto simp: disjoint_family_on_def indicator_def split: if_splits)

end

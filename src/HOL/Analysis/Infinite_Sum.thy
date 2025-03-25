(*
  Title:    HOL/Analysis/Infinite_Sum.thy
  Author:   Dominique Unruh, University of Tartu
            Manuel Eberl, University of Innsbruck

  A theory of sums over possibly infinite sets.
*)

section \<open>Infinite sums\<close>
\<^latex>\<open>\label{section:Infinite_Sum}\<close>

text \<open>In this theory, we introduce the definition of infinite sums, i.e., sums ranging over an
infinite, potentially uncountable index set with no particular ordering.
(This is different from series. Those are sums indexed by natural numbers,
and the order of the index set matters.)

Our definition is quite standard: $s:=\sum_{x\in A} f(x)$ is the limit of finite sums $s_F:=\sum_{x\in F} f(x)$ for increasing $F$.
That is, $s$ is the limit of the net $s_F$ where $F$ are finite subsets of $A$ ordered by inclusion.
We believe that this is the standard definition for such sums.
See, e.g., Definition 4.11 in \<^cite>\<open>"conway2013course"\<close>.
This definition is quite general: it is well-defined whenever $f$ takes values in some
commutative monoid endowed with a Hausdorff topology.
(Examples are reals, complex numbers, normed vector spaces, and more.)\<close>

theory Infinite_Sum
  imports
    Elementary_Topology
    "HOL-Library.Extended_Nonnegative_Real"
    "HOL-Library.Complex_Order"
begin

subsection \<open>Definition and syntax\<close>

definition HAS_SUM :: \<open>('a \<Rightarrow> 'b :: {comm_monoid_add, topological_space}) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool\<close> 
    where has_sum_def: \<open>HAS_SUM f A x \<equiv> (sum f \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>

abbreviation has_sum (infixr \<open>has'_sum\<close> 46) where
  "(f has_sum S) A \<equiv> HAS_SUM f A S"

definition summable_on :: "('a \<Rightarrow> 'b::{comm_monoid_add, topological_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr \<open>summable'_on\<close> 46) where
  "f summable_on A \<equiv> (\<exists>x. (f has_sum x) A)"

definition infsum :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infsum f A = (if f summable_on A then Lim (finite_subsets_at_top A) (sum f) else 0)"

abbreviation abs_summable_on :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr \<open>abs'_summable'_on\<close> 46) where
  "f abs_summable_on A \<equiv> (\<lambda>x. norm (f x)) summable_on A"

syntax (ASCII)
  "_infsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_add"
    (\<open>(\<open>indent=3 notation=\<open>binder INFSUM\<close>\<close>INFSUM (_/:_)./ _)\<close> [0, 51, 10] 10)
syntax
  "_infsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_add"
    (\<open>(\<open>indent=2 notation=\<open>binder \<Sum>\<^sub>\<infinity>\<close>\<close>\<Sum>\<^sub>\<infinity>(_/\<in>_)./ _)\<close> [0, 51, 10] 10)
syntax_consts
  "_infsum" \<rightleftharpoons> infsum
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>\<infinity>i\<in>A. b" \<rightleftharpoons> "CONST infsum (\<lambda>i. b) A"

syntax (ASCII)
  "_univinfsum" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>(\<open>indent=3 notation=\<open>binder INFSUM\<close>\<close>INFSUM _./ _)\<close> [0, 10] 10)
syntax
  "_univinfsum" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>(\<open>indent=2 notation=\<open>binder \<Sum>\<^sub>\<infinity>\<close>\<close>\<Sum>\<^sub>\<infinity>_./ _)\<close> [0, 10] 10)
syntax_consts
  "_univinfsum" \<rightleftharpoons> infsum
translations
  "\<Sum>\<^sub>\<infinity>x. t" \<rightleftharpoons> "CONST infsum (\<lambda>x. t) (CONST UNIV)"

syntax (ASCII)
  "_qinfsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>(\<open>indent=3 notation=\<open>binder INFSUM\<close>\<close>INFSUM _ |/ _./ _)\<close> [0, 0, 10] 10)
syntax
  "_qinfsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>(\<open>indent=2 notation=\<open>binder \<Sum>\<^sub>\<infinity>\<close>\<close>\<Sum>\<^sub>\<infinity>_ | (_)./ _)\<close> [0, 0, 10] 10)
syntax_consts
  "_qinfsum" \<rightleftharpoons> infsum
translations
  "\<Sum>\<^sub>\<infinity>x|P. t" => "CONST infsum (\<lambda>x. t) {x. P}"
print_translation \<open>
  [(\<^const_syntax>\<open>infsum\<close>, K (Collect_binder_tr' \<^syntax_const>\<open>_qinfsum\<close>))]
\<close>

subsection \<open>General properties\<close>

lemma infsumI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>(f has_sum x) A\<close>
  shows \<open>infsum f A = x\<close>
  by (metis assms finite_subsets_at_top_neq_bot infsum_def summable_on_def has_sum_def tendsto_Lim)

lemma infsum_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>x = y\<close>
  assumes \<open>(f has_sum x) A\<close>
  assumes \<open>(g has_sum y) B\<close>
  shows \<open>infsum f A = infsum g B\<close>
  using assms infsumI by blast

lemma infsum_eqI':
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>\<And>x. (f has_sum x) A \<longleftrightarrow> (g has_sum x) B\<close>
  shows \<open>infsum f A = infsum g B\<close>
  by (metis assms infsum_def infsum_eqI summable_on_def)

lemma infsum_not_exists:
  fixes f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>\<not> f summable_on A\<close>
  shows \<open>infsum f A = 0\<close>
  by (simp add: assms infsum_def)

lemma has_sum_unique:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_add, t2_space}"
  assumes "(f has_sum x) A" "(f has_sum y) A"
  shows "x = y"
  using assms infsumI by blast

lemma summable_iff_has_sum_infsum: "f summable_on A \<longleftrightarrow> (f has_sum (infsum f A)) A"
  using infsumI summable_on_def by blast

lemma has_sum_iff: "(f has_sum S) A \<longleftrightarrow> f summable_on A \<and> infsum f A = S"
  using infsumI summable_iff_has_sum_infsum by blast

lemma has_sum_infsum[simp]:
  assumes \<open>f summable_on S\<close>
  shows \<open>(f has_sum (infsum f S)) S\<close>
  using assms summable_iff_has_sum_infsum by blast

lemma has_sum_cong_neutral:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, topological_space}\<close>
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "(f has_sum x) S \<longleftrightarrow> (g has_sum x) T"
proof -
  have \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))
      = eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close> for P
  proof 
    assume \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> S\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (sum f F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> T\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> T\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (sum g F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> T\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (sum f ((F\<inter>S) \<union> (F0\<inter>S)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> S\<close> \<open>finite F0\<close> that in auto)
      also have \<open>sum f ((F\<inter>S) \<union> (F0\<inter>S)) = sum g F\<close>
        by (intro sum.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> T\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  next
    assume \<open>eventually P (filtermap (sum g) (finite_subsets_at_top T))\<close>
    then obtain F0 where \<open>finite F0\<close> and \<open>F0 \<subseteq> T\<close> and F0_P: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> T \<Longrightarrow> F \<supseteq> F0 \<Longrightarrow> P (sum g F)\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
    define F0' where \<open>F0' = F0 \<inter> S\<close>
    have [simp]: \<open>finite F0'\<close> \<open>F0' \<subseteq> S\<close>
      by (simp_all add: F0'_def \<open>finite F0\<close>)
    have \<open>P (sum f F)\<close> if \<open>finite F\<close> \<open>F \<subseteq> S\<close> \<open>F \<supseteq> F0'\<close> for F
    proof -
      have \<open>P (sum g ((F\<inter>T) \<union> (F0\<inter>T)))\<close>
        by (intro F0_P) (use \<open>F0 \<subseteq> T\<close> \<open>finite F0\<close> that in auto)
      also have \<open>sum g ((F\<inter>T) \<union> (F0\<inter>T)) = sum f F\<close>
        by (intro sum.mono_neutral_cong) (use that \<open>finite F0\<close> F0'_def assms in auto)
      finally show ?thesis .
    qed
    with \<open>F0' \<subseteq> S\<close> \<open>finite F0'\<close> show \<open>eventually P (filtermap (sum f) (finite_subsets_at_top S))\<close>
      by (metis (no_types, lifting) eventually_filtermap eventually_finite_subsets_at_top)
  qed

  then have tendsto_x: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top S) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top T)" for x
    by (simp add: le_filter_def filterlim_def)

  then show ?thesis
    by (simp add: has_sum_def)
qed

lemma summable_on_cong_neutral: 
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, topological_space}\<close>
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "f summable_on S \<longleftrightarrow> g summable_on T"
  using has_sum_cong_neutral[of T S g f, OF assms]
  by (simp add: summable_on_def)

lemma infsum_cong_neutral: 
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows \<open>infsum f S = infsum g T\<close>
  by (smt (verit, best) assms has_sum_cong_neutral infsum_eqI')

lemma has_sum_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "(f has_sum x) A \<longleftrightarrow> (g has_sum x) A"
  using assms by (intro has_sum_cong_neutral) auto

lemma summable_on_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "f summable_on A \<longleftrightarrow> g summable_on A"
  by (metis assms summable_on_def has_sum_cong)

lemma infsum_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsum f A = infsum g A"
  using assms infsum_eqI' has_sum_cong by blast

lemma summable_on_cofin_subset:
  fixes f :: "'a \<Rightarrow> 'b::topological_ab_group_add"
  assumes "f summable_on A" and [simp]: "finite F"
  shows "f summable_on (A - F)"
proof -
  from assms(1) obtain x where lim_f: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding summable_on_def has_sum_def by auto
  define F' where "F' = F\<inter>A"
  with assms have "finite F'" and "A-F = A-F'"
    by auto
  have "filtermap ((\<union>)F') (finite_subsets_at_top (A-F))
      \<le> finite_subsets_at_top A"
  proof (rule filter_leI)
    fix P assume "eventually P (finite_subsets_at_top A)"
    then obtain X where [simp]: "finite X" and XA: "X \<subseteq> A" 
      and P: "\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P Y"
      unfolding eventually_finite_subsets_at_top by auto
    define X' where "X' = X-F"
    hence [simp]: "finite X'" and [simp]: "X' \<subseteq> A-F"
      using XA by auto
    hence "finite Y \<and> X' \<subseteq> Y \<and> Y \<subseteq> A - F \<longrightarrow> P (F' \<union> Y)" for Y
      using P XA unfolding X'_def using F'_def \<open>finite F'\<close> by blast
    thus "eventually P (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))"
      unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (rule_tac x=X' in exI, simp)
  qed
  with lim_f have "(sum f \<longlongrightarrow> x) (filtermap ((\<union>)F') (finite_subsets_at_top (A-F)))"
    using tendsto_mono by blast
  have "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    if "((sum f \<circ> (\<union>) F') \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    using that unfolding o_def by auto
  hence "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_compose_filtermap [symmetric]
    by (simp add: \<open>(sum f \<longlongrightarrow> x) (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))\<close> 
        tendsto_compose_filtermap)
  have "\<forall>Y. finite Y \<and> Y \<subseteq> A - F \<longrightarrow> sum f (F' \<union> Y) = sum f F' + sum f Y"
    by (metis Diff_disjoint Int_Diff \<open>A - F = A - F'\<close> \<open>finite F'\<close> inf.orderE sum.union_disjoint)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top (A - F). sum f (F' \<union> x) = sum f F' + sum f x"
    unfolding eventually_finite_subsets_at_top
    using exI [where x = "{}"]
    by (simp add: \<open>\<And>P. P {} \<Longrightarrow> \<exists>x. P x\<close>) 
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))\<close> by fastforce
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> sum f F' + (x-sum f F')) (finite_subsets_at_top (A-F))"
    by simp
  hence "(sum f \<longlongrightarrow> x - sum f F') (finite_subsets_at_top (A-F))"
    using tendsto_add_const_iff by blast    
  thus "f summable_on (A - F)"
    unfolding summable_on_def has_sum_def by auto
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add}"
  assumes \<open>(f has_sum b) B\<close> and \<open>(f has_sum a) A\<close> and AB: "A \<subseteq> B"
  shows has_sum_Diff: "(f has_sum (b - a)) (B - A)"
proof -
  have finite_subsets1:
    "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
  proof (rule filter_leI)
    fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
    then obtain X where "finite X" and "X \<subseteq> B" 
      and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
      unfolding eventually_filtermap eventually_finite_subsets_at_top by auto

    hence "finite (X-A)" and "X-A \<subseteq> B - A"
      by auto
    moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
      using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
      by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
    ultimately show "eventually P (finite_subsets_at_top (B - A))"
      unfolding eventually_finite_subsets_at_top by meson
  qed
  have finite_subsets2: 
    "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
    apply (rule filter_leI)
      using assms unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (metis Int_subset_iff finite_Int inf_le2 subset_trans)

  from assms(1) have limB: "(sum f \<longlongrightarrow> b) (finite_subsets_at_top B)"
    using has_sum_def by auto
  from assms(2) have limA: "(sum f \<longlongrightarrow> a) (finite_subsets_at_top A)"
    using has_sum_def by blast
  have "((\<lambda>F. sum f (F\<inter>A)) \<longlongrightarrow> a) (finite_subsets_at_top B)"
  proof (subst asm_rl [of "(\<lambda>F. sum f (F\<inter>A)) = sum f \<circ> (\<lambda>F. F\<inter>A)"])
    show "(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)"
      unfolding o_def by auto
    show "((sum f \<circ> (\<lambda>F. F \<inter> A)) \<longlongrightarrow> a) (finite_subsets_at_top B)"
      unfolding o_def 
      using tendsto_compose_filtermap finite_subsets2 limA tendsto_mono
        \<open>(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)\<close> by fastforce
  qed

  with limB have "((\<lambda>F. sum f F - sum f (F\<inter>A)) \<longlongrightarrow> b - a) (finite_subsets_at_top B)"
    using tendsto_diff by blast
  have "sum f X - sum f (X \<inter> A) = sum f (X - A)" if "finite X" and "X \<subseteq> B" for X :: "'a set"
    using that by (metis add_diff_cancel_left' sum.Int_Diff)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f x - sum f (x \<inter> A) = sum f (x - A)"
    by (rule eventually_finite_subsets_at_top_weakI)  
  hence "((\<lambda>F. sum f (F-A)) \<longlongrightarrow> b - a) (finite_subsets_at_top B)"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>F. sum f F - sum f (F \<inter> A)) \<longlongrightarrow> b - a) (finite_subsets_at_top B)\<close> by fastforce
  hence "(sum f \<longlongrightarrow> b - a) (filtermap (\<lambda>F. F-A) (finite_subsets_at_top B))"
    by (subst tendsto_compose_filtermap[symmetric], simp add: o_def)
  thus ?thesis
    using finite_subsets1 has_sum_def tendsto_mono by blast
qed


lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add}"
  assumes "f summable_on B" and "f summable_on A" and "A \<subseteq> B"
  shows summable_on_Diff: "f summable_on (B-A)"
  by (meson assms summable_on_def has_sum_Diff)

lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "f summable_on B" and "f summable_on A" and AB: "A \<subseteq> B"
  shows infsum_Diff: "infsum f (B - A) = infsum f B - infsum f A"
  by (metis AB assms has_sum_Diff infsumI summable_on_def)

lemma has_sum_mono_neutral:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  (* Does this really require a linorder topology? (Instead of order topology.) *)
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  define f' g' where \<open>f' x = (if x \<in> A then f x else 0)\<close> and \<open>g' x = (if x \<in> B then g x else 0)\<close> for x
  have [simp]: \<open>f summable_on A\<close> \<open>g summable_on B\<close>
    using assms(1,2) summable_on_def by auto
  have \<open>(f' has_sum a) (A\<union>B)\<close>
    by (smt (verit, best) DiffE IntE Un_iff f'_def assms(1) has_sum_cong_neutral)
  then have f'_lim: \<open>(sum f' \<longlongrightarrow> a) (finite_subsets_at_top (A\<union>B))\<close>
    by (meson has_sum_def)
  have \<open>(g' has_sum b) (A\<union>B)\<close>
  by (smt (verit, best) DiffD1 DiffD2 IntE UnCI g'_def assms(2) has_sum_cong_neutral)
  then have g'_lim: \<open>(sum g' \<longlongrightarrow> b) (finite_subsets_at_top (A\<union>B))\<close>
    using has_sum_def by blast

  have "\<And>X i. \<lbrakk>X \<subseteq> A \<union> B; i \<in> X\<rbrakk> \<Longrightarrow> f' i \<le> g' i"
    using assms by (auto simp: f'_def g'_def)
  then have \<open>\<forall>\<^sub>F x in finite_subsets_at_top (A \<union> B). sum f' x \<le> sum g' x\<close>
    by (intro eventually_finite_subsets_at_top_weakI sum_mono)
  then show ?thesis
    using f'_lim finite_subsets_at_top_neq_bot g'_lim tendsto_le by blast
qed

lemma infsum_mono_neutral:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  by (smt (verit, best) assms has_sum_infsum has_sum_mono_neutral)

lemma has_sum_mono:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "(f has_sum x) A" and "(g has_sum y) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  using assms has_sum_mono_neutral by force

lemma infsum_mono:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  by (meson assms has_sum_infsum has_sum_mono)

lemma has_sum_finite[simp]:
  assumes "finite F"
  shows "(f has_sum (sum f F)) F"
  using assms
  by (auto intro: tendsto_Lim simp: finite_subsets_at_top_finite infsum_def has_sum_def principal_eq_bot_iff)

lemma summable_on_finite[simp]:
  fixes f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add,topological_space}\<close>
  assumes "finite F"
  shows "f summable_on F"
  using assms summable_on_def has_sum_finite by blast

lemma infsum_finite[simp]:
  assumes "finite F"
  shows "infsum f F = sum f F"
  by (simp add: assms infsumI)

lemma has_sum_finiteI: "finite A \<Longrightarrow> S = sum f A \<Longrightarrow> (f has_sum S) A"
  by simp

lemma has_sum_strict_mono_neutral:
  fixes f :: "'a \<Rightarrow> 'b :: {ordered_ab_group_add, topological_ab_group_add, linorder_topology}"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  assumes \<open>x \<in> B\<close> \<open>if x \<in> A then f x < g x else 0 < g x\<close>
  shows "a < b"
proof -
  define y where "y = (if x \<in> A then f x else 0)"
  have "a - y \<le> b - g x"
  proof (rule has_sum_mono_neutral)
    show "(f has_sum (a - y)) (A - (if x \<in> A then {x} else {}))"
      by (intro has_sum_Diff assms has_sum_finiteI) (auto simp: y_def)
    show "(g has_sum (b - g x)) (B - {x})"
      by (intro has_sum_Diff assms has_sum_finiteI) (use assms in auto)
  qed (use assms in \<open>auto split: if_splits\<close>)
  moreover have "y < g x"
    using assms(3,4,5)[of x] assms(6-) by (auto simp: y_def split: if_splits)
  ultimately show ?thesis
    by (metis diff_strict_left_mono diff_strict_mono leD neqE)
qed

lemma has_sum_strict_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {ordered_ab_group_add, topological_ab_group_add, linorder_topology}"
  assumes \<open>(f has_sum a) A\<close> and "(g has_sum b) A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>x \<in> A\<close> \<open>f x < g x\<close>
  shows "a < b"
  by (rule has_sum_strict_mono_neutral[OF assms(1,2), where x = x])
     (use assms(3-) in auto)

lemma has_sum_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "(f has_sum x) A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) x \<le> \<epsilon>"
proof -
  have "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    by (meson assms(1) has_sum_def)
  hence *: "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (sum f F) x < \<epsilon>"
    using assms(2) by (rule tendstoD)
  thus ?thesis
    unfolding eventually_finite_subsets_at_top by fastforce
qed

lemma infsum_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "f summable_on A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsum f A) \<le> \<epsilon>"
proof -
  from assms have "(f has_sum (infsum f A)) A"
    by (simp add: summable_iff_has_sum_infsum)
  from this and \<open>\<epsilon> > 0\<close> show ?thesis
    by (rule has_sum_finite_approximation)
qed

lemma abs_summable_summable:
  fixes f :: \<open>'a \<Rightarrow> 'b :: banach\<close>
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>f summable_on A\<close>
proof -
  from assms obtain L where lim: \<open>(sum (\<lambda>x. norm (f x)) \<longlongrightarrow> L) (finite_subsets_at_top A)\<close>
    unfolding has_sum_def summable_on_def by blast
  then have *: \<open>cauchy_filter (filtermap (sum (\<lambda>x. norm (f x))) (finite_subsets_at_top A))\<close>
    by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)
  have \<open>\<exists>P. eventually P (finite_subsets_at_top A) \<and>
              (\<forall>F F'. P F \<and> P F' \<longrightarrow> dist (sum f F) (sum f F') < e)\<close> if \<open>e>0\<close> for e
  proof -
    define d P where \<open>d = e/4\<close> and \<open>P F \<longleftrightarrow> finite F \<and> F \<subseteq> A \<and> dist (sum (\<lambda>x. norm (f x)) F) L < d\<close> for F
    then have \<open>d > 0\<close>
      by (simp add: d_def that)
    have ev_P: \<open>eventually P (finite_subsets_at_top A)\<close>
      using lim
      by (auto simp add: P_def[abs_def] \<open>0 < d\<close> eventually_conj_iff eventually_finite_subsets_at_top_weakI tendsto_iff)
    
    moreover have \<open>dist (sum f F1) (sum f F2) < e\<close> if \<open>P F1\<close> and \<open>P F2\<close> for F1 F2
    proof -
      from ev_P
      obtain F' where \<open>finite F'\<close> and \<open>F' \<subseteq> A\<close> and P_sup_F': \<open>finite F \<and> F \<supseteq> F' \<and> F \<subseteq> A \<Longrightarrow> P F\<close> for F
        by atomize_elim (simp add: eventually_finite_subsets_at_top)
      define F where \<open>F = F' \<union> F1 \<union> F2\<close>
      have \<open>finite F\<close> and \<open>F \<subseteq> A\<close>
        using F_def P_def[abs_def] that \<open>finite F'\<close> \<open>F' \<subseteq> A\<close> by auto
      have dist_F: \<open>dist (sum (\<lambda>x. norm (f x)) F) L < d\<close>
        by (metis F_def \<open>F \<subseteq> A\<close> P_def P_sup_F' \<open>finite F\<close> le_supE order_refl)

      have dist_F_subset: \<open>dist (sum f F) (sum f F') < 2*d\<close> if F': \<open>F' \<subseteq> F\<close> \<open>P F'\<close> for F'
      proof -
        have \<open>dist (sum f F) (sum f F') = norm (sum f (F-F'))\<close>
          unfolding dist_norm using \<open>finite F\<close> F' by (subst sum_diff) auto
        also have \<open>\<dots> \<le> norm (\<Sum>x\<in>F-F'. norm (f x))\<close>
          by (rule order.trans[OF sum_norm_le[OF order.refl]]) auto
        also have \<open>\<dots> = dist (\<Sum>x\<in>F. norm (f x)) (\<Sum>x\<in>F'. norm (f x))\<close>
          unfolding dist_norm using \<open>finite F\<close> F' by (subst sum_diff) auto
        also have \<open>\<dots> < 2 * d\<close>
          using dist_F F' unfolding P_def dist_norm real_norm_def by linarith
        finally show \<open>dist (sum f F) (sum f F') < 2*d\<close> .
      qed

      have \<open>dist (sum f F1) (sum f F2) \<le> dist (sum f F) (sum f F1) + dist (sum f F) (sum f F2)\<close>
        by (rule dist_triangle3)
      also have \<open>\<dots> < 2 * d + 2 * d\<close>
        by (intro add_strict_mono dist_F_subset that) (auto simp: F_def)
      also have \<open>\<dots> \<le> e\<close>
        by (auto simp: d_def)
      finally show \<open>dist (sum f F1) (sum f F2) < e\<close> .
    qed
    then show ?thesis
      using ev_P by blast
  qed
  then have \<open>cauchy_filter (filtermap (sum f) (finite_subsets_at_top A))\<close>
    by (simp add: cauchy_filter_metric_filtermap)
  moreover have "complete (UNIV::'b set)"
    by (meson Cauchy_convergent UNIV_I complete_def convergent_def)
  ultimately obtain L' where \<open>(sum f \<longlongrightarrow> L') (finite_subsets_at_top A)\<close>
    using complete_uniform[where S=UNIV] by (force simp add: filterlim_def)
  then show ?thesis
    using summable_on_def has_sum_def by blast
qed

text \<open>The converse of @{thm [source] abs_summable_summable} does not hold:
  Consider the Hilbert space of square-summable sequences.
  Let $e_i$ denote the sequence with 1 in the $i$th position and 0 elsewhere.
  Let $f(i) := e_i/i$ for $i\geq1$. We have \<^term>\<open>\<not> f abs_summable_on UNIV\<close> because $\lVert f(i)\rVert=1/i$
  and thus the sum over $\lVert f(i)\rVert$ diverges. On the other hand, we have \<^term>\<open>f summable_on UNIV\<close>;
  the limit is the sequence with $1/i$ in the $i$th position.

  (We have not formalized this separating example here because to the best of our knowledge,
  this Hilbert space has not been formalized in Isabelle/HOL yet.)\<close>

lemma norm_has_sum_bound:
  fixes f :: "'b \<Rightarrow> 'a::real_normed_vector"
    and A :: "'b set"
  assumes "((\<lambda>x. norm (f x)) has_sum n) A"
  assumes "(f has_sum a) A"
  shows "norm a \<le> n"
proof -
  have "norm a \<le> n + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof-
    have "\<exists>F. norm (a - sum f F) \<le> \<epsilon> \<and> finite F \<and> F \<subseteq> A"
      using has_sum_finite_approximation[where A=A and f=f and \<epsilon>="\<epsilon>"] assms \<open>0 < \<epsilon>\<close>
      by (metis dist_commute dist_norm)
    then obtain F where "norm (a - sum f F) \<le> \<epsilon>"
      and "finite F" and "F \<subseteq> A"
      by (simp add: atomize_elim)
    hence "norm a \<le> norm (sum f F) + \<epsilon>"
      by (metis add.commute diff_add_cancel dual_order.refl norm_triangle_mono)
    also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) F + \<epsilon>"
      using norm_sum by auto
    also have "\<dots> \<le> n + \<epsilon>"
    proof (intro add_right_mono [OF has_sum_mono_neutral])
      show "((\<lambda>x. norm (f x)) has_sum (\<Sum>x\<in>F. norm (f x))) F"
        by (simp add: \<open>finite F\<close>)
    qed (use \<open>F \<subseteq> A\<close> assms in auto)
    finally show ?thesis 
      by assumption
  qed
  thus ?thesis
    using linordered_field_class.field_le_epsilon by blast
qed

lemma norm_infsum_bound:
  fixes f :: "'b \<Rightarrow> 'a::real_normed_vector"
    and A :: "'b set"
  assumes "f abs_summable_on A"
  shows "norm (infsum f A) \<le> infsum (\<lambda>x. norm (f x)) A"
proof (cases "f summable_on A")
  case True
  have "((\<lambda>x. norm (f x)) has_sum (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))) A"
    by (simp add: assms)
  then show ?thesis
    by (metis True has_sum_infsum norm_has_sum_bound)
next
  case False
  obtain t where t_def: "(sum (\<lambda>x. norm (f x)) \<longlongrightarrow> t) (finite_subsets_at_top A)"
    using assms unfolding summable_on_def has_sum_def by blast
  have sumpos: "sum (\<lambda>x. norm (f x)) X \<ge> 0"
    for X
    by (simp add: sum_nonneg)
  have tgeq0:"t \<ge> 0"
  proof(rule ccontr)
    define S::"real set" where "S = {s. s < 0}"
    assume "\<not> 0 \<le> t"
    hence "t < 0" by simp
    hence "t \<in> S"
      unfolding S_def by blast
    moreover have "open S"
      by (metis S_def lessThan_def open_real_lessThan)
    ultimately have "\<forall>\<^sub>F X in finite_subsets_at_top A. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      using t_def unfolding tendsto_def by blast
    hence "\<exists>X. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      by (metis (no_types, lifting) eventually_mono filterlim_iff finite_subsets_at_top_neq_bot tendsto_Lim)
    then obtain X where "(\<Sum>x\<in>X. norm (f x)) \<in> S"
      by blast
    hence "(\<Sum>x\<in>X. norm (f x)) < 0"
      unfolding S_def by auto      
    thus False by (simp add: leD sumpos)
  qed
  have "\<exists>!h. (sum (\<lambda>x. norm (f x)) \<longlongrightarrow> h) (finite_subsets_at_top A)"
    using t_def finite_subsets_at_top_neq_bot tendsto_unique by blast
  hence "t = (Topological_Spaces.Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))))"
    using t_def unfolding Topological_Spaces.Lim_def
    by (metis the_equality)     
  hence "Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))) \<ge> 0"
    using tgeq0 by blast
  thus ?thesis unfolding infsum_def 
    using False by auto
qed

lemma infsum_tendsto:
  assumes \<open>f summable_on S\<close>
  shows \<open>((\<lambda>F. sum f F) \<longlongrightarrow> infsum f S) (finite_subsets_at_top S)\<close>
  using assms has_sum_def has_sum_infsum by blast

lemma has_sum_0: 
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>(f has_sum 0) M\<close>
  by (metis assms finite.intros(1) has_sum_cong has_sum_cong_neutral has_sum_finite sum.neutral_const)

lemma summable_on_0:
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>f summable_on M\<close>
  using assms summable_on_def has_sum_0 by blast

lemma infsum_0:
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>infsum f M = 0\<close>
  by (metis assms finite_subsets_at_top_neq_bot infsum_def has_sum_0 has_sum_def tendsto_Lim)

text \<open>Variants of @{thm [source] infsum_0} etc. suitable as simp-rules\<close>
lemma infsum_0_simp[simp]: \<open>infsum (\<lambda>_. 0) M = 0\<close>
  by (simp_all add: infsum_0)

lemma summable_on_0_simp[simp]: \<open>(\<lambda>_. 0) summable_on M\<close>
  by (simp_all add: summable_on_0)

lemma has_sum_0_simp[simp]: \<open>((\<lambda>_. 0) has_sum 0) M\<close>
  by (simp_all add: has_sum_0)


lemma has_sum_add:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add}"
  assumes \<open>(f has_sum a) A\<close>
  assumes \<open>(g has_sum b) A\<close>
  shows \<open>((\<lambda>x. f x + g x) has_sum (a + b)) A\<close>
proof -
  from assms have lim_f: \<open>(sum f \<longlongrightarrow> a)  (finite_subsets_at_top A)\<close>
    and lim_g: \<open>(sum g \<longlongrightarrow> b)  (finite_subsets_at_top A)\<close>
    by (simp_all add: has_sum_def)
  then have lim: \<open>(sum (\<lambda>x. f x + g x) \<longlongrightarrow> a + b) (finite_subsets_at_top A)\<close>
    unfolding sum.distrib by (rule tendsto_add)
  then show ?thesis
    by (simp_all add: has_sum_def)
qed

lemma summable_on_add:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add}"
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>(\<lambda>x. f x + g x) summable_on A\<close>
  by (metis (full_types) assms summable_on_def has_sum_add)

lemma infsum_add:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add, t2_space}"
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>infsum (\<lambda>x. f x + g x) A = infsum f A + infsum g A\<close>
proof -
  have \<open>((\<lambda>x. f x + g x) has_sum (infsum f A + infsum g A)) A\<close>
    by (simp add: assms has_sum_add)
  then show ?thesis
    using infsumI by blast
qed


lemma has_sum_Un_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes "(f has_sum a) A"
  assumes "(f has_sum b) B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>(f has_sum (a + b)) (A \<union> B)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 0)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 0)\<close> for x
  have fA: \<open>(fA has_sum a) (A \<union> B)\<close>
    by (smt (verit, ccfv_SIG) DiffD1 DiffD2 UnCI fA_def assms(1) has_sum_cong_neutral inf_sup_absorb)
  have fB: \<open>(fB has_sum b) (A \<union> B)\<close>
    by (smt (verit, best) DiffD1 DiffD2 IntE Un_iff fB_def assms(2) disj disjoint_iff has_sum_cong_neutral)
  have fAB: \<open>f x = fA x + fB x\<close> for x
    unfolding fA_def fB_def by simp
  show ?thesis
    unfolding fAB
    using fA fB by (rule has_sum_add)
qed

lemma summable_on_Un_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes "f summable_on A"
  assumes "f summable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>f summable_on (A \<union> B)\<close>
  by (meson assms disj summable_on_def has_sum_Un_disjoint)

lemma infsum_Un_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add, t2_space}"
  assumes "f summable_on A"
  assumes "f summable_on B"
  assumes disj: "A \<inter> B = {}"
  shows \<open>infsum f (A \<union> B) = infsum f A + infsum f B\<close>
  by (intro infsumI has_sum_Un_disjoint has_sum_infsum assms)  

lemma norm_summable_imp_has_sum:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "summable (\<lambda>n. norm (f n))" and "f sums S"
  shows   "(f has_sum S) (UNIV :: nat set)"
  unfolding has_sum_def tendsto_iff eventually_finite_subsets_at_top
proof clarsimp
  fix \<epsilon>::real 
  assume "\<epsilon> > 0"
  from assms obtain S' where S': "(\<lambda>n. norm (f n)) sums S'"
    by (auto simp: summable_def)
  with \<open>\<epsilon> > 0\<close> obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>S' - (\<Sum>i<n. norm (f i))\<bar> < \<epsilon>"
    by (auto simp: tendsto_iff eventually_at_top_linorder sums_def dist_norm abs_minus_commute)
  have "dist (sum f Y) S < \<epsilon>" if "finite Y" "{..<N} \<subseteq> Y" for Y
  proof -
    from that have "(\<lambda>n. if n \<in> Y then 0 else f n) sums (S - sum f Y)"
      by (intro sums_If_finite_set'[OF \<open>f sums S\<close>]) (auto simp: sum_negf)
    hence "S - sum f Y = (\<Sum>n. if n \<in> Y then 0 else f n)"
      by (simp add: sums_iff)
    also have "norm \<dots> \<le> (\<Sum>n. norm (if n \<in> Y then 0 else f n))"
      by (rule summable_norm[OF summable_comparison_test'[OF assms(1)]]) auto
    also have "\<dots> \<le> (\<Sum>n. if n < N then 0 else norm (f n))"
      using that by (intro suminf_le summable_comparison_test'[OF assms(1)]) auto
    also have "(\<lambda>n. if n \<in> {..<N} then 0 else norm (f n)) sums (S' - (\<Sum>i<N. norm (f i)))" 
      by (intro sums_If_finite_set'[OF S']) (auto simp: sum_negf)
    hence "(\<Sum>n. if n < N then 0 else norm (f n)) = S' - (\<Sum>i<N. norm (f i))"
      by (simp add: sums_iff)
    also have "S' - (\<Sum>i<N. norm (f i)) \<le> \<bar>S' - (\<Sum>i<N. norm (f i))\<bar>" by simp
    also have "\<dots> < \<epsilon>" by (rule N) auto
    finally show ?thesis by (simp add: dist_norm norm_minus_commute)
  qed
  then show "\<exists>X. finite X \<and> (\<forall>Y. finite Y \<and> X \<subseteq> Y \<longrightarrow> dist (sum f Y) S < \<epsilon>)"
    by (meson finite_lessThan subset_UNIV)
qed

lemma norm_summable_imp_summable_on:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "summable (\<lambda>n. norm (f n))"
  shows   "f summable_on UNIV"
  using norm_summable_imp_has_sum[OF assms, of "suminf f"] assms
  by (auto simp: sums_iff summable_on_def dest: summable_norm_cancel)

lemma sums_nonneg_imp_has_sum_strong:
  assumes "f sums (S::real)" "eventually (\<lambda>n. f n \<ge> 0) sequentially"
  shows   "(f has_sum S) UNIV"
proof -
  from assms(2) obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> f n \<ge> 0"
    by (auto simp: eventually_at_top_linorder)
  from assms(1) have "summable f"
    by (simp add: sums_iff)
  hence "summable (\<lambda>n. f (n + N))"
    by (rule summable_ignore_initial_segment)
  hence "summable (\<lambda>n. norm (f (n + N)))"
    using N by simp
  hence "summable (\<lambda>n. norm (f n))"
    using summable_iff_shift by blast
  with assms(1) show ?thesis
    using norm_summable_imp_has_sum by blast
qed

lemma sums_nonneg_imp_has_sum:
  assumes "f sums (S::real)" and "\<And>n. f n \<ge> 0"
  shows   "(f has_sum S) UNIV"
  by (rule sums_nonneg_imp_has_sum_strong) (use assms in auto)

lemma summable_nonneg_imp_summable_on_strong:
  assumes "summable f" "eventually (\<lambda>n. f n \<ge> (0::real)) sequentially"
  shows   "f summable_on UNIV"
  using assms has_sum_iff sums_nonneg_imp_has_sum_strong by blast

lemma summable_nonneg_imp_summable_on:
  assumes "summable f" "\<And>n. f n \<ge> (0::real)"
  shows   "f summable_on UNIV"
  by (rule summable_nonneg_imp_summable_on_strong) (use assms in auto)

text \<open>The following lemma indeed needs a complete space (as formalized by the premise \<^term>\<open>complete UNIV\<close>).
  The following two counterexamples show this:
  \begin{itemize}
  \item Consider the real vector space $V$ of sequences with finite support, and with the $\ell_2$-norm (sum of squares).
      Let $e_i$ denote the sequence with a $1$ at position $i$.
      Let $f : \mathbb Z \to V$ be defined as $f(n) := e_{\lvert n\rvert} / n$ (with $f(0) := 0$).
      We have that $\sum_{n\in\mathbb Z} f(n) = 0$ (it even converges absolutely). 
      But $\sum_{n\in\mathbb N} f(n)$ does not exist (it would converge against a sequence with infinite support).
  
  \item Let $f$ be a positive rational valued function such that $\sum_{x\in B} f(x)$ is $\sqrt 2$ and $\sum_{x\in A} f(x)$ is 1 (over the reals, with $A\subseteq B$).
      Then $\sum_{x\in B} f(x)$ does not exist over the rationals. But $\sum_{x\in A} f(x)$ exists.
  \end{itemize}

  The lemma also requires uniform continuity of the addition. And example of a topological group with continuous 
  but not uniformly continuous addition would be the positive reals with the usual multiplication as the addition.
  We do not know whether the lemma would also hold for such topological groups.\<close>

lemma summable_on_subset_aux:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::{ab_group_add, uniform_space}\<close>
  assumes \<open>complete (UNIV :: 'b set)\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'b,y). x+y)\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>f summable_on B\<close>
proof -
  let ?filter_fB = \<open>filtermap (sum f) (finite_subsets_at_top B)\<close>
  from \<open>f summable_on A\<close>
  obtain S where \<open>(sum f \<longlongrightarrow> S) (finite_subsets_at_top A)\<close> (is \<open>(sum f \<longlongrightarrow> S) ?filter_A\<close>)
    using summable_on_def has_sum_def by blast
  then have cauchy_fA: \<open>cauchy_filter (filtermap (sum f) (finite_subsets_at_top A))\<close> (is \<open>cauchy_filter ?filter_fA\<close>)
    by (auto intro!: nhds_imp_cauchy_filter simp: filterlim_def)

  have \<open>cauchy_filter (filtermap (sum f) (finite_subsets_at_top B))\<close>
  proof (unfold cauchy_filter_def, rule filter_leI)
    fix E :: \<open>('b\<times>'b) \<Rightarrow> bool\<close> assume \<open>eventually E uniformity\<close>
    then obtain E' where \<open>eventually E' uniformity\<close> and E'E'E: \<open>E' (x, y) \<longrightarrow> E' (y, z) \<longrightarrow> E (x, z)\<close> for x y z
      using uniformity_trans by blast
    obtain D where \<open>eventually D uniformity\<close> and DE: \<open>D (x, y) \<Longrightarrow> E' (x+c, y+c)\<close> for x y c
      using plus_cont \<open>eventually E' uniformity\<close>
      unfolding uniformly_continuous_on_uniformity filterlim_def le_filter_def uniformity_prod_def
      by (auto simp: case_prod_beta eventually_filtermap eventually_prod_same uniformity_refl)
    have DE': "E' (x, y)" if "D (x + c, y + c)" for x y c
      using DE[of "x + c" "y + c" "-c"] that by simp

    from \<open>eventually D uniformity\<close> and cauchy_fA have \<open>eventually D (?filter_fA \<times>\<^sub>F ?filter_fA)\<close>
      unfolding cauchy_filter_def le_filter_def by simp
    then obtain P1 P2
      where ev_P1: \<open>eventually (\<lambda>F. P1 (sum f F)) ?filter_A\<close> 
        and ev_P2: \<open>eventually (\<lambda>F. P2 (sum f F)) ?filter_A\<close>
        and P1P2E: \<open>P1 x \<Longrightarrow> P2 y \<Longrightarrow> D (x, y)\<close> for x y
      unfolding eventually_prod_filter eventually_filtermap
      by auto
    from ev_P1 obtain F1 where F1: \<open>finite F1\<close> \<open>F1 \<subseteq> A\<close> \<open>\<And>F. F\<supseteq>F1 \<Longrightarrow> finite F \<Longrightarrow> F\<subseteq>A \<Longrightarrow> P1 (sum f F)\<close>
      by (metis eventually_finite_subsets_at_top)
    from ev_P2 obtain F2 where F2: \<open>finite F2\<close> \<open>F2 \<subseteq> A\<close> \<open>\<And>F. F\<supseteq>F2 \<Longrightarrow> finite F \<Longrightarrow> F\<subseteq>A \<Longrightarrow> P2 (sum f F)\<close>
      by (metis eventually_finite_subsets_at_top)
    define F0 F0A F0B where \<open>F0 \<equiv> F1 \<union> F2\<close> and \<open>F0A \<equiv> F0 - B\<close> and \<open>F0B \<equiv> F0 \<inter> B\<close>
    have [simp]: \<open>finite F0\<close>  \<open>F0 \<subseteq> A\<close>
      using \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close> \<open>finite F1\<close> \<open>finite F2\<close> unfolding F0_def by blast+
 
    have *: "E' (sum f F1', sum f F2')"
      if "F1'\<supseteq>F0B" "F2'\<supseteq>F0B" "finite F1'" "finite F2'" "F1'\<subseteq>B" "F2'\<subseteq>B" for F1' F2'
    proof (intro DE'[where c = "sum f F0A"] P1P2E)
      have "P1 (sum f (F1' \<union> F0A))"
        using that assms F1(1,2) F2(1,2) by (intro F1) (auto simp: F0A_def F0B_def F0_def)
      thus "P1 (sum f F1' + sum f F0A)"
        by (subst (asm) sum.union_disjoint) (use that in \<open>auto simp: F0A_def\<close>)
    next
      have "P2 (sum f (F2' \<union> F0A))"
        using that assms F1(1,2) F2(1,2) by (intro F2) (auto simp: F0A_def F0B_def F0_def)
      thus "P2 (sum f F2' + sum f F0A)"
        by (subst (asm) sum.union_disjoint) (use that in \<open>auto simp: F0A_def\<close>)      
    qed

    have "eventually (\<lambda>x. E' (x, sum f F0B)) (filtermap (sum f) (finite_subsets_at_top B))"
     and "eventually (\<lambda>x. E' (sum f F0B, x)) (filtermap (sum f) (finite_subsets_at_top B))"
        unfolding eventually_filtermap eventually_finite_subsets_at_top
        by (rule exI[of _ F0B]; use * in \<open>force simp: F0B_def\<close>)+
      then 
    show \<open>eventually E (?filter_fB \<times>\<^sub>F ?filter_fB)\<close>
      unfolding eventually_prod_filter
      using E'E'E by blast
  qed

  then obtain x where \<open>?filter_fB \<le> nhds x\<close>
    using cauchy_filter_complete_converges[of ?filter_fB UNIV] \<open>complete (UNIV :: _)\<close>
    by (auto simp: filtermap_bot_iff)
  then have \<open>(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)\<close>
    by (auto simp: filterlim_def)
  then show ?thesis
    by (auto simp: summable_on_def has_sum_def)
qed

text \<open>A special case of @{thm [source] summable_on_subset_aux} for Banach spaces with fewer premises.\<close>

lemma summable_on_subset_banach:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::banach\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>f summable_on B\<close>
  by (meson Cauchy_convergent UNIV_I assms complete_def convergent_def isUCont_plus summable_on_subset_aux)

lemma has_sum_empty[simp]: \<open>(f has_sum 0) {}\<close>
  by (meson ex_in_conv has_sum_0)

lemma summable_on_empty[simp]: \<open>f summable_on {}\<close>
  by auto

lemma infsum_empty[simp]: \<open>infsum f {} = 0\<close>
  by simp

lemma sum_has_sum:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes \<open>finite A\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> (f has_sum (s a)) (B a)\<close>
  assumes \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>(f has_sum (sum s A)) (\<Union>a\<in>A. B a)\<close>
  using assms 
proof (induction)
  case empty
  then show ?case 
    by simp
next
  case (insert x A)
  have \<open>(f has_sum (s x)) (B x)\<close>
    by (simp add: insert.prems)
  moreover have IH: \<open>(f has_sum (sum s A)) (\<Union>a\<in>A. B a)\<close>
    using insert by simp
  ultimately have \<open>(f has_sum (s x + sum s A)) (B x \<union> (\<Union>a\<in>A. B a))\<close>
    using insert by (intro has_sum_Un_disjoint) auto
  then show ?case
    using insert.hyps by auto
qed


lemma summable_on_finite_union_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f summable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>f summable_on (\<Union>a\<in>A. B a)\<close>
  using sum_has_sum [of A f B] assms unfolding summable_on_def by metis

lemma sum_infsum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add, t2_space}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f summable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>sum (\<lambda>a. infsum f (B a)) A = infsum f (\<Union>a\<in>A. B a)\<close>
  by (metis (no_types, lifting) assms has_sum_infsum infsumI sum_has_sum)

text \<open>The lemmas \<open>infsum_comm_additive_general\<close> and \<open>infsum_comm_additive\<close> (and variants) below both state that the infinite sum commutes with
  a continuous additive function. \<open>infsum_comm_additive_general\<close> is stated more for more general type classes
  at the expense of a somewhat less compact formulation of the premises.
  E.g., by avoiding the constant \<^const>\<open>additive\<close> which introduces an additional sort constraint
  (group instead of monoid). For example, extended reals (\<^typ>\<open>ereal\<close>, \<^typ>\<open>ennreal\<close>) are not covered
  by \<open>infsum_comm_additive\<close>.\<close>


lemma has_sum_comm_additive_general: 
  fixes f :: \<open>'b :: {comm_monoid_add,topological_space} \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f \<circ> g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes cont: \<open>f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes infsum: \<open>(g has_sum x) S\<close>
  shows \<open>((f \<circ> g) has_sum (f x)) S\<close> 
proof -
  have \<open>(sum g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    using infsum has_sum_def by blast
  then have \<open>((f \<circ> sum g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    by (meson cont filterlim_def tendsto_at_iff_tendsto_nhds tendsto_compose_filtermap tendsto_mono)
  then have \<open>(sum (f \<circ> g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    using tendsto_cong f_sum
    by (simp add: Lim_transform_eventually eventually_finite_subsets_at_top_weakI)
  then show \<open>((f \<circ> g) has_sum (f x)) S\<close>
    using has_sum_def by blast 
qed

lemma summable_on_comm_additive_general:
  fixes f :: \<open>'b :: {comm_monoid_add,topological_space} \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f \<circ> g) F = f (sum g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>\<And>x. (g has_sum x) S \<Longrightarrow> f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f \<circ> g) summable_on S\<close>
  by (meson assms summable_on_def has_sum_comm_additive_general has_sum_def infsum_tendsto)

lemma infsum_comm_additive_general:
  fixes f :: \<open>'b :: {comm_monoid_add,t2_space} \<Rightarrow> 'c :: {comm_monoid_add,t2_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f \<circ> g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
  using assms
  by (intro infsumI has_sum_comm_additive_general has_sum_infsum) (auto simp: isCont_def)

lemma has_sum_comm_additive: 
  fixes f :: \<open>'b :: {ab_group_add,topological_space} \<Rightarrow> 'c :: {ab_group_add,topological_space}\<close>
  assumes \<open>additive f\<close>
  assumes \<open>f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes infsum: \<open>(g has_sum x) S\<close>
  shows \<open>((f \<circ> g) has_sum (f x)) S\<close>
  using assms
  by (intro has_sum_comm_additive_general has_sum_infsum) (auto simp: isCont_def additive.sum) 

lemma summable_on_comm_additive:
  fixes f :: \<open>'b :: {ab_group_add,t2_space} \<Rightarrow> 'c :: {ab_group_add,topological_space}\<close>
  assumes \<open>additive f\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f \<circ> g) summable_on S\<close>
  by (meson assms summable_on_def has_sum_comm_additive has_sum_infsum isContD)

lemma infsum_comm_additive:
  fixes f :: \<open>'b :: {ab_group_add,t2_space} \<Rightarrow> 'c :: {ab_group_add,t2_space}\<close>
  assumes \<open>additive f\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f \<circ> g) S = f (infsum g S)\<close>
  by (rule infsum_comm_additive_general; auto simp: assms additive.sum)

lemma nonneg_bdd_above_has_sum:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>(f has_sum (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)) A\<close>
proof -
  have \<open>(sum f \<longlongrightarrow> (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)) (finite_subsets_at_top A)\<close>
  proof (rule order_tendstoI)
    fix a assume \<open>a < (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
    then obtain F where \<open>a < sum f F\<close> and \<open>finite F\<close> and \<open>F \<subseteq> A\<close>
      by (metis (mono_tags, lifting) Collect_cong Collect_empty_eq assms(2) empty_subsetI finite.emptyI less_cSUP_iff mem_Collect_eq)
    have "\<And>Y. \<lbrakk>finite Y; F \<subseteq> Y; Y \<subseteq> A\<rbrakk> \<Longrightarrow> a < sum f Y"
      by (meson DiffE \<open>a < sum f F\<close> assms(1) less_le_trans subset_iff sum_mono2)
    then show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. a < sum f x\<close>
      by (metis \<open>F \<subseteq> A\<close> \<open>finite F\<close> eventually_finite_subsets_at_top)
  next
    fix a assume *: \<open>(SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F) < a\<close>
    have "sum f F \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)" if \<open>F\<subseteq>A\<close> and \<open>finite F\<close> for F
        by (rule cSUP_upper) (use that assms(2) in \<open>auto simp: conj_commute\<close>)
    then show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x < a\<close>
      by (metis (no_types, lifting) "*" eventually_finite_subsets_at_top_weakI order_le_less_trans)
  qed
  then show ?thesis
    using has_sum_def by blast
qed

lemma nonneg_bdd_above_summable_on:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>f summable_on A\<close>
  using assms summable_on_def nonneg_bdd_above_has_sum by blast

lemma nonneg_bdd_above_infsum:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>infsum f A = (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
  using assms by (auto intro!: infsumI nonneg_bdd_above_has_sum)

lemma nonneg_has_sum_complete:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>(f has_sum (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)) A\<close>
  using assms nonneg_bdd_above_has_sum by blast

lemma nonneg_summable_on_complete:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>f summable_on A\<close>
  using assms nonneg_bdd_above_summable_on by blast

lemma nonneg_infsum_complete:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>infsum f A = (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
  using assms nonneg_bdd_above_infsum by blast

lemma has_sum_nonneg:
  fixes f :: "'a \<Rightarrow> 'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "(f has_sum a) M"
    and "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "a \<ge> 0"
  by (metis (no_types, lifting) DiffD1 assms empty_iff has_sum_0 has_sum_mono_neutral order_refl)

lemma infsum_nonneg:
  fixes f :: "'a \<Rightarrow> 'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0" (is "?lhs \<ge> _")
  by (metis assms has_sum_infsum has_sum_nonneg infsum_not_exists linorder_linear)

lemma has_sum_mono2:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "(f has_sum S) A" "(f has_sum S') B" "A \<subseteq> B"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows   "S \<le> S'"
  by (metis add_0 add_right_mono assms diff_add_cancel has_sum_Diff has_sum_nonneg)

lemma infsum_mono2:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" "f summable_on B" "A \<subseteq> B"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows   "infsum f A \<le> infsum f B"
  by (rule has_sum_mono2[OF has_sum_infsum has_sum_infsum]) (use assms in auto)

lemma finite_sum_le_has_sum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "(f has_sum S) A" "finite B" "B \<subseteq> A"
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x \<ge> 0"
  shows   "sum f B \<le> S"
  by (meson assms has_sum_finite has_sum_mono2)

lemma finite_sum_le_infsum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" "finite B" "B \<subseteq> A"
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x \<ge> 0"
  shows   "sum f B \<le> infsum f A"
  by (rule finite_sum_le_has_sum[OF has_sum_infsum]) (use assms in auto)

lemma has_sum_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>(g has_sum x) (h ` A) \<longleftrightarrow> ((g \<circ> h) has_sum x) A\<close>
proof -
  have \<open>(g has_sum x) (h ` A) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top (h ` A))\<close>
    by (simp add: has_sum_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>F. sum g (h ` F)) \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>
    by (metis assms filterlim_filtermap filtermap_image_finite_subsets_at_top)
  also have \<open>\<dots> \<longleftrightarrow> (sum (g \<circ> h) \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>
  proof (intro tendsto_cong eventually_finite_subsets_at_top_weakI sum.reindex)
    show "\<And>X. \<lbrakk>finite X; X \<subseteq> A\<rbrakk> \<Longrightarrow> inj_on h X"
      using assms subset_inj_on by blast
  qed
  also have \<open>\<dots> \<longleftrightarrow> ((g \<circ> h) has_sum x) A\<close>
    by (simp add: has_sum_def)
  finally show ?thesis .
qed

lemma summable_on_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>g summable_on (h ` A) \<longleftrightarrow> (g \<circ> h) summable_on A\<close>
  by (simp add: assms summable_on_def has_sum_reindex)

lemma infsum_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>infsum g (h ` A) = infsum (g \<circ> h) A\<close>
  by (metis assms has_sum_infsum has_sum_reindex infsumI infsum_def)

lemma summable_on_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "(\<lambda>x. f (g x)) summable_on A \<longleftrightarrow> f summable_on B"
  by (smt (verit) assms bij_betw_def o_apply summable_on_cong summable_on_reindex) 

lemma infsum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infsum (\<lambda>x. f (g x)) A = infsum f B"
  by (metis (mono_tags, lifting) assms bij_betw_def infsum_cong infsum_reindex o_def)

lemma sum_uniformity:
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'b::{uniform_space,comm_monoid_add},y). x+y)\<close>
  assumes EE: \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually D uniformity\<close> 
    and \<open>\<And>M::'a set. \<And>f f' :: 'a \<Rightarrow> 'b. card M \<le> n \<and> (\<forall>m\<in>M. D (f m, f' m)) \<Longrightarrow> E (sum f M, sum f' M)\<close>
proof (atomize_elim, insert EE, induction n arbitrary: E rule:nat_induct)
  case 0
  then show ?case
    by (metis card_eq_0_iff equals0D le_zero_eq sum.infinite sum.not_neutral_contains_not_neutral uniformity_refl)
next
  case (Suc n)
  from plus_cont[unfolded uniformly_continuous_on_uniformity filterlim_def le_filter_def, rule_format, OF Suc.prems]
  obtain D1 D2 where \<open>eventually D1 uniformity\<close> and \<open>eventually D2 uniformity\<close> 
    and D1D2E: \<open>D1 (x, y) \<Longrightarrow> D2 (x', y') \<Longrightarrow> E (x + x', y + y')\<close> for x y x' y'
    apply atomize_elim
    by (auto simp: eventually_prod_filter case_prod_beta uniformity_prod_def eventually_filtermap)

  from Suc.IH[OF \<open>eventually D2 uniformity\<close>]
  obtain D3 where \<open>eventually D3 uniformity\<close> and D3: \<open>card M \<le> n \<Longrightarrow> (\<forall>m\<in>M. D3 (f m, f' m)) \<Longrightarrow> D2 (sum f M, sum f' M)\<close> 
    for M :: \<open>'a set\<close> and f f'
    by metis

  define D where \<open>D x \<equiv> D1 x \<and> D3 x\<close> for x
  have \<open>eventually D uniformity\<close>
    using D_def \<open>eventually D1 uniformity\<close> \<open>eventually D3 uniformity\<close> eventually_elim2 by blast

  have \<open>E (sum f M, sum f' M)\<close> 
    if \<open>card M \<le> Suc n\<close> and DM: \<open>\<forall>m\<in>M. D (f m, f' m)\<close>
    for M :: \<open>'a set\<close> and f f'
  proof (cases \<open>card M = 0\<close>)
    case True
    then show ?thesis
      by (metis Suc.prems card_eq_0_iff sum.empty sum.infinite uniformity_refl) 
  next
    case False
    with \<open>card M \<le> Suc n\<close> obtain N x where \<open>card N \<le> n\<close> and \<open>x \<notin> N\<close> and \<open>M = insert x N\<close>
      by (metis card_Suc_eq less_Suc_eq_0_disj less_Suc_eq_le)

    from DM have \<open>\<And>m. m\<in>N \<Longrightarrow> D (f m, f' m)\<close>
      using \<open>M = insert x N\<close> by blast
    with D3[OF \<open>card N \<le> n\<close>]
    have D2_N: \<open>D2 (sum f N, sum f' N)\<close>
      using D_def by blast

    from DM 
    have \<open>D (f x, f' x)\<close>
      using \<open>M = insert x N\<close> by blast
    then have \<open>D1 (f x, f' x)\<close>
      by (simp add: D_def)

    with D2_N
    have \<open>E (f x + sum f N, f' x + sum f' N)\<close>
      using D1D2E by presburger

    then show \<open>E (sum f M, sum f' M)\<close>
      by (metis False \<open>M = insert x N\<close> \<open>x \<notin> N\<close> card.infinite finite_insert sum.insert)
  qed
  with \<open>eventually D uniformity\<close> show ?case 
    by auto
qed

lemma has_sum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add,uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "(f has_sum a) (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_sum b x) (B x)\<close>
  shows "(b has_sum a) A"
proof -
  define F FB FA where \<open>F = finite_subsets_at_top (Sigma A B)\<close> and \<open>FB x = finite_subsets_at_top (B x)\<close>
    and \<open>FA = finite_subsets_at_top A\<close> for x

  from summableB
  have sum_b: \<open>(sum (\<lambda>y. f (x, y)) \<longlongrightarrow> b x) (FB x)\<close> if \<open>x \<in> A\<close> for x
    using FB_def[abs_def] has_sum_def that by auto
  from summableAB
  have sum_S: \<open>(sum f \<longlongrightarrow> a) F\<close>
    using F_def has_sum_def by blast

  have finite_proj: \<open>finite {b| b. (a,b) \<in> H}\<close> if \<open>finite H\<close> for H :: \<open>('a\<times>'b) set\<close> and a
    by (metis (no_types, lifting) finite_imageI finite_subset image_eqI mem_Collect_eq snd_conv subsetI that)

  have \<open>(sum b \<longlongrightarrow> a) FA\<close>
  proof (rule tendsto_iff_uniformity[THEN iffD2, rule_format])
    fix E :: \<open>('c \<times> 'c) \<Rightarrow> bool\<close>
    assume \<open>eventually E uniformity\<close>
    then obtain D where D_uni: \<open>eventually D uniformity\<close> and DDE': \<open>\<And>x y z. D (x, y) \<Longrightarrow> D (y, z) \<Longrightarrow> E (x, z)\<close>
      by (metis (no_types, lifting) \<open>eventually E uniformity\<close> uniformity_transE)
    from sum_S obtain G where \<open>finite G\<close> and \<open>G \<subseteq> Sigma A B\<close>
      and G_sum: \<open>G \<subseteq> H \<Longrightarrow> H \<subseteq> Sigma A B \<Longrightarrow> finite H \<Longrightarrow> D (sum f H, a)\<close> for H
      unfolding tendsto_iff_uniformity
      by (metis (mono_tags, lifting) D_uni F_def eventually_finite_subsets_at_top)
    have \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> by auto
    thm uniformity_prod_def
    define Ga where \<open>Ga a = {b. (a,b) \<in> G}\<close> for a
    have Ga_fin: \<open>finite (Ga a)\<close> and Ga_B: \<open>Ga a \<subseteq> B a\<close> for a
      using \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> finite_proj by (auto simp: Ga_def finite_proj)

    have \<open>E (sum b M, a)\<close> if \<open>M \<supseteq> fst ` G\<close> and \<open>finite M\<close> and \<open>M \<subseteq> A\<close> for M
    proof -
      define FMB where \<open>FMB = finite_subsets_at_top (Sigma M B)\<close>
      have \<open>eventually (\<lambda>H. D (\<Sum>a\<in>M. b a, \<Sum>(a,b)\<in>H. f (a,b))) FMB\<close>
      proof -
        obtain D' where D'_uni: \<open>eventually D' uniformity\<close> 
          and \<open>card M' \<le> card M \<and> (\<forall>m\<in>M'. D' (g m, g' m)) \<Longrightarrow> D (sum g M', sum g' M')\<close>
        for M' :: \<open>'a set\<close> and g g'
          using sum_uniformity[OF plus_cont \<open>eventually D uniformity\<close>] by blast
        then have D'_sum_D: \<open>(\<forall>m\<in>M. D' (g m, g' m)) \<Longrightarrow> D (sum g M, sum g' M)\<close> for g g'
          by auto

        obtain Ha where \<open>Ha a \<supseteq> Ga a\<close> and Ha_fin: \<open>finite (Ha a)\<close> and Ha_B: \<open>Ha a \<subseteq> B a\<close>
          and D'_sum_Ha: \<open>Ha a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (b a, sum (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
        proof -
          from sum_b[unfolded tendsto_iff_uniformity, rule_format, OF _ D'_uni[THEN uniformity_sym]]
          obtain Ha0 where \<open>finite (Ha0 a)\<close> and \<open>Ha0 a \<subseteq> B a\<close>
            and \<open>Ha0 a \<subseteq> L \<Longrightarrow> L \<subseteq> B a \<Longrightarrow> finite L \<Longrightarrow> D' (b a, sum (\<lambda>b. f (a,b)) L)\<close> if \<open>a \<in> A\<close> for a L
            unfolding FB_def eventually_finite_subsets_at_top unfolding prod.case by metis
          moreover define Ha where \<open>Ha a = Ha0 a \<union> Ga a\<close> for a
          ultimately show ?thesis
            using that[where Ha=Ha]
            using Ga_fin Ga_B by auto
        qed

        have \<open>D (\<Sum>a\<in>M. b a, \<Sum>(a,b)\<in>H. f (a,b))\<close> if \<open>finite H\<close> and \<open>H \<subseteq> Sigma M B\<close> and \<open>H \<supseteq> Sigma M Ha\<close> for H
        proof -
          define Ha' where \<open>Ha' a = {b| b. (a,b) \<in> H}\<close> for a
          have [simp]: \<open>finite (Ha' a)\<close> and [simp]: \<open>Ha' a \<supseteq> Ha a\<close> and [simp]: \<open>Ha' a \<subseteq> B a\<close> if \<open>a \<in> M\<close> for a
            unfolding Ha'_def using \<open>finite H\<close> \<open>H \<subseteq> Sigma M B\<close> \<open>Sigma M Ha \<subseteq> H\<close> that finite_proj by auto
          have \<open>Sigma M Ha' = H\<close>
            using that by (auto simp: Ha'_def)
          then have *: \<open>(\<Sum>(a,b)\<in>H. f (a,b)) = (\<Sum>a\<in>M. \<Sum>b\<in>Ha' a. f (a,b))\<close>
            by (simp add: \<open>finite M\<close> sum.Sigma)
          have \<open>D' (b a, sum (\<lambda>b. f (a,b)) (Ha' a))\<close> if \<open>a \<in> M\<close> for a
            using D'_sum_Ha \<open>M \<subseteq> A\<close> that by auto
          then have \<open>D (\<Sum>a\<in>M. b a, \<Sum>a\<in>M. sum (\<lambda>b. f (a,b)) (Ha' a))\<close>
            by (rule_tac D'_sum_D, auto)
          with * show ?thesis
            by auto
        qed
        moreover have \<open>Sigma M Ha \<subseteq> Sigma M B\<close>
          using Ha_B \<open>M \<subseteq> A\<close> by auto
        ultimately show ?thesis
          unfolding FMB_def eventually_finite_subsets_at_top
          by (metis (no_types, lifting) Ha_fin finite_SigmaI subsetD that(2) that(3))
      qed
      moreover have \<open>eventually (\<lambda>H. D (\<Sum>(a,b)\<in>H. f (a,b), a)) FMB\<close>
        unfolding FMB_def eventually_finite_subsets_at_top
      proof (rule exI[of _ G], safe)
        fix Y assume Y: "finite Y" "G \<subseteq> Y" "Y \<subseteq> Sigma M B"
        thus "D (\<Sum>(a,b)\<in>Y. f (a, b), a)"
          using G_sum[of Y] Y using that(3) by fastforce
      qed (use \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> that in auto)
      ultimately have \<open>\<forall>\<^sub>F x in FMB. E (sum b M, a)\<close>
        by eventually_elim (use DDE' in auto)
      then show \<open>E (sum b M, a)\<close>
        using FMB_def by force
    qed
    then show \<open>\<forall>\<^sub>F x in FA. E (sum b x, a)\<close>
      using \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      by (metis (mono_tags, lifting) FA_def eventually_finite_subsets_at_top)
  qed
  then show ?thesis
    by (simp add: FA_def has_sum_def)
qed

lemma summable_on_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add, t2_space, uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "(\<lambda>(x,y). f x y) summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) summable_on (B x)\<close>
  shows \<open>(\<lambda>x. infsum (f x) (B x)) summable_on A\<close>
proof -
  from summableAB obtain a where a: \<open>((\<lambda>(x,y). f x y) has_sum a) (Sigma A B)\<close>
    using has_sum_infsum by blast
  from summableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x has_sum infsum (f x) (B x)) (B x)\<close>
    by (auto intro!: has_sum_infsum)
  show ?thesis
    using plus_cont a b
    by (smt (verit) has_sum_Sigma[where f=\<open>\<lambda>(x,y). f x y\<close>] has_sum_cong old.prod.case summable_on_def) 
qed

lemma infsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add, t2_space, uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "f summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from summableAB have a: \<open>(f has_sum infsum f (Sigma A B)) (Sigma A B)\<close>
    using has_sum_infsum by blast
  from summableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_sum infsum (\<lambda>y. f (x, y)) (B x)) (B x)\<close>
    by (auto intro!: has_sum_infsum)
  show ?thesis
    using plus_cont a b by (auto intro: infsumI[symmetric] has_sum_Sigma simp: summable_on_def)
qed

lemma infsum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add, t2_space, uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "(\<lambda>(x,y). f x y) summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) summable_on (B x)\<close>
  shows \<open>infsum (\<lambda>x. infsum (f x) (B x)) A = infsum (\<lambda>(x,y). f x y) (Sigma A B)\<close>
  using infsum_Sigma[of \<open>\<lambda>(x,y). f x y\<close> A B]
  using assms by auto

text \<open>A special case of @{thm [source] infsum_Sigma} etc. for Banach spaces. It has less premises.\<close>
lemma
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::banach\<close>
  assumes [simp]: "(\<lambda>(x,y). f x y) summable_on (Sigma A B)"
  shows infsum_Sigma'_banach: \<open>infsum (\<lambda>x. infsum (f x) (B x)) A = infsum (\<lambda>(x,y). f x y) (Sigma A B)\<close> (is ?thesis1)
    and summable_on_Sigma_banach: \<open>(\<lambda>x. infsum (f x) (B x)) summable_on A\<close> (is ?thesis2)
proof -
  have fsum: \<open>(f x) summable_on (B x)\<close> if \<open>x \<in> A\<close> for x
  proof -
    from assms
    have \<open>(\<lambda>(x,y). f x y) summable_on (Pair x ` B x)\<close>
      by (meson image_subset_iff summable_on_subset_banach mem_Sigma_iff that)
    then have \<open>((\<lambda>(x,y). f x y) \<circ> Pair x) summable_on (B x)\<close>
      by (metis summable_on_reindex inj_on_def prod.inject)
    then show ?thesis
      by (auto simp: o_def)
  qed
  show ?thesis1
    using fsum assms infsum_Sigma' isUCont_plus by blast
  show ?thesis2
    using fsum assms isUCont_plus summable_on_Sigma by blast
qed

lemma infsum_Sigma_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::banach\<close>
  assumes [simp]: "f summable_on (Sigma A B)"
  shows \<open>infsum (\<lambda>x. infsum (\<lambda>y. f (x,y)) (B x)) A = infsum f (Sigma A B)\<close>
  using assms by (simp add: infsum_Sigma'_banach)

lemma infsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,uniform_space}"
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes \<open>(\<lambda>(x, y). f x y) summable_on (A \<times> B)\<close>
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> (f a) summable_on B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> (\<lambda>a. f a b) summable_on A\<close>
  shows \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
proof -
  have "(\<lambda>(x, y). f y x) \<circ> prod.swap summable_on A \<times> B"
    by (simp add: assms(2) summable_on_cong)
  then have fyx: \<open>(\<lambda>(x, y). f y x) summable_on (B \<times> A)\<close>
    by (metis has_sum_reindex infsum_reindex inj_swap product_swap summable_iff_has_sum_infsum)
  have \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using assms infsum_Sigma' by blast
  also have \<open>\<dots> = infsum (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infsum_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
    by (smt (verit) fyx assms(1) assms(4) infsum_Sigma' infsum_cong)
  finally show ?thesis .
qed

lemma infsum_swap_banach:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::banach"
  assumes \<open>(\<lambda>(x, y). f x y) summable_on (A \<times> B)\<close>
  shows "infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B"
proof -
  have \<section>: \<open>(\<lambda>(x, y). f y x) summable_on (B \<times> A)\<close>
    by (metis (mono_tags, lifting) assms case_swap inj_swap o_apply product_swap summable_on_cong summable_on_reindex)
  have \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    using assms infsum_Sigma'_banach by blast
  also have \<open>\<dots> = infsum (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infsum_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
    by (metis (mono_tags, lifting) \<section> infsum_Sigma'_banach infsum_cong)
  finally show ?thesis .
qed

lemma nonneg_infsum_le_0D:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,ordered_ab_group_add,linorder_topology}"
  assumes "infsum f A \<le> 0"
    and abs_sum: "f summable_on A"
    and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
proof (rule ccontr)
  assume \<open>f x \<noteq> 0\<close>
  have ex: \<open>f summable_on (A-{x})\<close>
    by (rule summable_on_cofin_subset) (use assms in auto)
  have pos: \<open>infsum f (A - {x}) \<ge> 0\<close>
    by (rule infsum_nonneg) (use nneg in auto)

  have [trans]: \<open>x \<ge> y \<Longrightarrow> y > z \<Longrightarrow> x > z\<close> for x y z :: 'b by auto

  have \<open>infsum f A = infsum f (A-{x}) + infsum f {x}\<close>
    by (subst infsum_Un_disjoint[symmetric]) (use assms ex in \<open>auto simp: insert_absorb\<close>)
  also have \<open>\<dots> \<ge> infsum f {x}\<close> (is \<open>_ \<ge> \<dots>\<close>)
    using pos by (rule add_increasing) simp
  also have \<open>\<dots> = f x\<close> (is \<open>_ = \<dots>\<close>)
    by (subst infsum_finite) auto
  also have \<open>\<dots> > 0\<close>
    using \<open>f x \<noteq> 0\<close> assms(4) nneg by fastforce
  finally show False
    using assms by auto
qed

lemma nonneg_has_sum_le_0D:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,ordered_ab_group_add,linorder_topology}"
  assumes "(f has_sum a) A" \<open>a \<le> 0\<close>
    and "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
  by (metis assms infsumI nonneg_infsum_le_0D summable_on_def)

lemma has_sum_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, semiring_0}"
  assumes \<open>(f has_sum a) A\<close>
  shows "((\<lambda>x. f x * c) has_sum (a * c)) A"
  using assms tendsto_mult_right 
  by (force simp add: has_sum_def sum_distrib_right)

lemma infsum_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>c \<noteq> 0 \<Longrightarrow> f summable_on A\<close>
  shows "infsum (\<lambda>x. f x * c) A = infsum f A * c"
  using assms has_sum_cmult_left infsumI summable_iff_has_sum_infsum by fastforce

lemma summable_on_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>f summable_on A\<close>
  shows "(\<lambda>x. f x * c) summable_on A"
  using assms summable_on_def has_sum_cmult_left by blast

lemma has_sum_cmult_right:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, semiring_0}"
  assumes \<open>(f has_sum a) A\<close>
  shows "((\<lambda>x. c * f x) has_sum (c * a)) A"
  using assms tendsto_mult_left 
  by (force simp add: has_sum_def sum_distrib_left)

lemma infsum_cmult_right:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>c \<noteq> 0 \<Longrightarrow> f summable_on A\<close>
  shows \<open>infsum (\<lambda>x. c * f x) A = c * infsum f A\<close>
  using assms has_sum_cmult_right infsumI summable_iff_has_sum_infsum by fastforce

lemma summable_on_cmult_right:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>f summable_on A\<close>
  shows "(\<lambda>x. c * f x) summable_on A"
  using assms summable_on_def has_sum_cmult_right by blast

lemma summable_on_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  assumes \<open>c \<noteq> 0\<close>
  shows "(\<lambda>x. f x * c) summable_on A \<longleftrightarrow> f summable_on A"
proof
  assume \<open>f summable_on A\<close>
  then show \<open>(\<lambda>x. f x * c) summable_on A\<close>
    by (rule summable_on_cmult_left)
next
  assume \<open>(\<lambda>x. f x * c) summable_on A\<close>
  then have \<open>(\<lambda>x. f x * c * inverse c) summable_on A\<close>
    by (rule summable_on_cmult_left)
  then show \<open>f summable_on A\<close>
    by (smt (verit, del_insts) assms divide_inverse nonzero_divide_eq_eq summable_on_cong)
qed

lemma summable_on_cmult_right':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  assumes \<open>c \<noteq> 0\<close>
  shows "(\<lambda>x. c * f x) summable_on A \<longleftrightarrow> f summable_on A"
    by (metis (no_types, lifting) assms left_inverse mult.assoc mult_1 summable_on_cmult_right summable_on_cong)

lemma infsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  shows "infsum (\<lambda>x. f x * c) A = infsum f A * c"
  by (metis (full_types) infsum_cmult_left infsum_not_exists mult_eq_0_iff summable_on_cmult_left')

lemma infsum_cmult_right':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space,topological_semigroup_mult,division_ring}"
  shows "infsum (\<lambda>x. c * f x) A = c * infsum f A"
  by (metis (full_types) infsum_cmult_right infsum_not_exists mult_eq_0_iff summable_on_cmult_right')

lemma has_sum_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>((\<lambda>_. c) has_sum of_nat (card F) * c) F\<close>
  by (metis assms has_sum_finite sum_constant)

lemma infsum_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infsum (\<lambda>_. c) F = of_nat (card F) * c\<close>
  by (simp add: assms)

lemma infsum_diverge_constant:
  \<comment> \<open>This probably does not really need all of \<^class>\<open>archimedean_field\<close> but Isabelle/HOL
       has no type class such as, e.g., "archimedean ring".\<close>
  fixes c :: \<open>'a::{archimedean_field, comm_monoid_add, linorder_topology, topological_semigroup_mult}\<close>
  assumes \<open>infinite A\<close> and \<open>c \<noteq> 0\<close>
  shows \<open>\<not> (\<lambda>_. c) summable_on A\<close>
proof (rule notI)
  assume \<open>(\<lambda>_. c) summable_on A\<close>
  then have \<open>(\<lambda>_. inverse c * c) summable_on A\<close>
    by (rule summable_on_cmult_right)
  then have [simp]: \<open>(\<lambda>_. 1::'a) summable_on A\<close>
    using assms by auto
  have \<open>infsum (\<lambda>_. 1) A \<ge> d\<close> for d :: 'a
  proof -
    obtain n :: nat where \<open>of_nat n \<ge> d\<close>
      by (meson real_arch_simple)
    from assms
    obtain F where \<open>F \<subseteq> A\<close> and \<open>finite F\<close> and \<open>card F = n\<close>
      by (meson infinite_arbitrarily_large)
    note \<open>d \<le> of_nat n\<close>
    also have \<open>of_nat n = infsum (\<lambda>_. 1::'a) F\<close>
      by (simp add: \<open>card F = n\<close> \<open>finite F\<close>)
    also have \<open>\<dots> \<le> infsum (\<lambda>_. 1::'a) A\<close>
      apply (rule infsum_mono_neutral)
      using \<open>finite F\<close> \<open>F \<subseteq> A\<close> by auto
    finally show ?thesis .
  qed                                                        
  then show False
    by (meson linordered_field_no_ub not_less)
qed

lemma has_sum_constant_archimedean[simp]:
  \<comment> \<open>This probably does not really need all of \<^class>\<open>archimedean_field\<close> but Isabelle/HOL
       has no type class such as, e.g., "archimedean ring".\<close>
  fixes c :: \<open>'a::{archimedean_field, comm_monoid_add, linorder_topology, topological_semigroup_mult}\<close>
  shows \<open>infsum (\<lambda>_. c) A = of_nat (card A) * c\<close>
  by (metis infsum_0 infsum_constant infsum_diverge_constant infsum_not_exists sum.infinite sum_constant)

lemma has_sum_uminus:
  fixes f :: \<open>'a \<Rightarrow> 'b::topological_ab_group_add\<close>
  shows \<open>((\<lambda>x. - f x) has_sum a) A \<longleftrightarrow> (f has_sum (- a)) A\<close>
  by (auto simp add: sum_negf[abs_def] tendsto_minus_cancel_left has_sum_def)

lemma summable_on_uminus:
  fixes f :: \<open>'a \<Rightarrow> 'b::topological_ab_group_add\<close>
  shows\<open>(\<lambda>x. - f x) summable_on A \<longleftrightarrow> f summable_on A\<close>
  by (metis summable_on_def has_sum_uminus verit_minus_simplify(4))

lemma infsum_uminus:
  fixes f :: \<open>'a \<Rightarrow> 'b::{topological_ab_group_add, t2_space}\<close>
  shows \<open>infsum (\<lambda>x. - f x) A = - infsum f A\<close>
  by (metis (full_types) add.inverse_inverse add.inverse_neutral infsumI infsum_def has_sum_infsum has_sum_uminus)

lemma has_sum_le_finite_sums:
  fixes a :: \<open>'a::{comm_monoid_add,topological_space,linorder_topology}\<close>
  assumes \<open>(f has_sum a) A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>a \<le> b\<close>
  by (metis assms eventually_finite_subsets_at_top_weakI finite_subsets_at_top_neq_bot has_sum_def tendsto_upperbound)

lemma infsum_le_finite_sums:
  fixes b :: \<open>'a::{comm_monoid_add,topological_space,linorder_topology}\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>infsum f A \<le> b\<close>
  by (meson assms has_sum_infsum has_sum_le_finite_sums)


lemma summable_on_scaleR_left [intro]:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) summable_on A"
proof (cases \<open>c = 0\<close>)
  case False
  then have "(\<lambda>y. y *\<^sub>R c) \<circ> f summable_on A"
    using assms by (auto simp add: scaleR_left.additive_axioms summable_on_comm_additive)
  then show ?thesis
    by (metis (mono_tags, lifting) comp_apply summable_on_cong)
qed auto


lemma summable_on_scaleR_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) summable_on A"
proof (cases \<open>c = 0\<close>)
  case False
  then have "(*\<^sub>R) c \<circ> f summable_on A"
  using assms by (auto simp add: scaleR_right.additive_axioms summable_on_comm_additive)
  then show ?thesis
    by (metis (mono_tags, lifting) comp_apply summable_on_cong)
qed auto

lemma infsum_scaleR_left:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "infsum (\<lambda>x. f x *\<^sub>R c) A = infsum f A *\<^sub>R c"
proof (cases \<open>c = 0\<close>)
  case False
  then have "infsum ((\<lambda>y. y *\<^sub>R c) \<circ> f) A = infsum f A *\<^sub>R c"
  using assms by (auto simp add: scaleR_left.additive_axioms infsum_comm_additive)
  then show ?thesis
    by (metis (mono_tags, lifting) comp_apply infsum_cong)
qed auto

lemma infsum_scaleR_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  shows   "infsum (\<lambda>x. c *\<^sub>R f x) A = c *\<^sub>R infsum f A"
proof -
  consider (summable) \<open>f summable_on A\<close> | (c0) \<open>c = 0\<close> | (not_summable) \<open>\<not> f summable_on A\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then have "infsum ((*\<^sub>R) c \<circ> f) A = c *\<^sub>R infsum f A"
      by (auto simp add: scaleR_right.additive_axioms infsum_comm_additive)
    then show ?thesis
      by (metis (mono_tags, lifting) comp_apply infsum_cong)
  next
    case c0
    then show ?thesis by auto
  next
    case not_summable
    have \<open>\<not> (\<lambda>x. c *\<^sub>R f x) summable_on A\<close>
    proof (rule notI)
      assume \<open>(\<lambda>x. c *\<^sub>R f x) summable_on A\<close>
      then have \<open>(\<lambda>x. inverse c *\<^sub>R c *\<^sub>R f x) summable_on A\<close>
        using summable_on_scaleR_right by blast
      with not_summable show False
        by simp
    qed
    then show ?thesis
      by (simp add: infsum_not_exists not_summable(1)) 
  qed
qed


lemma infsum_Un_Int:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, t2_space}"
  assumes "f summable_on A - B" "f summable_on B - A" \<open>f summable_on A \<inter> B\<close>
  shows   "infsum f (A \<union> B) = infsum f A + infsum f B - infsum f (A \<inter> B)"
proof -
  obtain \<open>f summable_on A\<close> \<open>f summable_on B\<close>
    using assms by (metis Int_Diff_Un Int_Diff_disjoint inf_commute summable_on_Un_disjoint)
  then have \<open>infsum f (A \<union> B) = infsum f A + infsum f (B - A)\<close>
    using assms(2) infsum_Un_disjoint by fastforce
  moreover have \<open>infsum f (B - A) = infsum f B - infsum f (A \<inter> B)\<close>
    using assms by (metis Diff_Int2 Un_Int_eq(2) \<open>f summable_on B\<close> inf_le2 infsum_Diff)
  ultimately show ?thesis
    by auto
qed

lemma inj_combinator':
  assumes "x \<notin> F"
  shows \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B \<times> B x)\<close>
proof -
  have "inj_on ((\<lambda>(y, g). g(x := y)) \<circ> prod.swap) (Pi\<^sub>E F B \<times> B x)"
    using inj_combinator[of x F B] assms by (intro comp_inj_on) (auto simp: product_swap)
  thus ?thesis
    by (simp add: o_def)
qed

lemma infsum_prod_PiE:
  \<comment> \<open>See also \<open>infsum_prod_PiE_abs\<close> below with incomparable premises.\<close>
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {comm_monoid_mult, topological_semigroup_mult, division_ring, banach}"
  assumes finite: "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x summable_on B x"
  assumes "(\<lambda>g. \<Prod>x\<in>A. f x (g x)) summable_on (PiE A B)"
  shows   "infsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsum (f x) (B x))"
proof (use finite assms(2-) in induction)
  case empty
  then show ?case 
    by auto
next
  case (insert x F)
  have pi: \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close>
    unfolding PiE_insert_eq 
    by (subst swap_product [symmetric]) (simp add: image_image case_prod_unfold)
  have prod: \<open>(\<Prod>x'\<in>F. f x' ((p(x:=y)) x')) = (\<Prod>x'\<in>F. f x' (p x'))\<close> for p y
    by (rule prod.cong) (use insert.hyps in auto)
  have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B \<times> B x)\<close>
    using \<open>x \<notin> F\<close> by (rule inj_combinator')

  have summable1: \<open>(\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) summable_on Pi\<^sub>E (insert x F) B\<close>
    using insert.prems(2) .
  also have \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close>
    by (simp only: pi)
  also have "(\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) summable_on \<dots> \<longleftrightarrow>
               ((\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) \<circ> (\<lambda>(g,y). g(x:=y))) summable_on (Pi\<^sub>E F B \<times> B x)"
    using inj by (rule summable_on_reindex)
  also have "(\<Prod>z\<in>F. f z ((g(x := y)) z)) = (\<Prod>z\<in>F. f z (g z))" for g y
    using insert.hyps by (intro prod.cong) auto
  hence "((\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) \<circ> (\<lambda>(g,y). g(x:=y))) =
             (\<lambda>(p, y). f x y * (\<Prod>x'\<in>F. f x' (p x')))"
    using insert.hyps by (auto simp: fun_eq_iff cong: prod.cong_simp)
  finally have summable2: \<open>(\<lambda>(p, y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B \<times> B x\<close> .

  then have \<open>(\<lambda>p. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close>
    by (rule summable_on_Sigma_banach)
  then have \<open>(\<lambda>p. (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close>
    by (metis (mono_tags, lifting) infsum_cmult_left' infsum_cong summable_on_cong)
  then have summable3: \<open>(\<lambda>p. (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close> if \<open>(\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) \<noteq> 0\<close>
    using summable_on_cmult_right' that by blast

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x F) B. \<Prod>x\<in>insert x F. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E F B \<times> B x. \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x'))\<close>
    by (smt (verit, ccfv_SIG) comp_apply infsum_cong infsum_reindex inj pi prod.cong split_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x')))\<close>
    using insert.hyps by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    using prod by presburger
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    using infsum_Sigma'_banach summable2 by force
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>
    by (smt (verit) infsum_cmult_left' infsum_cmult_right' infsum_cong)
  also have \<open>\<dots> = (\<Prod>x\<in>insert x F. infsum (f x) (B x))\<close>
    using insert summable3 by auto
  finally show ?case
    by simp
qed

lemma infsum_prod_PiE_abs:
  \<comment> \<open>See also @{thm [source] infsum_prod_PiE} above with incomparable premises.\<close>
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, real_normed_div_algebra, comm_semiring_1}"
  assumes finite: "finite A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows   "infsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsum (f x) (B x))"
proof (use finite assms(2) in induction)
  case empty
  then show ?case 
    by auto
next
  case (insert x A)
  
  have pi: \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close> for x F and B :: "'a \<Rightarrow> 'b set"
    unfolding PiE_insert_eq 
    by (subst swap_product [symmetric]) (simp add: image_image case_prod_unfold)
  have prod: \<open>(\<Prod>x'\<in>A. f x' ((p(x:=y)) x')) = (\<Prod>x'\<in>A. f x' (p x'))\<close> for p y
    by (rule prod.cong) (use insert.hyps in auto)
  have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E A B \<times> B x)\<close>
    using \<open>x \<notin> A\<close> by (rule inj_combinator')

  define s where \<open>s x = infsum (\<lambda>y. norm (f x y)) (B x)\<close> for x

  have \<open>(\<Sum>p\<in>P. norm (\<Prod>x\<in>F. f x (p x))) \<le> prod s F\<close> 
    if P: \<open>P \<subseteq> Pi\<^sub>E F B\<close> and [simp]: \<open>finite P\<close> \<open>finite F\<close> 
      and sum: \<open>\<And>x. x \<in> F \<Longrightarrow> f x abs_summable_on B x\<close> for P F
  proof -
    define B' where \<open>B' x = {p x| p. p\<in>P}\<close> for x
    have fin_B'[simp]: \<open>finite (B' x)\<close> for x
      using that by (auto simp: B'_def)
    have [simp]: \<open>finite (Pi\<^sub>E F B')\<close>
      by (simp add: finite_PiE)
    have [simp]: \<open>P \<subseteq> Pi\<^sub>E F B'\<close>
      using that by (auto simp: B'_def)
    have B'B: \<open>B' x \<subseteq> B x\<close> if \<open>x \<in> F\<close> for x
      unfolding B'_def using P that 
      by auto
    have s_bound: \<open>(\<Sum>y\<in>B' x. norm (f x y)) \<le> s x\<close> if \<open>x \<in> F\<close> for x
      by (metis B'B fin_B' finite_sum_le_has_sum has_sum_infsum norm_ge_zero s_def sum that)
    have \<open>(\<Sum>p\<in>P. norm (\<Prod>x\<in>F. f x (p x))) \<le> (\<Sum>p\<in>Pi\<^sub>E F B'. norm (\<Prod>x\<in>F. f x (p x)))\<close>
      by (simp add: sum_mono2)
    also have \<open>\<dots> = (\<Sum>p\<in>Pi\<^sub>E F B'. \<Prod>x\<in>F. norm (f x (p x)))\<close>
      by (simp add: prod_norm)
    also have \<open>\<dots> = (\<Prod>x\<in>F. \<Sum>y\<in>B' x. norm (f x y))\<close>
    proof (use \<open>finite F\<close> in induction)
      case empty
      then show ?case by simp
    next
      case (insert x F)
      have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B' \<times> B' x)\<close>
        by (simp add: inj_combinator' insert.hyps)
      then have \<open>(\<Sum>p\<in>Pi\<^sub>E (insert x F) B'. \<Prod>x\<in>insert x F. norm (f x (p x)))
         =  (\<Sum>(p,y)\<in>Pi\<^sub>E F B' \<times> B' x. \<Prod>x'\<in>insert x F. norm (f x' ((p(x := y)) x')))\<close>
        by (simp add: pi sum.reindex case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>(p, y)\<in>Pi\<^sub>E F B' \<times> B' x. norm (f x y) * (\<Prod>x'\<in>F. norm (f x' (p x'))))\<close>
        by (smt (verit, del_insts) fun_upd_apply insert.hyps prod.cong prod.insert split_def sum.cong)
      also have \<open>\<dots> = (\<Sum>y\<in>B' x. norm (f x y)) * (\<Sum>p\<in>Pi\<^sub>E F B'. \<Prod>x'\<in>F. norm (f x' (p x')))\<close>
        by (simp add: sum_product sum.swap [of _ "Pi\<^sub>E F B'"] sum.cartesian_product)
      also have \<open>\<dots> = (\<Prod>x\<in>insert x F. \<Sum>y\<in>B' x. norm (f x y))\<close>
        using insert by force
      finally show ?case .
    qed
    also have \<open>\<dots> \<le> (\<Prod>x\<in>F. s x)\<close>
      using s_bound by (simp add: prod_mono sum_nonneg)
    finally show ?thesis .
  qed
  then have "bdd_above
     (sum (\<lambda>g. norm (\<Prod>x\<in>insert x A. f x (g x))) ` {F. F \<subseteq> Pi\<^sub>E (insert x A) B \<and> finite F})"
    using insert.hyps insert.prems by (intro bdd_aboveI) blast
  then have \<open>(\<lambda>g. \<Prod>x\<in>insert x A. f x (g x)) abs_summable_on Pi\<^sub>E (insert x A) B\<close>
    using nonneg_bdd_above_summable_on
    by (metis (mono_tags, lifting) Collect_cong norm_ge_zero)
  also have \<open>Pi\<^sub>E (insert x A) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E A B \<times> B x)\<close>
    by (simp only: pi)
  also have "(\<lambda>g. \<Prod>x\<in>insert x A. f x (g x)) abs_summable_on \<dots> \<longleftrightarrow>
               ((\<lambda>g. \<Prod>x\<in>insert x A. f x (g x)) \<circ> (\<lambda>(g,y). g(x:=y))) abs_summable_on (Pi\<^sub>E A B \<times> B x)"
    using inj by (subst summable_on_reindex) (auto simp: o_def)
  also have "(\<Prod>z\<in>A. f z ((g(x := y)) z)) = (\<Prod>z\<in>A. f z (g z))" for g y
    using insert.hyps by (intro prod.cong) auto
  hence "((\<lambda>g. \<Prod>x\<in>insert x A. f x (g x)) \<circ> (\<lambda>(g,y). g(x:=y))) =
             (\<lambda>(p, y). f x y * (\<Prod>x'\<in>A. f x' (p x')))"
    using insert.hyps by (auto simp: fun_eq_iff cong: prod.cong_simp)
  finally have summable2: \<open>(\<lambda>(p, y). f x y * (\<Prod>x'\<in>A. f x' (p x'))) abs_summable_on Pi\<^sub>E A B \<times> B x\<close> .

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x A) B. \<Prod>x\<in>insert x A. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E A B \<times> B x. \<Prod>x'\<in>insert x A. f x' ((p(x:=y)) x'))\<close>
    using inj by (simp add: pi infsum_reindex o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p,y) \<in> Pi\<^sub>E A B \<times> B x. f x y * (\<Prod>x'\<in>A. f x' (p x')))\<close>
    using prod insert.hyps by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E A B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>A. f x' (p x')))\<close>
    using abs_summable_summable infsum_Sigma'_banach summable2 by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E A B. \<Prod>x'\<in>A. f x' (p x'))\<close>
    by (smt (verit, best) infsum_cmult_left' infsum_cmult_right' infsum_cong)
  finally show ?case
    by (simp add: insert)
qed



subsection \<open>Absolute convergence\<close>

lemma abs_summable_countable:
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
proof -
  have fin: \<open>finite {x\<in>A. norm (f x) \<ge> t}\<close> if \<open>t > 0\<close> for t
  proof (rule ccontr)
    assume *: \<open>infinite {x \<in> A. t \<le> norm (f x)}\<close>
    have \<open>infsum (\<lambda>x. norm (f x)) A \<ge> b\<close> for b
    proof -
      obtain b' where b': \<open>of_nat b' \<ge> b / t\<close>
        by (meson real_arch_simple)
      from *
      obtain F where cardF: \<open>card F \<ge> b'\<close> and \<open>finite F\<close> and F: \<open>F \<subseteq> {x \<in> A. t \<le> norm (f x)}\<close>
        by (meson finite_if_finite_subsets_card_bdd nle_le)
      have \<open>b \<le> of_nat b' * t\<close>
        using b' \<open>t > 0\<close> by (simp add: field_simps split: if_splits)
      also have \<open>\<dots> \<le> of_nat (card F) * t\<close>
        by (simp add: cardF that)
      also have \<open>\<dots> = sum (\<lambda>x. t) F\<close>
        by simp
      also have \<open>\<dots> \<le> sum (\<lambda>x. norm (f x)) F\<close>
        by (metis (mono_tags, lifting) F in_mono mem_Collect_eq sum_mono)
      also have \<open>\<dots> = infsum (\<lambda>x. norm (f x)) F\<close>
        using \<open>finite F\<close> by (rule infsum_finite[symmetric])
      also have \<open>\<dots> \<le> infsum (\<lambda>x. norm (f x)) A\<close>
        by (rule infsum_mono_neutral) (use \<open>finite F\<close> assms F in auto)
      finally show ?thesis .
    qed
    then show False
      by (meson gt_ex linorder_not_less)
  qed
  have \<open>countable (\<Union>i\<in>{1..}. {x\<in>A. norm (f x) \<ge> 1/of_nat i})\<close>
    by (rule countable_UN) (use fin in \<open>auto intro!: countable_finite\<close>)
  also have \<open>\<dots> = {x\<in>A. f x \<noteq> 0}\<close>
  proof safe
    fix x assume x: "x \<in> A" "f x \<noteq> 0"
    define i where "i = max 1 (nat (ceiling (1 / norm (f x))))"
    have "i \<ge> 1"
      by (simp add: i_def)
    moreover have "real i \<ge> 1 / norm (f x)"
      unfolding i_def by linarith
    hence "1 / real i \<le> norm (f x)" using \<open>f x \<noteq> 0\<close>
      by (auto simp: divide_simps mult_ac)
    ultimately show "x \<in> (\<Union>i\<in>{1..}. {x \<in> A. 1 / real i \<le> norm (f x)})"
      using \<open>x \<in> A\<close> by auto
  qed auto
  finally show ?thesis .
qed

(* Logically belongs in the section about reals, but needed as a dependency here *)
lemma summable_on_iff_abs_summable_on_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  shows \<open>f summable_on A \<longleftrightarrow> f abs_summable_on A\<close>
proof (rule iffI)
  assume \<open>f summable_on A\<close>
  define n A\<^sub>p A\<^sub>n
    where \<open>n \<equiv> \<lambda>x. norm (f x)\<close> and \<open>A\<^sub>p = {x\<in>A. f x \<ge> 0}\<close> and \<open>A\<^sub>n = {x\<in>A. f x < 0}\<close> for x
  have A: \<open>A\<^sub>p \<union> A\<^sub>n = A\<close> \<open>A\<^sub>p \<inter> A\<^sub>n = {}\<close>
    by (auto simp: A\<^sub>p_def A\<^sub>n_def)
  from \<open>f summable_on A\<close> have \<open>f summable_on A\<^sub>p\<close> \<open>f summable_on A\<^sub>n\<close>
    using A\<^sub>p_def A\<^sub>n_def summable_on_subset_banach by fastforce+
  then have \<open>n summable_on A\<^sub>p\<close>
    by (smt (verit) A\<^sub>p_def n_def mem_Collect_eq real_norm_def summable_on_cong)
  moreover have \<open>n summable_on A\<^sub>n\<close>
    by (smt (verit, best) \<open>f summable_on A\<^sub>n\<close>  summable_on_uminus A\<^sub>n_def n_def summable_on_cong mem_Collect_eq real_norm_def)
  ultimately show \<open>n summable_on A\<close>
    using A summable_on_Un_disjoint by blast
next
  show \<open>f abs_summable_on A \<Longrightarrow> f summable_on A\<close>
    using abs_summable_summable by blast
qed

lemma abs_summable_on_Sigma_iff:
  shows   "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof (intro iffI conjI ballI)
  assume asm: \<open>f abs_summable_on Sigma A B\<close>
  then have \<open>(\<lambda>x. infsum (\<lambda>y. norm (f (x,y))) (B x)) summable_on A\<close>
    by (simp add: cond_case_prod_eta summable_on_Sigma_banach)
  then show \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_summable_on A\<close>
    using summable_on_iff_abs_summable_on_real by force

  show \<open>(\<lambda>y. f (x, y)) abs_summable_on B x\<close> if \<open>x \<in> A\<close> for x
  proof -
    from asm have \<open>f abs_summable_on Pair x ` B x\<close>
      by (simp add: image_subset_iff summable_on_subset_banach that)
    then show ?thesis
      by (metis (mono_tags, lifting) o_def inj_on_def summable_on_reindex prod.inject summable_on_cong)
  qed
next
  assume asm: \<open>(\<forall>x\<in>A. (\<lambda>xa. f (x, xa)) abs_summable_on B x) \<and>
    (\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_summable_on A\<close>
  have \<open>(\<Sum>xy\<in>F. norm (f xy)) \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y)))\<close>
    if \<open>F \<subseteq> Sigma A B\<close> and [simp]: \<open>finite F\<close> for F
  proof -
    have [simp]: \<open>(SIGMA x:fst ` F. {y. (x, y) \<in> F}) = F\<close>
      by (auto intro!: set_eqI simp add: Domain.DomainI fst_eq_Domain)
    have [simp]: \<open>finite {y. (x, y) \<in> F}\<close> for x
      by (metis \<open>finite F\<close> Range.intros finite_Range finite_subset mem_Collect_eq subsetI)
    have \<open>(\<Sum>xy\<in>F. norm (f xy)) = (\<Sum>x\<in>fst ` F. \<Sum>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      by (simp add: sum.Sigma)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      by auto
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      using asm that(1) by (intro infsum_mono infsum_mono_neutral) auto
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      by (rule infsum_mono_neutral) (use asm that(1) in \<open>auto simp add: infsum_nonneg\<close>)
    finally show ?thesis .
  qed
  then show \<open>f abs_summable_on Sigma A B\<close>
    by (intro nonneg_bdd_above_summable_on) (auto simp: bdd_above_def)
qed

lemma abs_summable_on_comparison_test:
  assumes "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> norm (g x)"
  shows   "f abs_summable_on A"
proof (rule nonneg_bdd_above_summable_on)
  show "bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F \<subseteq> A \<and> finite F})"
  proof (rule bdd_aboveI2)
    fix F assume F: "F \<in> {F. F \<subseteq> A \<and> finite F}"
    have \<open>sum (\<lambda>x. norm (f x)) F \<le> sum (\<lambda>x. norm (g x)) F\<close>
      using assms F by (intro sum_mono) auto
    also have \<open>\<dots> = infsum (\<lambda>x. norm (g x)) F\<close>
      using F by simp
    also have \<open>\<dots> \<le> infsum (\<lambda>x. norm (g x)) A\<close>
      by (smt (verit) F assms(1) infsum_mono2 mem_Collect_eq norm_ge_zero summable_on_subset_banach)
    finally show "(\<Sum>x\<in>F. norm (f x)) \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (g x))" .
  qed
qed auto

lemma abs_summable_iff_bdd_above:
  fixes f :: \<open>'a \<Rightarrow> 'b::real_normed_vector\<close>
  shows \<open>f abs_summable_on A \<longleftrightarrow> bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F\<subseteq>A \<and> finite F})\<close>
proof (rule iffI)
  assume \<open>f abs_summable_on A\<close>
  show \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F \<subseteq> A \<and> finite F})\<close>
  proof (rule bdd_aboveI2)
    fix F assume F: "F \<in> {F. F \<subseteq> A \<and> finite F}"
    show "(\<Sum>x\<in>F. norm (f x)) \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))"
      by (rule finite_sum_le_infsum) (use \<open>f abs_summable_on A\<close> F in auto)
  qed
next
  assume \<open>bdd_above (sum (\<lambda>x. norm (f x)) ` {F. F\<subseteq>A \<and> finite F})\<close>
  then show \<open>f abs_summable_on A\<close>
    by (simp add: nonneg_bdd_above_summable_on)
qed

lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule nonneg_bdd_above_summable_on)
  show "bdd_above (sum (\<lambda>xa. norm (x xa * y xa)) ` {F. F \<subseteq> A \<and> finite F})"
  proof (rule bdd_aboveI2)
    fix F assume F: \<open>F \<in> {F. F \<subseteq> A \<and> finite F}\<close>
    then have r1: "finite F" and b4: "F \<subseteq> A"
      by auto
  
    have a1: "(\<Sum>\<^sub>\<infinity>i\<in>F. norm (x i * x i)) \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * x i))"
      by (metis (no_types, lifting) b4 infsum_mono2 norm_ge_zero summable_on_subset_banach x2_sum)

    have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
      unfolding norm_mult by (smt (verit, best) abs_norm_cancel mult_mono not_sum_squares_lt_zero)
    hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm (x i * x i) + norm (y i * y i))"
      by (simp add: sum_mono)
    also have "\<dots> = (\<Sum>i\<in>F. norm (x i * x i)) + (\<Sum>i\<in>F. norm (y i * y i))"
      by (simp add: sum.distrib)
    also have "\<dots> = (\<Sum>\<^sub>\<infinity>i\<in>F. norm (x i * x i)) + (\<Sum>\<^sub>\<infinity>i\<in>F. norm (y i * y i))"
      by (simp add: \<open>finite F\<close>)
    also have "\<dots> \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>\<infinity>i\<in>A. norm (y i * y i))"
      using F assms
      by (intro add_mono infsum_mono2) auto
    finally show \<open>(\<Sum>xa\<in>F. norm (x xa * y xa)) \<le> (\<Sum>\<^sub>\<infinity>i\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>\<infinity>i\<in>A. norm (y i * y i))\<close>
      by simp
  qed
qed auto

subsection \<open>Extended reals and nats\<close>

lemma summable_on_ennreal[simp]: \<open>(f::_ \<Rightarrow> ennreal) summable_on S\<close> and summable_on_enat[simp]: \<open>(f::_ \<Rightarrow> enat) summable_on S\<close>
  by (simp_all add: nonneg_summable_on_complete)

lemma has_sum_superconst_infinite_ennreal:
  fixes f :: \<open>'a \<Rightarrow> ennreal\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "(f has_sum \<infinity>) S"
proof -
  have \<open>(sum f \<longlongrightarrow> \<infinity>) (finite_subsets_at_top S)\<close>
  proof (rule order_tendstoI)
    fix y :: ennreal assume \<open>y < \<infinity>\<close>
    then have \<open>y / b < \<infinity>\<close> \<open>y < top\<close>
      using b ennreal_divide_eq_top_iff top.not_eq_extremum by force+
    then obtain F where \<open>finite F\<close> and \<open>F \<subseteq> S\<close> and cardF: \<open>card F > y / b\<close>
      using \<open>infinite S\<close>
      by (metis ennreal_Ex_less_of_nat infinite_arbitrarily_large infinity_ennreal_def)
    moreover have \<open>sum f Y > y\<close> if \<open>finite Y\<close> and \<open>F \<subseteq> Y\<close> and \<open>Y \<subseteq> S\<close> for Y
    proof -
      have \<open>y < b * card F\<close>
        by (metis b \<open>y < top\<close> cardF divide_less_ennreal ennreal_mult_eq_top_iff gr_implies_not_zero mult.commute top.not_eq_extremum)
      also have \<open>\<dots> \<le> b * card Y\<close>
        by (meson b card_mono less_imp_le mult_left_mono of_nat_le_iff that)
      also have \<open>\<dots> = sum (\<lambda>_. b) Y\<close>
        by (simp add: mult.commute)
      also have \<open>\<dots> \<le> sum f Y\<close>
        using geqb by (meson subset_eq sum_mono that(3))
      finally show ?thesis .
    qed
    ultimately show \<open>\<forall>\<^sub>F x in finite_subsets_at_top S. y < sum f x\<close>
      unfolding eventually_finite_subsets_at_top by auto
  qed auto
  then show ?thesis
    by (simp add: has_sum_def)
qed

lemma infsum_superconst_infinite_ennreal:
  fixes f :: \<open>'a \<Rightarrow> ennreal\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infsum f S = \<infinity>"
  using assms infsumI has_sum_superconst_infinite_ennreal by blast

lemma infsum_superconst_infinite_ereal:
  fixes f :: \<open>'a \<Rightarrow> ereal\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infsum f S = \<infinity>"
proof -
  obtain b' where b': \<open>e2ennreal b' = b\<close> and \<open>b' > 0\<close>
    using b by blast
  have "0 < e2ennreal b"
    using b' b
    by (metis dual_order.refl enn2ereal_e2ennreal gr_zeroI order_less_le zero_ennreal.abs_eq)
  hence *: \<open>infsum (e2ennreal \<circ> f) S = \<infinity>\<close>
    using assms b'
    by (intro infsum_superconst_infinite_ennreal[where b=b']) (auto intro!: e2ennreal_mono)
  have \<open>infsum f S = infsum (enn2ereal \<circ> (e2ennreal \<circ> f)) S\<close>
    using geqb b by (intro infsum_cong) (fastforce simp: enn2ereal_e2ennreal)
  also have \<open>\<dots> = enn2ereal \<infinity>\<close>
    using * by (simp add: infsum_comm_additive_general continuous_at_enn2ereal nonneg_summable_on_complete)
  also have \<open>\<dots> = \<infinity>\<close>
    by simp
  finally show ?thesis .
qed

lemma has_sum_superconst_infinite_ereal:
  fixes f :: \<open>'a \<Rightarrow> ereal\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "(f has_sum \<infinity>) S"
  by (metis Infty_neq_0(1) assms infsum_def has_sum_infsum infsum_superconst_infinite_ereal)

lemma infsum_superconst_infinite_enat:
  fixes f :: \<open>'a \<Rightarrow> enat\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infsum f S = \<infinity>"
proof -
  have \<open>ennreal_of_enat (infsum f S) = infsum (ennreal_of_enat \<circ> f) S\<close>
    by (simp flip: infsum_comm_additive_general)
  also have \<open>\<dots> = \<infinity>\<close>
    by (metis assms(3) b comp_def ennreal_of_enat_0 ennreal_of_enat_le_iff geqb infsum_superconst_infinite_ennreal leD leI)
  also have \<open>\<dots> = ennreal_of_enat \<infinity>\<close>
    by simp
  finally show ?thesis
    by (rule ennreal_of_enat_inj[THEN iffD1])
qed

lemma has_sum_superconst_infinite_enat:
  fixes f :: \<open>'a \<Rightarrow> enat\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "(f has_sum \<infinity>) S"
  by (metis assms i0_lb has_sum_infsum infsum_superconst_infinite_enat nonneg_summable_on_complete)

text \<open>This lemma helps to relate a real-valued infsum to a supremum over extended nonnegative reals.\<close>

lemma infsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof -
  have \<section>: "\<And>F. \<lbrakk>finite F; F \<subseteq> A\<rbrakk> \<Longrightarrow> sum (ennreal \<circ> f) F = ennreal (sum f F)"
    by (metis (mono_tags, lifting) comp_def fnn subsetD sum.cong sum_ennreal)
  then have \<open>ennreal (infsum f A) = infsum (ennreal \<circ> f) A\<close>
    by (simp add: infsum_comm_additive_general local.summable)
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))\<close>
    by (metis (mono_tags, lifting) \<section> image_cong mem_Collect_eq nonneg_infsum_complete zero_le)
  finally show ?thesis .
qed

text \<open>This lemma helps to related a real-valued infsum to a supremum over extended reals.\<close>

lemma infsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have "\<And>F. \<lbrakk>finite F; F \<subseteq> A\<rbrakk> \<Longrightarrow> sum (ereal \<circ> f) F = ereal (sum f F)"
    by auto
  then have \<open>ereal (infsum f A) = infsum (ereal \<circ> f) A\<close>
    by (simp add: infsum_comm_additive_general local.summable)
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))\<close>
    by (subst nonneg_infsum_complete) (simp_all add: assms)
  finally show ?thesis .
qed


subsection \<open>Real numbers\<close>

text \<open>Most lemmas in the general property section already apply to real numbers.
      A few ones that are specific to reals are given here.\<close>

lemma infsum_nonneg_is_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsum f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
proof -
  have *: "ereal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
    using assms by (rule infsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
    by (metis (no_types, lifting) * MInfty_neq_ereal(2) PInfty_neq_ereal(2) SUP_cong abs_eq_infinity_cases ereal_SUP)
  finally show ?thesis by simp
qed


lemma has_sum_nonneg_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f summable_on A" and "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "(f has_sum (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))) A"
  by (metis (mono_tags, lifting) assms has_sum_infsum infsum_nonneg_is_SUPREMUM_real)

lemma summable_countable_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  assumes \<open>f summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_summable_countable assms summable_on_iff_abs_summable_on_real by blast

subsection \<open>Complex numbers\<close>

lemma has_sum_cnj_iff[simp]: 
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>((\<lambda>x. cnj (f x)) has_sum cnj a) M \<longleftrightarrow> (f has_sum a) M\<close>
  by (simp add: has_sum_def lim_cnj del: cnj_sum add: cnj_sum[symmetric, abs_def, of f])

lemma summable_on_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) summable_on A \<longleftrightarrow> f summable_on A"
  by (metis complex_cnj_cnj summable_on_def has_sum_cnj_iff)

lemma infsum_cnj[simp]: \<open>infsum (\<lambda>x. cnj (f x)) M = cnj (infsum f M)\<close>
  by (metis complex_cnj_zero infsumI has_sum_cnj_iff infsum_def summable_on_cnj_iff has_sum_infsum)

lemma has_sum_Re:
  assumes "(f has_sum a) M"
  shows "((\<lambda>x. Re (f x)) has_sum Re a) M"
  using has_sum_comm_additive[where f=Re]
  using  assms tendsto_Re by (fastforce simp add: o_def additive_def)

lemma infsum_Re:
  assumes "f summable_on M"
  shows "infsum (\<lambda>x. Re (f x)) M = Re (infsum f M)"
  by (simp add: assms has_sum_Re infsumI)

lemma summable_on_Re: 
  assumes "f summable_on M"
  shows "(\<lambda>x. Re (f x)) summable_on M"
  by (metis assms has_sum_Re summable_on_def)

lemma has_sum_Im:
  assumes "(f has_sum a) M"
  shows "((\<lambda>x. Im (f x)) has_sum Im a) M"
  using has_sum_comm_additive[where f=Im]
  using  assms tendsto_Im by (fastforce simp add: o_def additive_def)

lemma infsum_Im: 
  assumes "f summable_on M"
  shows "infsum (\<lambda>x. Im (f x)) M = Im (infsum f M)"
  by (simp add: assms has_sum_Im infsumI)

lemma summable_on_Im: 
  assumes "f summable_on M"
  shows "(\<lambda>x. Im (f x)) summable_on M"
  by (metis assms has_sum_Im summable_on_def)

lemma nonneg_infsum_le_0D_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "infsum f A \<le> 0"
    and abs_sum: "f summable_on A"
    and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
proof -
  have \<open>Im (f x) = 0\<close>
    using assms(4) less_eq_complex_def nneg by auto
  moreover have \<open>Re (f x) = 0\<close>
    using assms by (auto simp add: summable_on_Re infsum_Re less_eq_complex_def intro: nonneg_infsum_le_0D[where A=A])
  ultimately show ?thesis
    by (simp add: complex_eqI)
qed

lemma nonneg_has_sum_le_0D_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "(f has_sum a) A" and \<open>a \<le> 0\<close>
    and "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0" and "x \<in> A"
  shows "f x = 0"
  by (metis assms infsumI nonneg_infsum_le_0D_complex summable_on_def)

text \<open>The lemma @{thm [source] infsum_mono_neutral} above applies to various linear ordered monoids such as the reals but not to the complex numbers.
      Thus we have a separate corollary for those:\<close>

lemma infsum_mono_neutral_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes [simp]: "f summable_on A"
    and [simp]: "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows \<open>infsum f A \<le> infsum g B\<close>
proof -
  have \<open>infsum (\<lambda>x. Re (f x)) A \<le> infsum (\<lambda>x. Re (g x)) B\<close>
    by (smt (verit) assms infsum_cong infsum_mono_neutral less_eq_complex_def summable_on_Re zero_complex.simps(1))
  then have Re: \<open>Re (infsum f A) \<le> Re (infsum g B)\<close>
    by (metis assms(1-2) infsum_Re)
  have \<open>infsum (\<lambda>x. Im (f x)) A = infsum (\<lambda>x. Im (g x)) B\<close>
    by (smt (verit, best) assms(3-5) infsum_cong_neutral less_eq_complex_def zero_complex.simps(2))
  then have Im: \<open>Im (infsum f A) = Im (infsum g B)\<close>
    by (metis assms(1-2) infsum_Im)
  from Re Im show ?thesis
    by (auto simp: less_eq_complex_def)
qed

lemma infsum_mono_complex:
  \<comment> \<open>For \<^typ>\<open>real\<close>, @{thm [source] infsum_mono} can be used. 
      But \<^typ>\<open>complex\<close> does not have the right typeclass.\<close>
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f summable_on A" and g_sum: "g summable_on A"
  assumes leq: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsum f A \<le> infsum g A"
  by (metis DiffE IntD1 f_sum g_sum infsum_mono_neutral_complex leq)


lemma infsum_nonneg_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f summable_on M"
    and "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0" (is "?lhs \<ge> _")
  by (metis assms infsum_0_simp summable_on_0_simp infsum_mono_complex)

lemma infsum_cmod:
  assumes "f summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum (\<lambda>x. cmod (f x)) M = cmod (infsum f M)"
proof -
  have \<open>complex_of_real (infsum (\<lambda>x. cmod (f x)) M) = infsum (\<lambda>x. complex_of_real (cmod (f x))) M\<close>
  proof (rule infsum_comm_additive[symmetric, unfolded o_def])
    have "(\<lambda>z. Re (f z)) summable_on M"
      using assms summable_on_Re by blast
    also have "?this \<longleftrightarrow> f abs_summable_on M"
      using fnn by (intro summable_on_cong) (auto simp: less_eq_complex_def cmod_def)
    finally show \<dots> .
  qed (auto simp: additive_def)
  also have \<open>\<dots> = infsum f M\<close>
    using fnn cmod_eq_Re complex_is_Real_iff less_eq_complex_def by (force cong: infsum_cong)
  finally show ?thesis
    by (metis abs_of_nonneg infsum_def le_less_trans norm_ge_zero norm_infsum_bound norm_of_real not_le order_refl)
qed


lemma summable_on_iff_abs_summable_on_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>f summable_on A \<longleftrightarrow> f abs_summable_on A\<close>
proof (rule iffI)
  assume \<open>f summable_on A\<close>
  define i r ni nr n where \<open>i x = Im (f x)\<close> and \<open>r x = Re (f x)\<close>
    and \<open>ni x = norm (i x)\<close> and \<open>nr x = norm (r x)\<close> and \<open>n x = norm (f x)\<close> for x
  from \<open>f summable_on A\<close> have \<open>i summable_on A\<close>
    by (simp add: i_def[abs_def] summable_on_Im)
  then have [simp]: \<open>ni summable_on A\<close>
    using ni_def[abs_def] summable_on_iff_abs_summable_on_real by force

  from \<open>f summable_on A\<close> have \<open>r summable_on A\<close>
    by (simp add: r_def[abs_def] summable_on_Re)
  then have [simp]: \<open>nr summable_on A\<close>
    by (metis nr_def summable_on_cong summable_on_iff_abs_summable_on_real)

  have n_sum: \<open>n x \<le> nr x + ni x\<close> for x
    by (simp add: n_def nr_def ni_def r_def i_def cmod_le)

  have *: \<open>(\<lambda>x. nr x + ni x) summable_on A\<close>
    by (simp add: summable_on_add)
  have "bdd_above (sum n ` {F. F \<subseteq> A \<and> finite F})"
    apply (rule bdd_aboveI[where M=\<open>infsum (\<lambda>x. nr x + ni x) A\<close>])
    using * n_sum by (auto simp flip: infsum_finite simp: ni_def nr_def intro!: infsum_mono_neutral)
  then show \<open>n summable_on A\<close>
    by (simp add: n_def nonneg_bdd_above_summable_on)
next
  show \<open>f abs_summable_on A \<Longrightarrow> f summable_on A\<close>
    using abs_summable_summable by blast
qed

lemma summable_countable_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_summable_countable assms summable_on_iff_abs_summable_on_complex by blast


(* TODO: figure all this out *)
inductive (in topological_space) convergent_filter :: "'a filter \<Rightarrow> bool" where
  "F \<le> nhds x \<Longrightarrow> convergent_filter F"

lemma (in topological_space) convergent_filter_iff: "convergent_filter F \<longleftrightarrow> (\<exists>x. F \<le> nhds x)"
  by (auto simp: convergent_filter.simps)

lemma (in uniform_space) cauchy_filter_mono:
  "cauchy_filter F \<Longrightarrow> F' \<le> F \<Longrightarrow> cauchy_filter F'"
  unfolding cauchy_filter_def by (meson dual_order.trans prod_filter_mono)

lemma (in uniform_space) convergent_filter_cauchy: 
  assumes "convergent_filter F"
  shows   "cauchy_filter F"
  using assms cauchy_filter_mono nhds_imp_cauchy_filter[OF order.refl]
  by (auto simp: convergent_filter_iff)

lemma (in topological_space) convergent_filter_bot [simp, intro]: "convergent_filter bot"
  by (simp add: convergent_filter_iff)



class complete_uniform_space = uniform_space +
  assumes cauchy_filter_convergent': "cauchy_filter (F :: 'a filter) \<Longrightarrow> F \<noteq> bot \<Longrightarrow> convergent_filter F"

lemma (in complete_uniform_space)
  cauchy_filter_convergent: "cauchy_filter (F :: 'a filter) \<Longrightarrow> convergent_filter F"
  using cauchy_filter_convergent'[of F] by (cases "F = bot") auto

lemma (in complete_uniform_space) convergent_filter_iff_cauchy:
  "convergent_filter F \<longleftrightarrow> cauchy_filter F"
  using convergent_filter_cauchy cauchy_filter_convergent by blast

definition countably_generated_filter :: "'a filter \<Rightarrow> bool" where
  "countably_generated_filter F \<longleftrightarrow> (\<exists>U :: nat \<Rightarrow> 'a set. F = (INF (n::nat). principal (U n)))"

lemma countably_generated_filter_has_antimono_basis:
  assumes "countably_generated_filter F"
  obtains B :: "nat \<Rightarrow> 'a set"
  where "antimono B" and "F = (INF n. principal (B n))" and
        "\<And>P. eventually P F \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
proof -
  from assms obtain B where B: "F = (INF (n::nat). principal (B n))"
    unfolding countably_generated_filter_def by blast

  define B' where "B' = (\<lambda>n. \<Inter>k\<le>n. B k)"
  have "antimono B'"
    unfolding decseq_def B'_def by force

  have "(INF n. principal (B' n)) = (INF n. INF k\<in>{..n}. principal (B k))"
    unfolding B'_def by (intro INF_cong refl INF_principal_finite [symmetric]) auto
  also have "\<dots> = (INF (n::nat). principal (B n))"
    apply (intro antisym)
    apply (meson INF_lower INF_mono atMost_iff order_refl)
    apply (meson INF_greatest INF_lower UNIV_I)
    done
  also have "\<dots> = F"
    by (simp add: B)
  finally have F: "F = (INF n. principal (B' n))" ..

  moreover have "eventually P F \<longleftrightarrow> (\<exists>i. eventually P (principal (B' i)))" for P
    unfolding F using \<open>antimono B'\<close>
    apply (subst eventually_INF_base)
      apply (auto simp: decseq_def)
    by (meson nat_le_linear)
  ultimately show ?thesis
    using \<open>antimono B'\<close> that[of B'] unfolding eventually_principal by blast
qed

lemma (in uniform_space) cauchy_filter_iff:
  "cauchy_filter F \<longleftrightarrow> (\<forall>P. eventually P uniformity \<longrightarrow> (\<exists>X. eventually (\<lambda>x. x \<in> X) F \<and> (\<forall>z\<in>X\<times>X. P z)))" 
  unfolding cauchy_filter_def le_filter_def
  apply (auto simp: eventually_prod_same)
   apply (metis (full_types) eventually_mono mem_Collect_eq)
  apply blast
  done

lemma (in uniform_space) controlled_sequences_convergent_imp_complete_aux_sequence:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  fixes F :: "'a filter"
  assumes "cauchy_filter F" "F \<noteq> bot"
  assumes "\<And>n. eventually (\<lambda>z. z \<in> U n) uniformity"
  obtains g G where
    "antimono G" "\<And>n. g n \<in> G n"
    "\<And>n. eventually (\<lambda>x. x \<in> G n) F" "\<And>n. G n \<times> G n \<subseteq> U n"
proof -
  have "\<exists>C. eventually (\<lambda>x. x \<in> C) F \<and> C \<times> C \<subseteq> U n" for n
    using assms(1) assms(3)[of n] unfolding cauchy_filter_iff by blast
  then obtain G where G: "\<And>n. eventually (\<lambda>x. x \<in> G n) F" "\<And>n. G n \<times> G n \<subseteq> U n"
    by metis
  define G' where "G' = (\<lambda>n. \<Inter>k\<le>n. G k)"
  have 1: "eventually (\<lambda>x. x \<in> G' n) F" for n
    using G by (auto simp: G'_def intro: eventually_ball_finite)
  have 2: "G' n \<times> G' n \<subseteq> U n" for n
    using G unfolding G'_def by fast
  have 3: "antimono G'"
    unfolding G'_def decseq_def by force

  have "\<exists>g. g \<in> G' n" for n
    using 1 assms(2) eventually_happens' by auto
  then obtain g where g: "\<And>n. g n \<in> G' n"
    by metis
  from g 1 2 3 that[of G' g] show ?thesis
    by metis
qed

definition lift_filter :: "('a set \<Rightarrow> 'b filter) \<Rightarrow> 'a filter \<Rightarrow> 'b filter" where
  "lift_filter f F = (INF X\<in>{X. eventually (\<lambda>x. x \<in> X) F}. f X)"

lemma lift_filter_top [simp]: "lift_filter g top = g UNIV"
proof -
  have "{X. \<forall>x::'b. x \<in> X} = {UNIV}"
    by auto
  thus ?thesis
    by (simp add: lift_filter_def)
qed

lemma eventually_lift_filter_iff:
  assumes "mono g"
  shows   "eventually P (lift_filter g F) \<longleftrightarrow> (\<exists>X. eventually (\<lambda>x. x \<in> X) F \<and> eventually P (g X))"
  unfolding lift_filter_def
proof (subst eventually_INF_base, goal_cases)
  case 1
  thus ?case by (auto intro: exI[of _ UNIV])
next
  case (2 X Y)
  thus ?case
    by (auto intro!: exI[of _ "X \<inter> Y"] eventually_conj monoD[OF assms])
qed auto

lemma lift_filter_le:
  assumes "eventually (\<lambda>x. x \<in> X) F" "g X \<le> F'"
  shows   "lift_filter g F \<le> F'"
  unfolding lift_filter_def
  by (metis INF_lower2 assms mem_Collect_eq)

definition lift_filter' :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a filter \<Rightarrow> 'b filter" where
  "lift_filter' f F = lift_filter (principal \<circ> f) F"

lemma lift_filter'_top [simp]: "lift_filter' g top = principal (g UNIV)"
  by (simp add: lift_filter'_def)

lemma eventually_lift_filter'_iff:
  assumes "mono g"
  shows   "eventually P (lift_filter' g F) \<longleftrightarrow> (\<exists>X. eventually (\<lambda>x. x \<in> X) F \<and> (\<forall>x\<in>g X. P x))"
  unfolding lift_filter'_def using assms
  by (subst eventually_lift_filter_iff) (auto simp: mono_def eventually_principal)

lemma lift_filter'_le:
  assumes "eventually (\<lambda>x. x \<in> X) F" "principal (g X) \<le> F'"
  shows   "lift_filter' g F \<le> F'"
  unfolding lift_filter'_def using assms
  by (intro lift_filter_le[where X = X]) auto


lemma (in uniform_space) comp_uniformity_le_uniformity:
  "lift_filter' (\<lambda>X. X O X) uniformity \<le> uniformity"
  unfolding le_filter_def
proof safe
  fix P assume P: "eventually P uniformity"
  have [simp]: "mono (\<lambda>X::('a \<times> 'a) set. X O X)"
    by (intro monoI) auto
  from P obtain P' where P': "eventually P' uniformity " "(\<And>x y z. P' (x, y) \<Longrightarrow> P' (y, z) \<Longrightarrow> P (x, z))"
    using uniformity_transE by blast
  show "eventually P (lift_filter' (\<lambda>X. X O X) uniformity)"
    by (auto simp: eventually_lift_filter'_iff intro!: exI[of _ "{x. P' x}"] P')
qed

lemma (in uniform_space) comp_mem_uniformity_sets:
  assumes "eventually (\<lambda>z. z \<in> X) uniformity"
  obtains Y where "eventually (\<lambda>z. z \<in> Y) uniformity" "Y O Y \<subseteq> X"
proof -
  have [simp]: "mono (\<lambda>X::('a \<times> 'a) set. X O X)"
    by (intro monoI) auto
  have "eventually (\<lambda>z. z \<in> X) (lift_filter' (\<lambda>X. X O X) uniformity)"
    using assms comp_uniformity_le_uniformity using filter_leD by blast
  thus ?thesis using that
    by (auto simp: eventually_lift_filter'_iff)
qed

lemma (in uniform_space) le_nhds_of_cauchy_adhp_aux:
  assumes "\<And>P. eventually P uniformity \<Longrightarrow> (\<exists>X. eventually (\<lambda>y. y \<in> X) F \<and> (\<forall>z\<in>X \<times> X. P z) \<and> (\<exists>y. P (x, y) \<and> y \<in> X))"
  shows   "F \<le> nhds x"
  unfolding le_filter_def
proof safe
  fix P assume "eventually P (nhds x)"
  hence "\<forall>\<^sub>F z in uniformity. z \<in> {z. fst z = x \<longrightarrow> P (snd z)}"
    by (simp add: eventually_nhds_uniformity case_prod_unfold)
  then obtain Y where Y: "\<forall>\<^sub>F z in uniformity. z \<in> Y" "Y O Y \<subseteq> {z. fst z = x \<longrightarrow> P (snd z)}"
    using comp_mem_uniformity_sets by blast
  obtain X y where Xy: "eventually (\<lambda>y. y \<in> X) F" "X\<times>X \<subseteq> Y" "(x, y) \<in> Y" "y \<in> X"
    using assms[OF Y(1)] by blast
  have *: "P x" if "x \<in> X" for x
    using Y(2) Xy(2-4) that unfolding relcomp_unfold by force  
  show "eventually P F"
    by (rule eventually_mono[OF Xy(1)]) (use * in auto)
qed

lemma (in uniform_space) eventually_uniformity_imp_nhds:
  assumes "eventually P uniformity"
  shows   "eventually (\<lambda>y. P (x, y)) (nhds x)"
  using assms unfolding eventually_nhds_uniformity by (elim eventually_mono) auto

lemma (in uniform_space) controlled_sequences_convergent_imp_complete_aux:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes U: "\<And>n. eventually (\<lambda>z. z \<in> U n) uniformity"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). (\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (u m, u n) \<in> U N) \<Longrightarrow> convergent u"
  assumes "cauchy_filter F"
  shows   "convergent_filter F"
proof (cases "F = bot")
  case False
  note F = \<open>cauchy_filter F\<close> \<open>F \<noteq> bot\<close>
  from gen obtain B :: "nat \<Rightarrow> ('a \<times> 'a) set" where B:
    "antimono B" "uniformity = (INF n. principal (B n))"
    "\<And>P. eventually P uniformity \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis by blast

  have ev_B: "eventually (\<lambda>z. z \<in> B n) uniformity" for n
    by (subst B(3)) auto
  hence ev_B': "eventually (\<lambda>z. z \<in> B n \<inter> U n) uniformity" for n
    using U by (auto intro: eventually_conj)

  obtain g G where gG: "antimono G" "\<And>n. g n \<in> G n"
    "\<And>n. eventually (\<lambda>x. x \<in> G n) F" "\<And>n. G n \<times> G n \<subseteq> B n \<inter> U n"
    using controlled_sequences_convergent_imp_complete_aux_sequence[of F "\<lambda>n. B n \<inter> U n", OF F ev_B']
    by metis

  have "convergent g"
  proof (rule conv)
    fix N m n :: nat
    assume mn: "N \<le> m" "N \<le> n"
    have "(g m, g n) \<in> G m \<times> G n"
      using gG by auto
    also from mn have "\<dots> \<subseteq> G N \<times> G N"
      by (intro Sigma_mono gG antimonoD[OF gG(1)])
    also have "\<dots> \<subseteq> U N"
      using gG by blast
    finally show "(g m, g n) \<in> U N" .
  qed
  then obtain L where G: "g \<longlonglongrightarrow> L"
    unfolding convergent_def by blast

  have "F \<le> nhds L"
  proof (rule le_nhds_of_cauchy_adhp_aux)
    fix P :: "'a \<times> 'a \<Rightarrow> bool"
    assume P: "eventually P uniformity"
    hence "eventually (\<lambda>n. \<forall>x\<in>B n. P x) sequentially"
      using \<open>antimono B\<close> unfolding B(3) eventually_sequentially decseq_def by blast
    moreover have "eventually (\<lambda>n. P (L, g n)) sequentially"
      using P eventually_compose_filterlim eventually_uniformity_imp_nhds G by blast
    ultimately have "eventually (\<lambda>n. (\<forall>x\<in>B n. P x) \<and> P (L, g n)) sequentially"
      by eventually_elim auto
    then obtain n where "\<forall>x\<in>B n. P x" "P (L, g n)"
      unfolding eventually_at_top_linorder by blast
    then show "\<exists>X. (\<forall>\<^sub>F y in F. y \<in> X) \<and> (\<forall>z\<in>X \<times> X. P z) \<and> (\<exists>y. P (L, y) \<and> y \<in> X)"
      using gG by blast+
  qed
  thus "convergent_filter F"
    by (auto simp: convergent_filter_iff)
qed auto

theorem (in uniform_space) controlled_sequences_convergent_imp_complete:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes U: "\<And>n. eventually (\<lambda>z. z \<in> U n) uniformity"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). (\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (u m, u n) \<in> U N) \<Longrightarrow> convergent u"
  shows "class.complete_uniform_space open uniformity"
  by unfold_locales (use assms controlled_sequences_convergent_imp_complete_aux in blast)

lemma filtermap_prod_filter: "filtermap (map_prod f g) (F \<times>\<^sub>F G) = filtermap f F \<times>\<^sub>F filtermap g G"
proof (intro antisym)
  show "filtermap (map_prod f g) (F \<times>\<^sub>F G) \<le> filtermap f F \<times>\<^sub>F filtermap g G"
    by (auto simp: le_filter_def eventually_filtermap eventually_prod_filter)
next
  show "filtermap f F \<times>\<^sub>F filtermap g G \<le> filtermap (map_prod f g) (F \<times>\<^sub>F G)"
    unfolding le_filter_def
  proof safe
    fix P assume P: "eventually P (filtermap (map_prod f g) (F \<times>\<^sub>F G))"
    then obtain Pf Pg where *: "eventually Pf F" "eventually Pg G" "\<forall>x. Pf x \<longrightarrow> (\<forall>y. Pg y \<longrightarrow> P (f x, g y))"
      by (auto simp: eventually_filtermap eventually_prod_filter)

    define Pf' where "Pf' = (\<lambda>x. \<exists>y. x = f y \<and> Pf y)"
    define Pg' where "Pg' = (\<lambda>x. \<exists>y. x = g y \<and> Pg y)"

    from *(1) have "\<forall>\<^sub>F x in F. Pf' (f x)"
      by eventually_elim (auto simp: Pf'_def)
    moreover from *(2) have "\<forall>\<^sub>F x in G. Pg' (g x)"
      by eventually_elim (auto simp: Pg'_def)
    moreover have "(\<forall>x y. Pf' x \<longrightarrow> Pg' y \<longrightarrow> P (x, y))"
      using *(3) by (auto simp: Pf'_def Pg'_def)
    ultimately show "eventually P (filtermap f F \<times>\<^sub>F filtermap g G)"
      unfolding eventually_prod_filter eventually_filtermap
      by blast
  qed
qed
      

lemma (in uniform_space) Cauchy_seq_iff_tendsto:
  "Cauchy f \<longleftrightarrow> filterlim (map_prod f f) uniformity (at_top \<times>\<^sub>F at_top)"
  unfolding Cauchy_uniform cauchy_filter_def filterlim_def filtermap_prod_filter ..

theorem (in uniform_space) controlled_seq_imp_Cauchy_seq:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes U: "\<And>P. eventually P uniformity \<Longrightarrow> (\<exists>n. \<forall>x\<in>U n. P x)"
  assumes controlled: "\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (f m, f n) \<in> U N"
  shows   "Cauchy f"
  unfolding Cauchy_seq_iff_tendsto
proof -
  show "filterlim (map_prod f f) uniformity (sequentially \<times>\<^sub>F sequentially)"
    unfolding filterlim_def le_filter_def
  proof safe
    fix P :: "'a \<times> 'a \<Rightarrow> bool"
    assume P: "eventually P uniformity"
    from U[OF this] obtain N where "\<forall>x\<in>U N. P x"
      by blast
    then show "eventually P (filtermap (map_prod f f) (sequentially \<times>\<^sub>F sequentially))"
      unfolding eventually_filtermap eventually_prod_sequentially
      by (metis controlled map_prod_simp)
  qed
qed

lemma (in uniform_space) Cauchy_seq_convergent_imp_complete_aux:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). Cauchy u \<Longrightarrow> convergent u"
  assumes "cauchy_filter F"
  shows   "convergent_filter F"
proof -
  from gen obtain B :: "nat \<Rightarrow> ('a \<times> 'a) set" where B:
    "antimono B" "uniformity = (INF n. principal (B n))"
    "\<And>P. eventually P uniformity \<longleftrightarrow> (\<exists>i. \<forall>x\<in>B i. P x)"
    using countably_generated_filter_has_antimono_basis by blast

  show ?thesis
  proof (rule controlled_sequences_convergent_imp_complete_aux[where U = B])
    show "\<forall>\<^sub>F z in uniformity. z \<in> B n" for n
      unfolding B(3) by blast
  next
    fix f :: "nat \<Rightarrow> 'a"
    assume f: "\<And>N m n. N \<le> m \<Longrightarrow> N \<le> n \<Longrightarrow> (f m, f n) \<in> B N"
    have "Cauchy f" using f B
      by (intro controlled_seq_imp_Cauchy_seq[where U = B]) auto
    with conv show "convergent f"
      by simp
  qed fact+
qed

theorem (in uniform_space) Cauchy_seq_convergent_imp_complete:
  fixes U :: "nat \<Rightarrow> ('a \<times> 'a) set"
  assumes gen: "countably_generated_filter (uniformity :: ('a \<times> 'a) filter)"
  assumes conv: "\<And>(u :: nat \<Rightarrow> 'a). Cauchy u \<Longrightarrow> convergent u"
  shows   "class.complete_uniform_space open uniformity"
  by unfold_locales (use assms Cauchy_seq_convergent_imp_complete_aux in blast)

lemma (in metric_space) countably_generated_uniformity:
  "countably_generated_filter uniformity"
proof -
  have "(INF e\<in>{0<..}. principal {(x, y). dist (x::'a) y < e}) =
        (INF n\<in>UNIV. principal {(x, y). dist x y < 1 / real (Suc n)})" (is "?F = ?G")
    unfolding uniformity_dist
  proof (intro antisym)
    have "?G = (INF e\<in>(\<lambda>n. 1 / real (Suc n)) ` UNIV. principal {(x, y). dist x y < e})"
      by (simp add: image_image)
    also have "\<dots> \<ge> ?F"
      by (intro INF_superset_mono) auto
    finally show "?F \<le> ?G" .
  next
    show "?G \<le> ?F"
      unfolding le_filter_def
    proof safe
      fix P assume "eventually P ?F"
      then obtain \<epsilon> where \<epsilon>: "\<epsilon> > 0" "eventually P (principal {(x, y). dist x y < \<epsilon>})"
      proof (subst (asm) eventually_INF_base, goal_cases)
        case (2 \<epsilon>1 \<epsilon>2)
        thus ?case
          by (intro bexI[of _ "min \<epsilon>1 \<epsilon>2"]) auto
      qed auto
      from \<open>\<epsilon> > 0\<close> obtain n where "1 / real (Suc n) < \<epsilon>"
        using nat_approx_posE by blast
      then have "eventually P (principal {(x, y). dist x y < 1 / real (Suc n)})"
        using \<epsilon>(2) by (auto simp: eventually_principal)
      thus "eventually P ?G"
        by (intro eventually_INF1) auto
    qed
  qed
  thus "countably_generated_filter uniformity"
    unfolding countably_generated_filter_def uniformity_dist by fast
qed

subclass (in complete_space) complete_uniform_space
proof (rule Cauchy_seq_convergent_imp_complete)
  show "convergent f" if "Cauchy f" for f
    using Cauchy_convergent that by blast
qed (fact countably_generated_uniformity)

lemma (in complete_uniform_space) complete_UNIV_cuspace [intro]: "complete UNIV"
  unfolding complete_uniform using cauchy_filter_convergent
  by (auto simp: convergent_filter.simps)



lemma norm_infsum_le:
  assumes "(f has_sum S) X"
  assumes "(g has_sum T) X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> norm (f x) \<le> g x"
  shows   "norm S \<le> T"
proof (rule tendsto_le)
  show "((\<lambda>Y. norm (\<Sum>x\<in>Y. f x)) \<longlongrightarrow> norm S) (finite_subsets_at_top X)"
    using assms(1) unfolding has_sum_def by (intro tendsto_norm)
  show "((\<lambda>Y. \<Sum>x\<in>Y. g x) \<longlongrightarrow> T) (finite_subsets_at_top X)"
    using assms(2) unfolding has_sum_def .
  show "\<forall>\<^sub>F x in finite_subsets_at_top X. norm (sum f x) \<le> (\<Sum>x\<in>x. g x)"
    by (simp add: assms(3) eventually_finite_subsets_at_top_weakI subsetD sum_norm_le)
qed auto

(*
lemma summable_on_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add, t2_space, uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "(\<lambda>(x,y). f x y) summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (f x) summable_on (B x)\<close>
  shows \<open>(\<lambda>x. infsum (f x) (B x)) summable_on A\<close>
*)

lemma has_sum_imp_summable: "(f has_sum S) A \<Longrightarrow> f summable_on A"
  by (auto simp: summable_on_def)

lemma has_sum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "((\<lambda>x. f (g x)) has_sum S) A = (f has_sum S) B"
proof -
  have "((\<lambda>x. f (g x)) has_sum S) A \<longleftrightarrow> (f has_sum S) (g ` A)"
    by (subst has_sum_reindex) (use assms in \<open>auto dest: bij_betw_imp_inj_on simp: o_def\<close>)
  then show ?thesis
    using assms bij_betw_imp_surj_on by blast 
qed

lemma has_sum_reindex_bij_witness:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  assumes "s = s'"
  shows   "(g has_sum s) S = (h has_sum s') T"
  by (smt (verit, del_insts) assms bij_betwI' has_sum_cong has_sum_reindex_bij_betw)

lemma summable_on_reindex_bij_witness:
  assumes "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
  assumes "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
  assumes "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
  assumes "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  shows   "g summable_on S \<longleftrightarrow> h summable_on T"
  using has_sum_reindex_bij_witness[of S i j T h g, OF assms]
  by (simp add: summable_on_def)

lemma has_sum_homomorphism:
  assumes "(f has_sum S) A" "h 0 = 0" "\<And>a b. h (a + b) = h a + h b" "continuous_on UNIV h"
  shows   "((\<lambda>x. h (f x)) has_sum (h S)) A"
proof -
  have "sum (h \<circ> f) X = h (sum f X)" for X
    by (induction X rule: infinite_finite_induct) (simp_all add: assms)
  hence sum_h: "sum (h \<circ> f) = h \<circ> sum f"
    by (intro ext) auto
  then have "((h \<circ> f) has_sum h S) A"
    using assms
    by (metis UNIV_I continuous_on_def has_sum_comm_additive_general o_apply)
  thus ?thesis
    by (simp add: o_def)
qed

lemma summable_on_homomorphism:
  assumes "f summable_on A" "h 0 = 0" "\<And>a b. h (a + b) = h a + h b" "continuous_on UNIV h"
  shows   "(\<lambda>x. h (f x)) summable_on A"
proof -
  from assms(1) obtain S where "(f has_sum S) A"
    by (auto simp: summable_on_def)
  hence "((\<lambda>x. h (f x)) has_sum h S) A"
    by (rule has_sum_homomorphism) (use assms in auto)
  thus ?thesis
    by (auto simp: summable_on_def)
qed

lemma infsum_homomorphism_strong:
  fixes h :: "'a :: {t2_space, topological_comm_monoid_add} \<Rightarrow>
                'b :: {t2_space, topological_comm_monoid_add}"
  assumes "(\<lambda>x. h (f x)) summable_on A \<longleftrightarrow> f summable_on A"
  assumes "h 0 = 0" 
  assumes "\<And>S. (f has_sum S) A \<Longrightarrow> ((\<lambda>x. h (f x)) has_sum (h S)) A"
  shows   "infsum (\<lambda>x. h (f x)) A = h (infsum f A)"
  by (metis assms has_sum_infsum infsumI infsum_not_exists)

lemma has_sum_bounded_linear:
  assumes "bounded_linear h" and "(f has_sum S) A"
  shows "((\<lambda>x. h (f x)) has_sum h S) A"
proof -
  interpret bounded_linear h by fact
  from assms(2) show ?thesis
    by (rule has_sum_homomorphism) (auto simp: add intro!: continuous_on)
qed

lemma summable_on_bounded_linear:
  assumes "bounded_linear h" and "f summable_on A"
  shows "(\<lambda>x. h (f x)) summable_on A"
  by (metis assms has_sum_bounded_linear summable_on_def)

lemma summable_on_bounded_linear_iff:
  assumes "bounded_linear h" and "bounded_linear h'" and "\<And>x. h' (h x) = x"
  shows "(\<lambda>x. h (f x)) summable_on A \<longleftrightarrow> f summable_on A"
  by (metis (full_types) assms summable_on_bounded_linear summable_on_cong)

lemma infsum_bounded_linear_strong:
  fixes h :: "'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_vector"
  assumes "(\<lambda>x. h (f x)) summable_on A \<longleftrightarrow> f summable_on A"
  assumes "bounded_linear h"
  shows   "infsum (\<lambda>x. h (f x)) A = h (infsum f A)"
proof -
  interpret bounded_linear h by fact
  show ?thesis
    by (rule infsum_homomorphism_strong)
       (insert assms, auto intro: add continuous_on has_sum_bounded_linear)
qed

lemma infsum_bounded_linear_strong':
  fixes mult :: "'c :: zero \<Rightarrow> 'a :: real_normed_vector \<Rightarrow> 'b :: real_normed_vector"
  assumes "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. mult c (f x)) summable_on A \<longleftrightarrow> f summable_on A"
  assumes "bounded_linear (mult c)"
  assumes [simp]: "\<And>x. mult 0 x = 0"
  shows   "infsum (\<lambda>x. mult c (f x)) A = mult c (infsum f A)"
  by (metis assms infsum_0 infsum_bounded_linear_strong)

lemma has_sum_scaleR:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes "(f has_sum S) A"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_sum (c *\<^sub>R S)) A"
  using has_sum_bounded_linear[OF bounded_linear_scaleR_right[of c], of f A S] assms by simp

lemma has_sum_scaleR_iff:
  fixes f :: "'a \<Rightarrow> 'b :: real_normed_vector"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c *\<^sub>R f x) has_sum S) A \<longleftrightarrow> (f has_sum (S /\<^sub>R c)) A"
  using has_sum_scaleR[of f A "S /\<^sub>R c" c] has_sum_scaleR[of "\<lambda>x. c *\<^sub>R f x" A S "inverse c"] assms
  by auto

lemma has_sum_of_nat: "(f has_sum S) A \<Longrightarrow> ((\<lambda>x. of_nat (f x)) has_sum of_nat S) A"
  by (erule has_sum_homomorphism) (auto intro!: continuous_intros)

lemma has_sum_of_int: "(f has_sum S) A \<Longrightarrow> ((\<lambda>x. of_int (f x)) has_sum of_int S) A"
  by (erule has_sum_homomorphism) (auto intro!: continuous_intros)

lemma summable_on_of_nat: "f summable_on A \<Longrightarrow> (\<lambda>x. of_nat (f x)) summable_on A"
  by (erule summable_on_homomorphism) (auto intro!: continuous_intros)

lemma summable_on_of_int: "f summable_on A \<Longrightarrow> (\<lambda>x. of_int (f x)) summable_on A"
  by (erule summable_on_homomorphism) (auto intro!: continuous_intros)

lemma summable_on_of_real:
  "f summable_on A \<Longrightarrow> (\<lambda>x. of_real (f x) :: 'a :: real_normed_algebra_1) summable_on A"
  using summable_on_bounded_linear[of "of_real :: real \<Rightarrow> 'a", OF bounded_linear_of_real, of f A]
  by simp

lemma has_sum_of_real_iff:
  "((\<lambda>x. of_real (f x) :: 'a :: real_normed_div_algebra) has_sum (of_real c)) A \<longleftrightarrow> 
   (f has_sum c) A"
proof -
  have "((\<lambda>x. of_real (f x) :: 'a) has_sum (of_real c)) A \<longleftrightarrow>
        (sum (\<lambda>x. of_real (f x) :: 'a) \<longlongrightarrow> of_real c) (finite_subsets_at_top A)"
    by (simp add: has_sum_def)
  also have "sum (\<lambda>x. of_real (f x) :: 'a) = (\<lambda>X. of_real (sum f X))"
    by simp
  also have "((\<lambda>X. of_real (sum f X) :: 'a) \<longlongrightarrow> of_real c) (finite_subsets_at_top A) \<longleftrightarrow> 
             (f has_sum c) A"
    unfolding has_sum_def tendsto_of_real_iff ..
  finally show ?thesis .
qed

lemma has_sum_of_real:
  "(f has_sum S) A \<Longrightarrow> ((\<lambda>x. of_real (f x) :: 'a :: real_normed_algebra_1) has_sum of_real S) A"
  using has_sum_bounded_linear[of "of_real :: real \<Rightarrow> 'a", OF bounded_linear_of_real, of f A S]
  by simp

lemma summable_on_discrete_iff:
  fixes f :: "'a \<Rightarrow> 'b :: {discrete_topology, topological_comm_monoid_add, cancel_comm_monoid_add}"
  shows "f summable_on A \<longleftrightarrow> finite {x\<in>A. f x \<noteq> 0}"
proof
  assume *: "finite {x\<in>A. f x \<noteq> 0}"
  hence "f summable_on {x\<in>A. f x \<noteq> 0}"
    by (rule summable_on_finite)
  then show "f summable_on A"
    by (smt (verit) DiffE mem_Collect_eq summable_on_cong_neutral) 
next
  assume "f summable_on A"
  then obtain S where "(f has_sum S) A"
    by (auto simp: summable_on_def)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = S"
    unfolding has_sum_def tendsto_discrete .
  then obtain X where X: "finite X" "X \<subseteq> A" "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> sum f Y = S"
    unfolding eventually_finite_subsets_at_top by metis
  have "{x\<in>A. f x \<noteq> 0} \<subseteq> X"
  proof
    fix x assume x: "x \<in> {x\<in>A. f x \<noteq> 0}"
    show "x \<in> X"
    proof (rule ccontr)
      assume [simp]: "x \<notin> X"
      have "sum f (insert x X) = S"
        using X x by (intro X) auto
      then have "f x = 0"
        using X by auto
      with x show False
        by auto
    qed
  qed
  thus "finite {x\<in>A. f x \<noteq> 0}"
    using X(1) finite_subset by blast
qed

lemma has_sum_imp_sums: "(f has_sum S) (UNIV :: nat set) \<Longrightarrow> f sums S"
  unfolding sums_def has_sum_def by (rule filterlim_compose[OF _ filterlim_lessThan_at_top])

lemma summable_on_imp_summable: "f summable_on (UNIV :: nat set) \<Longrightarrow> summable f"
  unfolding summable_on_def summable_def by (auto dest: has_sum_imp_sums)

lemma summable_on_UNIV_nonneg_real_iff:
  assumes "\<And>n. f n \<ge> (0 :: real)"
  shows   "f summable_on UNIV \<longleftrightarrow> summable f"
  using assms by (auto intro: norm_summable_imp_summable_on summable_on_imp_summable)

lemma summable_on_imp_bounded_partial_sums:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_add, linorder_topology}"
  assumes f: "f summable_on A"
  shows   "\<exists>C. eventually (\<lambda>X. sum f X \<le> C) (finite_subsets_at_top A)"
proof -
  from assms obtain S where S: "(sum f \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding summable_on_def has_sum_def by blast
  show ?thesis
  proof (cases "\<exists>C. C > S")
    case True
    then obtain C where C: "C > S"
      by blast
    have "\<forall>\<^sub>F X in finite_subsets_at_top A. sum f X < C"
      using S C by (rule order_tendstoD(2))
    thus ?thesis
      by (meson eventually_mono nless_le)
  next
    case False thus ?thesis
      by (meson not_eventuallyD not_le_imp_less)
  qed
qed

lemma has_sum_mono':
  fixes S S' :: "'a :: {linorder_topology, ordered_comm_monoid_add, topological_comm_monoid_add}"
  assumes f: "(f has_sum S) A" "(f has_sum S') B" 
     and AB: "A \<subseteq> B" "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows   "S \<le> S'"
  using AB has_sum_mono_neutral[OF f] by fastforce


context
  assumes "SORT_CONSTRAINT('a :: {topological_comm_monoid_add, order_topology,
             ordered_comm_monoid_add, conditionally_complete_linorder})"
begin

text \<open>
  Any family of non-negative numbers with bounded partial sums is summable, and the sum
  is simply the supremum of the partial sums.
\<close>
lemma nonneg_bounded_partial_sums_imp_has_sum_SUP:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (0::'a)"
      and bound:  "eventually (\<lambda>X. sum f X \<le> C) (finite_subsets_at_top A)"
  shows   "(f has_sum (SUP X\<in>{X. X \<subseteq> A \<and> finite X}. sum f X)) A"
proof -
  from bound obtain X0
    where X0: "X0 \<subseteq> A" "finite X0" "\<And>X. X0 \<subseteq> X \<Longrightarrow> X \<subseteq> A \<Longrightarrow> finite X \<Longrightarrow> sum f X \<le> C"
    by (force simp: eventually_finite_subsets_at_top)
  have bound': "sum f X \<le> C" if "X \<subseteq> A" "finite X" for X
  proof -
    have "sum f X \<le> sum f (X \<union> X0)"
      using that X0 assms(1) by (intro sum_mono2) auto
    also have "\<dots> \<le> C"
      by (simp add: X0 that)
    finally show ?thesis .
  qed
  hence bdd: "bdd_above (sum f ` {X. X \<subseteq> A \<and> finite X})"
    by (auto simp: bdd_above_def)

  show ?thesis unfolding has_sum_def
  proof (rule increasing_tendsto)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. sum f X \<le> Sup (sum f ` {X. X \<subseteq> A \<and> finite X})"
      by (intro eventually_finite_subsets_at_top_weakI cSUP_upper[OF _ bdd]) auto
  next
    fix y assume "y < Sup (sum f ` {X. X \<subseteq> A \<and> finite X})"
    then obtain X where X: "X \<subseteq> A" "finite X" "y < sum f X"
      by (subst (asm) less_cSUP_iff[OF _ bdd]) auto
    from X have "eventually (\<lambda>X'. X \<subseteq> X' \<and> X' \<subseteq> A \<and> finite X') (finite_subsets_at_top A)"
      by (auto simp: eventually_finite_subsets_at_top)
    thus "eventually (\<lambda>X'. y < sum f X') (finite_subsets_at_top A)"
    proof eventually_elim
      case (elim X')
      note \<open>y < sum f X\<close>
      also have "sum f X \<le> sum f X'"
        using nonneg elim by (intro sum_mono2) auto
      finally show ?case .
    qed
  qed
qed

lemma nonneg_bounded_partial_sums_imp_summable_on:
  assumes nonneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> (0::'a)"
      and bound:  "eventually (\<lambda>X. sum f X \<le> C) (finite_subsets_at_top A)"
  shows   "f summable_on A"
  using nonneg_bounded_partial_sums_imp_has_sum_SUP[OF assms] by (auto simp: summable_on_def)

end

context
  assumes "SORT_CONSTRAINT('a :: {topological_comm_monoid_add, linorder_topology,
             ordered_comm_monoid_add, conditionally_complete_linorder})"
begin

lemma summable_on_comparison_test:
  assumes "f summable_on A" and "\<And>x. x \<in> A \<Longrightarrow> g x \<le> f x" and "\<And>x. x \<in> A \<Longrightarrow> (0::'a) \<le> g x"
  shows   "g summable_on A"
proof -
  obtain C where C: "\<forall>\<^sub>F X in finite_subsets_at_top A. sum f X \<le> C"
    using assms(1) summable_on_imp_bounded_partial_sums by blast
  show ?thesis
  proof (rule nonneg_bounded_partial_sums_imp_summable_on)
    show "\<forall>\<^sub>F X in finite_subsets_at_top A. sum g X \<le> C"
      using C assms 
      unfolding eventually_finite_subsets_at_top
      by (smt (verit, ccfv_SIG) order_trans subsetD sum_mono)
  qed (use assms in auto)
qed

end



lemma summable_on_subset:
  fixes f :: "_ \<Rightarrow> 'a :: {uniform_topological_group_add, topological_comm_monoid_add, ab_group_add, complete_uniform_space}"
  assumes "f summable_on A" "B \<subseteq> A"
  shows "f summable_on B"
  by (rule summable_on_subset_aux[OF _ _ assms]) (auto simp: uniformly_continuous_add)

lemma summable_on_union:
  fixes f :: "_ \<Rightarrow> 'a :: {uniform_topological_group_add, topological_comm_monoid_add, ab_group_add, complete_uniform_space}"
  assumes "f summable_on A" "f summable_on B"
  shows "f summable_on (A \<union> B)"
proof -
  have "f summable_on (A \<union> (B - A))"
    by (meson Diff_disjoint Diff_subset assms summable_on_Un_disjoint summable_on_subset)
  also have "A \<union> (B - A) = A \<union> B"
    by blast
  finally show ?thesis .
qed

lemma summable_on_insert_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {uniform_topological_group_add, topological_comm_monoid_add, ab_group_add, complete_uniform_space}"
  shows "f summable_on insert x A \<longleftrightarrow> f summable_on A"
  using summable_on_union[of f A "{x}"] by (auto intro: summable_on_subset)

lemma has_sum_insert:
  fixes f :: "'a \<Rightarrow> 'b :: topological_comm_monoid_add"
  assumes "x \<notin> A" and "(f has_sum S) A"
  shows   "(f has_sum (f x + S)) (insert x A)"
proof -
  have "(f has_sum (f x + S)) ({x} \<union> A)"
    using assms by (intro has_sum_Un_disjoint) (auto intro: has_sum_finiteI)
  thus ?thesis by simp
qed

lemma infsum_insert:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_add, t2_space}"
  assumes "f summable_on A" "a \<notin> A"
  shows   "infsum f (insert a A) = f a + infsum f A"
  by (meson assms has_sum_insert infsumI summable_iff_has_sum_infsum)

lemma has_sum_SigmaD:
  fixes f :: "'b \<times> 'c \<Rightarrow> 'a :: {topological_comm_monoid_add,t3_space}"
  assumes sum1: "(f has_sum S) (Sigma A B)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_sum g x) (B x)"
  shows   "(g has_sum S) A"
  unfolding has_sum_def tendsto_def eventually_finite_subsets_at_top
proof (safe, goal_cases)
  case (1 X)
  with nhds_closed[of S X] obtain X'
    where X': "S \<in> X'" "closed X'" "X' \<subseteq> X" "eventually (\<lambda>y. y \<in> X') (nhds S)" by blast
  from X'(4) obtain X'' where X'': "S \<in> X''" "open X''" "X'' \<subseteq> X'"
    by (auto simp: eventually_nhds)
  with sum1 obtain Y :: "('b \<times> 'c) set"
    where Y: "Y \<subseteq> Sigma A B" "finite Y"
             "\<And>Z. Y \<subseteq> Z \<Longrightarrow> Z \<subseteq> Sigma A B \<Longrightarrow> finite Z \<Longrightarrow> sum f Z \<in> X''"
    unfolding has_sum_def tendsto_def eventually_finite_subsets_at_top by force
  define Y1 :: "'b set" where "Y1 = fst ` Y"
  from Y have Y1: "Y1 \<subseteq> A" by (auto simp: Y1_def)
  define Y2 :: "'b \<Rightarrow> 'c set" where "Y2 = (\<lambda>x. {y. (x, y) \<in> Y})"
  have Y2: "finite (Y2 x)" "Y2 x \<subseteq> B x" if "x \<in> A" for x
    using that Y(1,2) unfolding Y2_def
    by (force simp: image_iff intro: finite_subset[of _ "snd ` Y"])+

  show ?case
  proof (rule exI[of _ Y1], safe, goal_cases)
    case (3 Z)
    define H where "H = (INF x\<in>Z. filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
    
    have "sum g Z \<in> X'"
    proof (rule Lim_in_closed_set)
      show "closed X'" by fact
    next
      show "((\<lambda>B'. sum (\<lambda>x. sum (\<lambda>y. f (x, y)) (B' x)) Z) \<longlongrightarrow> sum g Z) H"
        unfolding H_def
      proof (intro tendsto_sum filterlim_INF')
        fix x assume x: "x \<in> Z"
        with 3 have "x \<in> A" by auto
        from sum2[OF this] have "(sum (\<lambda>y. f (x, y)) \<longlongrightarrow> g x) (finite_subsets_at_top (B x))"
          by (simp add: has_sum_def)
        thus "((\<lambda>B'. sum (\<lambda>y. f (x, y)) (B' x)) \<longlongrightarrow> g x)
                 (filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))"
          by (rule filterlim_compose[OF _ filterlim_filtercomap])
      qed auto
    next
      show "\<forall>\<^sub>F h in H. sum (\<lambda>x. sum (\<lambda>y. f (x, y)) (h x)) Z \<in> X'"
        unfolding H_def
      proof (subst eventually_INF_finite[OF \<open>finite Z\<close>], rule exI, safe)
        fix x assume x: "x \<in> Z"
        hence x': "x \<in> A" using 3 by auto
        show "eventually (\<lambda>h. finite (h x) \<and> Y2 x \<subseteq> h x \<and> h x \<subseteq> B x)
                (filtercomap (\<lambda>p. p x) (finite_subsets_at_top (B x)))" using 3 Y2[OF x']
          by (intro eventually_filtercomapI)
             (auto simp: eventually_finite_subsets_at_top intro: exI[of _ "Y2 x"])
      next
        fix h
        assume *: "\<forall>x\<in>Z. finite (h x) \<and> Y2 x \<subseteq> h x \<and> h x \<subseteq> B x"
        hence "sum (\<lambda>x. sum (\<lambda>y. f (x, y)) (h x)) Z = sum f (Sigma Z h)"
          using \<open>finite Z\<close> by (subst sum.Sigma) auto
        also have "\<dots> \<in> X''"
          using * 3 Y(1,2) by (intro Y; force simp: Y1_def Y2_def)
        also have "X'' \<subseteq> X'" by fact
        finally show "sum (\<lambda>x. sum (\<lambda>y. f (x, y)) (h x)) Z \<in> X'" .
      qed
    next
      have "H = (INF x\<in>SIGMA x:Z. {X. finite X \<and> X \<subseteq> B x}.
                  principal {y. finite (y (fst x)) \<and> snd x \<subseteq> y (fst x) \<and> y (fst x) \<subseteq> B (fst x)})"
        unfolding H_def finite_subsets_at_top_def filtercomap_INF filtercomap_principal
        by (simp add: INF_Sigma)
      also have "\<dots> \<noteq> bot"
      proof (rule INF_filter_not_bot, subst INF_principal_finite, goal_cases)
        case (2 X)
        define H' where
          "H' = (\<Inter>x\<in>X. {y. finite (y (fst x)) \<and> snd x \<subseteq> y (fst x) \<and> y (fst x) \<subseteq> B (fst x)})"
        from 2 have "(\<lambda>x. \<Union>(y,Y)\<in>X. if x = y then Y else {}) \<in> H'"
          by (force split: if_splits simp: H'_def)
        hence "H' \<noteq> {}" by blast
        thus "principal H' \<noteq> bot" by (simp add: principal_eq_bot_iff)
      qed
      finally show "H \<noteq> bot" .
    qed
    also have "X' \<subseteq> X" by fact
    finally show "sum g Z \<in> X" .
  qed (insert Y(1,2), auto simp: Y1_def)
qed

lemma has_sum_finite_iff: 
  fixes S :: "'a :: {topological_comm_monoid_add,t2_space}"
  assumes "finite A"
  shows   "(f has_sum S) A \<longleftrightarrow> S = (\<Sum>x\<in>A. f x)"
proof
  assume "S = (\<Sum>x\<in>A. f x)"
  thus "(f has_sum S) A"
    by (intro has_sum_finiteI assms)
next
  assume "(f has_sum S) A"
  moreover have "(f has_sum (\<Sum>x\<in>A. f x)) A"
    by (intro has_sum_finiteI assms) auto
  ultimately show "S = (\<Sum>x\<in>A. f x)"
    using has_sum_unique by blast
qed

lemma has_sum_finite_neutralI:
  assumes "finite B" "B \<subseteq> A" "\<And>x. x \<in> A - B \<Longrightarrow> f x = 0" "c = (\<Sum>x\<in>B. f x)"
  shows   "(f has_sum c) A"
proof -
  have "(f has_sum c) B"
    by (rule has_sum_finiteI) (use assms in auto)
  also have "?this \<longleftrightarrow> (f has_sum c) A"
    by (intro has_sum_cong_neutral) (use assms in auto)
  finally show ?thesis .
qed

lemma has_sum_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: {topological_comm_monoid_add, t3_space}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_sum g x) (B x)"
  assumes g: "(g has_sum S) A"
  assumes summable: "f summable_on Sigma A B"
  shows   "(f has_sum S) (Sigma A B)"
  by (metis f g has_sum_SigmaD has_sum_infsum has_sum_unique local.summable)

lemma summable_on_SigmaD1:
  fixes f :: "_ \<Rightarrow> _ \<Rightarrow> 'a :: {complete_uniform_space, uniform_topological_group_add, ab_group_add, topological_comm_monoid_add}"
  assumes f: "(\<lambda>(x,y). f x y) summable_on Sigma A B"
  assumes x: "x \<in> A"
  shows   "f x summable_on B x"
proof -
  have "(\<lambda>(x,y). f x y) summable_on Sigma {x} B"
    using f by (rule summable_on_subset) (use x in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>y. f x y) \<circ> snd) summable_on Sigma {x} B"
    by (intro summable_on_cong) auto
  also have "\<dots> \<longleftrightarrow> (\<lambda>y. f x y) summable_on snd ` Sigma {x} B"
    by (intro summable_on_reindex [symmetric] inj_onI) auto
  also have "snd ` Sigma {x} B = B x"
    by (force simp: Sigma_def)
  finally show ?thesis .
qed

lemma has_sum_swap:
  "(f has_sum S) (A \<times> B) \<longleftrightarrow> ((\<lambda>(x,y). f (y,x)) has_sum S) (B \<times> A)"
proof -
  have "bij_betw (\<lambda>(x,y). (y,x)) (B \<times> A) (A \<times> B)"
    by (rule bij_betwI[of _ _ _ "\<lambda>(x,y). (y,x)"]) auto
  from has_sum_reindex_bij_betw[OF this, where f = f] show ?thesis
    by (simp add: case_prod_unfold)
qed


lemma summable_on_swap:
  "f summable_on (A \<times> B) \<longleftrightarrow> (\<lambda>(x,y). f (y,x)) summable_on (B \<times> A)"
  by (metis has_sum_swap summable_on_def)

lemma has_sum_cmult_right_iff:
  fixes c :: "'a :: {topological_semigroup_mult, field}"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. c * f x) has_sum S) A \<longleftrightarrow> (f has_sum (S / c)) A"
  using has_sum_cmult_right[of f A "S/c" c]
        has_sum_cmult_right[of "\<lambda>x. c * f x" A S "inverse c"] assms
  by (auto simp: field_simps)

lemma has_sum_cmult_left_iff:
  fixes c :: "'a :: {topological_semigroup_mult, field}"
  assumes "c \<noteq> 0"
  shows   "((\<lambda>x. f x * c) has_sum S) A \<longleftrightarrow> (f has_sum (S / c)) A"
  by (smt (verit, best) assms has_sum_cmult_right_iff has_sum_cong mult.commute)

lemma finite_nonzero_values_imp_summable_on:
  assumes "finite {x\<in>X. f x \<noteq> 0}"
  shows   "f summable_on X"
  by (smt (verit, del_insts) Diff_iff assms mem_Collect_eq summable_on_cong_neutral summable_on_finite)

lemma summable_on_of_int_iff:
  "(\<lambda>x::'a. of_int (f x) :: 'b :: real_normed_algebra_1) summable_on A \<longleftrightarrow> f summable_on A"
proof
  assume "f summable_on A"
  thus "(\<lambda>x. of_int (f x)) summable_on A"
    by (rule summable_on_homomorphism) auto
next
  assume "(\<lambda>x. of_int (f x) :: 'b) summable_on A"
  then obtain S where "((\<lambda>x. of_int (f x) :: 'b) has_sum S) A"
    by (auto simp: summable_on_def)
  hence "(sum (\<lambda>x. of_int (f x) :: 'b) \<longlongrightarrow> S) (finite_subsets_at_top A)"
    unfolding has_sum_def .
  moreover have "1/2 > (0 :: real)"
    by auto
  ultimately have "eventually (\<lambda>X. dist (sum (\<lambda>x. of_int (f x) :: 'b) X) S < 1/2)
                     (finite_subsets_at_top A)"
    unfolding tendsto_iff by blast
  then obtain X where X: "finite X" "X \<subseteq> A"
     "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> dist (sum (\<lambda>x. of_int (f x)) Y) S < 1/2"
    unfolding eventually_finite_subsets_at_top by metis

  have "sum f Y = sum f X" if "finite Y" "X \<subseteq> Y" "Y \<subseteq> A" for Y
  proof -
    have "dist (sum (\<lambda>x. of_int (f x)) X) S < 1/2"
      by (intro X) auto
    moreover have "dist (sum (\<lambda>x. of_int (f x)) Y) S < 1/2"
      by (intro X that)
    ultimately have "dist (sum (\<lambda>x. of_int (f x)) X) (sum (\<lambda>x. of_int (f x) :: 'b) Y) <
                       1/2 + 1/2"
      using dist_triangle_less_add by blast
    thus ?thesis
      by (simp add: dist_norm flip: of_int_sum of_int_diff)
  qed
  then have "{x\<in>A. f x \<noteq> 0} \<subseteq> X"
    by (smt (verit) X finite_insert insert_iff mem_Collect_eq subset_eq sum.insert)
  with \<open>finite X\<close> have "finite {x\<in>A. f x \<noteq> 0}"
    using finite_subset by blast
  thus "f summable_on A"
    by (rule finite_nonzero_values_imp_summable_on)
qed

lemma summable_on_of_nat_iff:
  "(\<lambda>x::'a. of_nat (f x) :: 'b :: real_normed_algebra_1) summable_on A \<longleftrightarrow> f summable_on A"
proof
  assume "f summable_on A"
  thus "(\<lambda>x. of_nat (f x) :: 'b) summable_on A"
    by (rule summable_on_homomorphism) auto
next
  assume "(\<lambda>x. of_nat (f x) :: 'b) summable_on A"
  hence "(\<lambda>x. of_int (int (f x)) :: 'b) summable_on A"
    by simp
  also have "?this \<longleftrightarrow> (\<lambda>x. int (f x)) summable_on A"
    by (rule summable_on_of_int_iff)
  also have "\<dots> \<longleftrightarrow> f summable_on A"
    by (simp add: summable_on_discrete_iff)
  finally show "f summable_on A" .
qed

lemma infsum_of_nat:
  "infsum (\<lambda>x::'a. of_nat (f x) :: 'b :: {real_normed_algebra_1}) A = of_nat (infsum f A)"
  by (metis has_sum_infsum has_sum_of_nat infsumI infsum_def of_nat_0 summable_on_of_nat_iff)

lemma infsum_of_int:
  "infsum (\<lambda>x::'a. of_int (f x) :: 'b :: {real_normed_algebra_1}) A = of_int (infsum f A)"
  by (metis has_sum_infsum has_sum_of_int infsumI infsum_not_exists of_int_0 summable_on_of_int_iff)


lemma summable_on_SigmaI:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, ordered_comm_monoid_add, topological_comm_monoid_add,
                          conditionally_complete_linorder}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_sum g x) (B x)"
  assumes g: "g summable_on A"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f (x, y) \<ge> (0 :: 'a)"
  shows   "f summable_on Sigma A B"
proof -
  have g_nonneg: "g x \<ge> 0" if "x \<in> A" for x
    using f by (rule has_sum_nonneg) (use f_nonneg that in auto)
  obtain C where C: "eventually (\<lambda>X. sum g X \<le> C) (finite_subsets_at_top A)"
    using summable_on_imp_bounded_partial_sums[OF g] by blast

  have sum_g_le: "sum g X \<le> C" if X: "finite X" "X \<subseteq> A" for X
  proof -
    from C obtain X' where X':
      "finite X'" "X' \<subseteq> A" "\<And>Y. finite Y \<Longrightarrow> X' \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> sum g Y \<le> C"
      unfolding eventually_finite_subsets_at_top by metis
    have "sum g X \<le> sum g (X \<union> X')"
      using X X' by (intro sum_mono2 g_nonneg) auto
    also have "\<dots> \<le> C"
      using X X'(1,2) by (intro X'(3)) auto
    finally show ?thesis .
  qed

  have "sum f Y \<le> C" if Y: "finite Y" "Y \<subseteq> Sigma A B" for Y
  proof -
    define Y1 and Y2 where "Y1 = fst ` Y" and "Y2 = (\<lambda>x. snd ` {z\<in>Y. fst z = x})"
    have Y12: "Y = Sigma Y1 Y2"
      unfolding Y1_def Y2_def by force
    have [intro]: "finite Y1" "\<And>x. x \<in> Y1 \<Longrightarrow> finite (Y2 x)"
      using Y unfolding Y1_def Y2_def by auto
    have Y12_subset: "Y1 \<subseteq> A" "\<And>x. Y2 x \<subseteq> B x"
      using Y by (auto simp: Y1_def Y2_def)

    have "sum f Y = sum f (Sigma Y1 Y2)"
      by (simp add: Y12)
    also have "\<dots> = (\<Sum>x\<in>Y1. \<Sum>y\<in>Y2 x. f (x, y))"
      by (subst sum.Sigma) auto
    also have "\<dots> \<le> (\<Sum>x\<in>Y1. g x)"
    proof (rule sum_mono)
      fix x assume x: "x \<in> Y1"
      show "(\<Sum>y\<in>Y2 x. f (x, y)) \<le> g x"
      proof (rule has_sum_mono')
        show "((\<lambda>y. f (x, y)) has_sum (\<Sum>y\<in>Y2 x. f (x, y))) (Y2 x)"
          using x by (intro has_sum_finite) auto
        show "((\<lambda>y. f (x, y)) has_sum g x) (B x)"
          by (rule f) (use x Y12_subset in auto)
        show "f (x, y) \<ge> 0" if "y \<in> B x - Y2 x" for y
          using x that Y12_subset by (intro f_nonneg) auto
      qed (use Y12_subset in auto)
    qed
    also have "\<dots> \<le> C"
      using Y12_subset by (intro sum_g_le) auto
    finally show ?thesis .
  qed

  hence "\<forall>\<^sub>F X in finite_subsets_at_top (Sigma A B). sum f X \<le> C"
    unfolding eventually_finite_subsets_at_top by auto
  thus ?thesis
    by (metis SigmaE f_nonneg nonneg_bounded_partial_sums_imp_summable_on)
qed

lemma summable_on_UnionI:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, ordered_comm_monoid_add, topological_comm_monoid_add,
                          conditionally_complete_linorder}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> (f has_sum g x) (B x)"
  assumes g: "g summable_on A"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f y \<ge> (0 :: 'a)"
  assumes disj: "disjoint_family_on B A"
  shows   "f summable_on (\<Union>x\<in>A. B x)"
proof -
  have "f \<circ> snd summable_on Sigma A B"
    using assms by (intro summable_on_SigmaI[where g = g]) auto
  also have "?this \<longleftrightarrow> f summable_on (snd ` Sigma A B)" using assms
    by (subst summable_on_reindex; force simp: disjoint_family_on_def inj_on_def)
  also have "snd ` (Sigma A B) = (\<Union>x\<in>A. B x)"
    by force
  finally show ?thesis .
qed

lemma summable_on_SigmaD:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c :: {topological_comm_monoid_add,t3_space}"
  assumes sum1: "f summable_on (Sigma A B)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)"
  shows   "(\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) summable_on A"
  using assms unfolding summable_on_def
  by (smt (verit, del_insts) assms has_sum_SigmaD has_sum_cong has_sum_infsum)

lemma summable_on_UnionD:
  fixes f :: "'a \<Rightarrow> 'c :: {topological_comm_monoid_add,t3_space}"
  assumes sum1: "f summable_on (\<Union>x\<in>A. B x)"
  assumes sum2: "\<And>x. x \<in> A \<Longrightarrow> f summable_on (B x)"
  assumes disj: "disjoint_family_on B A"
  shows   "(\<lambda>x. infsum f (B x)) summable_on A"
proof -
  have "(\<Union>x\<in>A. B x) = snd ` Sigma A B"
    by (force simp: Sigma_def)
  with sum1 have "f summable_on (snd ` Sigma A B)"
    by simp
  also have "?this \<longleftrightarrow> (f \<circ> snd) summable_on (Sigma A B)"
    using disj by (intro summable_on_reindex inj_onI) (force simp: disjoint_family_on_def)
  finally show "(\<lambda>x. infsum f (B x)) summable_on A"
    using summable_on_SigmaD[of "f \<circ> snd" A B] sum2 by simp
qed

lemma summable_on_Union_iff:
  fixes f :: "_ \<Rightarrow> 'a :: {linorder_topology, ordered_comm_monoid_add, topological_comm_monoid_add,
                          conditionally_complete_linorder, t3_space}"
  assumes f: "\<And>x. x \<in> A \<Longrightarrow> (f has_sum g x) (B x)"
  assumes f_nonneg: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> f y \<ge> 0"
  assumes disj: "disjoint_family_on B A"
  shows   "f summable_on (\<Union>x\<in>A. B x) \<longleftrightarrow> g summable_on A"
proof
  assume "g summable_on A"
  thus "f summable_on (\<Union>x\<in>A. B x)"
    using summable_on_UnionI[of A f B g] assms by auto
next
  assume "f summable_on (\<Union>x\<in>A. B x)"
  hence "(\<lambda>x. infsum f (B x)) summable_on A"
    using assms by (intro summable_on_UnionD) (auto dest: has_sum_imp_summable)
  also have "?this \<longleftrightarrow> g summable_on A"
    using assms by (intro summable_on_cong) (auto simp: infsumI)
  finally show "g summable_on A" .
qed

lemma has_sum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add,uniform_space,uniform_topological_group_add}\<close>
  assumes summableAB: "(f has_sum a) (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> ((\<lambda>y. f (x, y)) has_sum (b x)) (B x)\<close>
  shows "(b has_sum a) A"
  by (intro has_sum_Sigma[OF _ assms] uniformly_continuous_add)

lemma abs_summable_on_comparison_test':
  assumes "g summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> norm (f x) \<le> g x"
  shows   "(\<lambda>x. norm (f x)) summable_on A"
proof (rule Infinite_Sum.abs_summable_on_comparison_test)
  have "g summable_on A \<longleftrightarrow> (\<lambda>x. norm (g x)) summable_on A"
    by (metis summable_on_iff_abs_summable_on_real)
  with assms show "(\<lambda>x. norm (g x)) summable_on A" by blast
qed (use assms in fastforce)

lemma has_sum_geometric_from_1:
  fixes z :: "'a :: {real_normed_field, banach}"
  assumes "norm z < 1"
  shows   "((\<lambda>n. z ^ n) has_sum (z / (1 - z))) {1..}"
proof -
  have [simp]: "z \<noteq> 1"
    using assms by auto
  have "(\<lambda>n. z ^ Suc n) sums (1 / (1 - z) - 1)"
    using geometric_sums[of z] assms by (subst sums_Suc_iff) auto
  also have "1 / (1 - z) - 1 = z / (1 - z)"
    by (auto simp: field_simps)
  finally have "(\<lambda>n. z ^ Suc n) sums (z / (1 - z))" .
  moreover have "summable (\<lambda>n. norm (z ^ Suc n))"
    using assms
    by (subst summable_Suc_iff) (auto simp: norm_power intro!: summable_geometric)
  ultimately have "((\<lambda>n. z ^ Suc n) has_sum (z / (1 - z))) UNIV"
    by (intro norm_summable_imp_has_sum)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. n-1" "\<lambda>n. n+1"]) auto
  finally show ?thesis .
qed 

lemma has_sum_divide_const:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, field, semiring_0}"
  shows "(f has_sum S) A \<Longrightarrow> ((\<lambda>x. f x / c) has_sum (S / c)) A"
  using has_sum_cmult_right[of f A S "inverse c"] by (simp add: field_simps)

lemma has_sum_uminusI:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, ring_1}"
  shows "(f has_sum S) A \<Longrightarrow> ((\<lambda>x. -f x) has_sum (-S)) A"
  using has_sum_cmult_right[of f A S "-1"] by simp

end


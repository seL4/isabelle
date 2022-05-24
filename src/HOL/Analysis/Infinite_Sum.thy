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
See, e.g., Definition 4.11 in \cite{conway2013course}.
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

definition has_sum :: \<open>('a \<Rightarrow> 'b :: {comm_monoid_add, topological_space}) \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>has_sum f A x \<longleftrightarrow> (sum f \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>

definition summable_on :: "('a \<Rightarrow> 'b::{comm_monoid_add, topological_space}) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "summable'_on" 46) where
  "f summable_on A \<longleftrightarrow> (\<exists>x. has_sum f A x)"

definition infsum :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infsum f A = (if f summable_on A then Lim (finite_subsets_at_top A) (sum f) else 0)"

abbreviation abs_summable_on :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a set \<Rightarrow> bool" (infixr "abs'_summable'_on" 46) where
  "f abs_summable_on A \<equiv> (\<lambda>x. norm (f x)) summable_on A"

syntax (ASCII)
  "_infsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_add"  ("(3INFSUM (_/:_)./ _)" [0, 51, 10] 10)
syntax
  "_infsum" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b::topological_comm_monoid_add"  ("(2\<Sum>\<^sub>\<infinity>(_/\<in>_)./ _)" [0, 51, 10] 10)
translations \<comment> \<open>Beware of argument permutation!\<close>
  "\<Sum>\<^sub>\<infinity>i\<in>A. b" \<rightleftharpoons> "CONST infsum (\<lambda>i. b) A"

syntax (ASCII)
  "_univinfsum" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3INFSUM _./ _)" [0, 10] 10)
syntax
  "_univinfsum" :: "pttrn \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Sum>\<^sub>\<infinity>_./ _)" [0, 10] 10)
translations
  "\<Sum>\<^sub>\<infinity>x. t" \<rightleftharpoons> "CONST infsum (\<lambda>x. t) (CONST UNIV)"

syntax (ASCII)
  "_qinfsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(3INFSUM _ |/ _./ _)" [0, 0, 10] 10)
syntax
  "_qinfsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"  ("(2\<Sum>\<^sub>\<infinity>_ | (_)./ _)" [0, 0, 10] 10)
translations
  "\<Sum>\<^sub>\<infinity>x|P. t" => "CONST infsum (\<lambda>x. t) {x. P}"

print_translation \<open>
let
  fun sum_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qinfsum"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | sum_tr' _ = raise Match;
in [(@{const_syntax infsum}, K sum_tr')] end
\<close>

subsection \<open>General properties\<close>

lemma infsumI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>has_sum f A x\<close>
  shows \<open>infsum f A = x\<close>
  by (metis assms finite_subsets_at_top_neq_bot infsum_def summable_on_def has_sum_def tendsto_Lim)

lemma infsum_eqI:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>x = y\<close>
  assumes \<open>has_sum f A x\<close>
  assumes \<open>has_sum g B y\<close>
  shows \<open>infsum f A = infsum g B\<close>
  by (metis assms(1) assms(2) assms(3) finite_subsets_at_top_neq_bot infsum_def summable_on_def has_sum_def tendsto_Lim)

lemma infsum_eqI':
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>\<And>x. has_sum f A x \<longleftrightarrow> has_sum g B x\<close>
  shows \<open>infsum f A = infsum g B\<close>
  by (metis assms infsum_def infsum_eqI summable_on_def)

lemma infsum_not_exists:
  fixes f :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, t2_space}\<close>
  assumes \<open>\<not> f summable_on A\<close>
  shows \<open>infsum f A = 0\<close>
  by (simp add: assms infsum_def)

lemma summable_iff_has_sum_infsum: "f summable_on A \<longleftrightarrow> has_sum f A (infsum f A)"
  using infsumI summable_on_def by blast

lemma has_sum_infsum[simp]:
  assumes \<open>f summable_on S\<close>
  shows \<open>has_sum f S (infsum f S)\<close>
  using assms by (auto simp: summable_on_def infsum_def has_sum_def tendsto_Lim)

lemma has_sum_cong_neutral:
  fixes f g :: \<open>'a \<Rightarrow> 'b::{comm_monoid_add, topological_space}\<close>
  assumes \<open>\<And>x. x\<in>T-S \<Longrightarrow> g x = 0\<close>
  assumes \<open>\<And>x. x\<in>S-T \<Longrightarrow> f x = 0\<close>
  assumes \<open>\<And>x. x\<in>S\<inter>T \<Longrightarrow> f x = g x\<close>
  shows "has_sum f S x \<longleftrightarrow> has_sum g T x"
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
        apply (rule F0_P)
        using \<open>F0 \<subseteq> S\<close>  \<open>finite F0\<close> that by auto
      also have \<open>sum f ((F\<inter>S) \<union> (F0\<inter>S)) = sum g F\<close>
        apply (rule sum.mono_neutral_cong)
        using that \<open>finite F0\<close> F0'_def assms by auto
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
        apply (rule F0_P)
        using \<open>F0 \<subseteq> T\<close>  \<open>finite F0\<close> that by auto
      also have \<open>sum g ((F\<inter>T) \<union> (F0\<inter>T)) = sum f F\<close>
        apply (rule sum.mono_neutral_cong)
        using that \<open>finite F0\<close> F0'_def assms by auto
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
  apply (rule infsum_eqI')
  using assms by (rule has_sum_cong_neutral)

lemma has_sum_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "has_sum f A x \<longleftrightarrow> has_sum g A x"
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
  assumes \<open>has_sum f B b\<close> and \<open>has_sum f A a\<close> and AB: "A \<subseteq> B"
  shows has_sum_Diff: "has_sum f (B - A) (b - a)"
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
  proof (subst asm_rl [of "(\<lambda>F. sum f (F\<inter>A)) = sum f o (\<lambda>F. F\<inter>A)"])
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
  hence limBA: "(sum f \<longlongrightarrow> b - a) (finite_subsets_at_top (B-A))"
    apply (rule tendsto_mono[rotated])
    by (rule finite_subsets1)
  thus ?thesis
    by (simp add: has_sum_def)
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
  assumes \<open>has_sum f A a\<close> and "has_sum g B b"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "a \<le> b"
proof -
  define f' g' where \<open>f' x = (if x \<in> A then f x else 0)\<close> and \<open>g' x = (if x \<in> B then g x else 0)\<close> for x
  have [simp]: \<open>f summable_on A\<close> \<open>g summable_on B\<close>
    using assms(1,2) summable_on_def by auto
  have \<open>has_sum f' (A\<union>B) a\<close>
    apply (subst has_sum_cong_neutral[where g=f and T=A])
    by (auto simp: f'_def assms(1))
  then have f'_lim: \<open>(sum f' \<longlongrightarrow> a) (finite_subsets_at_top (A\<union>B))\<close>
    by (meson has_sum_def)
  have \<open>has_sum g' (A\<union>B) b\<close>
    apply (subst has_sum_cong_neutral[where g=g and T=B])
    by (auto simp: g'_def assms(2))
  then have g'_lim: \<open>(sum g' \<longlongrightarrow> b) (finite_subsets_at_top (A\<union>B))\<close>
    using has_sum_def by blast

  have *: \<open>\<forall>\<^sub>F x in finite_subsets_at_top (A \<union> B). sum f' x \<le> sum g' x\<close>
    apply (rule eventually_finite_subsets_at_top_weakI)
    apply (rule sum_mono)
    using assms by (auto simp: f'_def g'_def)
  show ?thesis
    apply (rule tendsto_le)
    using * g'_lim f'_lim by auto
qed

lemma infsum_mono_neutral:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" and "g summable_on B"
  assumes \<open>\<And>x. x \<in> A\<inter>B \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>\<And>x. x \<in> A-B \<Longrightarrow> f x \<le> 0\<close>
  assumes \<open>\<And>x. x \<in> B-A \<Longrightarrow> g x \<ge> 0\<close>
  shows "infsum f A \<le> infsum g B"
  by (rule has_sum_mono_neutral[of f A _ g B _]) (use assms in \<open>auto intro: has_sum_infsum\<close>)

lemma has_sum_mono:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "has_sum f A x" and "has_sum g A y"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "x \<le> y"
  apply (rule has_sum_mono_neutral)
  using assms by auto

lemma infsum_mono:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
  shows "infsum f A \<le> infsum g A"
  apply (rule infsum_mono_neutral)
  using assms by auto

lemma has_sum_finite[simp]:
  assumes "finite F"
  shows "has_sum f F (sum f F)"
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
  using assms by (auto intro: tendsto_Lim simp: finite_subsets_at_top_finite infsum_def principal_eq_bot_iff)

lemma has_sum_finite_approximation:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "has_sum f A x" and "\<epsilon> > 0"
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
  from assms have "has_sum f A (infsum f A)"
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
  then obtain L' where \<open>(sum f \<longlongrightarrow> L') (finite_subsets_at_top A)\<close>
    apply atomize_elim unfolding filterlim_def
    apply (rule complete_uniform[where S=UNIV, simplified, THEN iffD1, rule_format])
      apply (auto simp add: filtermap_bot_iff)
    by (meson Cauchy_convergent UNIV_I complete_def convergent_def)
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
  assumes "has_sum (\<lambda>x. norm (f x)) A n"
  assumes "has_sum f A a"
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
      apply (rule add_right_mono)
      apply (rule has_sum_mono_neutral[where A=F and B=A and f=\<open>\<lambda>x. norm (f x)\<close> and g=\<open>\<lambda>x. norm (f x)\<close>])
      using \<open>finite F\<close> \<open>F \<subseteq> A\<close> assms by auto
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
  show ?thesis
    apply (rule norm_has_sum_bound[where A=A and f=f and a=\<open>infsum f A\<close> and n=\<open>infsum (\<lambda>x. norm (f x)) A\<close>])
    using assms True
    by (metis finite_subsets_at_top_neq_bot infsum_def summable_on_def has_sum_def tendsto_Lim)+
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
    proof-
      have "closed {s::real. s \<ge> 0}"
        using Elementary_Topology.closed_sequential_limits[where S = "{s::real. s \<ge> 0}"]
        by (metis Lim_bounded2 mem_Collect_eq)
      moreover have "{s::real. s \<ge> 0} = UNIV - S"
        unfolding S_def by auto
      ultimately have "closed (UNIV - S)"
        by simp
      thus ?thesis
        by (simp add: Compl_eq_Diff_UNIV open_closed) 
    qed
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
  using assms by (simp flip: has_sum_def)


lemma has_sum_0: 
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>has_sum f M 0\<close>
  unfolding has_sum_def
  apply (subst tendsto_cong[where g=\<open>\<lambda>_. 0\<close>])
   apply (rule eventually_finite_subsets_at_top_weakI)
  using assms by (auto simp add: subset_iff)

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
lemma has_sum_0_simp[simp]: \<open>has_sum (\<lambda>_. 0) M 0\<close>
  by (simp_all add: has_sum_0)


lemma has_sum_add:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add}"
  assumes \<open>has_sum f A a\<close>
  assumes \<open>has_sum g A b\<close>
  shows \<open>has_sum (\<lambda>x. f x + g x) A (a + b)\<close>
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
  by (metis (full_types) assms(1) assms(2) summable_on_def has_sum_add)

lemma infsum_add:
  fixes f g :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add, t2_space}"
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>infsum (\<lambda>x. f x + g x) A = infsum f A + infsum g A\<close>
proof -
  have \<open>has_sum (\<lambda>x. f x + g x) A (infsum f A + infsum g A)\<close>
    by (simp add: assms(1) assms(2) has_sum_add)
  then show ?thesis
    using infsumI by blast
qed


lemma has_sum_Un_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes "has_sum f A a"
  assumes "has_sum f B b"
  assumes disj: "A \<inter> B = {}"
  shows \<open>has_sum f (A \<union> B) (a + b)\<close>
proof -
  define fA fB where \<open>fA x = (if x \<in> A then f x else 0)\<close>
    and \<open>fB x = (if x \<notin> A then f x else 0)\<close> for x
  have fA: \<open>has_sum fA (A \<union> B) a\<close>
    apply (subst has_sum_cong_neutral[where T=A and g=f])
    using assms by (auto simp: fA_def)
  have fB: \<open>has_sum fB (A \<union> B) b\<close>
    apply (subst has_sum_cong_neutral[where T=B and g=f])
    using assms by (auto simp: fB_def)
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
  by (meson assms(1) assms(2) disj summable_on_def has_sum_Un_disjoint)

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
  shows   "has_sum f (UNIV :: nat set) S"
  unfolding has_sum_def tendsto_iff eventually_finite_subsets_at_top
proof (safe, goal_cases)
  case (1 \<epsilon>)
  from assms(1) obtain S' where S': "(\<lambda>n. norm (f n)) sums S'"
    by (auto simp: summable_def)
  with 1 obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> \<bar>S' - (\<Sum>i<n. norm (f i))\<bar> < \<epsilon>"
    by (auto simp: tendsto_iff eventually_at_top_linorder sums_def dist_norm abs_minus_commute)
  
  show ?case
  proof (rule exI[of _ "{..<N}"], safe, goal_cases)
    case (2 Y)
    from 2 have "(\<lambda>n. if n \<in> Y then 0 else f n) sums (S - sum f Y)"
      by (intro sums_If_finite_set'[OF \<open>f sums S\<close>]) (auto simp: sum_negf)
    hence "S - sum f Y = (\<Sum>n. if n \<in> Y then 0 else f n)"
      by (simp add: sums_iff)
    also have "norm \<dots> \<le> (\<Sum>n. norm (if n \<in> Y then 0 else f n))"
      by (rule summable_norm[OF summable_comparison_test'[OF assms(1)]]) auto
    also have "\<dots> \<le> (\<Sum>n. if n < N then 0 else norm (f n))"
      using 2 by (intro suminf_le summable_comparison_test'[OF assms(1)]) auto
    also have "(\<lambda>n. if n \<in> {..<N} then 0 else norm (f n)) sums (S' - (\<Sum>i<N. norm (f i)))" 
      by (intro sums_If_finite_set'[OF S']) (auto simp: sum_negf)
    hence "(\<Sum>n. if n < N then 0 else norm (f n)) = S' - (\<Sum>i<N. norm (f i))"
      by (simp add: sums_iff)
    also have "S' - (\<Sum>i<N. norm (f i)) \<le> \<bar>S' - (\<Sum>i<N. norm (f i))\<bar>" by simp
    also have "\<dots> < \<epsilon>" by (rule N) auto
    finally show ?case by (simp add: dist_norm norm_minus_commute)
  qed auto
qed

lemma norm_summable_imp_summable_on:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "summable (\<lambda>n. norm (f n))"
  shows   "f summable_on UNIV"
  using norm_summable_imp_has_sum[OF assms, of "suminf f"] assms
  by (auto simp: sums_iff summable_on_def dest: summable_norm_cancel)

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

lemma summable_on_subset:
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

    show \<open>eventually E (?filter_fB \<times>\<^sub>F ?filter_fB)\<close>
      unfolding eventually_prod_filter
    proof (safe intro!: exI)
      show "eventually (\<lambda>x. E' (x, sum f F0B)) (filtermap (sum f) (finite_subsets_at_top B))"
       and "eventually (\<lambda>x. E' (sum f F0B, x)) (filtermap (sum f) (finite_subsets_at_top B))"
        unfolding eventually_filtermap eventually_finite_subsets_at_top
        by (rule exI[of _ F0B]; use * in \<open>force simp: F0B_def\<close>)+
    next
      show "E (x, y)" if "E' (x, sum f F0B)" and "E' (sum f F0B, y)" for x y
        using E'E'E that by blast
    qed
  qed

  then obtain x where \<open>?filter_fB \<le> nhds x\<close>
    using cauchy_filter_complete_converges[of ?filter_fB UNIV] \<open>complete (UNIV :: _)\<close>
    by (auto simp: filtermap_bot_iff)
  then have \<open>(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)\<close>
    by (auto simp: filterlim_def)
  then show ?thesis
    by (auto simp: summable_on_def has_sum_def)
qed

text \<open>A special case of @{thm [source] summable_on_subset} for Banach spaces with less premises.\<close>

lemma summable_on_subset_banach:
  fixes A B and f :: \<open>'a \<Rightarrow> 'b::banach\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>B \<subseteq> A\<close>
  shows \<open>f summable_on B\<close>
  by (rule summable_on_subset[OF _ _ assms])
     (auto simp: complete_def convergent_def dest!: Cauchy_convergent)

lemma has_sum_empty[simp]: \<open>has_sum f {} 0\<close>
  by (meson ex_in_conv has_sum_0)

lemma summable_on_empty[simp]: \<open>f summable_on {}\<close>
  by auto

lemma infsum_empty[simp]: \<open>infsum f {} = 0\<close>
  by simp

lemma sum_has_sum:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> has_sum f (B a) (s a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>has_sum f (\<Union>a\<in>A. B a) (sum s A)\<close>
  using assms
proof (insert finite conv disj, induction)
  case empty
  then show ?case 
    by simp
next
  case (insert x A)
  have \<open>has_sum f (B x) (s x)\<close>
    by (simp add: insert.prems)
  moreover have IH: \<open>has_sum f (\<Union>a\<in>A. B a) (sum s A)\<close>
    using insert by simp
  ultimately have \<open>has_sum f (B x \<union> (\<Union>a\<in>A. B a)) (s x + sum s A)\<close>
    apply (rule has_sum_Un_disjoint)
    using insert by auto
  then show ?case
    using insert.hyps by auto
qed


lemma summable_on_finite_union_disjoint:
  fixes f :: "'a \<Rightarrow> 'b::topological_comm_monoid_add"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f summable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>f summable_on (\<Union>a\<in>A. B a)\<close>
  using finite conv disj apply induction by (auto intro!: summable_on_Un_disjoint)

lemma sum_infsum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_comm_monoid_add, t2_space}"
  assumes finite: \<open>finite A\<close>
  assumes conv: \<open>\<And>a. a \<in> A \<Longrightarrow> f summable_on (B a)\<close>
  assumes disj: \<open>\<And>a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a\<noteq>a' \<Longrightarrow> B a \<inter> B a' = {}\<close>
  shows \<open>sum (\<lambda>a. infsum f (B a)) A = infsum f (\<Union>a\<in>A. B a)\<close>
  by (rule sym, rule infsumI)
     (use sum_has_sum[of A f B \<open>\<lambda>a. infsum f (B a)\<close>] assms in auto)

text \<open>The lemmas \<open>infsum_comm_additive_general\<close> and \<open>infsum_comm_additive\<close> (and variants) below both state that the infinite sum commutes with
  a continuous additive function. \<open>infsum_comm_additive_general\<close> is stated more for more general type classes
  at the expense of a somewhat less compact formulation of the premises.
  E.g., by avoiding the constant \<^const>\<open>additive\<close> which introduces an additional sort constraint
  (group instead of monoid). For example, extended reals (\<^typ>\<open>ereal\<close>, \<^typ>\<open>ennreal\<close>) are not covered
  by \<open>infsum_comm_additive\<close>.\<close>


lemma has_sum_comm_additive_general: 
  fixes f :: \<open>'b :: {comm_monoid_add,topological_space} \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes cont: \<open>f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes infsum: \<open>has_sum g S x\<close>
  shows \<open>has_sum (f o g) S (f x)\<close> 
proof -
  have \<open>(sum g \<longlongrightarrow> x) (finite_subsets_at_top S)\<close>
    using infsum has_sum_def by blast
  then have \<open>((f o sum g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_compose_at)
    using assms by auto
  then have \<open>(sum (f o g) \<longlongrightarrow> f x) (finite_subsets_at_top S)\<close>
    apply (rule tendsto_cong[THEN iffD1, rotated])
    using f_sum by fastforce
  then show \<open>has_sum (f o g) S (f x)\<close>
    using has_sum_def by blast 
qed

lemma summable_on_comm_additive_general:
  fixes f :: \<open>'b :: {comm_monoid_add,topological_space} \<Rightarrow> 'c :: {comm_monoid_add,topological_space}\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
    \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>\<And>x. has_sum g S x \<Longrightarrow> f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f o g) summable_on S\<close>
  by (meson assms summable_on_def has_sum_comm_additive_general has_sum_def infsum_tendsto)

lemma infsum_comm_additive_general:
  fixes f :: \<open>'b :: {comm_monoid_add,t2_space} \<Rightarrow> 'c :: {comm_monoid_add,t2_space}\<close>
  assumes f_sum: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> sum (f o g) F = f (sum g F)\<close>
      \<comment> \<open>Not using \<^const>\<open>additive\<close> because it would add sort constraint \<^class>\<open>ab_group_add\<close>\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f o g) S = f (infsum g S)\<close>
  using assms
  by (intro infsumI has_sum_comm_additive_general has_sum_infsum) (auto simp: isCont_def)

lemma has_sum_comm_additive: 
  fixes f :: \<open>'b :: {ab_group_add,topological_space} \<Rightarrow> 'c :: {ab_group_add,topological_space}\<close>
  assumes \<open>additive f\<close>
  assumes \<open>f \<midarrow>x\<rightarrow> f x\<close>
    \<comment> \<open>For \<^class>\<open>t2_space\<close>, this is equivalent to \<open>isCont f x\<close> by @{thm [source] isCont_def}.\<close>
  assumes infsum: \<open>has_sum g S x\<close>
  shows \<open>has_sum (f o g) S (f x)\<close>
  using assms
  by (intro has_sum_comm_additive_general has_sum_infsum) (auto simp: isCont_def additive.sum) 

lemma summable_on_comm_additive:
  fixes f :: \<open>'b :: {ab_group_add,t2_space} \<Rightarrow> 'c :: {ab_group_add,topological_space}\<close>
  assumes \<open>additive f\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f o g) summable_on S\<close>
  by (meson assms(1) assms(2) assms(3) summable_on_def has_sum_comm_additive has_sum_infsum isContD)

lemma infsum_comm_additive:
  fixes f :: \<open>'b :: {ab_group_add,t2_space} \<Rightarrow> 'c :: {ab_group_add,t2_space}\<close>
  assumes \<open>additive f\<close>
  assumes \<open>isCont f (infsum g S)\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>infsum (f o g) S = f (infsum g S)\<close>
  by (rule infsum_comm_additive_general; auto simp: assms additive.sum)

lemma nonneg_bdd_above_has_sum:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>has_sum f A (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
proof -
  have \<open>(sum f \<longlongrightarrow> (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)) (finite_subsets_at_top A)\<close>
  proof (rule order_tendstoI)
    fix a assume \<open>a < (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
    then obtain F where \<open>a < sum f F\<close> and \<open>finite F\<close> and \<open>F \<subseteq> A\<close>
      by (metis (mono_tags, lifting) Collect_cong Collect_empty_eq assms(2) empty_subsetI finite.emptyI less_cSUP_iff mem_Collect_eq)
    show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. a < sum f x\<close>
      unfolding eventually_finite_subsets_at_top
    proof (rule exI[of _ F], safe)
      fix Y assume Y: "finite Y" "F \<subseteq> Y" "Y \<subseteq> A"
      have "a < sum f F"
        by fact
      also have "\<dots> \<le> sum f Y"
        using assms Y by (intro sum_mono2) auto
      finally show "a < sum f Y" .
    qed (use \<open>finite F\<close> \<open>F \<subseteq> A\<close> in auto)
  next
    fix a assume *: \<open>(SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F) < a\<close>
    have \<open>sum f F < a\<close> if \<open>F\<subseteq>A\<close> and \<open>finite F\<close> for F
    proof -
      have "sum f F \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)"
        by (rule cSUP_upper) (use that assms(2) in \<open>auto simp: conj_commute\<close>)
      also have "\<dots> < a"
        by fact
      finally show ?thesis .
    qed
    then show \<open>\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x < a\<close>
      by (rule eventually_finite_subsets_at_top_weakI)
  qed
  then show ?thesis
    using has_sum_def by blast
qed

lemma nonneg_bdd_above_summable_on:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>f summable_on A\<close>
  using assms(1) assms(2) summable_on_def nonneg_bdd_above_has_sum by blast

lemma nonneg_bdd_above_infsum:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {conditionally_complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes \<open>bdd_above (sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>infsum f A = (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
  using assms by (auto intro!: infsumI nonneg_bdd_above_has_sum)

lemma nonneg_has_sum_complete:
  fixes f :: \<open>'a \<Rightarrow> 'b :: {complete_linorder, ordered_comm_monoid_add, linorder_topology}\<close>
  assumes \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>has_sum f A (SUP F\<in>{F. finite F \<and> F\<subseteq>A}. sum f F)\<close>
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
  assumes "has_sum f M a"
    and "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "a \<ge> 0"
  by (metis (no_types, lifting) DiffD1 assms(1) assms(2) empty_iff has_sum_0 has_sum_mono_neutral order_refl)

lemma infsum_nonneg:
  fixes f :: "'a \<Rightarrow> 'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0" (is "?lhs \<ge> _")
  apply (cases \<open>f summable_on M\<close>)
   apply (metis assms infsum_0_simp summable_on_0_simp infsum_mono)
  using assms by (auto simp add: infsum_not_exists)

lemma has_sum_mono2:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "has_sum f A S" "has_sum f B S'" "A \<subseteq> B"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows   "S \<le> S'"
proof -
  have "has_sum f (B - A) (S' - S)"
    by (rule has_sum_Diff) fact+
  hence "S' - S \<ge> 0"
    by (rule has_sum_nonneg) (use assms(4) in auto)
  thus ?thesis
    by (metis add_0 add_mono_thms_linordered_semiring(3) diff_add_cancel)
qed

lemma infsum_mono2:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" "f summable_on B" "A \<subseteq> B"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> f x \<ge> 0"
  shows   "infsum f A \<le> infsum f B"
  by (rule has_sum_mono2[OF has_sum_infsum has_sum_infsum]) (use assms in auto)

lemma finite_sum_le_has_sum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "has_sum f A S" "finite B" "B \<subseteq> A"
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x \<ge> 0"
  shows   "sum f B \<le> S"
proof (rule has_sum_mono2)
  show "has_sum f A S"
    by fact
  show "has_sum f B (sum f B)"
    by (rule has_sum_finite) fact+
qed (use assms in auto)

lemma finite_sum_le_infsum:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, ordered_comm_monoid_add,linorder_topology}"
  assumes "f summable_on A" "finite B" "B \<subseteq> A"
  assumes "\<And>x. x \<in> A - B \<Longrightarrow> f x \<ge> 0"
  shows   "sum f B \<le> infsum f A"
  by (rule finite_sum_le_has_sum[OF has_sum_infsum]) (use assms in auto)

lemma has_sum_reindex:
  assumes \<open>inj_on h A\<close>
  shows \<open>has_sum g (h ` A) x \<longleftrightarrow> has_sum (g \<circ> h) A x\<close>
proof -
  have \<open>has_sum g (h ` A) x \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top (h ` A))\<close>
    by (simp add: has_sum_def)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>F. sum g (h ` F)) \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>
    apply (subst filtermap_image_finite_subsets_at_top[symmetric])
    using assms by (auto simp: filterlim_def filtermap_filtermap)
  also have \<open>\<dots> \<longleftrightarrow> (sum (g \<circ> h) \<longlongrightarrow> x) (finite_subsets_at_top A)\<close>
    apply (rule tendsto_cong)
    apply (rule eventually_finite_subsets_at_top_weakI)
    apply (rule sum.reindex)
    using assms subset_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> has_sum (g \<circ> h) A x\<close>
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
  by (metis (no_types, opaque_lifting) assms finite_subsets_at_top_neq_bot infsum_def 
        summable_on_reindex has_sum_def has_sum_infsum has_sum_reindex tendsto_Lim)

lemma summable_on_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "(\<lambda>x. f (g x)) summable_on A \<longleftrightarrow> f summable_on B"
proof -
  thm summable_on_reindex
  have \<open>(\<lambda>x. f (g x)) summable_on A \<longleftrightarrow> f summable_on g ` A\<close>
    apply (rule summable_on_reindex[symmetric, unfolded o_def])
    using assms bij_betw_imp_inj_on by blast
  also have \<open>\<dots> \<longleftrightarrow> f summable_on B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed

lemma infsum_reindex_bij_betw:
  assumes "bij_betw g A B"
  shows   "infsum (\<lambda>x. f (g x)) A = infsum f B"
proof -
  have \<open>infsum (\<lambda>x. f (g x)) A = infsum f (g ` A)\<close>
    by (metis (mono_tags, lifting) assms bij_betw_imp_inj_on infsum_cong infsum_reindex o_def)
  also have \<open>\<dots> = infsum f B\<close>
    using assms bij_betw_imp_surj_on by blast
  finally show ?thesis .
qed

lemma sum_uniformity:
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'b::{uniform_space,comm_monoid_add},y). x+y)\<close>
  assumes \<open>eventually E uniformity\<close>
  obtains D where \<open>eventually D uniformity\<close> 
    and \<open>\<And>M::'a set. \<And>f f' :: 'a \<Rightarrow> 'b. card M \<le> n \<and> (\<forall>m\<in>M. D (f m, f' m)) \<Longrightarrow> E (sum f M, sum f' M)\<close>
proof (atomize_elim, insert \<open>eventually E uniformity\<close>, induction n arbitrary: E rule:nat_induct)
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
  with \<open>eventually D uniformity\<close>
  show ?case 
    by auto
qed

lemma has_sum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add,uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "has_sum f (Sigma A B) a"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> has_sum (\<lambda>y. f (x, y)) (B x) (b x)\<close>
  shows "has_sum b A a"
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
    apply (subst asm_rl[of \<open>{b| b. (a,b) \<in> H} = snd ` {ab. ab \<in> H \<and> fst ab = a}\<close>])
    by (auto simp: image_iff that)

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
          apply (rule sum_uniformity[OF plus_cont \<open>eventually D uniformity\<close>, where n=\<open>card M\<close>])
          by auto
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
            apply (subst sum.Sigma)
            using \<open>finite M\<close> by auto
          have \<open>D' (b a, sum (\<lambda>b. f (a,b)) (Ha' a))\<close> if \<open>a \<in> M\<close> for a
            apply (rule D'_sum_Ha)
            using that \<open>M \<subseteq> A\<close> by auto
          then have \<open>D (\<Sum>a\<in>M. b a, \<Sum>a\<in>M. sum (\<lambda>b. f (a,b)) (Ha' a))\<close>
            by (rule_tac D'_sum_D, auto)
          with * show ?thesis
            by auto
        qed
        moreover have \<open>Sigma M Ha \<subseteq> Sigma M B\<close>
          using Ha_B \<open>M \<subseteq> A\<close> by auto
        ultimately show ?thesis
          unfolding FMB_def eventually_finite_subsets_at_top
          by (intro exI[of _ "Sigma M Ha"])
             (use Ha_fin that(2,3) in \<open>fastforce intro!: finite_SigmaI\<close>)
      qed
      moreover have \<open>eventually (\<lambda>H. D (\<Sum>(a,b)\<in>H. f (a,b), a)) FMB\<close>
        unfolding FMB_def eventually_finite_subsets_at_top
      proof (rule exI[of _ G], safe)
        fix Y assume Y: "finite Y" "G \<subseteq> Y" "Y \<subseteq> Sigma M B"
        have "Y \<subseteq> Sigma A B"
          using Y \<open>M \<subseteq> A\<close> by blast
        thus "D (\<Sum>(a,b)\<in>Y. f (a, b), a)"
          using G_sum[of Y] Y by auto
      qed (use \<open>finite G\<close> \<open>G \<subseteq> Sigma A B\<close> that in auto)
      ultimately have \<open>\<forall>\<^sub>F x in FMB. E (sum b M, a)\<close>
        by eventually_elim (use DDE' in auto)
      then show \<open>E (sum b M, a)\<close>
        by (rule eventually_const[THEN iffD1, rotated]) (force simp: FMB_def)
    qed
    then show \<open>\<forall>\<^sub>F x in FA. E (sum b x, a)\<close>
      using \<open>finite (fst ` G)\<close> and \<open>fst ` G \<subseteq> A\<close>
      by (auto intro!: exI[of _ \<open>fst ` G\<close>] simp add: FA_def eventually_finite_subsets_at_top)
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
  from summableAB obtain a where a: \<open>has_sum (\<lambda>(x,y). f x y) (Sigma A B) a\<close>
    using has_sum_infsum by blast
  from summableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> has_sum (f x) (B x) (infsum (f x) (B x))\<close>
    by (auto intro!: has_sum_infsum)
  show ?thesis
    using plus_cont a b 
    by (auto intro: has_sum_Sigma[where f=\<open>\<lambda>(x,y). f x y\<close>, simplified] simp: summable_on_def)
qed

lemma infsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::{comm_monoid_add, t2_space, uniform_space}\<close>
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes summableAB: "f summable_on (Sigma A B)"
  assumes summableB: \<open>\<And>x. x\<in>A \<Longrightarrow> (\<lambda>y. f (x, y)) summable_on (B x)\<close>
  shows "infsum f (Sigma A B) = infsum (\<lambda>x. infsum (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from summableAB have a: \<open>has_sum f (Sigma A B) (infsum f (Sigma A B))\<close>
    using has_sum_infsum by blast
  from summableB have b: \<open>\<And>x. x\<in>A \<Longrightarrow> has_sum (\<lambda>y. f (x, y)) (B x) (infsum (\<lambda>y. f (x, y)) (B x))\<close>
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
  have [simp]: \<open>(f x) summable_on (B x)\<close> if \<open>x \<in> A\<close> for x
  proof -
    from assms
    have \<open>(\<lambda>(x,y). f x y) summable_on (Pair x ` B x)\<close>
      by (meson image_subset_iff summable_on_subset_banach mem_Sigma_iff that)
    then have \<open>((\<lambda>(x,y). f x y) o Pair x) summable_on (B x)\<close>
      apply (rule_tac summable_on_reindex[THEN iffD1])
      by (simp add: inj_on_def)
    then show ?thesis
      by (auto simp: o_def)
  qed
  show ?thesis1
    apply (rule infsum_Sigma')
    by auto
  show ?thesis2
    apply (rule summable_on_Sigma)
    by auto
qed

lemma infsum_Sigma_banach:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
    and f :: \<open>'a \<times> 'b \<Rightarrow> 'c::banach\<close>
  assumes [simp]: "f summable_on (Sigma A B)"
  shows \<open>infsum (\<lambda>x. infsum (\<lambda>y. f (x,y)) (B x)) A = infsum f (Sigma A B)\<close>
  using assms
  by (subst infsum_Sigma'_banach) auto

lemma infsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{comm_monoid_add,t2_space,uniform_space}"
  assumes plus_cont: \<open>uniformly_continuous_on UNIV (\<lambda>(x::'c,y). x+y)\<close>
  assumes \<open>(\<lambda>(x, y). f x y) summable_on (A \<times> B)\<close>
  assumes \<open>\<And>a. a\<in>A \<Longrightarrow> (f a) summable_on B\<close>
  assumes \<open>\<And>b. b\<in>B \<Longrightarrow> (\<lambda>a. f a b) summable_on A\<close>
  shows \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
proof -
  have [simp]: \<open>(\<lambda>(x, y). f y x) summable_on (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst summable_on_reindex)
    using assms by (auto simp: o_def)
  have \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    apply (subst infsum_Sigma)
    using assms by auto
  also have \<open>\<dots> = infsum (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infsum_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
    apply (subst infsum_Sigma)
    using assms by auto
  finally show ?thesis .
qed

lemma infsum_swap_banach:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::banach"
  assumes \<open>(\<lambda>(x, y). f x y) summable_on (A \<times> B)\<close>
  shows "infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B"
proof -
  have [simp]: \<open>(\<lambda>(x, y). f y x) summable_on (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst summable_on_reindex)
    using assms by (auto simp: o_def)
  have \<open>infsum (\<lambda>x. infsum (\<lambda>y. f x y) B) A = infsum (\<lambda>(x,y). f x y) (A \<times> B)\<close>
    apply (subst infsum_Sigma'_banach)
    using assms by auto
  also have \<open>\<dots> = infsum (\<lambda>(x,y). f y x) (B \<times> A)\<close>
    apply (subst product_swap[symmetric])
    apply (subst infsum_reindex)
    using assms by (auto simp: o_def)
  also have \<open>\<dots> = infsum (\<lambda>y. infsum (\<lambda>x. f x y) A) B\<close>
    apply (subst infsum_Sigma'_banach)
    using assms by auto
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
  assumes "has_sum f A a" \<open>a \<le> 0\<close>
    and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
  by (metis assms(1) assms(2) assms(4) infsumI nonneg_infsum_le_0D summable_on_def nneg)

lemma has_sum_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, semiring_0}"
  assumes \<open>has_sum f A a\<close>
  shows "has_sum (\<lambda>x. f x * c) A (a * c)"
proof -
  from assms have \<open>(sum f \<longlongrightarrow> a) (finite_subsets_at_top A)\<close>
    using has_sum_def by blast
  then have \<open>((\<lambda>F. sum f F * c) \<longlongrightarrow> a * c) (finite_subsets_at_top A)\<close>
    by (simp add: tendsto_mult_right)
  then have \<open>(sum (\<lambda>x. f x * c) \<longlongrightarrow> a * c) (finite_subsets_at_top A)\<close>
    apply (rule tendsto_cong[THEN iffD1, rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    using sum_distrib_right by blast
  then show ?thesis
    using infsumI has_sum_def by blast
qed

lemma infsum_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>c \<noteq> 0 \<Longrightarrow> f summable_on A\<close>
  shows "infsum (\<lambda>x. f x * c) A = infsum f A * c"
proof (cases \<open>c=0\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then have \<open>has_sum f A (infsum f A)\<close>
    by (simp add: assms)
  then show ?thesis
    by (auto intro!: infsumI has_sum_cmult_left)
qed

lemma summable_on_cmult_left:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>f summable_on A\<close>
  shows "(\<lambda>x. f x * c) summable_on A"
  using assms summable_on_def has_sum_cmult_left by blast

lemma has_sum_cmult_right:
  fixes f :: "'a \<Rightarrow> 'b :: {topological_semigroup_mult, semiring_0}"
  assumes \<open>has_sum f A a\<close>
  shows "has_sum (\<lambda>x. c * f x) A (c * a)"
proof -
  from assms have \<open>(sum f \<longlongrightarrow> a) (finite_subsets_at_top A)\<close>
    using has_sum_def by blast
  then have \<open>((\<lambda>F. c * sum f F) \<longlongrightarrow> c * a) (finite_subsets_at_top A)\<close>
    by (simp add: tendsto_mult_left)
  then have \<open>(sum (\<lambda>x. c * f x) \<longlongrightarrow> c * a) (finite_subsets_at_top A)\<close>
    apply (rule tendsto_cong[THEN iffD1, rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    using sum_distrib_left by blast
  then show ?thesis
    using infsumI has_sum_def by blast
qed

lemma infsum_cmult_right:
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, semiring_0}"
  assumes \<open>c \<noteq> 0 \<Longrightarrow> f summable_on A\<close>
  shows \<open>infsum (\<lambda>x. c * f x) A = c * infsum f A\<close>
proof (cases \<open>c=0\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then have \<open>has_sum f A (infsum f A)\<close>
    by (simp add: assms)
  then show ?thesis
    by (auto intro!: infsumI has_sum_cmult_right)
qed

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
    by (metis (no_types, lifting) assms summable_on_cong mult.assoc mult.right_neutral right_inverse)
qed

lemma summable_on_cmult_right':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  assumes \<open>c \<noteq> 0\<close>
  shows "(\<lambda>x. c * f x) summable_on A \<longleftrightarrow> f summable_on A"
proof
  assume \<open>f summable_on A\<close>
  then show \<open>(\<lambda>x. c * f x) summable_on A\<close>
    by (rule summable_on_cmult_right)
next
  assume \<open>(\<lambda>x. c * f x) summable_on A\<close>
  then have \<open>(\<lambda>x. inverse c * (c * f x)) summable_on A\<close>
    by (rule summable_on_cmult_right)
  then show \<open>f summable_on A\<close>
    by (metis (no_types, lifting) assms summable_on_cong left_inverse mult.assoc mult.left_neutral)
qed

lemma infsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space, topological_semigroup_mult, division_ring}"
  shows "infsum (\<lambda>x. f x * c) A = infsum f A * c"
proof (cases \<open>c \<noteq> 0 \<longrightarrow> f summable_on A\<close>)
  case True
  then show ?thesis
    apply (rule_tac infsum_cmult_left) by auto
next
  case False
  note asm = False
  then show ?thesis
  proof (cases \<open>c=0\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    with asm have nex: \<open>\<not> f summable_on A\<close>
      by simp
    moreover have nex': \<open>\<not> (\<lambda>x. f x * c) summable_on A\<close>
      using asm False apply (subst summable_on_cmult_left') by auto
    ultimately show ?thesis
      unfolding infsum_def by simp
  qed
qed

lemma infsum_cmult_right':
  fixes f :: "'a \<Rightarrow> 'b :: {t2_space,topological_semigroup_mult,division_ring}"
  shows "infsum (\<lambda>x. c * f x) A = c * infsum f A"
proof (cases \<open>c \<noteq> 0 \<longrightarrow> f summable_on A\<close>)
  case True
  then show ?thesis
    apply (rule_tac infsum_cmult_right) by auto
next
  case False
  note asm = False
  then show ?thesis
  proof (cases \<open>c=0\<close>)
    case True
    then show ?thesis by auto
  next
    case False
    with asm have nex: \<open>\<not> f summable_on A\<close>
      by simp
    moreover have nex': \<open>\<not> (\<lambda>x. c * f x) summable_on A\<close>
      using asm False apply (subst summable_on_cmult_right') by auto
    ultimately show ?thesis
      unfolding infsum_def by simp
  qed
qed


lemma has_sum_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>has_sum (\<lambda>_. c) F (of_nat (card F) * c)\<close>
  by (metis assms has_sum_finite sum_constant)

lemma infsum_constant[simp]:
  assumes \<open>finite F\<close>
  shows \<open>infsum (\<lambda>_. c) F = of_nat (card F) * c\<close>
  apply (subst infsum_finite[OF assms]) by simp

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
  apply (cases \<open>finite A\<close>)
   apply simp
  apply (cases \<open>c = 0\<close>)
   apply simp
  by (simp add: infsum_diverge_constant infsum_not_exists)

lemma has_sum_uminus:
  fixes f :: \<open>'a \<Rightarrow> 'b::topological_ab_group_add\<close>
  shows \<open>has_sum (\<lambda>x. - f x) A a \<longleftrightarrow> has_sum f A (- a)\<close>
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
  assumes \<open>has_sum f A a\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>a \<le> b\<close>
proof -
  from assms(1)
  have 1: \<open>(sum f \<longlongrightarrow> a) (finite_subsets_at_top A)\<close>
    unfolding has_sum_def .
  from assms(2)
  have 2: \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. sum f F \<le> b\<close>
    by (rule_tac eventually_finite_subsets_at_top_weakI)
  show \<open>a \<le> b\<close>
    using _ _ 1 2
    apply (rule tendsto_le[where f=\<open>\<lambda>_. b\<close>])
    by auto
qed

lemma infsum_le_finite_sums:
  fixes b :: \<open>'a::{comm_monoid_add,topological_space,linorder_topology}\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>infsum f A \<le> b\<close>
  by (meson assms(1) assms(2) has_sum_infsum has_sum_le_finite_sums)


lemma summable_on_scaleR_left [intro]:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. f x *\<^sub>R c) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>R c) = (\<lambda>y. y *\<^sub>R c) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleR_left.additive_axioms)


lemma summable_on_scaleR_right [intro]:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "(\<lambda>x. c *\<^sub>R f x) summable_on A"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>R f x) = (\<lambda>y. c *\<^sub>R y) o f\<close>], simp add: o_def)
   apply (rule summable_on_comm_additive)
  using assms by (auto simp add: scaleR_right.additive_axioms)

lemma infsum_scaleR_left:
  fixes c :: \<open>'a :: real_normed_vector\<close>
  assumes "c \<noteq> 0 \<Longrightarrow> f summable_on A"
  shows   "infsum (\<lambda>x. f x *\<^sub>R c) A = infsum f A *\<^sub>R c"
  apply (cases \<open>c \<noteq> 0\<close>)
   apply (subst asm_rl[of \<open>(\<lambda>x. f x *\<^sub>R c) = (\<lambda>y. y *\<^sub>R c) o f\<close>], simp add: o_def)
   apply (rule infsum_comm_additive)
  using assms by (auto simp add: scaleR_left.additive_axioms)

lemma infsum_scaleR_right:
  fixes f :: \<open>'a \<Rightarrow> 'b :: real_normed_vector\<close>
  shows   "infsum (\<lambda>x. c *\<^sub>R f x) A = c *\<^sub>R infsum f A"
proof -
  consider (summable) \<open>f summable_on A\<close> | (c0) \<open>c = 0\<close> | (not_summable) \<open>\<not> f summable_on A\<close> \<open>c \<noteq> 0\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (subst asm_rl[of \<open>(\<lambda>x. c *\<^sub>R f x) = (\<lambda>y. c *\<^sub>R y) o f\<close>], simp add: o_def)
      apply (rule infsum_comm_additive)
      using summable by (auto simp add: scaleR_right.additive_axioms)
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
      then have \<open>f summable_on A\<close>
        using not_summable by auto
      with not_summable show False
        by simp
    qed
    then show ?thesis
      by (simp add: infsum_not_exists not_summable(1)) 
  qed
qed


lemma infsum_Un_Int:
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add, t2_space}"
  assumes [simp]: "f summable_on A - B" "f summable_on B - A" \<open>f summable_on A \<inter> B\<close>
  shows   "infsum f (A \<union> B) = infsum f A + infsum f B - infsum f (A \<inter> B)"
proof -
  have [simp]: \<open>f summable_on A\<close>
    apply (subst asm_rl[of \<open>A = (A-B) \<union> (A\<inter>B)\<close>]) apply auto[1]
    apply (rule summable_on_Un_disjoint)
    by auto
  have \<open>infsum f (A \<union> B) = infsum f A + infsum f (B - A)\<close>
    apply (subst infsum_Un_disjoint[symmetric])
    by auto
  moreover have \<open>infsum f (B - A \<union> A \<inter> B) = infsum f (B - A) + infsum f (A \<inter> B)\<close>
    by (rule infsum_Un_disjoint) auto
  moreover have "B - A \<union> A \<inter> B = B"
    by blast
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
    apply (subst infsum_cmult_left[symmetric])
    using insert.prems(1) by blast
  then have summable3: \<open>(\<lambda>p. (\<Prod>x'\<in>F. f x' (p x'))) summable_on Pi\<^sub>E F B\<close> if \<open>(\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) \<noteq> 0\<close>
    apply (subst (asm) summable_on_cmult_right')
    using that by auto

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x F) B. \<Prod>x\<in>insert x F. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E F B \<times> B x. \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x'))\<close>
    apply (subst pi)
    apply (subst infsum_reindex)
    using inj by (auto simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x')))\<close>
    apply (subst prod.insert)
    using insert by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst prod) by rule
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using summable2 apply blast
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>
    apply (subst infsum_cmult_left')
    apply (subst infsum_cmult_right')
    by (rule refl)
  also have \<open>\<dots> = (\<Prod>x\<in>insert x F. infsum (f x) (B x))\<close>
    apply (subst prod.insert)
    using \<open>finite F\<close> \<open>x \<notin> F\<close> apply auto[2]
    apply (cases \<open>infsum (f x) (B x) = 0\<close>)
     apply simp
    apply (subst insert.IH)
      apply (simp add: insert.prems(1))
     apply (rule summable3)
    by auto
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
  case (insert x F)
  
  have pi: \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close> for x F and B :: "'a \<Rightarrow> 'b set"
    unfolding PiE_insert_eq 
    by (subst swap_product [symmetric]) (simp add: image_image case_prod_unfold)
  have prod: \<open>(\<Prod>x'\<in>F. f x' ((p(x:=y)) x')) = (\<Prod>x'\<in>F. f x' (p x'))\<close> for p y
    by (rule prod.cong) (use insert.hyps in auto)
  have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B \<times> B x)\<close>
    using \<open>x \<notin> F\<close> by (rule inj_combinator')

  define s where \<open>s x = infsum (\<lambda>y. norm (f x y)) (B x)\<close> for x

  have *: \<open>(\<Sum>p\<in>P. norm (\<Prod>x\<in>F. f x (p x))) \<le> prod s F\<close> 
    if P: \<open>P \<subseteq> Pi\<^sub>E F B\<close> and [simp]: \<open>finite P\<close> \<open>finite F\<close> 
      and sum: \<open>\<And>x. x \<in> F \<Longrightarrow> f x abs_summable_on B x\<close> for P F
  proof -
    define B' where \<open>B' x = {p x| p. p\<in>P}\<close> for x
    have [simp]: \<open>finite (B' x)\<close> for x
      using that by (auto simp: B'_def)
    have [simp]: \<open>finite (Pi\<^sub>E F B')\<close>
      by (simp add: finite_PiE)
    have [simp]: \<open>P \<subseteq> Pi\<^sub>E F B'\<close>
      using that by (auto simp: B'_def)
    have B'B: \<open>B' x \<subseteq> B x\<close> if \<open>x \<in> F\<close> for x
      unfolding B'_def using P that 
      by auto
    have s_bound: \<open>(\<Sum>y\<in>B' x. norm (f x y)) \<le> s x\<close> if \<open>x \<in> F\<close> for x
      apply (simp_all add: s_def flip: infsum_finite)
      apply (rule infsum_mono_neutral)
      using that sum B'B by auto
    have \<open>(\<Sum>p\<in>P. norm (\<Prod>x\<in>F. f x (p x))) \<le> (\<Sum>p\<in>Pi\<^sub>E F B'. norm (\<Prod>x\<in>F. f x (p x)))\<close>
      apply (rule sum_mono2)
      by auto
    also have \<open>\<dots> = (\<Sum>p\<in>Pi\<^sub>E F B'. \<Prod>x\<in>F. norm (f x (p x)))\<close>
      apply (subst prod_norm[symmetric])
      by simp
    also have \<open>\<dots> = (\<Prod>x\<in>F. \<Sum>y\<in>B' x. norm (f x y))\<close>
    proof (use \<open>finite F\<close> in induction)
      case empty
      then show ?case by simp
    next
      case (insert x F)
      have aux: \<open>a = b \<Longrightarrow> c * a = c * b\<close> for a b c :: real
        by auto
      have inj: \<open>inj_on (\<lambda>(g, y). g(x := y)) (Pi\<^sub>E F B' \<times> B' x)\<close>
        by (rule inj_combinator') (use insert.hyps in auto)
      have \<open>(\<Sum>p\<in>Pi\<^sub>E (insert x F) B'. \<Prod>x\<in>insert x F. norm (f x (p x)))
         =  (\<Sum>(p,y)\<in>Pi\<^sub>E F B' \<times> B' x. \<Prod>x'\<in>insert x F. norm (f x' ((p(x := y)) x')))\<close>
        apply (subst pi)
        apply (subst sum.reindex)
        using inj by (auto simp: case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>(p,y)\<in>Pi\<^sub>E F B' \<times> B' x. norm (f x y) * (\<Prod>x'\<in>F. norm (f x' ((p(x := y)) x'))))\<close>
        apply (subst prod.insert)
        using insert.hyps by (auto simp: case_prod_unfold)
      also have \<open>\<dots> = (\<Sum>(p, y)\<in>Pi\<^sub>E F B' \<times> B' x. norm (f x y) * (\<Prod>x'\<in>F. norm (f x' (p x'))))\<close>
        apply (rule sum.cong)
         apply blast
        unfolding case_prod_unfold
        apply (rule aux)
        apply (rule prod.cong)
        using insert.hyps(2) by auto
      also have \<open>\<dots> = (\<Sum>y\<in>B' x. norm (f x y)) * (\<Sum>p\<in>Pi\<^sub>E F B'. \<Prod>x'\<in>F. norm (f x' (p x')))\<close>
        apply (subst sum_product)
        apply (subst sum.swap)
        apply (subst sum.cartesian_product)
        by simp
      also have \<open>\<dots> = (\<Sum>y\<in>B' x. norm (f x y)) * (\<Prod>x\<in>F. \<Sum>y\<in>B' x. norm (f x y))\<close>
        by (simp add: insert.IH)
      also have \<open>\<dots> = (\<Prod>x\<in>insert x F. \<Sum>y\<in>B' x. norm (f x y))\<close>
        using insert.hyps(1) insert.hyps(2) by force
      finally show ?case .
    qed
    also have \<open>\<dots> = (\<Prod>x\<in>F. \<Sum>\<^sub>\<infinity>y\<in>B' x. norm (f x y))\<close>
      by auto
    also have \<open>\<dots> \<le> (\<Prod>x\<in>F. s x)\<close>
      apply (rule prod_mono)
      apply auto
      apply (simp add: sum_nonneg)
      using s_bound by presburger
    finally show ?thesis .
  qed
  have \<open>(\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) abs_summable_on Pi\<^sub>E (insert x F) B\<close>
    apply (rule nonneg_bdd_above_summable_on)
     apply (simp; fail)
    apply (rule bdd_aboveI[where M=\<open>\<Prod>x'\<in>insert x F. s x'\<close>])
    using * insert.hyps insert.prems by blast

  also have \<open>Pi\<^sub>E (insert x F) B = (\<lambda>(g,y). g(x:=y)) ` (Pi\<^sub>E F B \<times> B x)\<close>
    by (simp only: pi)
  also have "(\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) abs_summable_on \<dots> \<longleftrightarrow>
               ((\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) \<circ> (\<lambda>(g,y). g(x:=y))) abs_summable_on (Pi\<^sub>E F B \<times> B x)"
    using inj by (subst summable_on_reindex) (auto simp: o_def)
  also have "(\<Prod>z\<in>F. f z ((g(x := y)) z)) = (\<Prod>z\<in>F. f z (g z))" for g y
    using insert.hyps by (intro prod.cong) auto
  hence "((\<lambda>g. \<Prod>x\<in>insert x F. f x (g x)) \<circ> (\<lambda>(g,y). g(x:=y))) =
             (\<lambda>(p, y). f x y * (\<Prod>x'\<in>F. f x' (p x')))"
    using insert.hyps by (auto simp: fun_eq_iff cong: prod.cong_simp)
  finally have summable2: \<open>(\<lambda>(p, y). f x y * (\<Prod>x'\<in>F. f x' (p x'))) abs_summable_on Pi\<^sub>E F B \<times> B x\<close> .

  have \<open>(\<Sum>\<^sub>\<infinity>g\<in>Pi\<^sub>E (insert x F) B. \<Prod>x\<in>insert x F. f x (g x))
     = (\<Sum>\<^sub>\<infinity>(p,y)\<in>Pi\<^sub>E F B \<times> B x. \<Prod>x'\<in>insert x F. f x' ((p(x:=y)) x'))\<close>
    apply (subst pi)
    apply (subst infsum_reindex)
    using inj by (auto simp: o_def case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' ((p(x:=y)) x')))\<close>
    apply (subst prod.insert)
    using insert by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(p, y)\<in>Pi\<^sub>E F B \<times> B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst prod) by rule
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Sum>\<^sub>\<infinity>y\<in>B x. f x y * (\<Prod>x'\<in>F. f x' (p x')))\<close>
    apply (subst infsum_Sigma_banach[symmetric])
    using summable2 abs_summable_summable apply blast
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>B x. f x y) * (\<Sum>\<^sub>\<infinity>p\<in>Pi\<^sub>E F B. \<Prod>x'\<in>F. f x' (p x'))\<close>
    apply (subst infsum_cmult_left')
    apply (subst infsum_cmult_right')
    by (rule refl)
  also have \<open>\<dots> = (\<Prod>x\<in>insert x F. infsum (f x) (B x))\<close>
    apply (subst prod.insert)
    using \<open>finite F\<close> \<open>x \<notin> F\<close> apply auto[2]
    apply (cases \<open>infsum (f x) (B x) = 0\<close>)
     apply (simp; fail)
    apply (subst insert.IH)
      apply (auto simp add: insert.prems(1))
    done
  finally show ?case
    by simp
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
    where \<open>n x = norm (f x)\<close> and \<open>A\<^sub>p = {x\<in>A. f x \<ge> 0}\<close> and \<open>A\<^sub>n = {x\<in>A. f x < 0}\<close> for x
  have [simp]: \<open>A\<^sub>p \<union> A\<^sub>n = A\<close> \<open>A\<^sub>p \<inter> A\<^sub>n = {}\<close>
    by (auto simp: A\<^sub>p_def A\<^sub>n_def)
  from \<open>f summable_on A\<close> have [simp]: \<open>f summable_on A\<^sub>p\<close> \<open>f summable_on A\<^sub>n\<close>
    using A\<^sub>p_def A\<^sub>n_def summable_on_subset_banach by fastforce+
  then have [simp]: \<open>n summable_on A\<^sub>p\<close>
    apply (subst summable_on_cong[where g=f])
    by (simp_all add: A\<^sub>p_def n_def)
  moreover have [simp]: \<open>n summable_on A\<^sub>n\<close>
    apply (subst summable_on_cong[where g=\<open>\<lambda>x. - f x\<close>])
     apply (simp add: A\<^sub>n_def n_def[abs_def])
    by (simp add: summable_on_uminus)
  ultimately have [simp]: \<open>n summable_on (A\<^sub>p \<union> A\<^sub>n)\<close>
    apply (rule summable_on_Un_disjoint) by simp
  then show \<open>n summable_on A\<close>
    by simp
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
    apply (rule_tac summable_on_Sigma_banach)
    by (auto simp: case_prod_unfold)
  then show \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x, y))) abs_summable_on A\<close>
    using summable_on_iff_abs_summable_on_real by force

  show \<open>(\<lambda>y. f (x, y)) abs_summable_on B x\<close> if \<open>x \<in> A\<close> for x
  proof -
    from asm have \<open>f abs_summable_on Pair x ` B x\<close>
      apply (rule summable_on_subset_banach)
      using that by auto
    then show ?thesis
      apply (subst (asm) summable_on_reindex)
      by (auto simp: o_def inj_on_def)
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
      apply (subst sum.Sigma)
      by auto
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>{y. (x,y)\<in>F}. norm (f (x,y)))\<close>
      apply (subst infsum_finite)
      by auto
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>B x. norm (f (x,y)))\<close>
      apply (rule infsum_mono)
        apply (simp; fail)
       apply (simp; fail)
      apply (rule infsum_mono_neutral)
      using asm that(1) by auto
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
    proof (rule infsum_mono_neutral)
      show "g abs_summable_on F"
        by (rule summable_on_subset_banach[OF assms(1)]) (use F in auto)
    qed (use F assms in auto)
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
      apply (rule infsum_mono_neutral)
      using b4 r1 x2_sum by auto

    have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
      unfolding norm_mult by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
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

lemma summable_on_ennreal[simp]: \<open>(f::_ \<Rightarrow> ennreal) summable_on S\<close>
  by (rule nonneg_summable_on_complete) simp

lemma summable_on_enat[simp]: \<open>(f::_ \<Rightarrow> enat) summable_on S\<close>
  by (rule nonneg_summable_on_complete) simp

lemma has_sum_superconst_infinite_ennreal:
  fixes f :: \<open>'a \<Rightarrow> ennreal\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "has_sum f S \<infinity>"
proof -
  have \<open>(sum f \<longlongrightarrow> \<infinity>) (finite_subsets_at_top S)\<close>
  proof (rule order_tendstoI[rotated], simp)
    fix y :: ennreal assume \<open>y < \<infinity>\<close>
    then have \<open>y / b < \<infinity>\<close>
      by (metis b ennreal_divide_eq_top_iff gr_implies_not_zero infinity_ennreal_def top.not_eq_extremum)
    then obtain F where \<open>finite F\<close> and \<open>F \<subseteq> S\<close> and cardF: \<open>card F > y / b\<close>
      using \<open>infinite S\<close>
      by (metis ennreal_Ex_less_of_nat infinite_arbitrarily_large infinity_ennreal_def)
    moreover have \<open>sum f Y > y\<close> if \<open>finite Y\<close> and \<open>F \<subseteq> Y\<close> and \<open>Y \<subseteq> S\<close> for Y
    proof -
      have \<open>y < b * card F\<close>
        by (metis \<open>y < \<infinity>\<close> b cardF divide_less_ennreal ennreal_mult_eq_top_iff gr_implies_not_zero infinity_ennreal_def mult.commute top.not_eq_extremum)
      also have \<open>\<dots> \<le> b * card Y\<close>
        by (meson b card_mono less_imp_le mult_left_mono of_nat_le_iff that(1) that(2))
      also have \<open>\<dots> = sum (\<lambda>_. b) Y\<close>
        by (simp add: mult.commute)
      also have \<open>\<dots> \<le> sum f Y\<close>
        using geqb by (meson subset_eq sum_mono that(3))
      finally show ?thesis .
    qed
    ultimately show \<open>\<forall>\<^sub>F x in finite_subsets_at_top S. y < sum f x\<close>
      unfolding eventually_finite_subsets_at_top 
      by auto
  qed
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
  hence *: \<open>infsum (e2ennreal o f) S = \<infinity>\<close>
    using assms b'
    by (intro infsum_superconst_infinite_ennreal[where b=b']) (auto intro!: e2ennreal_mono)
  have \<open>infsum f S = infsum (enn2ereal o (e2ennreal o f)) S\<close>
    using geqb b by (intro infsum_cong) (fastforce simp: enn2ereal_e2ennreal)
  also have \<open>\<dots> = enn2ereal \<infinity>\<close>
    apply (subst infsum_comm_additive_general)
    using * by (auto simp: continuous_at_enn2ereal)
  also have \<open>\<dots> = \<infinity>\<close>
    by simp
  finally show ?thesis .
qed

lemma has_sum_superconst_infinite_ereal:
  fixes f :: \<open>'a \<Rightarrow> ereal\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "has_sum f S \<infinity>"
  by (metis Infty_neq_0(1) assms infsum_def has_sum_infsum infsum_superconst_infinite_ereal)

lemma infsum_superconst_infinite_enat:
  fixes f :: \<open>'a \<Rightarrow> enat\<close>
  assumes geqb: \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<ge> b\<close>
  assumes b: \<open>b > 0\<close>
  assumes \<open>infinite S\<close>
  shows "infsum f S = \<infinity>"
proof -
  have \<open>ennreal_of_enat (infsum f S) = infsum (ennreal_of_enat o f) S\<close>
    apply (rule infsum_comm_additive_general[symmetric])
    by auto
  also have \<open>\<dots> = \<infinity>\<close>
    by (metis assms(3) b comp_apply ennreal_of_enat_0 ennreal_of_enat_inj ennreal_of_enat_le_iff geqb infsum_superconst_infinite_ennreal not_gr_zero)
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
  shows "has_sum f S \<infinity>"
  by (metis assms i0_lb has_sum_infsum infsum_superconst_infinite_enat nonneg_summable_on_complete)

text \<open>This lemma helps to relate a real-valued infsum to a supremum over extended nonnegative reals.\<close>

lemma infsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof -
  have \<open>ennreal (infsum f A) = infsum (ennreal o f) A\<close>
    apply (rule infsum_comm_additive_general[symmetric])
    apply (subst sum_ennreal[symmetric])
    using assms by auto
  also have \<open>\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))\<close>
    apply (subst nonneg_infsum_complete, simp)
    apply (rule SUP_cong, blast)
    apply (subst sum_ennreal[symmetric])
    using fnn by auto
  finally show ?thesis .
qed

text \<open>This lemma helps to related a real-valued infsum to a supremum over extended reals.\<close>

lemma infsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have \<open>ereal (infsum f A) = infsum (ereal o f) A\<close>
    apply (rule infsum_comm_additive_general[symmetric])
    using assms by auto
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
  have "ereal (infsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
    using assms by (rule infsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
  proof (subst ereal_SUP)
    show "\<bar>SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a)\<bar> \<noteq> \<infinity>"
      using calculation by fastforce      
    show "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f F)) = (SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a))"
      by simp      
  qed
  finally show ?thesis by simp
qed


lemma has_sum_nonneg_SUPREMUM_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f summable_on A" and "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "has_sum f A (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
  by (metis (mono_tags, lifting) assms has_sum_infsum infsum_nonneg_is_SUPREMUM_real)

lemma summable_countable_real:
  fixes f :: \<open>'a \<Rightarrow> real\<close>
  assumes \<open>f summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_summable_countable assms summable_on_iff_abs_summable_on_real by blast

subsection \<open>Complex numbers\<close>

lemma has_sum_cnj_iff[simp]: 
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>has_sum (\<lambda>x. cnj (f x)) M (cnj a) \<longleftrightarrow> has_sum f M a\<close>
  by (simp add: has_sum_def lim_cnj del: cnj_sum add: cnj_sum[symmetric, abs_def, of f])

lemma summable_on_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) summable_on A \<longleftrightarrow> f summable_on A"
  by (metis complex_cnj_cnj summable_on_def has_sum_cnj_iff)

lemma infsum_cnj[simp]: \<open>infsum (\<lambda>x. cnj (f x)) M = cnj (infsum f M)\<close>
  by (metis complex_cnj_zero infsumI has_sum_cnj_iff infsum_def summable_on_cnj_iff has_sum_infsum)

lemma infsum_Re:
  assumes "f summable_on M"
  shows "infsum (\<lambda>x. Re (f x)) M = Re (infsum f M)"
  apply (rule infsum_comm_additive[where f=Re, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma has_sum_Re:
  assumes "has_sum f M a"
  shows "has_sum (\<lambda>x. Re (f x)) M (Re a)"
  apply (rule has_sum_comm_additive[where f=Re, unfolded o_def])
  using assms by (auto intro!: additive.intro tendsto_Re)

lemma summable_on_Re: 
  assumes "f summable_on M"
  shows "(\<lambda>x. Re (f x)) summable_on M"
  apply (rule summable_on_comm_additive[where f=Re, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma infsum_Im: 
  assumes "f summable_on M"
  shows "infsum (\<lambda>x. Im (f x)) M = Im (infsum f M)"
  apply (rule infsum_comm_additive[where f=Im, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma has_sum_Im:
  assumes "has_sum f M a"
  shows "has_sum (\<lambda>x. Im (f x)) M (Im a)"
  apply (rule has_sum_comm_additive[where f=Im, unfolded o_def])
  using assms by (auto intro!: additive.intro tendsto_Im)

lemma summable_on_Im: 
  assumes "f summable_on M"
  shows "(\<lambda>x. Im (f x)) summable_on M"
  apply (rule summable_on_comm_additive[where f=Im, unfolded o_def])
  using assms by (auto intro!: additive.intro)

lemma nonneg_infsum_le_0D_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "infsum f A \<le> 0"
    and abs_sum: "f summable_on A"
    and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
    and "x \<in> A"
  shows "f x = 0"
proof -
  have \<open>Im (f x) = 0\<close>
    apply (rule nonneg_infsum_le_0D[where A=A])
    using assms
    by (auto simp add: infsum_Im summable_on_Im less_eq_complex_def)
  moreover have \<open>Re (f x) = 0\<close>
    apply (rule nonneg_infsum_le_0D[where A=A])
    using assms by (auto simp add: summable_on_Re infsum_Re less_eq_complex_def)
  ultimately show ?thesis
    by (simp add: complex_eqI)
qed

lemma nonneg_has_sum_le_0D_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "has_sum f A a" and \<open>a \<le> 0\<close>
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
    apply (rule infsum_mono_neutral)
    using assms(3-5) by (auto simp add: summable_on_Re less_eq_complex_def)
  then have Re: \<open>Re (infsum f A) \<le> Re (infsum g B)\<close>
    by (metis assms(1-2) infsum_Re)
  have \<open>infsum (\<lambda>x. Im (f x)) A = infsum (\<lambda>x. Im (g x)) B\<close>
    apply (rule infsum_cong_neutral)
    using assms(3-5) by (auto simp add: summable_on_Re less_eq_complex_def)
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
  by (metis assms(1) assms(2) infsum_0_simp summable_on_0_simp infsum_mono_complex)

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
    apply (rule infsum_cong)
    using fnn cmod_eq_Re complex_is_Real_iff less_eq_complex_def by force
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
    apply (rule summable_on_add) by auto
  show \<open>n summable_on A\<close>
    apply (rule nonneg_bdd_above_summable_on)
     apply (simp add: n_def; fail)
    apply (rule bdd_aboveI[where M=\<open>infsum (\<lambda>x. nr x + ni x) A\<close>])
    using * n_sum by (auto simp flip: infsum_finite simp: ni_def[abs_def] nr_def[abs_def] intro!: infsum_mono_neutral)
next
  show \<open>f abs_summable_on A \<Longrightarrow> f summable_on A\<close>
    using abs_summable_summable by blast
qed

lemma summable_countable_complex:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f summable_on A\<close>
  shows \<open>countable {x\<in>A. f x \<noteq> 0}\<close>
  using abs_summable_countable assms summable_on_iff_abs_summable_on_complex by blast

end


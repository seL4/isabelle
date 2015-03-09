(*  Title:      HOL/Probability/Borel_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Armin Heller, TU München
*)

section {*Borel spaces*}

theory Borel_Space
imports
  Measurable
  "~~/src/HOL/Multivariate_Analysis/Multivariate_Analysis"
begin

lemma topological_basis_trivial: "topological_basis {A. open A}"
  by (auto simp: topological_basis_def)

lemma open_prod_generated: "open = generate_topology {A \<times> B | A B. open A \<and> open B}"
proof -
  have "{A \<times> B :: ('a \<times> 'b) set | A B. open A \<and> open B} = ((\<lambda>(a, b). a \<times> b) ` ({A. open A} \<times> {A. open A}))"
    by auto
  then show ?thesis
    by (auto intro: topological_basis_prod topological_basis_trivial topological_basis_imp_subbasis)  
qed

subsection {* Generic Borel spaces *}

definition borel :: "'a::topological_space measure" where
  "borel = sigma UNIV {S. open S}"

abbreviation "borel_measurable M \<equiv> measurable M borel"

lemma in_borel_measurable:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sigma_sets UNIV {S. open S}. f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma in_borel_measurable_borel:
   "f \<in> borel_measurable M \<longleftrightarrow>
    (\<forall>S \<in> sets borel.
      f -` S \<inter> space M \<in> sets M)"
  by (auto simp add: measurable_def borel_def)

lemma space_borel[simp]: "space borel = UNIV"
  unfolding borel_def by auto

lemma space_in_borel[measurable]: "UNIV \<in> sets borel"
  unfolding borel_def by auto

lemma sets_borel: "sets borel = sigma_sets UNIV {S. open S}"
  unfolding borel_def by (rule sets_measure_of) simp

lemma pred_Collect_borel[measurable (raw)]: "Measurable.pred borel P \<Longrightarrow> {x. P x} \<in> sets borel"
  unfolding borel_def pred_def by auto

lemma borel_open[measurable (raw generic)]:
  assumes "open A" shows "A \<in> sets borel"
proof -
  have "A \<in> {S. open S}" unfolding mem_Collect_eq using assms .
  thus ?thesis unfolding borel_def by auto
qed

lemma borel_closed[measurable (raw generic)]:
  assumes "closed A" shows "A \<in> sets borel"
proof -
  have "space borel - (- A) \<in> sets borel"
    using assms unfolding closed_def by (blast intro: borel_open)
  thus ?thesis by simp
qed

lemma borel_singleton[measurable]:
  "A \<in> sets borel \<Longrightarrow> insert x A \<in> sets (borel :: 'a::t1_space measure)"
  unfolding insert_def by (rule sets.Un) auto

lemma borel_comp[measurable]: "A \<in> sets borel \<Longrightarrow> - A \<in> sets borel"
  unfolding Compl_eq_Diff_UNIV by simp

lemma borel_measurable_vimage:
  fixes f :: "'a \<Rightarrow> 'x::t2_space"
  assumes borel[measurable]: "f \<in> borel_measurable M"
  shows "f -` {x} \<inter> space M \<in> sets M"
  by simp

lemma borel_measurableI:
  fixes f :: "'a \<Rightarrow> 'x\<Colon>topological_space"
  assumes "\<And>S. open S \<Longrightarrow> f -` S \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable M"
  unfolding borel_def
proof (rule measurable_measure_of, simp_all)
  fix S :: "'x set" assume "open S" thus "f -` S \<inter> space M \<in> sets M"
    using assms[of S] by simp
qed

lemma borel_measurable_const:
  "(\<lambda>x. c) \<in> borel_measurable M"
  by auto

lemma borel_measurable_indicator:
  assumes A: "A \<in> sets M"
  shows "indicator A \<in> borel_measurable M"
  unfolding indicator_def [abs_def] using A
  by (auto intro!: measurable_If_set)

lemma borel_measurable_count_space[measurable (raw)]:
  "f \<in> borel_measurable (count_space S)"
  unfolding measurable_def by auto

lemma borel_measurable_indicator'[measurable (raw)]:
  assumes [measurable]: "{x\<in>space M. f x \<in> A x} \<in> sets M"
  shows "(\<lambda>x. indicator (A x) (f x)) \<in> borel_measurable M"
  unfolding indicator_def[abs_def]
  by (auto intro!: measurable_If)

lemma borel_measurable_indicator_iff:
  "(indicator A :: 'a \<Rightarrow> 'x::{t1_space, zero_neq_one}) \<in> borel_measurable M \<longleftrightarrow> A \<inter> space M \<in> sets M"
    (is "?I \<in> borel_measurable M \<longleftrightarrow> _")
proof
  assume "?I \<in> borel_measurable M"
  then have "?I -` {1} \<inter> space M \<in> sets M"
    unfolding measurable_def by auto
  also have "?I -` {1} \<inter> space M = A \<inter> space M"
    unfolding indicator_def [abs_def] by auto
  finally show "A \<inter> space M \<in> sets M" .
next
  assume "A \<inter> space M \<in> sets M"
  moreover have "?I \<in> borel_measurable M \<longleftrightarrow>
    (indicator (A \<inter> space M) :: 'a \<Rightarrow> 'x) \<in> borel_measurable M"
    by (intro measurable_cong) (auto simp: indicator_def)
  ultimately show "?I \<in> borel_measurable M" by auto
qed

lemma borel_measurable_subalgebra:
  assumes "sets N \<subseteq> sets M" "space N = space M" "f \<in> borel_measurable N"
  shows "f \<in> borel_measurable M"
  using assms unfolding measurable_def by auto

lemma borel_measurable_restrict_space_iff_ereal:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes \<Omega>[measurable, simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable (restrict_space M \<Omega>) \<longleftrightarrow>
    (\<lambda>x. f x * indicator \<Omega> x) \<in> borel_measurable M"
  by (subst measurable_restrict_space_iff)
     (auto simp: indicator_def if_distrib[where f="\<lambda>x. a * x" for a] cong del: if_cong)

lemma borel_measurable_restrict_space_iff:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes \<Omega>[measurable, simp]: "\<Omega> \<inter> space M \<in> sets M"
  shows "f \<in> borel_measurable (restrict_space M \<Omega>) \<longleftrightarrow>
    (\<lambda>x. indicator \<Omega> x *\<^sub>R f x) \<in> borel_measurable M"
  by (subst measurable_restrict_space_iff)
     (auto simp: indicator_def if_distrib[where f="\<lambda>x. x *\<^sub>R a" for a] ac_simps cong del: if_cong)

lemma cbox_borel[measurable]: "cbox a b \<in> sets borel"
  by (auto intro: borel_closed)

lemma box_borel[measurable]: "box a b \<in> sets borel"
  by (auto intro: borel_open)

lemma borel_compact: "compact (A::'a::t2_space set) \<Longrightarrow> A \<in> sets borel"
  by (auto intro: borel_closed dest!: compact_imp_closed)

lemma second_countable_borel_measurable:
  fixes X :: "'a::second_countable_topology set set"
  assumes eq: "open = generate_topology X"
  shows "borel = sigma UNIV X"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI)
  interpret X: sigma_algebra UNIV "sigma_sets UNIV X"
    by (rule sigma_algebra_sigma_sets) simp

  fix S :: "'a set" assume "S \<in> Collect open"
  then have "generate_topology X S"
    by (auto simp: eq)
  then show "S \<in> sigma_sets UNIV X"
  proof induction
    case (UN K)
    then have K: "\<And>k. k \<in> K \<Longrightarrow> open k"
      unfolding eq by auto
    from ex_countable_basis obtain B :: "'a set set" where
      B:  "\<And>b. b \<in> B \<Longrightarrow> open b" "\<And>X. open X \<Longrightarrow> \<exists>b\<subseteq>B. (\<Union>b) = X" and "countable B"
      by (auto simp: topological_basis_def)
    from B(2)[OF K] obtain m where m: "\<And>k. k \<in> K \<Longrightarrow> m k \<subseteq> B" "\<And>k. k \<in> K \<Longrightarrow> (\<Union>m k) = k"
      by metis
    def U \<equiv> "(\<Union>k\<in>K. m k)"
    with m have "countable U"
      by (intro countable_subset[OF _ `countable B`]) auto
    have "\<Union>U = (\<Union>A\<in>U. A)" by simp
    also have "\<dots> = \<Union>K"
      unfolding U_def UN_simps by (simp add: m)
    finally have "\<Union>U = \<Union>K" .

    have "\<forall>b\<in>U. \<exists>k\<in>K. b \<subseteq> k"
      using m by (auto simp: U_def)
    then obtain u where u: "\<And>b. b \<in> U \<Longrightarrow> u b \<in> K" and "\<And>b. b \<in> U \<Longrightarrow> b \<subseteq> u b"
      by metis
    then have "(\<Union>b\<in>U. u b) \<subseteq> \<Union>K" "\<Union>U \<subseteq> (\<Union>b\<in>U. u b)"
      by auto
    then have "\<Union>K = (\<Union>b\<in>U. u b)"
      unfolding `\<Union>U = \<Union>K` by auto
    also have "\<dots> \<in> sigma_sets UNIV X"
      using u UN by (intro X.countable_UN' `countable U`) auto
    finally show "\<Union>K \<in> sigma_sets UNIV X" .
  qed auto
qed (auto simp: eq intro: generate_topology.Basis)

lemma borel_measurable_continuous_on_restrict:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes f: "continuous_on A f"
  shows "f \<in> borel_measurable (restrict_space borel A)"
proof (rule borel_measurableI)
  fix S :: "'b set" assume "open S"
  with f obtain T where "f -` S \<inter> A = T \<inter> A" "open T"
    by (metis continuous_on_open_invariant)
  then show "f -` S \<inter> space (restrict_space borel A) \<in> sets (restrict_space borel A)"
    by (force simp add: sets_restrict_space space_restrict_space)
qed

lemma borel_measurable_continuous_on1: "continuous_on UNIV f \<Longrightarrow> f \<in> borel_measurable borel"
  by (drule borel_measurable_continuous_on_restrict) simp

lemma borel_measurable_continuous_on_if:
  "A \<in> sets borel \<Longrightarrow> continuous_on A f \<Longrightarrow> continuous_on (- A) g \<Longrightarrow>
    (\<lambda>x. if x \<in> A then f x else g x) \<in> borel_measurable borel"
  by (auto simp add: measurable_If_restrict_space_iff Collect_neg_eq
           intro!: borel_measurable_continuous_on_restrict)

lemma borel_measurable_continuous_countable_exceptions:
  fixes f :: "'a::t1_space \<Rightarrow> 'b::topological_space"
  assumes X: "countable X"
  assumes "continuous_on (- X) f"
  shows "f \<in> borel_measurable borel"
proof (rule measurable_discrete_difference[OF _ X])
  have "X \<in> sets borel"
    by (rule sets.countable[OF _ X]) auto
  then show "(\<lambda>x. if x \<in> X then undefined else f x) \<in> borel_measurable borel"
    by (intro borel_measurable_continuous_on_if assms continuous_intros)
qed auto

lemma borel_measurable_continuous_on:
  assumes f: "continuous_on UNIV f" and g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f (g x)) \<in> borel_measurable M"
  using measurable_comp[OF g borel_measurable_continuous_on1[OF f]] by (simp add: comp_def)

lemma borel_measurable_continuous_on_indicator:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "A \<in> sets borel \<Longrightarrow> continuous_on A f \<Longrightarrow> (\<lambda>x. indicator A x *\<^sub>R f x) \<in> borel_measurable borel"
  by (subst borel_measurable_restrict_space_iff[symmetric])
     (auto intro: borel_measurable_continuous_on_restrict)

lemma borel_eq_countable_basis:
  fixes B::"'a::topological_space set set"
  assumes "countable B"
  assumes "topological_basis B"
  shows "borel = sigma UNIV B"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI, safe)
  interpret countable_basis using assms by unfold_locales
  fix X::"'a set" assume "open X"
  from open_countable_basisE[OF this] guess B' . note B' = this
  then show "X \<in> sigma_sets UNIV B"
    by (blast intro: sigma_sets_UNION `countable B` countable_subset)
next
  fix b assume "b \<in> B"
  hence "open b" by (rule topological_basis_open[OF assms(2)])
  thus "b \<in> sigma_sets UNIV (Collect open)" by auto
qed simp_all

lemma borel_measurable_Pair[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::second_countable_topology" and g :: "'a \<Rightarrow> 'c::second_countable_topology"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes g[measurable]: "g \<in> borel_measurable M"
  shows "(\<lambda>x. (f x, g x)) \<in> borel_measurable M"
proof (subst borel_eq_countable_basis)
  let ?B = "SOME B::'b set set. countable B \<and> topological_basis B"
  let ?C = "SOME B::'c set set. countable B \<and> topological_basis B"
  let ?P = "(\<lambda>(b, c). b \<times> c) ` (?B \<times> ?C)"
  show "countable ?P" "topological_basis ?P"
    by (auto intro!: countable_basis topological_basis_prod is_basis)

  show "(\<lambda>x. (f x, g x)) \<in> measurable M (sigma UNIV ?P)"
  proof (rule measurable_measure_of)
    fix S assume "S \<in> ?P"
    then obtain b c where "b \<in> ?B" "c \<in> ?C" and S: "S = b \<times> c" by auto
    then have borel: "open b" "open c"
      by (auto intro: is_basis topological_basis_open)
    have "(\<lambda>x. (f x, g x)) -` S \<inter> space M = (f -` b \<inter> space M) \<inter> (g -` c \<inter> space M)"
      unfolding S by auto
    also have "\<dots> \<in> sets M"
      using borel by simp
    finally show "(\<lambda>x. (f x, g x)) -` S \<inter> space M \<in> sets M" .
  qed auto
qed

lemma borel_measurable_continuous_Pair:
  fixes f :: "'a \<Rightarrow> 'b::second_countable_topology" and g :: "'a \<Rightarrow> 'c::second_countable_topology"
  assumes [measurable]: "f \<in> borel_measurable M"
  assumes [measurable]: "g \<in> borel_measurable M"
  assumes H: "continuous_on UNIV (\<lambda>x. H (fst x) (snd x))"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  have eq: "(\<lambda>x. H (f x) (g x)) = (\<lambda>x. (\<lambda>x. H (fst x) (snd x)) (f x, g x))" by auto
  show ?thesis
    unfolding eq by (rule borel_measurable_continuous_on[OF H]) auto
qed

subsection {* Borel spaces on order topologies *}


lemma borel_Iio:
  "borel = sigma UNIV (range lessThan :: 'a::{linorder_topology, second_countable_topology} set set)"
  unfolding second_countable_borel_measurable[OF open_generated_order]
proof (intro sigma_eqI sigma_sets_eqI)
  from countable_dense_setE guess D :: "'a set" . note D = this

  interpret L: sigma_algebra UNIV "sigma_sets UNIV (range lessThan)"
    by (rule sigma_algebra_sigma_sets) simp

  fix A :: "'a set" assume "A \<in> range lessThan \<union> range greaterThan"
  then obtain y where "A = {y <..} \<or> A = {..< y}"
    by blast
  then show "A \<in> sigma_sets UNIV (range lessThan)"
  proof
    assume A: "A = {y <..}"
    show ?thesis
    proof cases
      assume "\<forall>x>y. \<exists>d. y < d \<and> d < x"
      with D(2)[of "{y <..< x}" for x] have "\<forall>x>y. \<exists>d\<in>D. y < d \<and> d < x"
        by (auto simp: set_eq_iff)
      then have "A = UNIV - (\<Inter>d\<in>{d\<in>D. y < d}. {..< d})"
        by (auto simp: A) (metis less_asym)
      also have "\<dots> \<in> sigma_sets UNIV (range lessThan)"
        using D(1) by (intro L.Diff L.top L.countable_INT'') auto
      finally show ?thesis .
    next
      assume "\<not> (\<forall>x>y. \<exists>d. y < d \<and> d < x)"
      then obtain x where "y < x"  "\<And>d. y < d \<Longrightarrow> \<not> d < x"
        by auto
      then have "A = UNIV - {..< x}"
        unfolding A by (auto simp: not_less[symmetric])
      also have "\<dots> \<in> sigma_sets UNIV (range lessThan)"
        by auto
      finally show ?thesis .
    qed
  qed auto
qed auto

lemma borel_Ioi:
  "borel = sigma UNIV (range greaterThan :: 'a::{linorder_topology, second_countable_topology} set set)"
  unfolding second_countable_borel_measurable[OF open_generated_order]
proof (intro sigma_eqI sigma_sets_eqI)
  from countable_dense_setE guess D :: "'a set" . note D = this

  interpret L: sigma_algebra UNIV "sigma_sets UNIV (range greaterThan)"
    by (rule sigma_algebra_sigma_sets) simp

  fix A :: "'a set" assume "A \<in> range lessThan \<union> range greaterThan"
  then obtain y where "A = {y <..} \<or> A = {..< y}"
    by blast
  then show "A \<in> sigma_sets UNIV (range greaterThan)"
  proof
    assume A: "A = {..< y}"
    show ?thesis
    proof cases
      assume "\<forall>x<y. \<exists>d. x < d \<and> d < y"
      with D(2)[of "{x <..< y}" for x] have "\<forall>x<y. \<exists>d\<in>D. x < d \<and> d < y"
        by (auto simp: set_eq_iff)
      then have "A = UNIV - (\<Inter>d\<in>{d\<in>D. d < y}. {d <..})"
        by (auto simp: A) (metis less_asym)
      also have "\<dots> \<in> sigma_sets UNIV (range greaterThan)"
        using D(1) by (intro L.Diff L.top L.countable_INT'') auto
      finally show ?thesis .
    next
      assume "\<not> (\<forall>x<y. \<exists>d. x < d \<and> d < y)"
      then obtain x where "x < y"  "\<And>d. y > d \<Longrightarrow> x \<ge> d"
        by (auto simp: not_less[symmetric])
      then have "A = UNIV - {x <..}"
        unfolding A Compl_eq_Diff_UNIV[symmetric] by auto
      also have "\<dots> \<in> sigma_sets UNIV (range greaterThan)"
        by auto
      finally show ?thesis .
    qed
  qed auto
qed auto

lemma borel_measurableI_less:
  fixes f :: "'a \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  shows "(\<And>y. {x\<in>space M. f x < y} \<in> sets M) \<Longrightarrow> f \<in> borel_measurable M"
  unfolding borel_Iio
  by (rule measurable_measure_of) (auto simp: Int_def conj_commute)

lemma borel_measurableI_greater:
  fixes f :: "'a \<Rightarrow> 'b::{linorder_topology, second_countable_topology}"
  shows "(\<And>y. {x\<in>space M. y < f x} \<in> sets M) \<Longrightarrow> f \<in> borel_measurable M"
  unfolding borel_Ioi
  by (rule measurable_measure_of) (auto simp: Int_def conj_commute)

lemma borel_measurable_SUP[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{complete_linorder, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. SUP i:I. F i x) \<in> borel_measurable M"
  by (rule borel_measurableI_greater) (simp add: less_SUP_iff)

lemma borel_measurable_INF[measurable (raw)]:
  fixes F :: "_ \<Rightarrow> _ \<Rightarrow> _::{complete_linorder, linorder_topology, second_countable_topology}"
  assumes [simp]: "countable I"
  assumes [measurable]: "\<And>i. i \<in> I \<Longrightarrow> F i \<in> borel_measurable M"
  shows "(\<lambda>x. INF i:I. F i x) \<in> borel_measurable M"
  by (rule borel_measurableI_less) (simp add: INF_less_iff)

lemma borel_measurable_lfp[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_linorder, linorder_topology, second_countable_topology})"
  assumes "Order_Continuity.continuous F"
  assumes *: "\<And>f. f \<in> borel_measurable M \<Longrightarrow> F f \<in> borel_measurable M"
  shows "lfp F \<in> borel_measurable M"
proof -
  { fix i have "((F ^^ i) bot) \<in> borel_measurable M"
      by (induct i) (auto intro!: *) }
  then have "(\<lambda>x. SUP i. (F ^^ i) bot x) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. SUP i. (F ^^ i) bot x) = (SUP i. (F ^^ i) bot)"
    by auto
  also have "(SUP i. (F ^^ i) bot) = lfp F"
    by (rule continuous_lfp[symmetric]) fact
  finally show ?thesis .
qed

lemma borel_measurable_gfp[consumes 1, case_names continuity step]:
  fixes F :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b::{complete_linorder, linorder_topology, second_countable_topology})"
  assumes "Order_Continuity.down_continuous F"
  assumes *: "\<And>f. f \<in> borel_measurable M \<Longrightarrow> F f \<in> borel_measurable M"
  shows "gfp F \<in> borel_measurable M"
proof -
  { fix i have "((F ^^ i) top) \<in> borel_measurable M"
      by (induct i) (auto intro!: * simp: bot_fun_def) }
  then have "(\<lambda>x. INF i. (F ^^ i) top x) \<in> borel_measurable M"
    by measurable
  also have "(\<lambda>x. INF i. (F ^^ i) top x) = (INF i. (F ^^ i) top)"
    by auto
  also have "\<dots> = gfp F"
    by (rule down_continuous_gfp[symmetric]) fact
  finally show ?thesis .
qed

subsection {* Borel spaces on euclidean spaces *}

lemma borel_measurable_inner[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_inner}"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x \<bullet> g x) \<in> borel_measurable M"
  using assms
  by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma [measurable]:
  fixes a b :: "'a\<Colon>linorder_topology"
  shows lessThan_borel: "{..< a} \<in> sets borel"
    and greaterThan_borel: "{a <..} \<in> sets borel"
    and greaterThanLessThan_borel: "{a<..<b} \<in> sets borel"
    and atMost_borel: "{..a} \<in> sets borel"
    and atLeast_borel: "{a..} \<in> sets borel"
    and atLeastAtMost_borel: "{a..b} \<in> sets borel"
    and greaterThanAtMost_borel: "{a<..b} \<in> sets borel"
    and atLeastLessThan_borel: "{a..<b} \<in> sets borel"
  unfolding greaterThanAtMost_def atLeastLessThan_def
  by (blast intro: borel_open borel_closed open_lessThan open_greaterThan open_greaterThanLessThan
                   closed_atMost closed_atLeast closed_atLeastAtMost)+

notation
  eucl_less (infix "<e" 50)

lemma box_oc: "{x. a <e x \<and> x \<le> b} = {x. a <e x} \<inter> {..b}"
  and box_co: "{x. a \<le> x \<and> x <e b} = {a..} \<inter> {x. x <e b}"
  by auto

lemma eucl_ivals[measurable]:
  fixes a b :: "'a\<Colon>ordered_euclidean_space"
  shows "{x. x <e a} \<in> sets borel"
    and "{x. a <e x} \<in> sets borel"
    and "{..a} \<in> sets borel"
    and "{a..} \<in> sets borel"
    and "{a..b} \<in> sets borel"
    and  "{x. a <e x \<and> x \<le> b} \<in> sets borel"
    and "{x. a \<le> x \<and>  x <e b} \<in> sets borel"
  unfolding box_oc box_co
  by (auto intro: borel_open borel_closed)

lemma open_Collect_less:
  fixes f g :: "'i::topological_space \<Rightarrow> 'a :: {dense_linorder, linorder_topology}"
  assumes "continuous_on UNIV f"
  assumes "continuous_on UNIV g"
  shows "open {x. f x < g x}"
proof -
  have "open (\<Union>y. {x \<in> UNIV. f x \<in> {..< y}} \<inter> {x \<in> UNIV. g x \<in> {y <..}})" (is "open ?X")
    by (intro open_UN ballI open_Int continuous_open_preimage assms) auto
  also have "?X = {x. f x < g x}"
    by (auto intro: dense)
  finally show ?thesis .
qed

lemma closed_Collect_le:
  fixes f g :: "'i::topological_space \<Rightarrow> 'a :: {dense_linorder, linorder_topology}"
  assumes f: "continuous_on UNIV f"
  assumes g: "continuous_on UNIV g"
  shows "closed {x. f x \<le> g x}"
  using open_Collect_less[OF g f] unfolding not_less[symmetric] Collect_neg_eq open_closed .

lemma borel_measurable_less[measurable]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, dense_linorder, linorder_topology}"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows "{w \<in> space M. f w < g w} \<in> sets M"
proof -
  have "{w \<in> space M. f w < g w} = (\<lambda>x. (f x, g x)) -` {x. fst x < snd x} \<inter> space M"
    by auto
  also have "\<dots> \<in> sets M"
    by (intro measurable_sets[OF borel_measurable_Pair borel_open, OF assms open_Collect_less]
              continuous_intros)
  finally show ?thesis .
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, dense_linorder, linorder_topology}"
  assumes f[measurable]: "f \<in> borel_measurable M"
  assumes g[measurable]: "g \<in> borel_measurable M"
  shows borel_measurable_le[measurable]: "{w \<in> space M. f w \<le> g w} \<in> sets M"
    and borel_measurable_eq[measurable]: "{w \<in> space M. f w = g w} \<in> sets M"
    and borel_measurable_neq: "{w \<in> space M. f w \<noteq> g w} \<in> sets M"
  unfolding eq_iff not_less[symmetric]
  by measurable

lemma 
  fixes i :: "'a::{second_countable_topology, real_inner}"
  shows hafspace_less_borel: "{x. a < x \<bullet> i} \<in> sets borel"
    and hafspace_greater_borel: "{x. x \<bullet> i < a} \<in> sets borel"
    and hafspace_less_eq_borel: "{x. a \<le> x \<bullet> i} \<in> sets borel"
    and hafspace_greater_eq_borel: "{x. x \<bullet> i \<le> a} \<in> sets borel"
  by simp_all

subsection "Borel space equals sigma algebras over intervals"

lemma borel_sigma_sets_subset:
  "A \<subseteq> sets borel \<Longrightarrow> sigma_sets UNIV A \<subseteq> sets borel"
  using sets.sigma_sets_subset[of A borel] by simp

lemma borel_eq_sigmaI1:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV (F ` A))"
  assumes F: "\<And>i. i \<in> A \<Longrightarrow> F i \<in> sets borel"
  shows "borel = sigma UNIV (F ` A)"
  unfolding borel_def
proof (intro sigma_eqI antisym)
  have borel_rev_eq: "sigma_sets UNIV {S::'a set. open S} = sets borel"
    unfolding borel_def by simp
  also have "\<dots> = sigma_sets UNIV X"
    unfolding borel_eq by simp
  also have "\<dots> \<subseteq> sigma_sets UNIV (F`A)"
    using X by (intro sigma_algebra.sigma_sets_subset[OF sigma_algebra_sigma_sets]) auto
  finally show "sigma_sets UNIV {S. open S} \<subseteq> sigma_sets UNIV (F`A)" .
  show "sigma_sets UNIV (F`A) \<subseteq> sigma_sets UNIV {S. open S}"
    unfolding borel_rev_eq using F by (intro borel_sigma_sets_subset) auto
qed auto

lemma borel_eq_sigmaI2:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV ((\<lambda>(i, j). G i j)`B)"
  assumes X: "\<And>i j. (i, j) \<in> B \<Longrightarrow> G i j \<in> sets (sigma UNIV ((\<lambda>(i, j). F i j) ` A))"
  assumes F: "\<And>i j. (i, j) \<in> A \<Longrightarrow> F i j \<in> sets borel"
  shows "borel = sigma UNIV ((\<lambda>(i, j). F i j) ` A)"
  using assms
  by (intro borel_eq_sigmaI1[where X="(\<lambda>(i, j). G i j) ` B" and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI3:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and X :: "'a::topological_space set set"
  assumes borel_eq: "borel = sigma UNIV X"
  assumes X: "\<And>x. x \<in> X \<Longrightarrow> x \<in> sets (sigma UNIV ((\<lambda>(i, j). F i j) ` A))"
  assumes F: "\<And>i j. (i, j) \<in> A \<Longrightarrow> F i j \<in> sets borel"
  shows "borel = sigma UNIV ((\<lambda>(i, j). F i j) ` A)"
  using assms by (intro borel_eq_sigmaI1[where X=X and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_sigmaI4:
  fixes F :: "'i \<Rightarrow> 'a::topological_space set"
    and G :: "'l \<Rightarrow> 'k \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV ((\<lambda>(i, j). G i j)`A)"
  assumes X: "\<And>i j. (i, j) \<in> A \<Longrightarrow> G i j \<in> sets (sigma UNIV (range F))"
  assumes F: "\<And>i. F i \<in> sets borel"
  shows "borel = sigma UNIV (range F)"
  using assms by (intro borel_eq_sigmaI1[where X="(\<lambda>(i, j). G i j) ` A" and F=F]) auto

lemma borel_eq_sigmaI5:
  fixes F :: "'i \<Rightarrow> 'j \<Rightarrow> 'a::topological_space set" and G :: "'l \<Rightarrow> 'a::topological_space set"
  assumes borel_eq: "borel = sigma UNIV (range G)"
  assumes X: "\<And>i. G i \<in> sets (sigma UNIV (range (\<lambda>(i, j). F i j)))"
  assumes F: "\<And>i j. F i j \<in> sets borel"
  shows "borel = sigma UNIV (range (\<lambda>(i, j). F i j))"
  using assms by (intro borel_eq_sigmaI1[where X="range G" and F="(\<lambda>(i, j). F i j)"]) auto

lemma borel_eq_box:
  "borel = sigma UNIV (range (\<lambda> (a, b). box a b :: 'a \<Colon> euclidean_space set))"
    (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI1[OF borel_def])
  fix M :: "'a set" assume "M \<in> {S. open S}"
  then have "open M" by simp
  show "M \<in> ?SIGMA"
    apply (subst open_UNION_box[OF `open M`])
    apply (safe intro!: sets.countable_UN' countable_PiE countable_Collect)
    apply (auto intro: countable_rat)
    done
qed (auto simp: box_def)

lemma halfspace_gt_in_halfspace:
  assumes i: "i \<in> A"
  shows "{x\<Colon>'a. a < x \<bullet> i} \<in> 
    sigma_sets UNIV ((\<lambda> (a, i). {x\<Colon>'a\<Colon>euclidean_space. x \<bullet> i < a}) ` (UNIV \<times> A))"
  (is "?set \<in> ?SIGMA")
proof -
  interpret sigma_algebra UNIV ?SIGMA
    by (intro sigma_algebra_sigma_sets) simp_all
  have *: "?set = (\<Union>n. UNIV - {x\<Colon>'a. x \<bullet> i < a + 1 / real (Suc n)})"
  proof (safe, simp_all add: not_less)
    fix x :: 'a assume "a < x \<bullet> i"
    with reals_Archimedean[of "x \<bullet> i - a"]
    obtain n where "a + 1 / real (Suc n) < x \<bullet> i"
      by (auto simp: field_simps)
    then show "\<exists>n. a + 1 / real (Suc n) \<le> x \<bullet> i"
      by (blast intro: less_imp_le)
  next
    fix x n
    have "a < a + 1 / real (Suc n)" by auto
    also assume "\<dots> \<le> x"
    finally show "a < x" .
  qed
  show "?set \<in> ?SIGMA" unfolding *
    by (auto del: Diff intro!: Diff i)
qed

lemma borel_eq_halfspace_less:
  "borel = sigma UNIV ((\<lambda>(a, i). {x::'a::euclidean_space. x \<bullet> i < a}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_box])
  fix a b :: 'a
  have "box a b = {x\<in>space ?SIGMA. \<forall>i\<in>Basis. a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i}"
    by (auto simp: box_def)
  also have "\<dots> \<in> sets ?SIGMA"
    by (intro sets.sets_Collect_conj sets.sets_Collect_finite_All sets.sets_Collect_const)
       (auto intro!: halfspace_gt_in_halfspace countable_PiE countable_rat)
  finally show "box a b \<in> sets ?SIGMA" .
qed auto

lemma borel_eq_halfspace_le:
  "borel = sigma UNIV ((\<lambda> (a, i). {x::'a::euclidean_space. x \<bullet> i \<le> a}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have i: "i \<in> Basis" by auto
  have *: "{x::'a. x\<bullet>i < a} = (\<Union>n. {x. x\<bullet>i \<le> a - 1/real (Suc n)})"
  proof (safe, simp_all)
    fix x::'a assume *: "x\<bullet>i < a"
    with reals_Archimedean[of "a - x\<bullet>i"]
    obtain n where "x \<bullet> i < a - 1 / (real (Suc n))"
      by (auto simp: field_simps)
    then show "\<exists>n. x \<bullet> i \<le> a - 1 / (real (Suc n))"
      by (blast intro: less_imp_le)
  next
    fix x::'a and n
    assume "x\<bullet>i \<le> a - 1 / real (Suc n)"
    also have "\<dots> < a" by auto
    finally show "x\<bullet>i < a" .
  qed
  show "{x. x\<bullet>i < a} \<in> ?SIGMA" unfolding *
    by (intro sets.countable_UN) (auto intro: i)
qed auto

lemma borel_eq_halfspace_ge:
  "borel = sigma UNIV ((\<lambda> (a, i). {x\<Colon>'a\<Colon>euclidean_space. a \<le> x \<bullet> i}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_less])
  fix a :: real and i :: 'a assume i: "(a, i) \<in> UNIV \<times> Basis"
  have *: "{x::'a. x\<bullet>i < a} = space ?SIGMA - {x::'a. a \<le> x\<bullet>i}" by auto
  show "{x. x\<bullet>i < a} \<in> ?SIGMA" unfolding *
    using i by (intro sets.compl_sets) auto
qed auto

lemma borel_eq_halfspace_greater:
  "borel = sigma UNIV ((\<lambda> (a, i). {x\<Colon>'a\<Colon>euclidean_space. a < x \<bullet> i}) ` (UNIV \<times> Basis))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI2[OF borel_eq_halfspace_le])
  fix a :: real and i :: 'a assume "(a, i) \<in> (UNIV \<times> Basis)"
  then have i: "i \<in> Basis" by auto
  have *: "{x::'a. x\<bullet>i \<le> a} = space ?SIGMA - {x::'a. a < x\<bullet>i}" by auto
  show "{x. x\<bullet>i \<le> a} \<in> ?SIGMA" unfolding *
    by (intro sets.compl_sets) (auto intro: i)
qed auto

lemma borel_eq_atMost:
  "borel = sigma UNIV (range (\<lambda>a. {..a\<Colon>'a\<Colon>ordered_euclidean_space}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have "i \<in> Basis" by auto
  then have *: "{x::'a. x\<bullet>i \<le> a} = (\<Union>k::nat. {.. (\<Sum>n\<in>Basis. (if n = i then a else real k)*\<^sub>R n)})"
  proof (safe, simp_all add: eucl_le[where 'a='a] split: split_if_asm)
    fix x :: 'a
    from real_arch_simple[of "Max ((\<lambda>i. x\<bullet>i)`Basis)"] guess k::nat ..
    then have "\<And>i. i \<in> Basis \<Longrightarrow> x\<bullet>i \<le> real k"
      by (subst (asm) Max_le_iff) auto
    then show "\<exists>k::nat. \<forall>ia\<in>Basis. ia \<noteq> i \<longrightarrow> x \<bullet> ia \<le> real k"
      by (auto intro!: exI[of _ k])
  qed
  show "{x. x\<bullet>i \<le> a} \<in> ?SIGMA" unfolding *
    by (intro sets.countable_UN) auto
qed auto

lemma borel_eq_greaterThan:
  "borel = sigma UNIV (range (\<lambda>a\<Colon>'a\<Colon>ordered_euclidean_space. {x. a <e x}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_le])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have i: "i \<in> Basis" by auto
  have "{x::'a. x\<bullet>i \<le> a} = UNIV - {x::'a. a < x\<bullet>i}" by auto
  also have *: "{x::'a. a < x\<bullet>i} =
      (\<Union>k::nat. {x. (\<Sum>n\<in>Basis. (if n = i then a else -real k) *\<^sub>R n) <e x})" using i
  proof (safe, simp_all add: eucl_less_def split: split_if_asm)
    fix x :: 'a
    from reals_Archimedean2[of "Max ((\<lambda>i. -x\<bullet>i)`Basis)"]
    guess k::nat .. note k = this
    { fix i :: 'a assume "i \<in> Basis"
      then have "-x\<bullet>i < real k"
        using k by (subst (asm) Max_less_iff) auto
      then have "- real k < x\<bullet>i" by simp }
    then show "\<exists>k::nat. \<forall>ia\<in>Basis. ia \<noteq> i \<longrightarrow> -real k < x \<bullet> ia"
      by (auto intro!: exI[of _ k])
  qed
  finally show "{x. x\<bullet>i \<le> a} \<in> ?SIGMA"
    apply (simp only:)
    apply (intro sets.countable_UN sets.Diff)
    apply (auto intro: sigma_sets_top)
    done
qed auto

lemma borel_eq_lessThan:
  "borel = sigma UNIV (range (\<lambda>a\<Colon>'a\<Colon>ordered_euclidean_space. {x. x <e a}))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI4[OF borel_eq_halfspace_ge])
  fix a :: real and i :: 'a assume "(a, i) \<in> UNIV \<times> Basis"
  then have i: "i \<in> Basis" by auto
  have "{x::'a. a \<le> x\<bullet>i} = UNIV - {x::'a. x\<bullet>i < a}" by auto
  also have *: "{x::'a. x\<bullet>i < a} = (\<Union>k::nat. {x. x <e (\<Sum>n\<in>Basis. (if n = i then a else real k) *\<^sub>R n)})" using `i\<in> Basis`
  proof (safe, simp_all add: eucl_less_def split: split_if_asm)
    fix x :: 'a
    from reals_Archimedean2[of "Max ((\<lambda>i. x\<bullet>i)`Basis)"]
    guess k::nat .. note k = this
    { fix i :: 'a assume "i \<in> Basis"
      then have "x\<bullet>i < real k"
        using k by (subst (asm) Max_less_iff) auto
      then have "x\<bullet>i < real k" by simp }
    then show "\<exists>k::nat. \<forall>ia\<in>Basis. ia \<noteq> i \<longrightarrow> x \<bullet> ia < real k"
      by (auto intro!: exI[of _ k])
  qed
  finally show "{x. a \<le> x\<bullet>i} \<in> ?SIGMA"
    apply (simp only:)
    apply (intro sets.countable_UN sets.Diff)
    apply (auto intro: sigma_sets_top )
    done
qed auto

lemma borel_eq_atLeastAtMost:
  "borel = sigma UNIV (range (\<lambda>(a,b). {a..b} \<Colon>'a\<Colon>ordered_euclidean_space set))"
  (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix a::'a
  have *: "{..a} = (\<Union>n::nat. {- real n *\<^sub>R One .. a})"
  proof (safe, simp_all add: eucl_le[where 'a='a])
    fix x :: 'a
    from real_arch_simple[of "Max ((\<lambda>i. - x\<bullet>i)`Basis)"]
    guess k::nat .. note k = this
    { fix i :: 'a assume "i \<in> Basis"
      with k have "- x\<bullet>i \<le> real k"
        by (subst (asm) Max_le_iff) (auto simp: field_simps)
      then have "- real k \<le> x\<bullet>i" by simp }
    then show "\<exists>n::nat. \<forall>i\<in>Basis. - real n \<le> x \<bullet> i"
      by (auto intro!: exI[of _ k])
  qed
  show "{..a} \<in> ?SIGMA" unfolding *
    by (intro sets.countable_UN)
       (auto intro!: sigma_sets_top)
qed auto

lemma borel_sigma_sets_Ioc: "borel = sigma UNIV (range (\<lambda>(a, b). {a <.. b::real}))"
proof (rule borel_eq_sigmaI5[OF borel_eq_atMost])
  fix i :: real
  have "{..i} = (\<Union>j::nat. {-j <.. i})"
    by (auto simp: minus_less_iff reals_Archimedean2)
  also have "\<dots> \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))"
    by (intro sets.countable_nat_UN) auto 
  finally show "{..i} \<in> sets (sigma UNIV (range (\<lambda>(i, j). {i<..j})))" .
qed simp

lemma eucl_lessThan: "{x::real. x <e a} = lessThan a"
  by (simp add: eucl_less_def lessThan_def)

lemma borel_eq_atLeastLessThan:
  "borel = sigma UNIV (range (\<lambda>(a, b). {a ..< b :: real}))" (is "_ = ?SIGMA")
proof (rule borel_eq_sigmaI5[OF borel_eq_lessThan])
  have move_uminus: "\<And>x y::real. -x \<le> y \<longleftrightarrow> -y \<le> x" by auto
  fix x :: real
  have "{..<x} = (\<Union>i::nat. {-real i ..< x})"
    by (auto simp: move_uminus real_arch_simple)
  then show "{y. y <e x} \<in> ?SIGMA"
    by (auto intro: sigma_sets.intros(2-) simp: eucl_lessThan)
qed auto

lemma borel_eq_closed: "borel = sigma UNIV (Collect closed)"
  unfolding borel_def
proof (intro sigma_eqI sigma_sets_eqI, safe)
  fix x :: "'a set" assume "open x"
  hence "x = UNIV - (UNIV - x)" by auto
  also have "\<dots> \<in> sigma_sets UNIV (Collect closed)"
    by (force intro: sigma_sets.Compl simp: `open x`)
  finally show "x \<in> sigma_sets UNIV (Collect closed)" by simp
next
  fix x :: "'a set" assume "closed x"
  hence "x = UNIV - (UNIV - x)" by auto
  also have "\<dots> \<in> sigma_sets UNIV (Collect open)"
    by (force intro: sigma_sets.Compl simp: `closed x`)
  finally show "x \<in> sigma_sets UNIV (Collect open)" by simp
qed simp_all

lemma borel_measurable_halfspacesI:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>euclidean_space"
  assumes F: "borel = sigma UNIV (F ` (UNIV \<times> Basis))"
  and S_eq: "\<And>a i. S a i = f -` F (a,i) \<inter> space M" 
  shows "f \<in> borel_measurable M = (\<forall>i\<in>Basis. \<forall>a::real. S a i \<in> sets M)"
proof safe
  fix a :: real and i :: 'b assume i: "i \<in> Basis" and f: "f \<in> borel_measurable M"
  then show "S a i \<in> sets M" unfolding assms
    by (auto intro!: measurable_sets simp: assms(1))
next
  assume a: "\<forall>i\<in>Basis. \<forall>a. S a i \<in> sets M"
  then show "f \<in> borel_measurable M"
    by (auto intro!: measurable_measure_of simp: S_eq F)
qed

lemma borel_measurable_iff_halfspace_le:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. f w \<bullet> i \<le> a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_le]) auto

lemma borel_measurable_iff_halfspace_less:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. f w \<bullet> i < a} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_less]) auto

lemma borel_measurable_iff_halfspace_ge:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>euclidean_space"
  shows "f \<in> borel_measurable M = (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. a \<le> f w \<bullet> i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_ge]) auto

lemma borel_measurable_iff_halfspace_greater:
  fixes f :: "'a \<Rightarrow> 'c\<Colon>euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i\<in>Basis. \<forall>a. {w \<in> space M. a < f w \<bullet> i} \<in> sets M)"
  by (rule borel_measurable_halfspacesI[OF borel_eq_halfspace_greater]) auto

lemma borel_measurable_iff_le:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w \<le> a} \<in> sets M)"
  using borel_measurable_iff_halfspace_le[where 'c=real] by simp

lemma borel_measurable_iff_less:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. f w < a} \<in> sets M)"
  using borel_measurable_iff_halfspace_less[where 'c=real] by simp

lemma borel_measurable_iff_ge:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a \<le> f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_ge[where 'c=real]
  by simp

lemma borel_measurable_iff_greater:
  "(f::'a \<Rightarrow> real) \<in> borel_measurable M = (\<forall>a. {w \<in> space M. a < f w} \<in> sets M)"
  using borel_measurable_iff_halfspace_greater[where 'c=real] by simp

lemma borel_measurable_euclidean_space:
  fixes f :: "'a \<Rightarrow> 'c::euclidean_space"
  shows "f \<in> borel_measurable M \<longleftrightarrow> (\<forall>i\<in>Basis. (\<lambda>x. f x \<bullet> i) \<in> borel_measurable M)"
proof safe
  assume f: "\<forall>i\<in>Basis. (\<lambda>x. f x \<bullet> i) \<in> borel_measurable M"
  then show "f \<in> borel_measurable M"
    by (subst borel_measurable_iff_halfspace_le) auto
qed auto

subsection "Borel measurable operators"

lemma borel_measurable_norm[measurable]: "norm \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_sgn [measurable]: "(sgn::'a::real_normed_vector \<Rightarrow> 'a) \<in> borel_measurable borel"
  by (rule borel_measurable_continuous_countable_exceptions[where X="{0}"])
     (auto intro!: continuous_on_sgn continuous_on_id)

lemma borel_measurable_uminus[measurable (raw)]:
  fixes g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. - g x) \<in> borel_measurable M"
  by (rule borel_measurable_continuous_on[OF _ g]) (intro continuous_intros)

lemma borel_measurable_add[measurable (raw)]:
  fixes f g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x + g x) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma borel_measurable_setsum[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_diff[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x - g x) \<in> borel_measurable M"
  using borel_measurable_add [of f M "- g"] assms by (simp add: fun_Compl_def)

lemma borel_measurable_times[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_algebra}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x * g x) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma borel_measurable_setprod[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> 'b::{second_countable_topology, real_normed_field}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
proof cases
  assume "finite S"
  thus ?thesis using assms by induct auto
qed simp

lemma borel_measurable_dist[measurable (raw)]:
  fixes g f :: "'a \<Rightarrow> 'b::{second_countable_topology, metric_space}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. dist (f x) (g x)) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)
  
lemma borel_measurable_scaleR[measurable (raw)]:
  fixes g :: "'a \<Rightarrow> 'b::{second_countable_topology, real_normed_vector}"
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  shows "(\<lambda>x. f x *\<^sub>R g x) \<in> borel_measurable M"
  using f g by (rule borel_measurable_continuous_Pair) (intro continuous_intros)

lemma affine_borel_measurable_vector:
  fixes f :: "'a \<Rightarrow> 'x::real_normed_vector"
  assumes "f \<in> borel_measurable M"
  shows "(\<lambda>x. a + b *\<^sub>R f x) \<in> borel_measurable M"
proof (rule borel_measurableI)
  fix S :: "'x set" assume "open S"
  show "(\<lambda>x. a + b *\<^sub>R f x) -` S \<inter> space M \<in> sets M"
  proof cases
    assume "b \<noteq> 0"
    with `open S` have "open ((\<lambda>x. (- a + x) /\<^sub>R b) ` S)" (is "open ?S")
      using open_affinity [of S "inverse b" "- a /\<^sub>R b"]
      by (auto simp: algebra_simps)
    hence "?S \<in> sets borel" by auto
    moreover
    from `b \<noteq> 0` have "(\<lambda>x. a + b *\<^sub>R f x) -` S = f -` ?S"
      apply auto by (rule_tac x="a + b *\<^sub>R f x" in image_eqI, simp_all)
    ultimately show ?thesis using assms unfolding in_borel_measurable_borel
      by auto
  qed simp
qed

lemma borel_measurable_const_scaleR[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. b *\<^sub>R f x ::'a::real_normed_vector) \<in> borel_measurable M"
  using affine_borel_measurable_vector[of f M 0 b] by simp

lemma borel_measurable_const_add[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. a + f x ::'a::real_normed_vector) \<in> borel_measurable M"
  using affine_borel_measurable_vector[of f M a 1] by simp

lemma borel_measurable_inverse[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_div_algebra"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. inverse (f x)) \<in> borel_measurable M"
  apply (rule measurable_compose[OF f])
  apply (rule borel_measurable_continuous_countable_exceptions[of "{0}"])
  apply (auto intro!: continuous_on_inverse continuous_on_id)
  done

lemma borel_measurable_divide[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    (\<lambda>x. f x / g x::'b::{second_countable_topology, real_normed_div_algebra}) \<in> borel_measurable M"
  by (simp add: divide_inverse)

lemma borel_measurable_max[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. max (g x) (f x) :: 'b::{second_countable_topology, dense_linorder, linorder_topology}) \<in> borel_measurable M"
  by (simp add: max_def)

lemma borel_measurable_min[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. min (g x) (f x) :: 'b::{second_countable_topology, dense_linorder, linorder_topology}) \<in> borel_measurable M"
  by (simp add: min_def)

lemma borel_measurable_Min[measurable (raw)]:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M) \<Longrightarrow> (\<lambda>x. Min ((\<lambda>i. f i x)`I) :: 'b::{second_countable_topology, dense_linorder, linorder_topology}) \<in> borel_measurable M"
proof (induct I rule: finite_induct)
  case (insert i I) then show ?case
    by (cases "I = {}") auto
qed auto

lemma borel_measurable_Max[measurable (raw)]:
  "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable M) \<Longrightarrow> (\<lambda>x. Max ((\<lambda>i. f i x)`I) :: 'b::{second_countable_topology, dense_linorder, linorder_topology}) \<in> borel_measurable M"
proof (induct I rule: finite_induct)
  case (insert i I) then show ?case
    by (cases "I = {}") auto
qed auto

lemma borel_measurable_abs[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. \<bar>f x :: real\<bar>) \<in> borel_measurable M"
  unfolding abs_real_def by simp

lemma borel_measurable_nth[measurable (raw)]:
  "(\<lambda>x::real^'n. x $ i) \<in> borel_measurable borel"
  by (simp add: cart_eq_inner_axis)

lemma convex_measurable:
  fixes A :: "'a :: euclidean_space set"
  shows "X \<in> borel_measurable M \<Longrightarrow> X ` space M \<subseteq> A \<Longrightarrow> open A \<Longrightarrow> convex_on A q \<Longrightarrow> 
    (\<lambda>x. q (X x)) \<in> borel_measurable M"
  by (rule measurable_compose[where f=X and N="restrict_space borel A"])
     (auto intro!: borel_measurable_continuous_on_restrict convex_on_continuous measurable_restrict_space2)

lemma borel_measurable_ln[measurable (raw)]:
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. ln (f x)) \<in> borel_measurable M"
  apply (rule measurable_compose[OF f])
  apply (rule borel_measurable_continuous_countable_exceptions[of "{0}"])
  apply (auto intro!: continuous_on_ln continuous_on_id)
  done

lemma borel_measurable_log[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow> (\<lambda>x. log (g x) (f x)) \<in> borel_measurable M"
  unfolding log_def by auto

lemma borel_measurable_exp[measurable]:
  "(exp::'a::{real_normed_field,banach}\<Rightarrow>'a) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_at_imp_continuous_on ballI isCont_exp)

lemma measurable_real_floor[measurable]:
  "(floor :: real \<Rightarrow> int) \<in> measurable borel (count_space UNIV)"
proof -
  have "\<And>a x. \<lfloor>x\<rfloor> = a \<longleftrightarrow> (real a \<le> x \<and> x < real (a + 1))"
    by (auto intro: floor_eq2)
  then show ?thesis
    by (auto simp: vimage_def measurable_count_space_eq2_countable)
qed

lemma measurable_real_ceiling[measurable]:
  "(ceiling :: real \<Rightarrow> int) \<in> measurable borel (count_space UNIV)"
  unfolding ceiling_def[abs_def] by simp

lemma borel_measurable_real_floor: "(\<lambda>x::real. real \<lfloor>x\<rfloor>) \<in> borel_measurable borel"
  by simp

lemma borel_measurable_root [measurable]: "root n \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_sqrt [measurable]: "sqrt \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_power [measurable (raw)]:
  fixes f :: "_ \<Rightarrow> 'b::{power,real_normed_algebra}"
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. (f x) ^ n) \<in> borel_measurable M"
  by (intro borel_measurable_continuous_on [OF _ f] continuous_intros)

lemma borel_measurable_Re [measurable]: "Re \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_Im [measurable]: "Im \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_of_real [measurable]: "(of_real :: _ \<Rightarrow> (_::real_normed_algebra)) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_sin [measurable]: "(sin :: _ \<Rightarrow> (_::{real_normed_field,banach})) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_cos [measurable]: "(cos :: _ \<Rightarrow> (_::{real_normed_field,banach})) \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_arctan [measurable]: "arctan \<in> borel_measurable borel"
  by (intro borel_measurable_continuous_on1 continuous_intros)

lemma borel_measurable_complex_iff:
  "f \<in> borel_measurable M \<longleftrightarrow>
    (\<lambda>x. Re (f x)) \<in> borel_measurable M \<and> (\<lambda>x. Im (f x)) \<in> borel_measurable M"
  apply auto
  apply (subst fun_complex_eq)
  apply (intro borel_measurable_add)
  apply auto
  done

subsection "Borel space on the extended reals"

lemma borel_measurable_ereal[measurable (raw)]:
  assumes f: "f \<in> borel_measurable M" shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  using continuous_on_ereal f by (rule borel_measurable_continuous_on)

lemma borel_measurable_real_of_ereal[measurable (raw)]:
  fixes f :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  shows "(\<lambda>x. real (f x)) \<in> borel_measurable M"
  apply (rule measurable_compose[OF f])
  apply (rule borel_measurable_continuous_countable_exceptions[of "{\<infinity>, -\<infinity> }"])
  apply (auto intro: continuous_on_real simp: Compl_eq_Diff_UNIV)
  done

lemma borel_measurable_ereal_cases:
  fixes f :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real (f x)))) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x)) \<in> borel_measurable M"
proof -
  let ?F = "\<lambda>x. if f x = \<infinity> then H \<infinity> else if f x = - \<infinity> then H (-\<infinity>) else H (ereal (real (f x)))"
  { fix x have "H (f x) = ?F x" by (cases "f x") auto }
  with f H show ?thesis by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f[measurable]: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_abs[measurable(raw)]: "(\<lambda>x. \<bar>f x\<bar>) \<in> borel_measurable M"
    and borel_measurable_ereal_inverse[measurable(raw)]: "(\<lambda>x. inverse (f x) :: ereal) \<in> borel_measurable M"
    and borel_measurable_uminus_ereal[measurable(raw)]: "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M"
  by (auto simp del: abs_real_of_ereal simp: borel_measurable_ereal_cases[OF f] measurable_If)

lemma borel_measurable_uminus_eq_ereal[simp]:
  "(\<lambda>x. - f x :: ereal) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M" (is "?l = ?r")
proof
  assume ?l from borel_measurable_uminus_ereal[OF this] show ?r by simp
qed auto

lemma set_Collect_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "{x \<in> space M. H (ereal (real (f x))) (ereal (real (g x)))} \<in> sets M"
    "{x \<in> space borel. H (-\<infinity>) (ereal x)} \<in> sets borel"
    "{x \<in> space borel. H (\<infinity>) (ereal x)} \<in> sets borel"
    "{x \<in> space borel. H (ereal x) (-\<infinity>)} \<in> sets borel"
    "{x \<in> space borel. H (ereal x) (\<infinity>)} \<in> sets borel"
  shows "{x \<in> space M. H (f x) (g x)} \<in> sets M"
proof -
  let ?G = "\<lambda>y x. if g x = \<infinity> then H y \<infinity> else if g x = -\<infinity> then H y (-\<infinity>) else H y (ereal (real (g x)))"
  let ?F = "\<lambda>x. if f x = \<infinity> then ?G \<infinity> x else if f x = -\<infinity> then ?G (-\<infinity>) x else ?G (ereal (real (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  note * = this
  from assms show ?thesis
    by (subst *) (simp del: space_borel split del: split_if)
qed

lemma borel_measurable_ereal_iff:
  shows "(\<lambda>x. ereal (f x)) \<in> borel_measurable M \<longleftrightarrow> f \<in> borel_measurable M"
proof
  assume "(\<lambda>x. ereal (f x)) \<in> borel_measurable M"
  from borel_measurable_real_of_ereal[OF this]
  show "f \<in> borel_measurable M" by auto
qed auto

lemma borel_measurable_erealD[measurable_dest]:
  "(\<lambda>x. ereal (f x)) \<in> borel_measurable M \<Longrightarrow> g \<in> measurable N M \<Longrightarrow> (\<lambda>x. f (g x)) \<in> borel_measurable N"
  unfolding borel_measurable_ereal_iff by simp

lemma borel_measurable_ereal_iff_real:
  fixes f :: "'a \<Rightarrow> ereal"
  shows "f \<in> borel_measurable M \<longleftrightarrow>
    ((\<lambda>x. real (f x)) \<in> borel_measurable M \<and> f -` {\<infinity>} \<inter> space M \<in> sets M \<and> f -` {-\<infinity>} \<inter> space M \<in> sets M)"
proof safe
  assume *: "(\<lambda>x. real (f x)) \<in> borel_measurable M" "f -` {\<infinity>} \<inter> space M \<in> sets M" "f -` {-\<infinity>} \<inter> space M \<in> sets M"
  have "f -` {\<infinity>} \<inter> space M = {x\<in>space M. f x = \<infinity>}" "f -` {-\<infinity>} \<inter> space M = {x\<in>space M. f x = -\<infinity>}" by auto
  with * have **: "{x\<in>space M. f x = \<infinity>} \<in> sets M" "{x\<in>space M. f x = -\<infinity>} \<in> sets M" by simp_all
  let ?f = "\<lambda>x. if f x = \<infinity> then \<infinity> else if f x = -\<infinity> then -\<infinity> else ereal (real (f x))"
  have "?f \<in> borel_measurable M" using * ** by (intro measurable_If) auto
  also have "?f = f" by (auto simp: fun_eq_iff ereal_real)
  finally show "f \<in> borel_measurable M" .
qed simp_all

lemma borel_measurable_ereal_iff_Iio:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..< a} \<inter> space M \<in> sets M)"
  by (auto simp: borel_Iio measurable_iff_measure_of)

lemma borel_measurable_ereal_iff_Ioi:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a <..} \<inter> space M \<in> sets M)"
  by (auto simp: borel_Ioi measurable_iff_measure_of)

lemma vimage_sets_compl_iff:
  "f -` A \<inter> space M \<in> sets M \<longleftrightarrow> f -` (- A) \<inter> space M \<in> sets M"
proof -
  { fix A assume "f -` A \<inter> space M \<in> sets M"
    moreover have "f -` (- A) \<inter> space M = space M - f -` A \<inter> space M" by auto
    ultimately have "f -` (- A) \<inter> space M \<in> sets M" by auto }
  from this[of A] this[of "-A"] show ?thesis
    by (metis double_complement)
qed

lemma borel_measurable_iff_Iic_ereal:
  "(f::'a\<Rightarrow>ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {..a} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_ereal_iff_Ioi vimage_sets_compl_iff[where A="{a <..}" for a] by simp

lemma borel_measurable_iff_Ici_ereal:
  "(f::'a \<Rightarrow> ereal) \<in> borel_measurable M \<longleftrightarrow> (\<forall>a. f -` {a..} \<inter> space M \<in> sets M)"
  unfolding borel_measurable_ereal_iff_Iio vimage_sets_compl_iff[where A="{..< a}" for a] by simp

lemma borel_measurable_ereal2:
  fixes f g :: "'a \<Rightarrow> ereal" 
  assumes f: "f \<in> borel_measurable M"
  assumes g: "g \<in> borel_measurable M"
  assumes H: "(\<lambda>x. H (ereal (real (f x))) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (-\<infinity>) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (\<infinity>) (ereal (real (g x)))) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real (f x))) (-\<infinity>)) \<in> borel_measurable M"
    "(\<lambda>x. H (ereal (real (f x))) (\<infinity>)) \<in> borel_measurable M"
  shows "(\<lambda>x. H (f x) (g x)) \<in> borel_measurable M"
proof -
  let ?G = "\<lambda>y x. if g x = \<infinity> then H y \<infinity> else if g x = - \<infinity> then H y (-\<infinity>) else H y (ereal (real (g x)))"
  let ?F = "\<lambda>x. if f x = \<infinity> then ?G \<infinity> x else if f x = - \<infinity> then ?G (-\<infinity>) x else ?G (ereal (real (f x))) x"
  { fix x have "H (f x) (g x) = ?F x" by (cases "f x" "g x" rule: ereal2_cases) auto }
  note * = this
  from assms show ?thesis unfolding * by simp
qed

lemma
  fixes f :: "'a \<Rightarrow> ereal" assumes f: "f \<in> borel_measurable M"
  shows borel_measurable_ereal_eq_const: "{x\<in>space M. f x = c} \<in> sets M"
    and borel_measurable_ereal_neq_const: "{x\<in>space M. f x \<noteq> c} \<in> sets M"
  using f by auto

lemma [measurable(raw)]:
  fixes f :: "'a \<Rightarrow> ereal"
  assumes [measurable]: "f \<in> borel_measurable M" "g \<in> borel_measurable M"
  shows borel_measurable_ereal_add: "(\<lambda>x. f x + g x) \<in> borel_measurable M"
    and borel_measurable_ereal_times: "(\<lambda>x. f x * g x) \<in> borel_measurable M"
    and borel_measurable_ereal_min: "(\<lambda>x. min (g x) (f x)) \<in> borel_measurable M"
    and borel_measurable_ereal_max: "(\<lambda>x. max (g x) (f x)) \<in> borel_measurable M"
  by (simp_all add: borel_measurable_ereal2 min_def max_def)

lemma [measurable(raw)]:
  fixes f g :: "'a \<Rightarrow> ereal"
  assumes "f \<in> borel_measurable M"
  assumes "g \<in> borel_measurable M"
  shows borel_measurable_ereal_diff: "(\<lambda>x. f x - g x) \<in> borel_measurable M"
    and borel_measurable_ereal_divide: "(\<lambda>x. f x / g x) \<in> borel_measurable M"
  using assms by (simp_all add: minus_ereal_def divide_ereal_def)

lemma borel_measurable_ereal_setsum[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Sum>i\<in>S. f i x) \<in> borel_measurable M"
  using assms by (induction S rule: infinite_finite_induct) auto

lemma borel_measurable_ereal_setprod[measurable (raw)]:
  fixes f :: "'c \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. i \<in> S \<Longrightarrow> f i \<in> borel_measurable M"
  shows "(\<lambda>x. \<Prod>i\<in>S. f i x) \<in> borel_measurable M"
  using assms by (induction S rule: infinite_finite_induct) auto

lemma [measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes "\<And>i. f i \<in> borel_measurable M"
  shows borel_measurable_liminf: "(\<lambda>x. liminf (\<lambda>i. f i x)) \<in> borel_measurable M"
    and borel_measurable_limsup: "(\<lambda>x. limsup (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding liminf_SUP_INF limsup_INF_SUP using assms by auto

lemma sets_Collect_eventually_sequentially[measurable]:
  "(\<And>i. {x\<in>space M. P x i} \<in> sets M) \<Longrightarrow> {x\<in>space M. eventually (P x) sequentially} \<in> sets M"
  unfolding eventually_sequentially by simp

lemma sets_Collect_ereal_convergent[measurable]: 
  fixes f :: "nat \<Rightarrow> 'a => ereal"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. convergent (\<lambda>i. f i x)} \<in> sets M"
  unfolding convergent_ereal by auto

lemma borel_measurable_extreal_lim[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  have "\<And>x. lim (\<lambda>i. f i x) = (if convergent (\<lambda>i. f i x) then limsup (\<lambda>i. f i x) else (THE i. False))"
    by (simp add: lim_def convergent_def convergent_limsup_cl)
  then show ?thesis
    by simp
qed

lemma borel_measurable_ereal_LIMSEQ:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> u' x = liminf (\<lambda>n. u n x)"
    using u' by (simp add: lim_imp_Liminf[symmetric])
  with u show ?thesis by (simp cong: measurable_cong)
qed

lemma borel_measurable_extreal_suminf[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> ereal"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. (\<Sum>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

subsection {* LIMSEQ is borel measurable *}

lemma borel_measurable_LIMSEQ:
  fixes u :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes u': "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. u i x) ----> u' x"
  and u: "\<And>i. u i \<in> borel_measurable M"
  shows "u' \<in> borel_measurable M"
proof -
  have "\<And>x. x \<in> space M \<Longrightarrow> liminf (\<lambda>n. ereal (u n x)) = ereal (u' x)"
    using u' by (simp add: lim_imp_Liminf)
  moreover from u have "(\<lambda>x. liminf (\<lambda>n. ereal (u n x))) \<in> borel_measurable M"
    by auto
  ultimately show ?thesis by (simp cong: measurable_cong add: borel_measurable_ereal_iff)
qed

lemma borel_measurable_LIMSEQ_metric:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b :: metric_space"
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable M"
  assumes lim: "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. f i x) ----> g x"
  shows "g \<in> borel_measurable M"
  unfolding borel_eq_closed
proof (safe intro!: measurable_measure_of)
  fix A :: "'b set" assume "closed A" 

  have [measurable]: "(\<lambda>x. infdist (g x) A) \<in> borel_measurable M"
  proof (rule borel_measurable_LIMSEQ)
    show "\<And>x. x \<in> space M \<Longrightarrow> (\<lambda>i. infdist (f i x) A) ----> infdist (g x) A"
      by (intro tendsto_infdist lim)
    show "\<And>i. (\<lambda>x. infdist (f i x) A) \<in> borel_measurable M"
      by (intro borel_measurable_continuous_on[where f="\<lambda>x. infdist x A"]
        continuous_at_imp_continuous_on ballI continuous_infdist isCont_ident) auto
  qed

  show "g -` A \<inter> space M \<in> sets M"
  proof cases
    assume "A \<noteq> {}"
    then have "\<And>x. infdist x A = 0 \<longleftrightarrow> x \<in> A"
      using `closed A` by (simp add: in_closed_iff_infdist_zero)
    then have "g -` A \<inter> space M = {x\<in>space M. infdist (g x) A = 0}"
      by auto
    also have "\<dots> \<in> sets M"
      by measurable
    finally show ?thesis .
  qed simp
qed auto

lemma sets_Collect_Cauchy[measurable]: 
  fixes f :: "nat \<Rightarrow> 'a => 'b::{metric_space, second_countable_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "{x\<in>space M. Cauchy (\<lambda>i. f i x)} \<in> sets M"
  unfolding metric_Cauchy_iff2 using f by auto

lemma borel_measurable_lim[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. lim (\<lambda>i. f i x)) \<in> borel_measurable M"
proof -
  def u' \<equiv> "\<lambda>x. lim (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)"
  then have *: "\<And>x. lim (\<lambda>i. f i x) = (if Cauchy (\<lambda>i. f i x) then u' x else (THE x. False))"
    by (auto simp: lim_def convergent_eq_cauchy[symmetric])
  have "u' \<in> borel_measurable M"
  proof (rule borel_measurable_LIMSEQ_metric)
    fix x
    have "convergent (\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0)"
      by (cases "Cauchy (\<lambda>i. f i x)")
         (auto simp add: convergent_eq_cauchy[symmetric] convergent_def)
    then show "(\<lambda>i. if Cauchy (\<lambda>i. f i x) then f i x else 0) ----> u' x"
      unfolding u'_def 
      by (rule convergent_LIMSEQ_iff[THEN iffD1])
  qed measurable
  then show ?thesis
    unfolding * by measurable
qed

lemma borel_measurable_suminf[measurable (raw)]:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes f[measurable]: "\<And>i. f i \<in> borel_measurable M"
  shows "(\<lambda>x. suminf (\<lambda>i. f i x)) \<in> borel_measurable M"
  unfolding suminf_def sums_def[abs_def] lim_def[symmetric] by simp

lemma borel_measurable_sup[measurable (raw)]:
  "f \<in> borel_measurable M \<Longrightarrow> g \<in> borel_measurable M \<Longrightarrow>
    (\<lambda>x. sup (f x) (g x)::ereal) \<in> borel_measurable M"
  by simp

(* Proof by Jeremy Avigad and Luke Serafin *)
lemma isCont_borel:
  fixes f :: "'b::metric_space \<Rightarrow> 'a::metric_space"
  shows "{x. isCont f x} \<in> sets borel"
proof -
  let ?I = "\<lambda>j. inverse(real (Suc j))"

  { fix x
    have "isCont f x = (\<forall>i. \<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i)"
      unfolding continuous_at_eps_delta
    proof safe
      fix i assume "\<forall>e>0. \<exists>d>0. \<forall>y. dist y x < d \<longrightarrow> dist (f y) (f x) < e"
      moreover have "0 < ?I i / 2"
        by simp
      ultimately obtain d where d: "0 < d" "\<And>y. dist x y < d \<Longrightarrow> dist (f y) (f x) < ?I i / 2"
        by (metis dist_commute)
      then obtain j where j: "?I j < d"
        by (metis reals_Archimedean)

      show "\<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i"
      proof (safe intro!: exI[where x=j])
        fix y z assume *: "dist x y < ?I j" "dist x z < ?I j"
        have "dist (f y) (f z) \<le> dist (f y) (f x) + dist (f z) (f x)"
          by (rule dist_triangle2)
        also have "\<dots> < ?I i / 2 + ?I i / 2"
          by (intro add_strict_mono d less_trans[OF _ j] *)
        also have "\<dots> \<le> ?I i"
          by (simp add: field_simps real_of_nat_Suc)
        finally show "dist (f y) (f z) \<le> ?I i"
          by simp
      qed
    next
      fix e::real assume "0 < e"
      then obtain n where n: "?I n < e"
        by (metis reals_Archimedean)
      assume "\<forall>i. \<exists>j. \<forall>y z. dist x y < ?I j \<and> dist x z < ?I j \<longrightarrow> dist (f y) (f z) \<le> ?I i"
      from this[THEN spec, of "Suc n"]
      obtain j where j: "\<And>y z. dist x y < ?I j \<Longrightarrow> dist x z < ?I j \<Longrightarrow> dist (f y) (f z) \<le> ?I (Suc n)"
        by auto
      
      show "\<exists>d>0. \<forall>y. dist y x < d \<longrightarrow> dist (f y) (f x) < e"
      proof (safe intro!: exI[of _ "?I j"])
        fix y assume "dist y x < ?I j"
        then have "dist (f y) (f x) \<le> ?I (Suc n)"
          by (intro j) (auto simp: dist_commute)
        also have "?I (Suc n) < ?I n"
          by simp
        also note n
        finally show "dist (f y) (f x) < e" .
      qed simp
    qed }
  note * = this

  have **: "\<And>e y. open {x. dist x y < e}"
    using open_ball by (simp_all add: ball_def dist_commute)

  have "{x\<in>space borel. isCont f x} \<in> sets borel"
    unfolding *
    apply (intro sets.sets_Collect_countable_All sets.sets_Collect_countable_Ex)
    apply (simp add: Collect_all_eq)
    apply (intro borel_closed closed_INT ballI closed_Collect_imp open_Collect_conj **)
    apply auto
    done
  then show ?thesis
    by simp
qed

no_notation
  eucl_less (infix "<e" 50)

end

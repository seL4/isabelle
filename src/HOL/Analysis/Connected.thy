(*  Author:     L C Paulson, University of Cambridge
    Material split off from Topology_Euclidean_Space
*)

section \<open>Connected Components, Homeomorphisms, Baire property, etc\<close>

theory Connected
  imports
    "HOL-Library.Indicator_Function"
    Topology_Euclidean_Space
begin

subsection%unimportant\<open>Lemmas Combining Imports\<close>

lemma isCont_indicator:
  fixes x :: "'a::t2_space"
  shows "isCont (indicator A :: 'a \<Rightarrow> real) x = (x \<notin> frontier A)"
proof auto
  fix x
  assume cts_at: "isCont (indicator A :: 'a \<Rightarrow> real) x" and fr: "x \<in> frontier A"
  with continuous_at_open have 1: "\<forall>V::real set. open V \<and> indicator A x \<in> V \<longrightarrow>
    (\<exists>U::'a set. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> V))" by auto
  show False
  proof (cases "x \<in> A")
    assume x: "x \<in> A"
    hence "indicator A x \<in> ({0<..<2} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({0<..<2} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y > (0::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> A" using indicator_eq_0_iff by force
    hence "x \<in> interior A" using U interiorI by auto
    thus ?thesis using fr unfolding frontier_def by simp
  next
    assume x: "x \<notin> A"
    hence "indicator A x \<in> ({-1<..<1} :: real set)" by simp
    hence "\<exists>U. open U \<and> x \<in> U \<and> (\<forall>y\<in>U. indicator A y \<in> ({-1<..<1} :: real set))"
      using 1 open_greaterThanLessThan by blast
    then guess U .. note U = this
    hence "\<forall>y\<in>U. indicator A y < (1::real)"
      unfolding greaterThanLessThan_def by auto
    hence "U \<subseteq> -A" by auto
    hence "x \<in> interior (-A)" using U interiorI by auto
    thus ?thesis using fr interior_complement unfolding frontier_def by auto
  qed
next
  assume nfr: "x \<notin> frontier A"
  hence "x \<in> interior A \<or> x \<in> interior (-A)"
    by (auto simp: frontier_def closure_interior)
  thus "isCont ((indicator A)::'a \<Rightarrow> real) x"
  proof
    assume int: "x \<in> interior A"
    then obtain U where U: "open U" "x \<in> U" "U \<subseteq> A" unfolding interior_def by auto
    hence "\<forall>y\<in>U. indicator A y = (1::real)" unfolding indicator_def by auto
    hence "continuous_on U (indicator A)" by (simp add: continuous_on_const indicator_eq_1_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  next
    assume ext: "x \<in> interior (-A)"
    then obtain U where U: "open U" "x \<in> U" "U \<subseteq> -A" unfolding interior_def by auto
    then have "continuous_on U (indicator A)"
      using continuous_on_topological by (auto simp: subset_iff)
    thus ?thesis using U continuous_on_eq_continuous_at by auto
  qed
qed


subsection%unimportant \<open>Connectedness\<close>

lemma connected_local:
 "connected S \<longleftrightarrow>
  \<not> (\<exists>e1 e2.
      openin (subtopology euclidean S) e1 \<and>
      openin (subtopology euclidean S) e2 \<and>
      S \<subseteq> e1 \<union> e2 \<and>
      e1 \<inter> e2 = {} \<and>
      e1 \<noteq> {} \<and>
      e2 \<noteq> {})"
  unfolding connected_def openin_open
  by safe blast+

lemma exists_diff:
  fixes P :: "'a set \<Rightarrow> bool"
  shows "(\<exists>S. P (- S)) \<longleftrightarrow> (\<exists>S. P S)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have ?rhs if ?lhs
    using that by blast
  moreover have "P (- (- S))" if "P S" for S
  proof -
    have "S = - (- S)" by simp
    with that show ?thesis by metis
  qed
  ultimately show ?thesis by metis
qed

lemma connected_clopen: "connected S \<longleftrightarrow>
  (\<forall>T. openin (subtopology euclidean S) T \<and>
     closedin (subtopology euclidean S) T \<longrightarrow> T = {} \<or> T = S)" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "\<not> connected S \<longleftrightarrow>
    (\<exists>e1 e2. open e1 \<and> open (- e2) \<and> S \<subseteq> e1 \<union> (- e2) \<and> e1 \<inter> (- e2) \<inter> S = {} \<and> e1 \<inter> S \<noteq> {} \<and> (- e2) \<inter> S \<noteq> {})"
    unfolding connected_def openin_open closedin_closed
    by (metis double_complement)
  then have th0: "connected S \<longleftrightarrow>
    \<not> (\<exists>e2 e1. closed e2 \<and> open e1 \<and> S \<subseteq> e1 \<union> (- e2) \<and> e1 \<inter> (- e2) \<inter> S = {} \<and> e1 \<inter> S \<noteq> {} \<and> (- e2) \<inter> S \<noteq> {})"
    (is " _ \<longleftrightarrow> \<not> (\<exists>e2 e1. ?P e2 e1)")
    by (simp add: closed_def) metis
  have th1: "?rhs \<longleftrightarrow> \<not> (\<exists>t' t. closed t'\<and>t = S\<inter>t' \<and> t\<noteq>{} \<and> t\<noteq>S \<and> (\<exists>t'. open t' \<and> t = S \<inter> t'))"
    (is "_ \<longleftrightarrow> \<not> (\<exists>t' t. ?Q t' t)")
    unfolding connected_def openin_open closedin_closed by auto
  have "(\<exists>e1. ?P e2 e1) \<longleftrightarrow> (\<exists>t. ?Q e2 t)" for e2
  proof -
    have "?P e2 e1 \<longleftrightarrow> (\<exists>t. closed e2 \<and> t = S\<inter>e2 \<and> open e1 \<and> t = S\<inter>e1 \<and> t\<noteq>{} \<and> t \<noteq> S)" for e1
      by auto
    then show ?thesis
      by metis
  qed
  then have "\<forall>e2. (\<exists>e1. ?P e2 e1) \<longleftrightarrow> (\<exists>t. ?Q e2 t)"
    by blast
  then show ?thesis
    by (simp add: th0 th1)
qed

lemma connected_linear_image:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::real_normed_vector"
  assumes "linear f" and "connected s"
  shows "connected (f ` s)"
using connected_continuous_image assms linear_continuous_on linear_conv_bounded_linear by blast

subsection \<open>Connected components, considered as a connectedness relation or a set\<close>

definition%important "connected_component s x y \<equiv> \<exists>t. connected t \<and> t \<subseteq> s \<and> x \<in> t \<and> y \<in> t"

abbreviation "connected_component_set s x \<equiv> Collect (connected_component s x)"

lemma connected_componentI:
  "connected t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> x \<in> t \<Longrightarrow> y \<in> t \<Longrightarrow> connected_component s x y"
  by (auto simp: connected_component_def)

lemma connected_component_in: "connected_component s x y \<Longrightarrow> x \<in> s \<and> y \<in> s"
  by (auto simp: connected_component_def)

lemma connected_component_refl: "x \<in> s \<Longrightarrow> connected_component s x x"
  by (auto simp: connected_component_def) (use connected_sing in blast)

lemma connected_component_refl_eq [simp]: "connected_component s x x \<longleftrightarrow> x \<in> s"
  by (auto simp: connected_component_refl) (auto simp: connected_component_def)

lemma connected_component_sym: "connected_component s x y \<Longrightarrow> connected_component s y x"
  by (auto simp: connected_component_def)

lemma connected_component_trans:
  "connected_component s x y \<Longrightarrow> connected_component s y z \<Longrightarrow> connected_component s x z"
  unfolding connected_component_def
  by (metis Int_iff Un_iff Un_subset_iff equals0D connected_Un)

lemma connected_component_of_subset:
  "connected_component s x y \<Longrightarrow> s \<subseteq> t \<Longrightarrow> connected_component t x y"
  by (auto simp: connected_component_def)

lemma connected_component_Union: "connected_component_set s x = \<Union>{t. connected t \<and> x \<in> t \<and> t \<subseteq> s}"
  by (auto simp: connected_component_def)

lemma connected_connected_component [iff]: "connected (connected_component_set s x)"
  by (auto simp: connected_component_Union intro: connected_Union)

lemma connected_iff_eq_connected_component_set:
  "connected s \<longleftrightarrow> (\<forall>x \<in> s. connected_component_set s x = s)"
proof (cases "s = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain x where "x \<in> s" by auto
  show ?thesis
  proof
    assume "connected s"
    then show "\<forall>x \<in> s. connected_component_set s x = s"
      by (force simp: connected_component_def)
  next
    assume "\<forall>x \<in> s. connected_component_set s x = s"
    then show "connected s"
      by (metis \<open>x \<in> s\<close> connected_connected_component)
  qed
qed

lemma connected_component_subset: "connected_component_set s x \<subseteq> s"
  using connected_component_in by blast

lemma connected_component_eq_self: "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> connected_component_set s x = s"
  by (simp add: connected_iff_eq_connected_component_set)

lemma connected_iff_connected_component:
  "connected s \<longleftrightarrow> (\<forall>x \<in> s. \<forall>y \<in> s. connected_component s x y)"
  using connected_component_in by (auto simp: connected_iff_eq_connected_component_set)

lemma connected_component_maximal:
  "x \<in> t \<Longrightarrow> connected t \<Longrightarrow> t \<subseteq> s \<Longrightarrow> t \<subseteq> (connected_component_set s x)"
  using connected_component_eq_self connected_component_of_subset by blast

lemma connected_component_mono:
  "s \<subseteq> t \<Longrightarrow> connected_component_set s x \<subseteq> connected_component_set t x"
  by (simp add: Collect_mono connected_component_of_subset)

lemma connected_component_eq_empty [simp]: "connected_component_set s x = {} \<longleftrightarrow> x \<notin> s"
  using connected_component_refl by (fastforce simp: connected_component_in)

lemma connected_component_set_empty [simp]: "connected_component_set {} x = {}"
  using connected_component_eq_empty by blast

lemma connected_component_eq:
  "y \<in> connected_component_set s x \<Longrightarrow> (connected_component_set s y = connected_component_set s x)"
  by (metis (no_types, lifting)
      Collect_cong connected_component_sym connected_component_trans mem_Collect_eq)

lemma closed_connected_component:
  assumes s: "closed s"
  shows "closed (connected_component_set s x)"
proof (cases "x \<in> s")
  case False
  then show ?thesis
    by (metis connected_component_eq_empty closed_empty)
next
  case True
  show ?thesis
    unfolding closure_eq [symmetric]
  proof
    show "closure (connected_component_set s x) \<subseteq> connected_component_set s x"
      apply (rule connected_component_maximal)
        apply (simp add: closure_def True)
       apply (simp add: connected_imp_connected_closure)
      apply (simp add: s closure_minimal connected_component_subset)
      done
  next
    show "connected_component_set s x \<subseteq> closure (connected_component_set s x)"
      by (simp add: closure_subset)
  qed
qed

lemma connected_component_disjoint:
  "connected_component_set s a \<inter> connected_component_set s b = {} \<longleftrightarrow>
    a \<notin> connected_component_set s b"
  apply (auto simp: connected_component_eq)
  using connected_component_eq connected_component_sym
  apply blast
  done

lemma connected_component_nonoverlap:
  "connected_component_set s a \<inter> connected_component_set s b = {} \<longleftrightarrow>
    a \<notin> s \<or> b \<notin> s \<or> connected_component_set s a \<noteq> connected_component_set s b"
  apply (auto simp: connected_component_in)
  using connected_component_refl_eq
    apply blast
   apply (metis connected_component_eq mem_Collect_eq)
  apply (metis connected_component_eq mem_Collect_eq)
  done

lemma connected_component_overlap:
  "connected_component_set s a \<inter> connected_component_set s b \<noteq> {} \<longleftrightarrow>
    a \<in> s \<and> b \<in> s \<and> connected_component_set s a = connected_component_set s b"
  by (auto simp: connected_component_nonoverlap)

lemma connected_component_sym_eq: "connected_component s x y \<longleftrightarrow> connected_component s y x"
  using connected_component_sym by blast

lemma connected_component_eq_eq:
  "connected_component_set s x = connected_component_set s y \<longleftrightarrow>
    x \<notin> s \<and> y \<notin> s \<or> x \<in> s \<and> y \<in> s \<and> connected_component s x y"
  apply (cases "y \<in> s", simp)
   apply (metis connected_component_eq connected_component_eq_empty connected_component_refl_eq mem_Collect_eq)
  apply (cases "x \<in> s", simp)
   apply (metis connected_component_eq_empty)
  using connected_component_eq_empty
  apply blast
  done

lemma connected_iff_connected_component_eq:
  "connected s \<longleftrightarrow> (\<forall>x \<in> s. \<forall>y \<in> s. connected_component_set s x = connected_component_set s y)"
  by (simp add: connected_component_eq_eq connected_iff_connected_component)

lemma connected_component_idemp:
  "connected_component_set (connected_component_set s x) x = connected_component_set s x"
  apply (rule subset_antisym)
   apply (simp add: connected_component_subset)
  apply (metis connected_component_eq_empty connected_component_maximal
      connected_component_refl_eq connected_connected_component mem_Collect_eq set_eq_subset)
  done

lemma connected_component_unique:
  "\<lbrakk>x \<in> c; c \<subseteq> s; connected c;
    \<And>c'. x \<in> c' \<and> c' \<subseteq> s \<and> connected c'
              \<Longrightarrow> c' \<subseteq> c\<rbrakk>
        \<Longrightarrow> connected_component_set s x = c"
apply (rule subset_antisym)
apply (meson connected_component_maximal connected_component_subset connected_connected_component contra_subsetD)
by (simp add: connected_component_maximal)

lemma joinable_connected_component_eq:
  "\<lbrakk>connected t; t \<subseteq> s;
    connected_component_set s x \<inter> t \<noteq> {};
    connected_component_set s y \<inter> t \<noteq> {}\<rbrakk>
    \<Longrightarrow> connected_component_set s x = connected_component_set s y"
apply (simp add: ex_in_conv [symmetric])
apply (rule connected_component_eq)
by (metis (no_types, hide_lams) connected_component_eq_eq connected_component_in connected_component_maximal subsetD mem_Collect_eq)


lemma Union_connected_component: "\<Union>(connected_component_set s ` s) = s"
  apply (rule subset_antisym)
  apply (simp add: SUP_least connected_component_subset)
  using connected_component_refl_eq
  by force


lemma complement_connected_component_unions:
    "s - connected_component_set s x =
     \<Union>(connected_component_set s ` s - {connected_component_set s x})"
  apply (subst Union_connected_component [symmetric], auto)
  apply (metis connected_component_eq_eq connected_component_in)
  by (metis connected_component_eq mem_Collect_eq)

lemma connected_component_intermediate_subset:
        "\<lbrakk>connected_component_set u a \<subseteq> t; t \<subseteq> u\<rbrakk>
        \<Longrightarrow> connected_component_set t a = connected_component_set u a"
  apply (case_tac "a \<in> u")
  apply (simp add: connected_component_maximal connected_component_mono subset_antisym)
  using connected_component_eq_empty by blast


subsection \<open>The set of connected components of a set\<close>

definition%important components:: "'a::topological_space set \<Rightarrow> 'a set set"
  where "components s \<equiv> connected_component_set s ` s"

lemma components_iff: "s \<in> components u \<longleftrightarrow> (\<exists>x. x \<in> u \<and> s = connected_component_set u x)"
  by (auto simp: components_def)

lemma componentsI: "x \<in> u \<Longrightarrow> connected_component_set u x \<in> components u"
  by (auto simp: components_def)

lemma componentsE:
  assumes "s \<in> components u"
  obtains x where "x \<in> u" "s = connected_component_set u x"
  using assms by (auto simp: components_def)

lemma Union_components [simp]: "\<Union>(components u) = u"
  apply (rule subset_antisym)
  using Union_connected_component components_def apply fastforce
  apply (metis Union_connected_component components_def set_eq_subset)
  done

lemma pairwise_disjoint_components: "pairwise (\<lambda>X Y. X \<inter> Y = {}) (components u)"
  apply (simp add: pairwise_def)
  apply (auto simp: components_iff)
  apply (metis connected_component_eq_eq connected_component_in)+
  done

lemma in_components_nonempty: "c \<in> components s \<Longrightarrow> c \<noteq> {}"
    by (metis components_iff connected_component_eq_empty)

lemma in_components_subset: "c \<in> components s \<Longrightarrow> c \<subseteq> s"
  using Union_components by blast

lemma in_components_connected: "c \<in> components s \<Longrightarrow> connected c"
  by (metis components_iff connected_connected_component)

lemma in_components_maximal:
  "c \<in> components s \<longleftrightarrow>
    c \<noteq> {} \<and> c \<subseteq> s \<and> connected c \<and> (\<forall>d. d \<noteq> {} \<and> c \<subseteq> d \<and> d \<subseteq> s \<and> connected d \<longrightarrow> d = c)"
  apply (rule iffI)
   apply (simp add: in_components_nonempty in_components_connected)
   apply (metis (full_types) components_iff connected_component_eq_self connected_component_intermediate_subset connected_component_refl in_components_subset mem_Collect_eq rev_subsetD)
  apply (metis bot.extremum_uniqueI components_iff connected_component_eq_empty connected_component_maximal connected_component_subset connected_connected_component subset_emptyI)
  done

lemma joinable_components_eq:
  "connected t \<and> t \<subseteq> s \<and> c1 \<in> components s \<and> c2 \<in> components s \<and> c1 \<inter> t \<noteq> {} \<and> c2 \<inter> t \<noteq> {} \<Longrightarrow> c1 = c2"
  by (metis (full_types) components_iff joinable_connected_component_eq)

lemma closed_components: "\<lbrakk>closed s; c \<in> components s\<rbrakk> \<Longrightarrow> closed c"
  by (metis closed_connected_component components_iff)

lemma compact_components:
  fixes s :: "'a::heine_borel set"
  shows "\<lbrakk>compact s; c \<in> components s\<rbrakk> \<Longrightarrow> compact c"
by (meson bounded_subset closed_components in_components_subset compact_eq_bounded_closed)

lemma components_nonoverlap:
    "\<lbrakk>c \<in> components s; c' \<in> components s\<rbrakk> \<Longrightarrow> (c \<inter> c' = {}) \<longleftrightarrow> (c \<noteq> c')"
  apply (auto simp: in_components_nonempty components_iff)
    using connected_component_refl apply blast
   apply (metis connected_component_eq_eq connected_component_in)
  by (metis connected_component_eq mem_Collect_eq)

lemma components_eq: "\<lbrakk>c \<in> components s; c' \<in> components s\<rbrakk> \<Longrightarrow> (c = c' \<longleftrightarrow> c \<inter> c' \<noteq> {})"
  by (metis components_nonoverlap)

lemma components_eq_empty [simp]: "components s = {} \<longleftrightarrow> s = {}"
  by (simp add: components_def)

lemma components_empty [simp]: "components {} = {}"
  by simp

lemma connected_eq_connected_components_eq: "connected s \<longleftrightarrow> (\<forall>c \<in> components s. \<forall>c' \<in> components s. c = c')"
  by (metis (no_types, hide_lams) components_iff connected_component_eq_eq connected_iff_connected_component)

lemma components_eq_sing_iff: "components s = {s} \<longleftrightarrow> connected s \<and> s \<noteq> {}"
  apply (rule iffI)
  using in_components_connected apply fastforce
  apply safe
  using Union_components apply fastforce
   apply (metis components_iff connected_component_eq_self)
  using in_components_maximal
  apply auto
  done

lemma components_eq_sing_exists: "(\<exists>a. components s = {a}) \<longleftrightarrow> connected s \<and> s \<noteq> {}"
  apply (rule iffI)
  using connected_eq_connected_components_eq apply fastforce
  apply (metis components_eq_sing_iff)
  done

lemma connected_eq_components_subset_sing: "connected s \<longleftrightarrow> components s \<subseteq> {s}"
  by (metis Union_components components_empty components_eq_sing_iff connected_empty insert_subset order_refl subset_singletonD)

lemma connected_eq_components_subset_sing_exists: "connected s \<longleftrightarrow> (\<exists>a. components s \<subseteq> {a})"
  by (metis components_eq_sing_exists connected_eq_components_subset_sing empty_iff subset_iff subset_singletonD)

lemma in_components_self: "s \<in> components s \<longleftrightarrow> connected s \<and> s \<noteq> {}"
  by (metis components_empty components_eq_sing_iff empty_iff in_components_connected insertI1)

lemma components_maximal: "\<lbrakk>c \<in> components s; connected t; t \<subseteq> s; c \<inter> t \<noteq> {}\<rbrakk> \<Longrightarrow> t \<subseteq> c"
  apply (simp add: components_def ex_in_conv [symmetric], clarify)
  by (meson connected_component_def connected_component_trans)

lemma exists_component_superset: "\<lbrakk>t \<subseteq> s; s \<noteq> {}; connected t\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> components s \<and> t \<subseteq> c"
  apply (cases "t = {}", force)
  apply (metis components_def ex_in_conv connected_component_maximal contra_subsetD image_eqI)
  done

lemma components_intermediate_subset: "\<lbrakk>s \<in> components u; s \<subseteq> t; t \<subseteq> u\<rbrakk> \<Longrightarrow> s \<in> components t"
  apply (auto simp: components_iff)
  apply (metis connected_component_eq_empty connected_component_intermediate_subset)
  done

lemma in_components_unions_complement: "c \<in> components s \<Longrightarrow> s - c = \<Union>(components s - {c})"
  by (metis complement_connected_component_unions components_def components_iff)

lemma connected_intermediate_closure:
  assumes cs: "connected s" and st: "s \<subseteq> t" and ts: "t \<subseteq> closure s"
  shows "connected t"
proof (rule connectedI)
  fix A B
  assume A: "open A" and B: "open B" and Alap: "A \<inter> t \<noteq> {}" and Blap: "B \<inter> t \<noteq> {}"
    and disj: "A \<inter> B \<inter> t = {}" and cover: "t \<subseteq> A \<union> B"
  have disjs: "A \<inter> B \<inter> s = {}"
    using disj st by auto
  have "A \<inter> closure s \<noteq> {}"
    using Alap Int_absorb1 ts by blast
  then have Alaps: "A \<inter> s \<noteq> {}"
    by (simp add: A open_Int_closure_eq_empty)
  have "B \<inter> closure s \<noteq> {}"
    using Blap Int_absorb1 ts by blast
  then have Blaps: "B \<inter> s \<noteq> {}"
    by (simp add: B open_Int_closure_eq_empty)
  then show False
    using cs [unfolded connected_def] A B disjs Alaps Blaps cover st
    by blast
qed

lemma closedin_connected_component: "closedin (subtopology euclidean s) (connected_component_set s x)"
proof (cases "connected_component_set s x = {}")
  case True
  then show ?thesis
    by (metis closedin_empty)
next
  case False
  then obtain y where y: "connected_component s x y"
    by blast
  have *: "connected_component_set s x \<subseteq> s \<inter> closure (connected_component_set s x)"
    by (auto simp: closure_def connected_component_in)
  have "connected_component s x y \<Longrightarrow> s \<inter> closure (connected_component_set s x) \<subseteq> connected_component_set s x"
    apply (rule connected_component_maximal, simp)
    using closure_subset connected_component_in apply fastforce
    using * connected_intermediate_closure apply blast+
    done
  with y * show ?thesis
    by (auto simp: closedin_closed)
qed

lemma closedin_component:
   "C \<in> components s \<Longrightarrow> closedin (subtopology euclidean s) C"
  using closedin_connected_component componentsE by blast


subsection%unimportant\<open>Quotient maps\<close>

lemma quotient_map_imp_continuous_open:
  assumes T: "f ` S \<subseteq> T"
      and ope: "\<And>U. U \<subseteq> T
              \<Longrightarrow> (openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
                   openin (subtopology euclidean T) U)"
    shows "continuous_on S f"
proof -
  have [simp]: "S \<inter> f -` f ` S = S" by auto
  show ?thesis
    using ope [OF T]
    apply (simp add: continuous_on_open)
    by (meson ope openin_imp_subset openin_trans)
qed

lemma quotient_map_imp_continuous_closed:
  assumes T: "f ` S \<subseteq> T"
      and ope: "\<And>U. U \<subseteq> T
                  \<Longrightarrow> (closedin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
                       closedin (subtopology euclidean T) U)"
    shows "continuous_on S f"
proof -
  have [simp]: "S \<inter> f -` f ` S = S" by auto
  show ?thesis
    using ope [OF T]
    apply (simp add: continuous_on_closed)
    by (metis (no_types, lifting) ope closedin_imp_subset closedin_trans)
qed

lemma open_map_imp_quotient_map:
  assumes contf: "continuous_on S f"
      and T: "T \<subseteq> f ` S"
      and ope: "\<And>T. openin (subtopology euclidean S) T
                   \<Longrightarrow> openin (subtopology euclidean (f ` S)) (f ` T)"
    shows "openin (subtopology euclidean S) (S \<inter> f -` T) =
           openin (subtopology euclidean (f ` S)) T"
proof -
  have "T = f ` (S \<inter> f -` T)"
    using T by blast
  then show ?thesis
    using "ope" contf continuous_on_open by metis
qed

lemma closed_map_imp_quotient_map:
  assumes contf: "continuous_on S f"
      and T: "T \<subseteq> f ` S"
      and ope: "\<And>T. closedin (subtopology euclidean S) T
              \<Longrightarrow> closedin (subtopology euclidean (f ` S)) (f ` T)"
    shows "openin (subtopology euclidean S) (S \<inter> f -` T) \<longleftrightarrow>
           openin (subtopology euclidean (f ` S)) T"
          (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have *: "closedin (subtopology euclidean S) (S - (S \<inter> f -` T))"
    using closedin_diff by fastforce
  have [simp]: "(f ` S - f ` (S - (S \<inter> f -` T))) = T"
    using T by blast
  show ?rhs
    using ope [OF *, unfolded closedin_def] by auto
next
  assume ?rhs
  with contf show ?lhs
    by (auto simp: continuous_on_open)
qed

lemma continuous_right_inverse_imp_quotient_map:
  assumes contf: "continuous_on S f" and imf: "f ` S \<subseteq> T"
      and contg: "continuous_on T g" and img: "g ` T \<subseteq> S"
      and fg [simp]: "\<And>y. y \<in> T \<Longrightarrow> f(g y) = y"
      and U: "U \<subseteq> T"
    shows "openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (subtopology euclidean T) U"
          (is "?lhs = ?rhs")
proof -
  have f: "\<And>Z. openin (subtopology euclidean (f ` S)) Z \<Longrightarrow>
                openin (subtopology euclidean S) (S \<inter> f -` Z)"
  and  g: "\<And>Z. openin (subtopology euclidean (g ` T)) Z \<Longrightarrow>
                openin (subtopology euclidean T) (T \<inter> g -` Z)"
    using contf contg by (auto simp: continuous_on_open)
  show ?thesis
  proof
    have "T \<inter> g -` (g ` T \<inter> (S \<inter> f -` U)) = {x \<in> T. f (g x) \<in> U}"
      using imf img by blast
    also have "... = U"
      using U by auto
    finally have eq: "T \<inter> g -` (g ` T \<inter> (S \<inter> f -` U)) = U" .
    assume ?lhs
    then have *: "openin (subtopology euclidean (g ` T)) (g ` T \<inter> (S \<inter> f -` U))"
      by (meson img openin_Int openin_subtopology_Int_subset openin_subtopology_self)
    show ?rhs
      using g [OF *] eq by auto
  next
    assume rhs: ?rhs
    show ?lhs
      by (metis f fg image_eqI image_subset_iff imf img openin_subopen openin_subtopology_self openin_trans rhs)
  qed
qed

lemma continuous_left_inverse_imp_quotient_map:
  assumes "continuous_on S f"
      and "continuous_on (f ` S) g"
      and  "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
      and "U \<subseteq> f ` S"
    shows "openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (subtopology euclidean (f ` S)) U"
apply (rule continuous_right_inverse_imp_quotient_map)
using assms apply force+
done


subsection%unimportant \<open>Proving a function is constant by proving that a level set is open\<close>

lemma continuous_levelset_openin_cases:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (subtopology euclidean s) {x \<in> s. f x = a}
        \<Longrightarrow> (\<forall>x \<in> s. f x \<noteq> a) \<or> (\<forall>x \<in> s. f x = a)"
  unfolding connected_clopen
  using continuous_closedin_preimage_constant by auto

lemma continuous_levelset_openin:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (subtopology euclidean s) {x \<in> s. f x = a} \<Longrightarrow>
        (\<exists>x \<in> s. f x = a)  \<Longrightarrow> (\<forall>x \<in> s. f x = a)"
  using continuous_levelset_openin_cases[of s f ]
  by meson

lemma continuous_levelset_open:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  assumes "connected s"
    and "continuous_on s f"
    and "open {x \<in> s. f x = a}"
    and "\<exists>x \<in> s.  f x = a"
  shows "\<forall>x \<in> s. f x = a"
  using continuous_levelset_openin[OF assms(1,2), of a, unfolded openin_open]
  using assms (3,4)
  by fast


subsection%unimportant \<open>Connectedness is invariant under homeomorphisms.\<close>

lemma homeomorphic_connectedness:
  assumes "s homeomorphic t"
  shows "connected s \<longleftrightarrow> connected t"
using assms unfolding homeomorphic_def homeomorphism_def by (metis connected_continuous_image)


subsection\<open>Various separability-type properties\<close>

lemma univ_second_countable:
  obtains \<B> :: "'a::euclidean_space set set"
  where "countable \<B>" "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
       "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
by (metis ex_countable_basis topological_basis_def)

lemma subset_second_countable:
  obtains \<B> :: "'a:: euclidean_space set set"
    where "countable \<B>"
          "{} \<notin> \<B>"
          "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
          "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>"
      and opeB: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
      and \<B>:    "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
  proof -
    obtain \<C> :: "'a set set"
      where "countable \<C>" and ope: "\<And>C. C \<in> \<C> \<Longrightarrow> open C"
        and \<C>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<C> \<and> S = \<Union>U"
      by (metis univ_second_countable that)
    show ?thesis
    proof
      show "countable ((\<lambda>C. S \<inter> C) ` \<C>)"
        by (simp add: \<open>countable \<C>\<close>)
      show "\<And>C. C \<in> (\<inter>) S ` \<C> \<Longrightarrow> openin (subtopology euclidean S) C"
        using ope by auto
      show "\<And>T. openin (subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>\<subseteq>(\<inter>) S ` \<C>. T = \<Union>\<U>"
        by (metis \<C> image_mono inf_Sup openin_open)
    qed
  qed
  show ?thesis
  proof
    show "countable (\<B> - {{}})"
      using \<open>countable \<B>\<close> by blast
    show "\<And>C. \<lbrakk>C \<in> \<B> - {{}}\<rbrakk> \<Longrightarrow> openin (subtopology euclidean S) C"
      by (simp add: \<open>\<And>C. C \<in> \<B> \<Longrightarrow> openin (subtopology euclidean S) C\<close>)
    show "\<exists>\<U>\<subseteq>\<B> - {{}}. T = \<Union>\<U>" if "openin (subtopology euclidean S) T" for T
      using \<B> [OF that]
      apply clarify
      apply (rule_tac x="\<U> - {{}}" in exI, auto)
        done
  qed auto
qed

lemma univ_second_countable_sequence:
  obtains B :: "nat \<Rightarrow> 'a::euclidean_space set"
    where "inj B" "\<And>n. open(B n)" "\<And>S. open S \<Longrightarrow> \<exists>k. S = \<Union>{B n |n. n \<in> k}"
proof -
  obtain \<B> :: "'a set set"
  where "countable \<B>"
    and opn: "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
    and Un: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
    using univ_second_countable by blast
  have *: "infinite (range (\<lambda>n. ball (0::'a) (inverse(Suc n))))"
    apply (rule Infinite_Set.range_inj_infinite)
    apply (simp add: inj_on_def ball_eq_ball_iff)
    done
  have "infinite \<B>"
  proof
    assume "finite \<B>"
    then have "finite (Union ` (Pow \<B>))"
      by simp
    then have "finite (range (\<lambda>n. ball (0::'a) (inverse(Suc n))))"
      apply (rule rev_finite_subset)
      by (metis (no_types, lifting) PowI image_eqI image_subset_iff Un [OF open_ball])
    with * show False by simp
  qed
  obtain f :: "nat \<Rightarrow> 'a set" where "\<B> = range f" "inj f"
    by (blast intro: countable_as_injective_image [OF \<open>countable \<B>\<close> \<open>infinite \<B>\<close>])
  have *: "\<exists>k. S = \<Union>{f n |n. n \<in> k}" if "open S" for S
    using Un [OF that]
    apply clarify
    apply (rule_tac x="f-`U" in exI)
    using \<open>inj f\<close> \<open>\<B> = range f\<close> apply force
    done
  show ?thesis
    apply (rule that [OF \<open>inj f\<close> _ *])
    apply (auto simp: \<open>\<B> = range f\<close> opn)
    done
qed

proposition separable:
  fixes S :: "'a:: euclidean_space set"
  obtains T where "countable T" "T \<subseteq> S" "S \<subseteq> closure T"
proof -
  obtain \<B> :: "'a:: euclidean_space set set"
    where "countable \<B>"
      and "{} \<notin> \<B>"
      and ope: "\<And>C. C \<in> \<B> \<Longrightarrow> openin(subtopology euclidean S) C"
      and if_ope: "\<And>T. openin(subtopology euclidean S) T \<Longrightarrow> \<exists>\<U>. \<U> \<subseteq> \<B> \<and> T = \<Union>\<U>"
    by (meson subset_second_countable)
  then obtain f where f: "\<And>C. C \<in> \<B> \<Longrightarrow> f C \<in> C"
    by (metis equals0I)
  show ?thesis
  proof
    show "countable (f ` \<B>)"
      by (simp add: \<open>countable \<B>\<close>)
    show "f ` \<B> \<subseteq> S"
      using ope f openin_imp_subset by blast
    show "S \<subseteq> closure (f ` \<B>)"
    proof (clarsimp simp: closure_approachable)
      fix x and e::real
      assume "x \<in> S" "0 < e"
      have "openin (subtopology euclidean S) (S \<inter> ball x e)"
        by (simp add: openin_Int_open)
      with if_ope obtain \<U> where  \<U>: "\<U> \<subseteq> \<B>" "S \<inter> ball x e = \<Union>\<U>"
        by meson
      show "\<exists>C \<in> \<B>. dist (f C) x < e"
      proof (cases "\<U> = {}")
        case True
        then show ?thesis
          using \<open>0 < e\<close>  \<U> \<open>x \<in> S\<close> by auto
      next
        case False
        then obtain C where "C \<in> \<U>" by blast
        show ?thesis
        proof
          show "dist (f C) x < e"
            by (metis Int_iff Union_iff \<U> \<open>C \<in> \<U>\<close> dist_commute f mem_ball subsetCE)
          show "C \<in> \<B>"
            using \<open>\<U> \<subseteq> \<B>\<close> \<open>C \<in> \<U>\<close> by blast
        qed
      qed
    qed
  qed
qed

proposition Lindelof:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes \<F>: "\<And>S. S \<in> \<F> \<Longrightarrow> open S"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
proof -
  obtain \<B> :: "'a set set"
    where "countable \<B>" "\<And>C. C \<in> \<B> \<Longrightarrow> open C"
      and \<B>: "\<And>S. open S \<Longrightarrow> \<exists>U. U \<subseteq> \<B> \<and> S = \<Union>U"
    using univ_second_countable by blast
  define \<D> where "\<D> \<equiv> {S. S \<in> \<B> \<and> (\<exists>U. U \<in> \<F> \<and> S \<subseteq> U)}"
  have "countable \<D>"
    apply (rule countable_subset [OF _ \<open>countable \<B>\<close>])
    apply (force simp: \<D>_def)
    done
  have "\<And>S. \<exists>U. S \<in> \<D> \<longrightarrow> U \<in> \<F> \<and> S \<subseteq> U"
    by (simp add: \<D>_def)
  then obtain G where G: "\<And>S. S \<in> \<D> \<longrightarrow> G S \<in> \<F> \<and> S \<subseteq> G S"
    by metis
  have "\<Union>\<F> \<subseteq> \<Union>\<D>"
    unfolding \<D>_def by (blast dest: \<F> \<B>)
  moreover have "\<Union>\<D> \<subseteq> \<Union>\<F>"
    using \<D>_def by blast
  ultimately have eq1: "\<Union>\<F> = \<Union>\<D>" ..
  have eq2: "\<Union>\<D> = \<Union> (G ` \<D>)"
    using G eq1 by auto
  show ?thesis
    apply (rule_tac \<F>' = "G ` \<D>" in that)
    using G \<open>countable \<D>\<close>  apply (auto simp: eq1 eq2)
    done
qed

lemma Lindelof_openin:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> openin (subtopology euclidean U) S"
  obtains \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
proof -
  have "\<And>S. S \<in> \<F> \<Longrightarrow> \<exists>T. open T \<and> S = U \<inter> T"
    using assms by (simp add: openin_open)
  then obtain tf where tf: "\<And>S. S \<in> \<F> \<Longrightarrow> open (tf S) \<and> (S = U \<inter> tf S)"
    by metis
  have [simp]: "\<And>\<F>'. \<F>' \<subseteq> \<F> \<Longrightarrow> \<Union>\<F>' = U \<inter> \<Union>(tf ` \<F>')"
    using tf by fastforce
  obtain \<G> where "countable \<G> \<and> \<G> \<subseteq> tf ` \<F>" "\<Union>\<G> = \<Union>(tf ` \<F>)"
    using tf by (force intro: Lindelof [of "tf ` \<F>"])
  then obtain \<F>' where \<F>': "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
    by (clarsimp simp add: countable_subset_image)
  then show ?thesis ..
qed

lemma countable_disjoint_open_subsets:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes "\<And>S. S \<in> \<F> \<Longrightarrow> open S" and pw: "pairwise disjnt \<F>"
    shows "countable \<F>"
proof -
  obtain \<F>' where "\<F>' \<subseteq> \<F>" "countable \<F>'" "\<Union>\<F>' = \<Union>\<F>"
    by (meson assms Lindelof)
  with pw have "\<F> \<subseteq> insert {} \<F>'"
    by (fastforce simp add: pairwise_def disjnt_iff)
  then show ?thesis
    by (simp add: \<open>countable \<F>'\<close> countable_subset)
qed

lemma countable_disjoint_nonempty_interior_subsets:
  fixes \<F> :: "'a::euclidean_space set set"
  assumes pw: "pairwise disjnt \<F>" and int: "\<And>S. \<lbrakk>S \<in> \<F>; interior S = {}\<rbrakk> \<Longrightarrow> S = {}"
  shows "countable \<F>"
proof (rule countable_image_inj_on)
  have "disjoint (interior ` \<F>)"
    using pw by (simp add: disjoint_image_subset interior_subset)
  then show "countable (interior ` \<F>)"
    by (auto intro: countable_disjoint_open_subsets)
  show "inj_on interior \<F>"
    using pw apply (clarsimp simp: inj_on_def pairwise_def)
    apply (metis disjnt_def disjnt_subset1 inf.orderE int interior_subset)
    done
qed

lemma closedin_compact:
   "\<lbrakk>compact S; closedin (subtopology euclidean S) T\<rbrakk> \<Longrightarrow> compact T"
by (metis closedin_closed compact_Int_closed)

lemma closedin_compact_eq:
  fixes S :: "'a::t2_space set"
  shows
   "compact S
         \<Longrightarrow> (closedin (subtopology euclidean S) T \<longleftrightarrow>
              compact T \<and> T \<subseteq> S)"
by (metis closedin_imp_subset closedin_compact closed_subset compact_imp_closed)

lemma continuous_imp_closed_map:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "closedin (subtopology euclidean S) U"
          "continuous_on S f" "f ` S = T" "compact S"
    shows "closedin (subtopology euclidean T) (f ` U)"
  by (metis assms closedin_compact_eq compact_continuous_image continuous_on_subset subset_image_iff)

lemma continuous_imp_quotient_map:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::metric_space"
  assumes "continuous_on S f" "f ` S = T" "compact S" "U \<subseteq> T"
    shows "openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
           openin (subtopology euclidean T) U"
  by (metis (no_types, lifting) assms closed_map_imp_quotient_map continuous_imp_closed_map)


lemma open_map_restrict:
  assumes opeU: "openin (subtopology euclidean (S \<inter> f -` T')) U"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
    and "T' \<subseteq> T"
  shows "openin (subtopology euclidean T') (f ` U)"
proof -
  obtain V where "open V" "U = S \<inter> f -` T' \<inter> V"
    using opeU by (auto simp: openin_open)
  with oo [of "S \<inter> V"] \<open>T' \<subseteq> T\<close> show ?thesis
    by (fastforce simp add: openin_open)
qed

lemma closed_map_restrict:
  assumes cloU: "closedin (subtopology euclidean (S \<inter> f -` T')) U"
    and cc: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
    and "T' \<subseteq> T"
  shows "closedin (subtopology euclidean T') (f ` U)"
proof -
  obtain V where "closed V" "U = S \<inter> f -` T' \<inter> V"
    using cloU by (auto simp: closedin_closed)
  with cc [of "S \<inter> V"] \<open>T' \<subseteq> T\<close> show ?thesis
    by (fastforce simp add: closedin_closed)
qed

lemma connected_monotone_quotient_preimage:
  assumes "connected T"
      and contf: "continuous_on S f" and fim: "f ` S = T"
      and opT: "\<And>U. U \<subseteq> T
                 \<Longrightarrow> openin (subtopology euclidean S) (S \<inter> f -` U) \<longleftrightarrow>
                     openin (subtopology euclidean T) U"
      and connT: "\<And>y. y \<in> T \<Longrightarrow> connected (S \<inter> f -` {y})"
    shows "connected S"
proof (rule connectedI)
  fix U V
  assume "open U" and "open V" and "U \<inter> S \<noteq> {}" and "V \<inter> S \<noteq> {}"
    and "U \<inter> V \<inter> S = {}" and "S \<subseteq> U \<union> V"
  moreover
  have disjoint: "f ` (S \<inter> U) \<inter> f ` (S \<inter> V) = {}"
  proof -
    have False if "y \<in> f ` (S \<inter> U) \<inter> f ` (S \<inter> V)" for y
    proof -
      have "y \<in> T"
        using fim that by blast
      show ?thesis
        using connectedD [OF connT [OF \<open>y \<in> T\<close>] \<open>open U\<close> \<open>open V\<close>]
              \<open>S \<subseteq> U \<union> V\<close> \<open>U \<inter> V \<inter> S = {}\<close> that by fastforce
    qed
    then show ?thesis by blast
  qed
  ultimately have UU: "(S \<inter> f -` f ` (S \<inter> U)) = S \<inter> U" and VV: "(S \<inter> f -` f ` (S \<inter> V)) = S \<inter> V"
    by auto
  have opeU: "openin (subtopology euclidean T) (f ` (S \<inter> U))"
    by (metis UU \<open>open U\<close> fim image_Int_subset le_inf_iff opT openin_open_Int)
  have opeV: "openin (subtopology euclidean T) (f ` (S \<inter> V))"
    by (metis opT fim VV \<open>open V\<close> openin_open_Int image_Int_subset inf.bounded_iff)
  have "T \<subseteq> f ` (S \<inter> U) \<union> f ` (S \<inter> V)"
    using \<open>S \<subseteq> U \<union> V\<close> fim by auto
  then show False
    using \<open>connected T\<close> disjoint opeU opeV \<open>U \<inter> S \<noteq> {}\<close> \<open>V \<inter> S \<noteq> {}\<close>
    by (auto simp: connected_openin)
qed

lemma connected_open_monotone_preimage:
  assumes contf: "continuous_on S f" and fim: "f ` S = T"
    and ST: "\<And>C. openin (subtopology euclidean S) C \<Longrightarrow> openin (subtopology euclidean T) (f ` C)"
    and connT: "\<And>y. y \<in> T \<Longrightarrow> connected (S \<inter> f -` {y})"
    and "connected C" "C \<subseteq> T"
  shows "connected (S \<inter> f -` C)"
proof -
  have contf': "continuous_on (S \<inter> f -` C) f"
    by (meson contf continuous_on_subset inf_le1)
  have eqC: "f ` (S \<inter> f -` C) = C"
    using \<open>C \<subseteq> T\<close> fim by blast
  show ?thesis
  proof (rule connected_monotone_quotient_preimage [OF \<open>connected C\<close> contf' eqC])
    show "connected (S \<inter> f -` C \<inter> f -` {y})" if "y \<in> C" for y
    proof -
      have "S \<inter> f -` C \<inter> f -` {y} = S \<inter> f -` {y}"
        using that by blast
      moreover have "connected (S \<inter> f -` {y})"
        using \<open>C \<subseteq> T\<close> connT that by blast
      ultimately show ?thesis
        by metis
    qed
    have "\<And>U. openin (subtopology euclidean (S \<inter> f -` C)) U
               \<Longrightarrow> openin (subtopology euclidean C) (f ` U)"
      using open_map_restrict [OF _ ST \<open>C \<subseteq> T\<close>] by metis
    then show "\<And>D. D \<subseteq> C
          \<Longrightarrow> openin (subtopology euclidean (S \<inter> f -` C)) (S \<inter> f -` C \<inter> f -` D) =
              openin (subtopology euclidean C) D"
      using open_map_imp_quotient_map [of "(S \<inter> f -` C)" f] contf' by (simp add: eqC)
  qed
qed


lemma connected_closed_monotone_preimage:
  assumes contf: "continuous_on S f" and fim: "f ` S = T"
    and ST: "\<And>C. closedin (subtopology euclidean S) C \<Longrightarrow> closedin (subtopology euclidean T) (f ` C)"
    and connT: "\<And>y. y \<in> T \<Longrightarrow> connected (S \<inter> f -` {y})"
    and "connected C" "C \<subseteq> T"
  shows "connected (S \<inter> f -` C)"
proof -
  have contf': "continuous_on (S \<inter> f -` C) f"
    by (meson contf continuous_on_subset inf_le1)
  have eqC: "f ` (S \<inter> f -` C) = C"
    using \<open>C \<subseteq> T\<close> fim by blast
  show ?thesis
  proof (rule connected_monotone_quotient_preimage [OF \<open>connected C\<close> contf' eqC])
    show "connected (S \<inter> f -` C \<inter> f -` {y})" if "y \<in> C" for y
    proof -
      have "S \<inter> f -` C \<inter> f -` {y} = S \<inter> f -` {y}"
        using that by blast
      moreover have "connected (S \<inter> f -` {y})"
        using \<open>C \<subseteq> T\<close> connT that by blast
      ultimately show ?thesis
        by metis
    qed
    have "\<And>U. closedin (subtopology euclidean (S \<inter> f -` C)) U
               \<Longrightarrow> closedin (subtopology euclidean C) (f ` U)"
      using closed_map_restrict [OF _ ST \<open>C \<subseteq> T\<close>] by metis
    then show "\<And>D. D \<subseteq> C
          \<Longrightarrow> openin (subtopology euclidean (S \<inter> f -` C)) (S \<inter> f -` C \<inter> f -` D) =
              openin (subtopology euclidean C) D"
      using closed_map_imp_quotient_map [of "(S \<inter> f -` C)" f] contf' by (simp add: eqC)
  qed
qed



subsection\<open>A couple of lemmas about components (see Newman IV, 3.3 and 3.4)\<close>


lemma connected_Un_clopen_in_complement:
  fixes S U :: "'a::metric_space set"
  assumes "connected S" "connected U" "S \<subseteq> U" 
      and opeT: "openin (subtopology euclidean (U - S)) T" 
      and cloT: "closedin (subtopology euclidean (U - S)) T"
    shows "connected (S \<union> T)"
proof -
  have *: "\<lbrakk>\<And>x y. P x y \<longleftrightarrow> P y x; \<And>x y. P x y \<Longrightarrow> S \<subseteq> x \<or> S \<subseteq> y;
            \<And>x y. \<lbrakk>P x y; S \<subseteq> x\<rbrakk> \<Longrightarrow> False\<rbrakk> \<Longrightarrow> \<not>(\<exists>x y. (P x y))" for P
    by metis
  show ?thesis
    unfolding connected_closedin_eq
  proof (rule *)
    fix H1 H2
    assume H: "closedin (subtopology euclidean (S \<union> T)) H1 \<and> 
               closedin (subtopology euclidean (S \<union> T)) H2 \<and>
               H1 \<union> H2 = S \<union> T \<and> H1 \<inter> H2 = {} \<and> H1 \<noteq> {} \<and> H2 \<noteq> {}"
    then have clo: "closedin (subtopology euclidean S) (S \<inter> H1)"
                   "closedin (subtopology euclidean S) (S \<inter> H2)"
      by (metis Un_upper1 closedin_closed_subset inf_commute)+
    have Seq: "S \<inter> (H1 \<union> H2) = S"
      by (simp add: H)
    have "S \<inter> ((S \<union> T) \<inter> H1) \<union> S \<inter> ((S \<union> T) \<inter> H2) = S"
      using Seq by auto
    moreover have "H1 \<inter> (S \<inter> ((S \<union> T) \<inter> H2)) = {}"
      using H by blast
    ultimately have "S \<inter> H1 = {} \<or> S \<inter> H2 = {}"
      by (metis (no_types) H Int_assoc \<open>S \<inter> (H1 \<union> H2) = S\<close> \<open>connected S\<close>
          clo Seq connected_closedin inf_bot_right inf_le1)
    then show "S \<subseteq> H1 \<or> S \<subseteq> H2"
      using H \<open>connected S\<close> unfolding connected_closedin by blast
  next
    fix H1 H2
    assume H: "closedin (subtopology euclidean (S \<union> T)) H1 \<and>
               closedin (subtopology euclidean (S \<union> T)) H2 \<and>
               H1 \<union> H2 = S \<union> T \<and> H1 \<inter> H2 = {} \<and> H1 \<noteq> {} \<and> H2 \<noteq> {}" 
       and "S \<subseteq> H1"
    then have H2T: "H2 \<subseteq> T"
      by auto
    have "T \<subseteq> U"
      using Diff_iff opeT openin_imp_subset by auto
    with \<open>S \<subseteq> U\<close> have Ueq: "U = (U - S) \<union> (S \<union> T)" 
      by auto
    have "openin (subtopology euclidean ((U - S) \<union> (S \<union> T))) H2"
    proof (rule openin_subtopology_Un)
      show "openin (subtopology euclidean (S \<union> T)) H2"
        using \<open>H2 \<subseteq> T\<close> apply (auto simp: openin_closedin_eq)
        by (metis Diff_Diff_Int Diff_disjoint Diff_partition Diff_subset H Int_absorb1 Un_Diff)
      then show "openin (subtopology euclidean (U - S)) H2"
        by (meson H2T Un_upper2 opeT openin_subset_trans openin_trans)
    qed
    moreover have "closedin (subtopology euclidean ((U - S) \<union> (S \<union> T))) H2"
    proof (rule closedin_subtopology_Un)
      show "closedin (subtopology euclidean (U - S)) H2"
        using H H2T cloT closedin_subset_trans 
        by (blast intro: closedin_subtopology_Un closedin_trans)
    qed (simp add: H)
    ultimately
    have H2: "H2 = {} \<or> H2 = U"
      using Ueq \<open>connected U\<close> unfolding connected_clopen by metis   
    then have "H2 \<subseteq> S"
      by (metis Diff_partition H Un_Diff_cancel Un_subset_iff \<open>H2 \<subseteq> T\<close> assms(3) inf.orderE opeT openin_imp_subset)
    moreover have "T \<subseteq> H2 - S"
      by (metis (no_types) H2 H opeT openin_closedin_eq topspace_euclidean_subtopology)
    ultimately show False
      using H \<open>S \<subseteq> H1\<close> by blast
  qed blast
qed


proposition component_diff_connected:
  fixes S :: "'a::metric_space set"
  assumes "connected S" "connected U" "S \<subseteq> U" and C: "C \<in> components (U - S)"
  shows "connected(U - C)"
  using \<open>connected S\<close> unfolding connected_closedin_eq not_ex de_Morgan_conj
proof clarify
  fix H3 H4 
  assume clo3: "closedin (subtopology euclidean (U - C)) H3" 
    and clo4: "closedin (subtopology euclidean (U - C)) H4" 
    and "H3 \<union> H4 = U - C" and "H3 \<inter> H4 = {}" and "H3 \<noteq> {}" and "H4 \<noteq> {}"
    and * [rule_format]:
    "\<forall>H1 H2. \<not> closedin (subtopology euclidean S) H1 \<or>
                      \<not> closedin (subtopology euclidean S) H2 \<or>
                      H1 \<union> H2 \<noteq> S \<or> H1 \<inter> H2 \<noteq> {} \<or> \<not> H1 \<noteq> {} \<or> \<not> H2 \<noteq> {}"
  then have "H3 \<subseteq> U-C" and ope3: "openin (subtopology euclidean (U - C)) (U - C - H3)"
    and "H4 \<subseteq> U-C" and ope4: "openin (subtopology euclidean (U - C)) (U - C - H4)"
    by (auto simp: closedin_def)
  have "C \<noteq> {}" "C \<subseteq> U-S" "connected C"
    using C in_components_nonempty in_components_subset in_components_maximal by blast+
  have cCH3: "connected (C \<union> H3)"
  proof (rule connected_Un_clopen_in_complement [OF \<open>connected C\<close> \<open>connected U\<close> _ _ clo3])
    show "openin (subtopology euclidean (U - C)) H3"
      apply (simp add: openin_closedin_eq \<open>H3 \<subseteq> U - C\<close>)
      apply (simp add: closedin_subtopology)
      by (metis Diff_cancel Diff_triv Un_Diff clo4 \<open>H3 \<inter> H4 = {}\<close> \<open>H3 \<union> H4 = U - C\<close> closedin_closed inf_commute sup_bot.left_neutral)
  qed (use clo3 \<open>C \<subseteq> U - S\<close> in auto)
  have cCH4: "connected (C \<union> H4)"
  proof (rule connected_Un_clopen_in_complement [OF \<open>connected C\<close> \<open>connected U\<close> _ _ clo4])
    show "openin (subtopology euclidean (U - C)) H4"
      apply (simp add: openin_closedin_eq \<open>H4 \<subseteq> U - C\<close>)
      apply (simp add: closedin_subtopology)
      by (metis Diff_cancel Int_commute Un_Diff Un_Diff_Int \<open>H3 \<inter> H4 = {}\<close> \<open>H3 \<union> H4 = U - C\<close> clo3 closedin_closed)
  qed (use clo4 \<open>C \<subseteq> U - S\<close> in auto)
  have "closedin (subtopology euclidean S) (S \<inter> H3)" "closedin (subtopology euclidean S) (S \<inter> H4)"
    using clo3 clo4 \<open>S \<subseteq> U\<close> \<open>C \<subseteq> U - S\<close> by (auto simp: closedin_closed)
  moreover have "S \<inter> H3 \<noteq> {}"      
    using components_maximal [OF C cCH3] \<open>C \<noteq> {}\<close> \<open>C \<subseteq> U - S\<close> \<open>H3 \<noteq> {}\<close> \<open>H3 \<subseteq> U - C\<close> by auto
  moreover have "S \<inter> H4 \<noteq> {}"
    using components_maximal [OF C cCH4] \<open>C \<noteq> {}\<close> \<open>C \<subseteq> U - S\<close> \<open>H4 \<noteq> {}\<close> \<open>H4 \<subseteq> U - C\<close> by auto
  ultimately show False
    using * [of "S \<inter> H3" "S \<inter> H4"] \<open>H3 \<inter> H4 = {}\<close> \<open>C \<subseteq> U - S\<close> \<open>H3 \<union> H4 = U - C\<close> \<open>S \<subseteq> U\<close> 
    by auto
qed

subsection%unimportant\<open> Finite intersection property\<close>

text\<open>Also developed in HOL's toplogical spaces theory, but the Heine-Borel type class isn't available there.\<close>

lemma closed_imp_fip:
  fixes S :: "'a::heine_borel set"
  assumes "closed S"
      and T: "T \<in> \<F>" "bounded T"
      and clof: "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      and none: "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F>' \<noteq> {}"
    shows "S \<inter> \<Inter>\<F> \<noteq> {}"
proof -
  have "compact (S \<inter> T)"
    using \<open>closed S\<close> clof compact_eq_bounded_closed T by blast
  then have "(S \<inter> T) \<inter> \<Inter>\<F> \<noteq> {}"
    apply (rule compact_imp_fip)
     apply (simp add: clof)
    by (metis Int_assoc complete_lattice_class.Inf_insert finite_insert insert_subset none \<open>T \<in> \<F>\<close>)
  then show ?thesis by blast
qed

lemma closed_imp_fip_compact:
  fixes S :: "'a::heine_borel set"
  shows
   "\<lbrakk>closed S; \<And>T. T \<in> \<F> \<Longrightarrow> compact T;
     \<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> S \<inter> \<Inter>\<F>' \<noteq> {}\<rbrakk>
        \<Longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}"
by (metis Inf_greatest closed_imp_fip compact_eq_bounded_closed empty_subsetI finite.emptyI inf.orderE)

lemma closed_fip_Heine_Borel:
  fixes \<F> :: "'a::heine_borel set set"
  assumes "closed S" "T \<in> \<F>" "bounded T"
      and "\<And>T. T \<in> \<F> \<Longrightarrow> closed T"
      and "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> \<Inter>\<F>' \<noteq> {}"
    shows "\<Inter>\<F> \<noteq> {}"
proof -
  have "UNIV \<inter> \<Inter>\<F> \<noteq> {}"
    using assms closed_imp_fip [OF closed_UNIV] by auto
  then show ?thesis by simp
qed

lemma compact_fip_Heine_Borel:
  fixes \<F> :: "'a::heine_borel set set"
  assumes clof: "\<And>T. T \<in> \<F> \<Longrightarrow> compact T"
      and none: "\<And>\<F>'. \<lbrakk>finite \<F>'; \<F>' \<subseteq> \<F>\<rbrakk> \<Longrightarrow> \<Inter>\<F>' \<noteq> {}"
    shows "\<Inter>\<F> \<noteq> {}"
by (metis InterI all_not_in_conv clof closed_fip_Heine_Borel compact_eq_bounded_closed none)

lemma compact_sequence_with_limit:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel"
  shows "(f \<longlongrightarrow> l) sequentially \<Longrightarrow> compact (insert l (range f))"
apply (simp add: compact_eq_bounded_closed, auto)
apply (simp add: convergent_imp_bounded)
by (simp add: closed_limpt islimpt_insert sequence_unique_limpt)


subsection%unimportant\<open>Componentwise limits and continuity\<close>

text\<open>But is the premise really necessary? Need to generalise @{thm euclidean_dist_l2}\<close>
lemma Euclidean_dist_upper: "i \<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  by (metis (no_types) member_le_L2_set euclidean_dist_l2 finite_Basis)

text\<open>But is the premise \<^term>\<open>i \<in> Basis\<close> really necessary?\<close>
lemma open_preimage_inner:
  assumes "open S" "i \<in> Basis"
    shows "open {x. x \<bullet> i \<in> S}"
proof (rule openI, simp)
  fix x
  assume x: "x \<bullet> i \<in> S"
  with assms obtain e where "0 < e" and e: "ball (x \<bullet> i) e \<subseteq> S"
    by (auto simp: open_contains_ball_eq)
  have "\<exists>e>0. ball (y \<bullet> i) e \<subseteq> S" if dxy: "dist x y < e / 2" for y
  proof (intro exI conjI)
    have "dist (x \<bullet> i) (y \<bullet> i) < e / 2"
      by (meson \<open>i \<in> Basis\<close> dual_order.trans Euclidean_dist_upper not_le that)
    then have "dist (x \<bullet> i) z < e" if "dist (y \<bullet> i) z < e / 2" for z
      by (metis dist_commute dist_triangle_half_l that)
    then have "ball (y \<bullet> i) (e / 2) \<subseteq> ball (x \<bullet> i) e"
      using mem_ball by blast
      with e show "ball (y \<bullet> i) (e / 2) \<subseteq> S"
        by (metis order_trans)
  qed (simp add: \<open>0 < e\<close>)
  then show "\<exists>e>0. ball x e \<subseteq> {s. s \<bullet> i \<in> S}"
    by (metis (no_types, lifting) \<open>0 < e\<close> \<open>open S\<close> half_gt_zero_iff mem_Collect_eq mem_ball open_contains_ball_eq subsetI)
qed

proposition tendsto_componentwise_iff:
  fixes f :: "_ \<Rightarrow> 'b::euclidean_space"
  shows "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>i \<in> Basis. ((\<lambda>x. (f x \<bullet> i)) \<longlongrightarrow> (l \<bullet> i)) F)"
         (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding tendsto_def
    apply clarify
    apply (drule_tac x="{s. s \<bullet> i \<in> S}" in spec)
    apply (auto simp: open_preimage_inner)
    done
next
  assume R: ?rhs
  then have "\<And>e. e > 0 \<Longrightarrow> \<forall>i\<in>Basis. \<forall>\<^sub>F x in F. dist (f x \<bullet> i) (l \<bullet> i) < e"
    unfolding tendsto_iff by blast
  then have R': "\<And>e. e > 0 \<Longrightarrow> \<forall>\<^sub>F x in F. \<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e"
      by (simp add: eventually_ball_finite_distrib [symmetric])
  show ?lhs
  unfolding tendsto_iff
  proof clarify
    fix e::real
    assume "0 < e"
    have *: "L2_set (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis < e"
             if "\<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e / real DIM('b)" for x
    proof -
      have "L2_set (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis \<le> sum (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis"
        by (simp add: L2_set_le_sum)
      also have "... < DIM('b) * (e / real DIM('b))"
        apply (rule sum_bounded_above_strict)
        using that by auto
      also have "... = e"
        by (simp add: field_simps)
      finally show "L2_set (\<lambda>i. dist (f x \<bullet> i) (l \<bullet> i)) Basis < e" .
    qed
    have "\<forall>\<^sub>F x in F. \<forall>i\<in>Basis. dist (f x \<bullet> i) (l \<bullet> i) < e / DIM('b)"
      apply (rule R')
      using \<open>0 < e\<close> by simp
    then show "\<forall>\<^sub>F x in F. dist (f x) l < e"
      apply (rule eventually_mono)
      apply (subst euclidean_dist_l2)
      using * by blast
  qed
qed


corollary continuous_componentwise:
   "continuous F f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous F (\<lambda>x. (f x \<bullet> i)))"
by (simp add: continuous_def tendsto_componentwise_iff [symmetric])

corollary continuous_on_componentwise:
  fixes S :: "'a :: t2_space set"
  shows "continuous_on S f \<longleftrightarrow> (\<forall>i \<in> Basis. continuous_on S (\<lambda>x. (f x \<bullet> i)))"
  apply (simp add: continuous_on_eq_continuous_within)
  using continuous_componentwise by blast

lemma linear_componentwise_iff:
     "(linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. linear (\<lambda>x. f' x \<bullet> i))"
  apply (auto simp: linear_iff inner_left_distrib)
   apply (metis inner_left_distrib euclidean_eq_iff)
  by (metis euclidean_eqI inner_scaleR_left)

lemma bounded_linear_componentwise_iff:
     "(bounded_linear f') \<longleftrightarrow> (\<forall>i\<in>Basis. bounded_linear (\<lambda>x. f' x \<bullet> i))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: bounded_linear_inner_left_comp)
next
  assume ?rhs
  then have "(\<forall>i\<in>Basis. \<exists>K. \<forall>x. \<bar>f' x \<bullet> i\<bar> \<le> norm x * K)" "linear f'"
    by (auto simp: bounded_linear_def bounded_linear_axioms_def linear_componentwise_iff [symmetric] ball_conj_distrib)
  then obtain F where F: "\<And>i x. i \<in> Basis \<Longrightarrow> \<bar>f' x \<bullet> i\<bar> \<le> norm x * F i"
    by metis
  have "norm (f' x) \<le> norm x * sum F Basis" for x
  proof -
    have "norm (f' x) \<le> (\<Sum>i\<in>Basis. \<bar>f' x \<bullet> i\<bar>)"
      by (rule norm_le_l1)
    also have "... \<le> (\<Sum>i\<in>Basis. norm x * F i)"
      by (metis F sum_mono)
    also have "... = norm x * sum F Basis"
      by (simp add: sum_distrib_left)
    finally show ?thesis .
  qed
  then show ?lhs
    by (force simp: bounded_linear_def bounded_linear_axioms_def \<open>linear f'\<close>)
qed

subsection%unimportant\<open>Pasting functions together\<close>

subsubsection%unimportant\<open>on open sets\<close>

lemma pasting_lemma:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes clo: "\<And>i. i \<in> I \<Longrightarrow> openin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_on S g"
proof (clarsimp simp: continuous_openin_preimage_eq)
  fix U :: "'b set"
  assume "open U"
  have S: "\<And>i. i \<in> I \<Longrightarrow> (T i) \<subseteq> S"
    using clo openin_imp_subset by blast
  have *: "(S \<inter> g -` U) = (\<Union>i \<in> I. T i \<inter> f i -` U)"
    using S f g by fastforce
  show "openin (subtopology euclidean S) (S \<inter> g -` U)"
    apply (subst *)
    apply (rule openin_Union, clarify)
    using \<open>open U\<close> clo cont continuous_openin_preimage_gen openin_trans by blast
qed

lemma pasting_lemma_exists:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes S: "S \<subseteq> (\<Union>i \<in> I. T i)"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> openin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_on S g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> S \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_on S (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma [OF clo cont])
     apply (blast intro: f)+
    apply (metis (mono_tags, lifting) S UN_iff subsetCE someI)
    done
next
  fix x i
  assume "i \<in> I" "x \<in> S \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed

subsubsection%unimportant\<open>Likewise on closed sets, with a finiteness assumption\<close>

lemma pasting_lemma_closed:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "finite I"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
      and g: "\<And>x. x \<in> S \<Longrightarrow> \<exists>j. j \<in> I \<and> x \<in> T j \<and> g x = f j x"
    shows "continuous_on S g"
proof (clarsimp simp: continuous_closedin_preimage_eq)
  fix U :: "'b set"
  assume "closed U"
  have S: "\<And>i. i \<in> I \<Longrightarrow> (T i) \<subseteq> S"
    using clo closedin_imp_subset by blast
  have *: "(S \<inter> g -` U) = (\<Union>i \<in> I. T i \<inter> f i -` U)"
    using S f g by fastforce
  show "closedin (subtopology euclidean S) (S \<inter> g -` U)"
    apply (subst *)
    apply (rule closedin_Union)
    using \<open>finite I\<close> apply simp
    apply (blast intro: \<open>closed U\<close> continuous_closedin_preimage cont clo closedin_trans)
    done
qed

lemma pasting_lemma_exists_closed:
  fixes f :: "'i \<Rightarrow> 'a::topological_space \<Rightarrow> 'b::topological_space"
  assumes "finite I"
      and S: "S \<subseteq> (\<Union>i \<in> I. T i)"
      and clo: "\<And>i. i \<in> I \<Longrightarrow> closedin (subtopology euclidean S) (T i)"
      and cont: "\<And>i. i \<in> I \<Longrightarrow> continuous_on (T i) (f i)"
      and f: "\<And>i j x. \<lbrakk>i \<in> I; j \<in> I; x \<in> S \<inter> T i \<inter> T j\<rbrakk> \<Longrightarrow> f i x = f j x"
    obtains g where "continuous_on S g" "\<And>x i. \<lbrakk>i \<in> I; x \<in> S \<inter> T i\<rbrakk> \<Longrightarrow> g x = f i x"
proof
  show "continuous_on S (\<lambda>x. f (SOME i. i \<in> I \<and> x \<in> T i) x)"
    apply (rule pasting_lemma_closed [OF \<open>finite I\<close> clo cont])
     apply (blast intro: f)+
    apply (metis (mono_tags, lifting) S UN_iff subsetCE someI)
    done
next
  fix x i
  assume "i \<in> I" "x \<in> S \<inter> T i"
  then show "f (SOME i. i \<in> I \<and> x \<in> T i) x = f i x"
    by (metis (no_types, lifting) IntD2 IntI f someI_ex)
qed

lemma tube_lemma:
  assumes "compact K"
  assumes "open W"
  assumes "{x0} \<times> K \<subseteq> W"
  shows "\<exists>X0. x0 \<in> X0 \<and> open X0 \<and> X0 \<times> K \<subseteq> W"
proof -
  {
    fix y assume "y \<in> K"
    then have "(x0, y) \<in> W" using assms by auto
    with \<open>open W\<close>
    have "\<exists>X0 Y. open X0 \<and> open Y \<and> x0 \<in> X0 \<and> y \<in> Y \<and> X0 \<times> Y \<subseteq> W"
      by (rule open_prod_elim) blast
  }
  then obtain X0 Y where
    *: "\<forall>y \<in> K. open (X0 y) \<and> open (Y y) \<and> x0 \<in> X0 y \<and> y \<in> Y y \<and> X0 y \<times> Y y \<subseteq> W"
    by metis
  from * have "\<forall>t\<in>Y ` K. open t" "K \<subseteq> \<Union>(Y ` K)" by auto
  with \<open>compact K\<close> obtain CC where CC: "CC \<subseteq> Y ` K" "finite CC" "K \<subseteq> \<Union>CC"
    by (meson compactE)
  then obtain c where c: "\<And>C. C \<in> CC \<Longrightarrow> c C \<in> K \<and> C = Y (c C)"
    by (force intro!: choice)
  with * CC show ?thesis
    by (force intro!: exI[where x="\<Inter>C\<in>CC. X0 (c C)"]) (* SLOW *)
qed

lemma continuous_on_prod_compactE:
  fixes fx::"'a::topological_space \<times> 'b::topological_space \<Rightarrow> 'c::metric_space"
    and e::real
  assumes cont_fx: "continuous_on (U \<times> C) fx"
  assumes "compact C"
  assumes [intro]: "x0 \<in> U"
  notes [continuous_intros] = continuous_on_compose2[OF cont_fx]
  assumes "e > 0"
  obtains X0 where "x0 \<in> X0" "open X0"
    "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
proof -
  define psi where "psi = (\<lambda>(x, t). dist (fx (x, t)) (fx (x0, t)))"
  define W0 where "W0 = {(x, t) \<in> U \<times> C. psi (x, t) < e}"
  have W0_eq: "W0 = psi -` {..<e} \<inter> U \<times> C"
    by (auto simp: vimage_def W0_def)
  have "open {..<e}" by simp
  have "continuous_on (U \<times> C) psi"
    by (auto intro!: continuous_intros simp: psi_def split_beta')
  from this[unfolded continuous_on_open_invariant, rule_format, OF \<open>open {..<e}\<close>]
  obtain W where W: "open W" "W \<inter> U \<times> C = W0 \<inter> U \<times> C"
    unfolding W0_eq by blast
  have "{x0} \<times> C \<subseteq> W \<inter> U \<times> C"
    unfolding W
    by (auto simp: W0_def psi_def \<open>0 < e\<close>)
  then have "{x0} \<times> C \<subseteq> W" by blast
  from tube_lemma[OF \<open>compact C\<close> \<open>open W\<close> this]
  obtain X0 where X0: "x0 \<in> X0" "open X0" "X0 \<times> C \<subseteq> W"
    by blast

  have "\<forall>x\<in>X0 \<inter> U. \<forall>t \<in> C. dist (fx (x, t)) (fx (x0, t)) \<le> e"
  proof safe
    fix x assume x: "x \<in> X0" "x \<in> U"
    fix t assume t: "t \<in> C"
    have "dist (fx (x, t)) (fx (x0, t)) = psi (x, t)"
      by (auto simp: psi_def)
    also
    {
      have "(x, t) \<in> X0 \<times> C"
        using t x
        by auto
      also note \<open>\<dots> \<subseteq> W\<close>
      finally have "(x, t) \<in> W" .
      with t x have "(x, t) \<in> W \<inter> U \<times> C"
        by blast
      also note \<open>W \<inter> U \<times> C = W0 \<inter> U \<times> C\<close>
      finally  have "psi (x, t) < e"
        by (auto simp: W0_def)
    }
    finally show "dist (fx (x, t)) (fx (x0, t)) \<le> e" by simp
  qed
  from X0(1,2) this show ?thesis ..
qed


subsection%unimportant\<open>Constancy of a function from a connected set into a finite, disconnected or discrete set\<close>

text\<open>Still missing: versions for a set that is smaller than R, or countable.\<close>

lemma continuous_disconnected_range_constant:
  assumes S: "connected S"
      and conf: "continuous_on S f"
      and fim: "f ` S \<subseteq> t"
      and cct: "\<And>y. y \<in> t \<Longrightarrow> connected_component_set t y = {y}"
    shows "f constant_on S"
proof (cases "S = {}")
  case True then show ?thesis
    by (simp add: constant_on_def)
next
  case False
  { fix x assume "x \<in> S"
    then have "f ` S \<subseteq> {f x}"
    by (metis connected_continuous_image conf connected_component_maximal fim image_subset_iff rev_image_eqI S cct)
  }
  with False show ?thesis
    unfolding constant_on_def by blast
qed

lemma discrete_subset_disconnected:
  fixes S :: "'a::topological_space set"
  fixes t :: "'b::real_normed_vector set"
  assumes conf: "continuous_on S f"
      and no: "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
   shows "f ` S \<subseteq> {y. connected_component_set (f ` S) y = {y}}"
proof -
  { fix x assume x: "x \<in> S"
    then obtain e where "e>0" and ele: "\<And>y. \<lbrakk>y \<in> S; f y \<noteq> f x\<rbrakk> \<Longrightarrow> e \<le> norm (f y - f x)"
      using conf no [OF x] by auto
    then have e2: "0 \<le> e / 2"
      by simp
    have "f y = f x" if "y \<in> S" and ccs: "f y \<in> connected_component_set (f ` S) (f x)" for y
      apply (rule ccontr)
      using connected_closed [of "connected_component_set (f ` S) (f x)"] \<open>e>0\<close>
      apply (simp add: del: ex_simps)
      apply (drule spec [where x="cball (f x) (e / 2)"])
      apply (drule spec [where x="- ball(f x) e"])
      apply (auto simp: dist_norm open_closed [symmetric] simp del: le_divide_eq_numeral1 dest!: connected_component_in)
        apply (metis diff_self e2 ele norm_minus_commute norm_zero not_less)
       using centre_in_cball connected_component_refl_eq e2 x apply blast
      using ccs
      apply (force simp: cball_def dist_norm norm_minus_commute dest: ele [OF \<open>y \<in> S\<close>])
      done
    moreover have "connected_component_set (f ` S) (f x) \<subseteq> f ` S"
      by (auto simp: connected_component_in)
    ultimately have "connected_component_set (f ` S) (f x) = {f x}"
      by (auto simp: x)
  }
  with assms show ?thesis
    by blast
qed

lemma finite_implies_discrete:
  fixes S :: "'a::topological_space set"
  assumes "finite (f ` S)"
  shows "(\<forall>x \<in> S. \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x))"
proof -
  have "\<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)" if "x \<in> S" for x
  proof (cases "f ` S - {f x} = {}")
    case True
    with zero_less_numeral show ?thesis
      by (fastforce simp add: Set.image_subset_iff cong: conj_cong)
  next
    case False
    then obtain z where z: "z \<in> S" "f z \<noteq> f x"
      by blast
    have finn: "finite {norm (z - f x) |z. z \<in> f ` S - {f x}}"
      using assms by simp
    then have *: "0 < Inf{norm(z - f x) | z. z \<in> f ` S - {f x}}"
      apply (rule finite_imp_less_Inf)
      using z apply force+
      done
    show ?thesis
      by (force intro!: * cInf_le_finite [OF finn])
  qed
  with assms show ?thesis
    by blast
qed

text\<open>This proof requires the existence of two separate values of the range type.\<close>
lemma finite_range_constant_imp_connected:
  assumes "\<And>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
              \<lbrakk>continuous_on S f; finite(f ` S)\<rbrakk> \<Longrightarrow> f constant_on S"
    shows "connected S"
proof -
  { fix t u
    assume clt: "closedin (subtopology euclidean S) t"
       and clu: "closedin (subtopology euclidean S) u"
       and tue: "t \<inter> u = {}" and tus: "t \<union> u = S"
    have conif: "continuous_on S (\<lambda>x. if x \<in> t then 0 else 1)"
      apply (subst tus [symmetric])
      apply (rule continuous_on_cases_local)
      using clt clu tue
      apply (auto simp: tus continuous_on_const)
      done
    have fi: "finite ((\<lambda>x. if x \<in> t then 0 else 1) ` S)"
      by (rule finite_subset [of _ "{0,1}"]) auto
    have "t = {} \<or> u = {}"
      using assms [OF conif fi] tus [symmetric]
      by (auto simp: Ball_def constant_on_def) (metis IntI empty_iff one_neq_zero tue)
  }
  then show ?thesis
    by (simp add: connected_closedin_eq)
qed

lemma continuous_disconnected_range_constant_eq:
      "(connected S \<longleftrightarrow>
           (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
            \<forall>t. continuous_on S f \<and> f ` S \<subseteq> t \<and> (\<forall>y \<in> t. connected_component_set t y = {y})
            \<longrightarrow> f constant_on S))" (is ?thesis1)
  and continuous_discrete_range_constant_eq:
      "(connected S \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on S f \<and>
          (\<forall>x \<in> S. \<exists>e. 0 < e \<and> (\<forall>y. y \<in> S \<and> (f y \<noteq> f x) \<longrightarrow> e \<le> norm(f y - f x)))
          \<longrightarrow> f constant_on S))" (is ?thesis2)
  and continuous_finite_range_constant_eq:
      "(connected S \<longleftrightarrow>
         (\<forall>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
          continuous_on S f \<and> finite (f ` S)
          \<longrightarrow> f constant_on S))" (is ?thesis3)
proof -
  have *: "\<And>s t u v. \<lbrakk>s \<Longrightarrow> t; t \<Longrightarrow> u; u \<Longrightarrow> v; v \<Longrightarrow> s\<rbrakk>
    \<Longrightarrow> (s \<longleftrightarrow> t) \<and> (s \<longleftrightarrow> u) \<and> (s \<longleftrightarrow> v)"
    by blast
  have "?thesis1 \<and> ?thesis2 \<and> ?thesis3"
    apply (rule *)
    using continuous_disconnected_range_constant apply metis
    apply clarify
    apply (frule discrete_subset_disconnected; blast)
    apply (blast dest: finite_implies_discrete)
    apply (blast intro!: finite_range_constant_imp_connected)
    done
  then show ?thesis1 ?thesis2 ?thesis3
    by blast+
qed

lemma continuous_discrete_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes S: "connected S"
      and "continuous_on S f"
      and "\<And>x. x \<in> S \<Longrightarrow> \<exists>e>0. \<forall>y. y \<in> S \<and> f y \<noteq> f x \<longrightarrow> e \<le> norm (f y - f x)"
    shows "f constant_on S"
  using continuous_discrete_range_constant_eq [THEN iffD1, OF S] assms by blast

lemma continuous_finite_range_constant:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1"
  assumes "connected S"
      and "continuous_on S f"
      and "finite (f ` S)"
    shows "f constant_on S"
  using assms continuous_finite_range_constant_eq  by blast



subsection%unimportant \<open>Continuous Extension\<close>

definition clamp :: "'a::euclidean_space \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "clamp a b x = (if (\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)
    then (\<Sum>i\<in>Basis. (if x\<bullet>i < a\<bullet>i then a\<bullet>i else if x\<bullet>i \<le> b\<bullet>i then x\<bullet>i else b\<bullet>i) *\<^sub>R i)
    else a)"

lemma clamp_in_interval[simp]:
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> b \<bullet> i"
  shows "clamp a b x \<in> cbox a b"
  unfolding clamp_def
  using box_ne_empty(1)[of a b] assms by (auto simp: cbox_def)

lemma clamp_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "clamp a b x = x"
  using assms
  by (auto simp: clamp_def mem_box intro!: euclidean_eqI[where 'a='a])

lemma clamp_empty_interval:
  assumes "i \<in> Basis" "a \<bullet> i > b \<bullet> i"
  shows "clamp a b = (\<lambda>_. a)"
  using assms
  by (force simp: clamp_def[abs_def] split: if_splits intro!: ext)

lemma dist_clamps_le_dist_args:
  fixes x :: "'a::euclidean_space"
  shows "dist (clamp a b y) (clamp a b x) \<le> dist y x"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  then have "(\<Sum>i\<in>Basis. (dist (clamp a b y \<bullet> i) (clamp a b x \<bullet> i))\<^sup>2) \<le>
    (\<Sum>i\<in>Basis. (dist (y \<bullet> i) (x \<bullet> i))\<^sup>2)"
    by (auto intro!: sum_mono simp: clamp_def dist_real_def abs_le_square_iff[symmetric])
  then show ?thesis
    by (auto intro: real_sqrt_le_mono
      simp: euclidean_dist_l2[where y=x] euclidean_dist_l2[where y="clamp a b x"] L2_set_def)
qed (auto simp: clamp_def)

lemma clamp_continuous_at:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
    and x :: 'a
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous (at x) (\<lambda>x. f (clamp a b x))"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  show ?thesis
    unfolding continuous_at_eps_delta
  proof safe
    fix x :: 'a
    fix e :: real
    assume "e > 0"
    moreover have "clamp a b x \<in> cbox a b"
      by (simp add: clamp_in_interval le)
    moreover note f_cont[simplified continuous_on_iff]
    ultimately
    obtain d where d: "0 < d"
      "\<And>x'. x' \<in> cbox a b \<Longrightarrow> dist x' (clamp a b x) < d \<Longrightarrow> dist (f x') (f (clamp a b x)) < e"
      by force
    show "\<exists>d>0. \<forall>x'. dist x' x < d \<longrightarrow>
      dist (f (clamp a b x')) (f (clamp a b x)) < e"
      using le
      by (auto intro!: d clamp_in_interval dist_clamps_le_dist_args[THEN le_less_trans])
  qed
qed (auto simp: clamp_empty_interval)

lemma clamp_continuous_on:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes f_cont: "continuous_on (cbox a b) f"
  shows "continuous_on S (\<lambda>x. f (clamp a b x))"
  using assms
  by (auto intro: continuous_at_imp_continuous_on clamp_continuous_at)

lemma clamp_bounded:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::metric_space"
  assumes bounded: "bounded (f ` (cbox a b))"
  shows "bounded (range (\<lambda>x. f (clamp a b x)))"
proof cases
  assume le: "(\<forall>i\<in>Basis. a \<bullet> i \<le> b \<bullet> i)"
  from bounded obtain c where f_bound: "\<forall>x\<in>f ` cbox a b. dist undefined x \<le> c"
    by (auto simp: bounded_any_center[where a=undefined])
  then show ?thesis
    by (auto intro!: exI[where x=c] clamp_in_interval[OF le[rule_format]]
        simp: bounded_any_center[where a=undefined])
qed (auto simp: clamp_empty_interval image_def)


definition ext_cont :: "('a::euclidean_space \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b"
  where "ext_cont f a b = (\<lambda>x. f (clamp a b x))"

lemma ext_cont_cancel_cbox[simp]:
  fixes x a b :: "'a::euclidean_space"
  assumes x: "x \<in> cbox a b"
  shows "ext_cont f a b x = f x"
  using assms
  unfolding ext_cont_def
  by (auto simp: clamp_def mem_box intro!: euclidean_eqI[where 'a='a] arg_cong[where f=f])

lemma continuous_on_ext_cont[continuous_intros]:
  "continuous_on (cbox a b) f \<Longrightarrow> continuous_on S (ext_cont f a b)"
  by (auto intro!: clamp_continuous_on simp: ext_cont_def)

end

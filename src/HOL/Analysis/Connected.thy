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


text \<open>Proving a function is constant by proving that a level set is open\<close>

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

text \<open>Some arithmetical combinations (more to prove).\<close>

lemma open_scaling[intro]:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
    and "open s"
  shows "open((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  {
    fix x
    assume "x \<in> s"
    then obtain e where "e>0"
      and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> s" using assms(2)[unfolded open_dist, THEN bspec[where x=x]]
      by auto
    have "e * \<bar>c\<bar> > 0"
      using assms(1)[unfolded zero_less_abs_iff[symmetric]] \<open>e>0\<close> by auto
    moreover
    {
      fix y
      assume "dist y (c *\<^sub>R x) < e * \<bar>c\<bar>"
      then have "norm ((1 / c) *\<^sub>R y - x) < e"
        unfolding dist_norm
        using norm_scaleR[of c "(1 / c) *\<^sub>R y - x", unfolded scaleR_right_diff_distrib, unfolded scaleR_scaleR] assms(1)
          assms(1)[unfolded zero_less_abs_iff[symmetric]] by (simp del:zero_less_abs_iff)
      then have "y \<in> (*\<^sub>R) c ` s"
        using rev_image_eqI[of "(1 / c) *\<^sub>R y" s y "(*\<^sub>R) c"]
        using e[THEN spec[where x="(1 / c) *\<^sub>R y"]]
        using assms(1)
        unfolding dist_norm scaleR_scaleR
        by auto
    }
    ultimately have "\<exists>e>0. \<forall>x'. dist x' (c *\<^sub>R x) < e \<longrightarrow> x' \<in> (*\<^sub>R) c ` s"
      apply (rule_tac x="e * \<bar>c\<bar>" in exI, auto)
      done
  }
  then show ?thesis unfolding open_dist by auto
qed

lemma minus_image_eq_vimage:
  fixes A :: "'a::ab_group_add set"
  shows "(\<lambda>x. - x) ` A = (\<lambda>x. - x) -` A"
  by (auto intro!: image_eqI [where f="\<lambda>x. - x"])

lemma open_negations:
  fixes S :: "'a::real_normed_vector set"
  shows "open S \<Longrightarrow> open ((\<lambda>x. - x) ` S)"
  using open_scaling [of "- 1" S] by simp

lemma open_translation:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"
  shows "open((\<lambda>x. a + x) ` S)"
proof -
  {
    fix x
    have "continuous (at x) (\<lambda>x. x - a)"
      by (intro continuous_diff continuous_ident continuous_const)
  }
  moreover have "{x. x - a \<in> S} = (+) a ` S"
    by force
  ultimately show ?thesis
    by (metis assms continuous_open_vimage vimage_def)
qed

lemma open_neg_translation:
  fixes s :: "'a::real_normed_vector set"
  assumes "open s"
  shows "open((\<lambda>x. a - x) ` s)"
  using open_translation[OF open_negations[OF assms], of a]
  by (auto simp: image_image)

lemma open_affinity:
  fixes S :: "'a::real_normed_vector set"
  assumes "open S"  "c \<noteq> 0"
  shows "open ((\<lambda>x. a + c *\<^sub>R x) ` S)"
proof -
  have *: "(\<lambda>x. a + c *\<^sub>R x) = (\<lambda>x. a + x) \<circ> (\<lambda>x. c *\<^sub>R x)"
    unfolding o_def ..
  have "(+) a ` (*\<^sub>R) c ` S = ((+) a \<circ> (*\<^sub>R) c) ` S"
    by auto
  then show ?thesis
    using assms open_translation[of "(*\<^sub>R) c ` S" a]
    unfolding *
    by auto
qed

lemma interior_translation:
  fixes S :: "'a::real_normed_vector set"
  shows "interior ((\<lambda>x. a + x) ` S) = (\<lambda>x. a + x) ` (interior S)"
proof (rule set_eqI, rule)
  fix x
  assume "x \<in> interior ((+) a ` S)"
  then obtain e where "e > 0" and e: "ball x e \<subseteq> (+) a ` S"
    unfolding mem_interior by auto
  then have "ball (x - a) e \<subseteq> S"
    unfolding subset_eq Ball_def mem_ball dist_norm
    by (auto simp: diff_diff_eq)
  then show "x \<in> (+) a ` interior S"
    unfolding image_iff
    apply (rule_tac x="x - a" in bexI)
    unfolding mem_interior
    using \<open>e > 0\<close>
    apply auto
    done
next
  fix x
  assume "x \<in> (+) a ` interior S"
  then obtain y e where "e > 0" and e: "ball y e \<subseteq> S" and y: "x = a + y"
    unfolding image_iff Bex_def mem_interior by auto
  {
    fix z
    have *: "a + y - z = y + a - z" by auto
    assume "z \<in> ball x e"
    then have "z - a \<in> S"
      using e[unfolded subset_eq, THEN bspec[where x="z - a"]]
      unfolding mem_ball dist_norm y group_add_class.diff_diff_eq2 *
      by auto
    then have "z \<in> (+) a ` S"
      unfolding image_iff by (auto intro!: bexI[where x="z - a"])
  }
  then have "ball x e \<subseteq> (+) a ` S"
    unfolding subset_eq by auto
  then show "x \<in> interior ((+) a ` S)"
    unfolding mem_interior using \<open>e > 0\<close> by auto
qed

subsection \<open>Continuity implies uniform continuity on a compact domain\<close>

text\<open>From the proof of the Heine-Borel theorem: Lemma 2 in section 3.7, page 69 of
J. C. Burkill and H. Burkill. A Second Course in Mathematical Analysis (CUP, 2002)\<close>

lemma Heine_Borel_lemma:
  assumes "compact S" and Ssub: "S \<subseteq> \<Union>\<G>" and opn: "\<And>G. G \<in> \<G> \<Longrightarrow> open G"
  obtains e where "0 < e" "\<And>x. x \<in> S \<Longrightarrow> \<exists>G \<in> \<G>. ball x e \<subseteq> G"
proof -
  have False if neg: "\<And>e. 0 < e \<Longrightarrow> \<exists>x \<in> S. \<forall>G \<in> \<G>. \<not> ball x e \<subseteq> G"
  proof -
    have "\<exists>x \<in> S. \<forall>G \<in> \<G>. \<not> ball x (1 / Suc n) \<subseteq> G" for n
      using neg by simp
    then obtain f where "\<And>n. f n \<in> S" and fG: "\<And>G n. G \<in> \<G> \<Longrightarrow> \<not> ball (f n) (1 / Suc n) \<subseteq> G"
      by metis
    then obtain l r where "l \<in> S" "strict_mono r" and to_l: "(f \<circ> r) \<longlonglongrightarrow> l"
      using \<open>compact S\<close> compact_def that by metis
    then obtain G where "l \<in> G" "G \<in> \<G>"
      using Ssub by auto
    then obtain e where "0 < e" and e: "\<And>z. dist z l < e \<Longrightarrow> z \<in> G"
      using opn open_dist by blast
    obtain N1 where N1: "\<And>n. n \<ge> N1 \<Longrightarrow> dist (f (r n)) l < e/2"
      using to_l apply (simp add: lim_sequentially)
      using \<open>0 < e\<close> half_gt_zero that by blast
    obtain N2 where N2: "of_nat N2 > 2/e"
      using reals_Archimedean2 by blast
    obtain x where "x \<in> ball (f (r (max N1 N2))) (1 / real (Suc (r (max N1 N2))))" and "x \<notin> G"
      using fG [OF \<open>G \<in> \<G>\<close>, of "r (max N1 N2)"] by blast
    then have "dist (f (r (max N1 N2))) x < 1 / real (Suc (r (max N1 N2)))"
      by simp
    also have "... \<le> 1 / real (Suc (max N1 N2))"
      apply (simp add: divide_simps del: max.bounded_iff)
      using \<open>strict_mono r\<close> seq_suble by blast
    also have "... \<le> 1 / real (Suc N2)"
      by (simp add: field_simps)
    also have "... < e/2"
      using N2 \<open>0 < e\<close> by (simp add: field_simps)
    finally have "dist (f (r (max N1 N2))) x < e / 2" .
    moreover have "dist (f (r (max N1 N2))) l < e/2"
      using N1 max.cobounded1 by blast
    ultimately have "dist x l < e"
      using dist_triangle_half_r by blast
    then show ?thesis
      using e \<open>x \<notin> G\<close> by blast
  qed
  then show ?thesis
    by (meson that)
qed

lemma compact_uniformly_equicontinuous:
  assumes "compact S"
      and cont: "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk>
                        \<Longrightarrow> \<exists>d. 0 < d \<and>
                                (\<forall>f \<in> \<F>. \<forall>x' \<in> S. dist x' x < d \<longrightarrow> dist (f x') (f x) < e)"
      and "0 < e"
  obtains d where "0 < d"
                  "\<And>f x x'. \<lbrakk>f \<in> \<F>; x \<in> S; x' \<in> S; dist x' x < d\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
proof -
  obtain d where d_pos: "\<And>x e. \<lbrakk>x \<in> S; 0 < e\<rbrakk> \<Longrightarrow> 0 < d x e"
     and d_dist : "\<And>x x' e f. \<lbrakk>dist x' x < d x e; x \<in> S; x' \<in> S; 0 < e; f \<in> \<F>\<rbrakk> \<Longrightarrow> dist (f x') (f x) < e"
    using cont by metis
  let ?\<G> = "((\<lambda>x. ball x (d x (e / 2))) ` S)"
  have Ssub: "S \<subseteq> \<Union> ?\<G>"
    by clarsimp (metis d_pos \<open>0 < e\<close> dist_self half_gt_zero_iff)
  then obtain k where "0 < k" and k: "\<And>x. x \<in> S \<Longrightarrow> \<exists>G \<in> ?\<G>. ball x k \<subseteq> G"
    by (rule Heine_Borel_lemma [OF \<open>compact S\<close>]) auto
  moreover have "dist (f v) (f u) < e" if "f \<in> \<F>" "u \<in> S" "v \<in> S" "dist v u < k" for f u v
  proof -
    obtain G where "G \<in> ?\<G>" "u \<in> G" "v \<in> G"
      using k that
      by (metis \<open>dist v u < k\<close> \<open>u \<in> S\<close> \<open>0 < k\<close> centre_in_ball subsetD dist_commute mem_ball)
    then obtain w where w: "dist w u < d w (e / 2)" "dist w v < d w (e / 2)" "w \<in> S"
      by auto
    with that d_dist have "dist (f w) (f v) < e/2"
      by (metis \<open>0 < e\<close> dist_commute half_gt_zero)
    moreover
    have "dist (f w) (f u) < e/2"
      using that d_dist w by (metis \<open>0 < e\<close> dist_commute divide_pos_pos zero_less_numeral)
    ultimately show ?thesis
      using dist_triangle_half_r by blast
  qed
  ultimately show ?thesis using that by blast
qed

corollary compact_uniformly_continuous:
  fixes f :: "'a :: metric_space \<Rightarrow> 'b :: metric_space"
  assumes f: "continuous_on S f" and S: "compact S"
  shows "uniformly_continuous_on S f"
  using f
    unfolding continuous_on_iff uniformly_continuous_on_def
    by (force intro: compact_uniformly_equicontinuous [OF S, of "{f}"])

subsection%unimportant \<open>Topological stuff about the set of Reals\<close>

lemma open_real:
  fixes s :: "real set"
  shows "open s \<longleftrightarrow> (\<forall>x \<in> s. \<exists>e>0. \<forall>x'. \<bar>x' - x\<bar> < e --> x' \<in> s)"
  unfolding open_dist dist_norm by simp

lemma islimpt_approachable_real:
  fixes s :: "real set"
  shows "x islimpt s \<longleftrightarrow> (\<forall>e>0. \<exists>x'\<in> s. x' \<noteq> x \<and> \<bar>x' - x\<bar> < e)"
  unfolding islimpt_approachable dist_norm by simp

lemma closed_real:
  fixes s :: "real set"
  shows "closed s \<longleftrightarrow> (\<forall>x. (\<forall>e>0.  \<exists>x' \<in> s. x' \<noteq> x \<and> \<bar>x' - x\<bar> < e) \<longrightarrow> x \<in> s)"
  unfolding closed_limpt islimpt_approachable dist_norm by simp

lemma continuous_at_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous (at x) f \<longleftrightarrow> (\<forall>e>0. \<exists>d>0. \<forall>x'. norm(x' - x) < d --> \<bar>f x' - f x\<bar> < e)"
  unfolding continuous_at
  unfolding Lim_at
  unfolding dist_norm
  apply auto
  apply (erule_tac x=e in allE, auto)
  apply (rule_tac x=d in exI, auto)
  apply (erule_tac x=x' in allE, auto)
  apply (erule_tac x=e in allE, auto)
  done

lemma continuous_on_real_range:
  fixes f :: "'a::real_normed_vector \<Rightarrow> real"
  shows "continuous_on s f \<longleftrightarrow>
    (\<forall>x \<in> s. \<forall>e>0. \<exists>d>0. (\<forall>x' \<in> s. norm(x' - x) < d \<longrightarrow> \<bar>f x' - f x\<bar> < e))"
  unfolding continuous_on_iff dist_norm by simp


subsection%unimportant \<open>Cartesian products\<close>

lemma bounded_Times:
  assumes "bounded s" "bounded t"
  shows "bounded (s \<times> t)"
proof -
  obtain x y a b where "\<forall>z\<in>s. dist x z \<le> a" "\<forall>z\<in>t. dist y z \<le> b"
    using assms [unfolded bounded_def] by auto
  then have "\<forall>z\<in>s \<times> t. dist (x, y) z \<le> sqrt (a\<^sup>2 + b\<^sup>2)"
    by (auto simp: dist_Pair_Pair real_sqrt_le_mono add_mono power_mono)
  then show ?thesis unfolding bounded_any_center [where a="(x, y)"] by auto
qed

lemma mem_Times_iff: "x \<in> A \<times> B \<longleftrightarrow> fst x \<in> A \<and> snd x \<in> B"
  by (induct x) simp

lemma seq_compact_Times: "seq_compact s \<Longrightarrow> seq_compact t \<Longrightarrow> seq_compact (s \<times> t)"
  unfolding seq_compact_def
  apply clarify
  apply (drule_tac x="fst \<circ> f" in spec)
  apply (drule mp, simp add: mem_Times_iff)
  apply (clarify, rename_tac l1 r1)
  apply (drule_tac x="snd \<circ> f \<circ> r1" in spec)
  apply (drule mp, simp add: mem_Times_iff)
  apply (clarify, rename_tac l2 r2)
  apply (rule_tac x="(l1, l2)" in rev_bexI, simp)
  apply (rule_tac x="r1 \<circ> r2" in exI)
  apply (rule conjI, simp add: strict_mono_def)
  apply (drule_tac f=r2 in LIMSEQ_subseq_LIMSEQ, assumption)
  apply (drule (1) tendsto_Pair) back
  apply (simp add: o_def)
  done

lemma compact_Times:
  assumes "compact s" "compact t"
  shows "compact (s \<times> t)"
proof (rule compactI)
  fix C
  assume C: "\<forall>t\<in>C. open t" "s \<times> t \<subseteq> \<Union>C"
  have "\<forall>x\<in>s. \<exists>a. open a \<and> x \<in> a \<and> (\<exists>d\<subseteq>C. finite d \<and> a \<times> t \<subseteq> \<Union>d)"
  proof
    fix x
    assume "x \<in> s"
    have "\<forall>y\<in>t. \<exists>a b c. c \<in> C \<and> open a \<and> open b \<and> x \<in> a \<and> y \<in> b \<and> a \<times> b \<subseteq> c" (is "\<forall>y\<in>t. ?P y")
    proof
      fix y
      assume "y \<in> t"
      with \<open>x \<in> s\<close> C obtain c where "c \<in> C" "(x, y) \<in> c" "open c" by auto
      then show "?P y" by (auto elim!: open_prod_elim)
    qed
    then obtain a b c where b: "\<And>y. y \<in> t \<Longrightarrow> open (b y)"
      and c: "\<And>y. y \<in> t \<Longrightarrow> c y \<in> C \<and> open (a y) \<and> open (b y) \<and> x \<in> a y \<and> y \<in> b y \<and> a y \<times> b y \<subseteq> c y"
      by metis
    then have "\<forall>y\<in>t. open (b y)" "t \<subseteq> (\<Union>y\<in>t. b y)" by auto
    with compactE_image[OF \<open>compact t\<close>] obtain D where D: "D \<subseteq> t" "finite D" "t \<subseteq> (\<Union>y\<in>D. b y)"
      by metis
    moreover from D c have "(\<Inter>y\<in>D. a y) \<times> t \<subseteq> (\<Union>y\<in>D. c y)"
      by (fastforce simp: subset_eq)
    ultimately show "\<exists>a. open a \<and> x \<in> a \<and> (\<exists>d\<subseteq>C. finite d \<and> a \<times> t \<subseteq> \<Union>d)"
      using c by (intro exI[of _ "c`D"] exI[of _ "\<Inter>(a`D)"] conjI) (auto intro!: open_INT)
  qed
  then obtain a d where a: "\<And>x. x\<in>s \<Longrightarrow> open (a x)" "s \<subseteq> (\<Union>x\<in>s. a x)"
    and d: "\<And>x. x \<in> s \<Longrightarrow> d x \<subseteq> C \<and> finite (d x) \<and> a x \<times> t \<subseteq> \<Union>d x"
    unfolding subset_eq UN_iff by metis
  moreover
  from compactE_image[OF \<open>compact s\<close> a]
  obtain e where e: "e \<subseteq> s" "finite e" and s: "s \<subseteq> (\<Union>x\<in>e. a x)"
    by auto
  moreover
  {
    from s have "s \<times> t \<subseteq> (\<Union>x\<in>e. a x \<times> t)"
      by auto
    also have "\<dots> \<subseteq> (\<Union>x\<in>e. \<Union>d x)"
      using d \<open>e \<subseteq> s\<close> by (intro UN_mono) auto
    finally have "s \<times> t \<subseteq> (\<Union>x\<in>e. \<Union>d x)" .
  }
  ultimately show "\<exists>C'\<subseteq>C. finite C' \<and> s \<times> t \<subseteq> \<Union>C'"
    by (intro exI[of _ "(\<Union>x\<in>e. d x)"]) (auto simp: subset_eq)
qed

text\<open>Hence some useful properties follow quite easily.\<close>

lemma compact_scaling:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. c *\<^sub>R x) ` s)"
proof -
  let ?f = "\<lambda>x. scaleR c x"
  have *: "bounded_linear ?f" by (rule bounded_linear_scaleR_right)
  show ?thesis
    using compact_continuous_image[of s ?f] continuous_at_imp_continuous_on[of s ?f]
    using linear_continuous_at[OF *] assms
    by auto
qed

lemma compact_negations:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. - x) ` s)"
  using compact_scaling [OF assms, of "- 1"] by auto

lemma compact_sums:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"
    and "compact t"
  shows "compact {x + y | x y. x \<in> s \<and> y \<in> t}"
proof -
  have *: "{x + y | x y. x \<in> s \<and> y \<in> t} = (\<lambda>z. fst z + snd z) ` (s \<times> t)"
    apply auto
    unfolding image_iff
    apply (rule_tac x="(xa, y)" in bexI)
    apply auto
    done
  have "continuous_on (s \<times> t) (\<lambda>z. fst z + snd z)"
    unfolding continuous_on by (rule ballI) (intro tendsto_intros)
  then show ?thesis
    unfolding * using compact_continuous_image compact_Times [OF assms] by auto
qed

lemma compact_differences:
  fixes s t :: "'a::real_normed_vector set"
  assumes "compact s"
    and "compact t"
  shows "compact {x - y | x y. x \<in> s \<and> y \<in> t}"
proof-
  have "{x - y | x y. x\<in>s \<and> y \<in> t} =  {x + y | x y. x \<in> s \<and> y \<in> (uminus ` t)}"
    apply auto
    apply (rule_tac x= xa in exI, auto)
    done
  then show ?thesis
    using compact_sums[OF assms(1) compact_negations[OF assms(2)]] by auto
qed

lemma compact_translation:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. a + x) ` s)"
proof -
  have "{x + y |x y. x \<in> s \<and> y \<in> {a}} = (\<lambda>x. a + x) ` s"
    by auto
  then show ?thesis
    using compact_sums[OF assms compact_sing[of a]] by auto
qed

lemma compact_affinity:
  fixes s :: "'a::real_normed_vector set"
  assumes "compact s"
  shows "compact ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have "(+) a ` (*\<^sub>R) c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s"
    by auto
  then show ?thesis
    using compact_translation[OF compact_scaling[OF assms], of a c] by auto
qed

text \<open>Hence we get the following.\<close>

lemma compact_sup_maxdistance:
  fixes s :: "'a::metric_space set"
  assumes "compact s"
    and "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. \<forall>u\<in>s. \<forall>v\<in>s. dist u v \<le> dist x y"
proof -
  have "compact (s \<times> s)"
    using \<open>compact s\<close> by (intro compact_Times)
  moreover have "s \<times> s \<noteq> {}"
    using \<open>s \<noteq> {}\<close> by auto
  moreover have "continuous_on (s \<times> s) (\<lambda>x. dist (fst x) (snd x))"
    by (intro continuous_at_imp_continuous_on ballI continuous_intros)
  ultimately show ?thesis
    using continuous_attains_sup[of "s \<times> s" "\<lambda>x. dist (fst x) (snd x)"] by auto
qed


subsection \<open>The diameter of a set\<close>

definition%important diameter :: "'a::metric_space set \<Rightarrow> real" where
  "diameter S = (if S = {} then 0 else SUP (x,y)\<in>S\<times>S. dist x y)"

lemma diameter_empty [simp]: "diameter{} = 0"
  by (auto simp: diameter_def)

lemma diameter_singleton [simp]: "diameter{x} = 0"
  by (auto simp: diameter_def)

lemma diameter_le:
  assumes "S \<noteq> {} \<or> 0 \<le> d"
      and no: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> norm(x - y) \<le> d"
    shows "diameter S \<le> d"
using assms
  by (auto simp: dist_norm diameter_def intro: cSUP_least)

lemma diameter_bounded_bound:
  fixes s :: "'a :: metric_space set"
  assumes s: "bounded s" "x \<in> s" "y \<in> s"
  shows "dist x y \<le> diameter s"
proof -
  from s obtain z d where z: "\<And>x. x \<in> s \<Longrightarrow> dist z x \<le> d"
    unfolding bounded_def by auto
  have "bdd_above (case_prod dist ` (s\<times>s))"
  proof (intro bdd_aboveI, safe)
    fix a b
    assume "a \<in> s" "b \<in> s"
    with z[of a] z[of b] dist_triangle[of a b z]
    show "dist a b \<le> 2 * d"
      by (simp add: dist_commute)
  qed
  moreover have "(x,y) \<in> s\<times>s" using s by auto
  ultimately have "dist x y \<le> (SUP (x,y)\<in>s\<times>s. dist x y)"
    by (rule cSUP_upper2) simp
  with \<open>x \<in> s\<close> show ?thesis
    by (auto simp: diameter_def)
qed

lemma diameter_lower_bounded:
  fixes s :: "'a :: metric_space set"
  assumes s: "bounded s"
    and d: "0 < d" "d < diameter s"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. d < dist x y"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  moreover have "s \<noteq> {}"
    using d by (auto simp: diameter_def)
  ultimately have "diameter s \<le> d"
    by (auto simp: not_less diameter_def intro!: cSUP_least)
  with \<open>d < diameter s\<close> show False by auto
qed

lemma diameter_bounded:
  assumes "bounded s"
  shows "\<forall>x\<in>s. \<forall>y\<in>s. dist x y \<le> diameter s"
    and "\<forall>d>0. d < diameter s \<longrightarrow> (\<exists>x\<in>s. \<exists>y\<in>s. dist x y > d)"
  using diameter_bounded_bound[of s] diameter_lower_bounded[of s] assms
  by auto

lemma bounded_two_points:
  "bounded S \<longleftrightarrow> (\<exists>e. \<forall>x\<in>S. \<forall>y\<in>S. dist x y \<le> e)"
  apply (rule iffI)
  subgoal using diameter_bounded(1) by auto
  subgoal using bounded_any_center[of S] by meson
  done

lemma diameter_compact_attained:
  assumes "compact s"
    and "s \<noteq> {}"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. dist x y = diameter s"
proof -
  have b: "bounded s" using assms(1)
    by (rule compact_imp_bounded)
  then obtain x y where xys: "x\<in>s" "y\<in>s"
    and xy: "\<forall>u\<in>s. \<forall>v\<in>s. dist u v \<le> dist x y"
    using compact_sup_maxdistance[OF assms] by auto
  then have "diameter s \<le> dist x y"
    unfolding diameter_def
    apply clarsimp
    apply (rule cSUP_least, fast+)
    done
  then show ?thesis
    by (metis b diameter_bounded_bound order_antisym xys)
qed

lemma diameter_ge_0:
  assumes "bounded S"  shows "0 \<le> diameter S"
  by (metis all_not_in_conv assms diameter_bounded_bound diameter_empty dist_self order_refl)

lemma diameter_subset:
  assumes "S \<subseteq> T" "bounded T"
  shows "diameter S \<le> diameter T"
proof (cases "S = {} \<or> T = {}")
  case True
  with assms show ?thesis
    by (force simp: diameter_ge_0)
next
  case False
  then have "bdd_above ((\<lambda>x. case x of (x, xa) \<Rightarrow> dist x xa) ` (T \<times> T))"
    using \<open>bounded T\<close> diameter_bounded_bound by (force simp: bdd_above_def)
  with False \<open>S \<subseteq> T\<close> show ?thesis
    apply (simp add: diameter_def)
    apply (rule cSUP_subset_mono, auto)
    done
qed

lemma diameter_closure:
  assumes "bounded S"
  shows "diameter(closure S) = diameter S"
proof (rule order_antisym)
  have "False" if "diameter S < diameter (closure S)"
  proof -
    define d where "d = diameter(closure S) - diameter(S)"
    have "d > 0"
      using that by (simp add: d_def)
    then have "diameter(closure(S)) - d / 2 < diameter(closure(S))"
      by simp
    have dd: "diameter (closure S) - d / 2 = (diameter(closure(S)) + diameter(S)) / 2"
      by (simp add: d_def divide_simps)
     have bocl: "bounded (closure S)"
      using assms by blast
    moreover have "0 \<le> diameter S"
      using assms diameter_ge_0 by blast
    ultimately obtain x y where "x \<in> closure S" "y \<in> closure S" and xy: "diameter(closure(S)) - d / 2 < dist x y"
      using diameter_bounded(2) [OF bocl, rule_format, of "diameter(closure(S)) - d / 2"] \<open>d > 0\<close> d_def by auto
    then obtain x' y' where x'y': "x' \<in> S" "dist x' x < d/4" "y' \<in> S" "dist y' y < d/4"
      using closure_approachable
      by (metis \<open>0 < d\<close> zero_less_divide_iff zero_less_numeral)
    then have "dist x' y' \<le> diameter S"
      using assms diameter_bounded_bound by blast
    with x'y' have "dist x y \<le> d / 4 + diameter S + d / 4"
      by (meson add_mono_thms_linordered_semiring(1) dist_triangle dist_triangle3 less_eq_real_def order_trans)
    then show ?thesis
      using xy d_def by linarith
  qed
  then show "diameter (closure S) \<le> diameter S"
    by fastforce
  next
    show "diameter S \<le> diameter (closure S)"
      by (simp add: assms bounded_closure closure_subset diameter_subset)
qed

lemma diameter_cball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(cball a r) = (if r < 0 then 0 else 2*r)"
proof -
  have "diameter(cball a r) = 2*r" if "r \<ge> 0"
  proof (rule order_antisym)
    show "diameter (cball a r) \<le> 2*r"
    proof (rule diameter_le)
      fix x y assume "x \<in> cball a r" "y \<in> cball a r"
      then have "norm (x - a) \<le> r" "norm (a - y) \<le> r"
        by (auto simp: dist_norm norm_minus_commute)
      then have "norm (x - y) \<le> r+r"
        using norm_diff_triangle_le by blast
      then show "norm (x - y) \<le> 2*r" by simp
    qed (simp add: that)
    have "2*r = dist (a + r *\<^sub>R (SOME i. i \<in> Basis)) (a - r *\<^sub>R (SOME i. i \<in> Basis))"
      apply (simp add: dist_norm)
      by (metis abs_of_nonneg mult.right_neutral norm_numeral norm_scaleR norm_some_Basis real_norm_def scaleR_2 that)
    also have "... \<le> diameter (cball a r)"
      apply (rule diameter_bounded_bound)
      using that by (auto simp: dist_norm)
    finally show "2*r \<le> diameter (cball a r)" .
  qed
  then show ?thesis by simp
qed

lemma diameter_ball [simp]:
  fixes a :: "'a::euclidean_space"
  shows "diameter(ball a r) = (if r < 0 then 0 else 2*r)"
proof -
  have "diameter(ball a r) = 2*r" if "r > 0"
    by (metis bounded_ball diameter_closure closure_ball diameter_cball less_eq_real_def linorder_not_less that)
  then show ?thesis
    by (simp add: diameter_def)
qed

lemma diameter_closed_interval [simp]: "diameter {a..b} = (if b < a then 0 else b-a)"
proof -
  have "{a .. b} = cball ((a+b)/2) ((b-a)/2)"
    by (auto simp: dist_norm abs_if divide_simps split: if_split_asm)
  then show ?thesis
    by simp
qed

lemma diameter_open_interval [simp]: "diameter {a<..<b} = (if b < a then 0 else b-a)"
proof -
  have "{a <..< b} = ball ((a+b)/2) ((b-a)/2)"
    by (auto simp: dist_norm abs_if divide_simps split: if_split_asm)
  then show ?thesis
    by simp
qed

proposition Lebesgue_number_lemma:
  assumes "compact S" "\<C> \<noteq> {}" "S \<subseteq> \<Union>\<C>" and ope: "\<And>B. B \<in> \<C> \<Longrightarrow> open B"
  obtains \<delta> where "0 < \<delta>" "\<And>T. \<lbrakk>T \<subseteq> S; diameter T < \<delta>\<rbrakk> \<Longrightarrow> \<exists>B \<in> \<C>. T \<subseteq> B"
proof (cases "S = {}")
  case True
  then show ?thesis
    by (metis \<open>\<C> \<noteq> {}\<close> zero_less_one empty_subsetI equals0I subset_trans that)
next
  case False
  { fix x assume "x \<in> S"
    then obtain C where C: "x \<in> C" "C \<in> \<C>"
      using \<open>S \<subseteq> \<Union>\<C>\<close> by blast
    then obtain r where r: "r>0" "ball x (2*r) \<subseteq> C"
      by (metis mult.commute mult_2_right not_le ope openE field_sum_of_halves zero_le_numeral zero_less_mult_iff)
    then have "\<exists>r C. r > 0 \<and> ball x (2*r) \<subseteq> C \<and> C \<in> \<C>"
      using C by blast
  }
  then obtain r where r: "\<And>x. x \<in> S \<Longrightarrow> r x > 0 \<and> (\<exists>C \<in> \<C>. ball x (2*r x) \<subseteq> C)"
    by metis
  then have "S \<subseteq> (\<Union>x \<in> S. ball x (r x))"
    by auto
  then obtain \<T> where "finite \<T>" "S \<subseteq> \<Union>\<T>" and \<T>: "\<T> \<subseteq> (\<lambda>x. ball x (r x)) ` S"
    by (rule compactE [OF \<open>compact S\<close>]) auto
  then obtain S0 where "S0 \<subseteq> S" "finite S0" and S0: "\<T> = (\<lambda>x. ball x (r x)) ` S0"
    by (meson finite_subset_image)
  then have "S0 \<noteq> {}"
    using False \<open>S \<subseteq> \<Union>\<T>\<close> by auto
  define \<delta> where "\<delta> = Inf (r ` S0)"
  have "\<delta> > 0"
    using \<open>finite S0\<close> \<open>S0 \<subseteq> S\<close> \<open>S0 \<noteq> {}\<close> r by (auto simp: \<delta>_def finite_less_Inf_iff)
  show ?thesis
  proof
    show "0 < \<delta>"
      by (simp add: \<open>0 < \<delta>\<close>)
    show "\<exists>B \<in> \<C>. T \<subseteq> B" if "T \<subseteq> S" and dia: "diameter T < \<delta>" for T
    proof (cases "T = {}")
      case True
      then show ?thesis
        using \<open>\<C> \<noteq> {}\<close> by blast
    next
      case False
      then obtain y where "y \<in> T" by blast
      then have "y \<in> S"
        using \<open>T \<subseteq> S\<close> by auto
      then obtain x where "x \<in> S0" and x: "y \<in> ball x (r x)"
        using \<open>S \<subseteq> \<Union>\<T>\<close> S0 that by blast
      have "ball y \<delta> \<subseteq> ball y (r x)"
        by (metis \<delta>_def \<open>S0 \<noteq> {}\<close> \<open>finite S0\<close> \<open>x \<in> S0\<close> empty_is_image finite_imageI finite_less_Inf_iff imageI less_irrefl not_le subset_ball)
      also have "... \<subseteq> ball x (2*r x)"
        by clarsimp (metis dist_commute dist_triangle_less_add mem_ball mult_2 x)
      finally obtain C where "C \<in> \<C>" "ball y \<delta> \<subseteq> C"
        by (meson r \<open>S0 \<subseteq> S\<close> \<open>x \<in> S0\<close> dual_order.trans subsetCE)
      have "bounded T"
        using \<open>compact S\<close> bounded_subset compact_imp_bounded \<open>T \<subseteq> S\<close> by blast
      then have "T \<subseteq> ball y \<delta>"
        using \<open>y \<in> T\<close> dia diameter_bounded_bound by fastforce
      then show ?thesis
        apply (rule_tac x=C in bexI)
        using \<open>ball y \<delta> \<subseteq> C\<close> \<open>C \<in> \<C>\<close> by auto
    qed
  qed
qed

lemma diameter_cbox:
  fixes a b::"'a::euclidean_space"
  shows "(\<forall>i \<in> Basis. a \<bullet> i \<le> b \<bullet> i) \<Longrightarrow> diameter (cbox a b) = dist a b"
  by (force simp: diameter_def intro!: cSup_eq_maximum L2_set_mono
     simp: euclidean_dist_l2[where 'a='a] cbox_def dist_norm)

subsection \<open>Separation between points and sets\<close>

proposition separate_point_closed:
  fixes s :: "'a::heine_borel set"
  assumes "closed s" and "a \<notin> s"
  shows "\<exists>d>0. \<forall>x\<in>s. d \<le> dist a x"
proof (cases "s = {}")
  case True
  then show ?thesis by(auto intro!: exI[where x=1])
next
  case False
  from assms obtain x where "x\<in>s" "\<forall>y\<in>s. dist a x \<le> dist a y"
    using \<open>s \<noteq> {}\<close> by (blast intro: distance_attains_inf [of s a])
  with \<open>x\<in>s\<close> show ?thesis using dist_pos_lt[of a x] and\<open>a \<notin> s\<close>
    by blast
qed

proposition separate_compact_closed:
  fixes s t :: "'a::heine_borel set"
  assumes "compact s"
    and t: "closed t" "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof cases
  assume "s \<noteq> {} \<and> t \<noteq> {}"
  then have "s \<noteq> {}" "t \<noteq> {}" by auto
  let ?inf = "\<lambda>x. infdist x t"
  have "continuous_on s ?inf"
    by (auto intro!: continuous_at_imp_continuous_on continuous_infdist continuous_ident)
  then obtain x where x: "x \<in> s" "\<forall>y\<in>s. ?inf x \<le> ?inf y"
    using continuous_attains_inf[OF \<open>compact s\<close> \<open>s \<noteq> {}\<close>] by auto
  then have "0 < ?inf x"
    using t \<open>t \<noteq> {}\<close> in_closed_iff_infdist_zero by (auto simp: less_le infdist_nonneg)
  moreover have "\<forall>x'\<in>s. \<forall>y\<in>t. ?inf x \<le> dist x' y"
    using x by (auto intro: order_trans infdist_le)
  ultimately show ?thesis by auto
qed (auto intro!: exI[of _ 1])

proposition separate_closed_compact:
  fixes s t :: "'a::heine_borel set"
  assumes "closed s"
    and "compact t"
    and "s \<inter> t = {}"
  shows "\<exists>d>0. \<forall>x\<in>s. \<forall>y\<in>t. d \<le> dist x y"
proof -
  have *: "t \<inter> s = {}"
    using assms(3) by auto
  show ?thesis
    using separate_compact_closed[OF assms(2,1) *] by (force simp: dist_commute)
qed

proposition compact_in_open_separated:
  fixes A::"'a::heine_borel set"
  assumes "A \<noteq> {}"
  assumes "compact A"
  assumes "open B"
  assumes "A \<subseteq> B"
  obtains e where "e > 0" "{x. infdist x A \<le> e} \<subseteq> B"
proof atomize_elim
  have "closed (- B)" "compact A" "- B \<inter> A = {}"
    using assms by (auto simp: open_Diff compact_eq_bounded_closed)
  from separate_closed_compact[OF this]
  obtain d'::real where d': "d'>0" "\<And>x y. x \<notin> B \<Longrightarrow> y \<in> A \<Longrightarrow> d' \<le> dist x y"
    by auto
  define d where "d = d' / 2"
  hence "d>0" "d < d'" using d' by auto
  with d' have d: "\<And>x y. x \<notin> B \<Longrightarrow> y \<in> A \<Longrightarrow> d < dist x y"
    by force
  show "\<exists>e>0. {x. infdist x A \<le> e} \<subseteq> B"
  proof (rule ccontr)
    assume "\<nexists>e. 0 < e \<and> {x. infdist x A \<le> e} \<subseteq> B"
    with \<open>d > 0\<close> obtain x where x: "infdist x A \<le> d" "x \<notin> B"
      by auto
    from assms have "closed A" "A \<noteq> {}" by (auto simp: compact_eq_bounded_closed)
    from infdist_attains_inf[OF this]
    obtain y where y: "y \<in> A" "infdist x A = dist x y"
      by auto
    have "dist x y \<le> d" using x y by simp
    also have "\<dots> < dist x y" using y d x by auto
    finally show False by simp
  qed
qed


subsection%unimportant \<open>Compact sets and the closure operation\<close>

lemma closed_scaling:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closed ((\<lambda>x. c *\<^sub>R x) ` S)"
proof (cases "c = 0")
  case True then show ?thesis
    by (auto simp: image_constant_conv)
next
  case False
  from assms have "closed ((\<lambda>x. inverse c *\<^sub>R x) -` S)"
    by (simp add: continuous_closed_vimage)
  also have "(\<lambda>x. inverse c *\<^sub>R x) -` S = (\<lambda>x. c *\<^sub>R x) ` S"
    using \<open>c \<noteq> 0\<close> by (auto elim: image_eqI [rotated])
  finally show ?thesis .
qed

lemma closed_negations:
  fixes S :: "'a::real_normed_vector set"
  assumes "closed S"
  shows "closed ((\<lambda>x. -x) ` S)"
  using closed_scaling[OF assms, of "- 1"] by simp

lemma compact_closed_sums:
  fixes S :: "'a::real_normed_vector set"
  assumes "compact S" and "closed T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  let ?S = "{x + y |x y. x \<in> S \<and> y \<in> T}"
  {
    fix x l
    assume as: "\<forall>n. x n \<in> ?S"  "(x \<longlongrightarrow> l) sequentially"
    from as(1) obtain f where f: "\<forall>n. x n = fst (f n) + snd (f n)"  "\<forall>n. fst (f n) \<in> S"  "\<forall>n. snd (f n) \<in> T"
      using choice[of "\<lambda>n y. x n = (fst y) + (snd y) \<and> fst y \<in> S \<and> snd y \<in> T"] by auto
    obtain l' r where "l'\<in>S" and r: "strict_mono r" and lr: "(((\<lambda>n. fst (f n)) \<circ> r) \<longlongrightarrow> l') sequentially"
      using assms(1)[unfolded compact_def, THEN spec[where x="\<lambda> n. fst (f n)"]] using f(2) by auto
    have "((\<lambda>n. snd (f (r n))) \<longlongrightarrow> l - l') sequentially"
      using tendsto_diff[OF LIMSEQ_subseq_LIMSEQ[OF as(2) r] lr] and f(1)
      unfolding o_def
      by auto
    then have "l - l' \<in> T"
      using assms(2)[unfolded closed_sequential_limits,
        THEN spec[where x="\<lambda> n. snd (f (r n))"],
        THEN spec[where x="l - l'"]]
      using f(3)
      by auto
    then have "l \<in> ?S"
      using \<open>l' \<in> S\<close>
      apply auto
      apply (rule_tac x=l' in exI)
      apply (rule_tac x="l - l'" in exI, auto)
      done
  }
  moreover have "?S = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by force
  ultimately show ?thesis
    unfolding closed_sequential_limits
    by (metis (no_types, lifting))
qed

lemma closed_compact_sums:
  fixes S T :: "'a::real_normed_vector set"
  assumes "closed S" "compact T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
proof -
  have "(\<Union>x\<in> T. \<Union>y \<in> S. {x + y}) = (\<Union>x\<in> S. \<Union>y \<in> T. {x + y})"
    by auto
  then show ?thesis
    using compact_closed_sums[OF assms(2,1)] by simp
qed

lemma compact_closed_differences:
  fixes S T :: "'a::real_normed_vector set"
  assumes "compact S" "closed T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> uminus ` T. {x + y}) = (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
    by force
  then show ?thesis
    using compact_closed_sums[OF assms(1) closed_negations[OF assms(2)]] by auto
qed

lemma closed_compact_differences:
  fixes S T :: "'a::real_normed_vector set"
  assumes "closed S" "compact T"
  shows "closed (\<Union>x\<in> S. \<Union>y \<in> T. {x - y})"
proof -
  have "(\<Union>x\<in> S. \<Union>y \<in> uminus ` T. {x + y}) = {x - y |x y. x \<in> S \<and> y \<in> T}"
    by auto
 then show ?thesis
  using closed_compact_sums[OF assms(1) compact_negations[OF assms(2)]] by simp
qed

lemma closed_translation:
  fixes a :: "'a::real_normed_vector"
  assumes "closed S"
  shows "closed ((\<lambda>x. a + x) ` S)"
proof -
  have "(\<Union>x\<in> {a}. \<Union>y \<in> S. {x + y}) = ((+) a ` S)" by auto
  then show ?thesis
    using compact_closed_sums[OF compact_sing[of a] assms] by auto
qed

lemma closure_translation:
  fixes a :: "'a::real_normed_vector"
  shows "closure ((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (closure s)"
proof -
  have *: "(+) a ` (- s) = - (+) a ` s"
    apply auto
    unfolding image_iff
    apply (rule_tac x="x - a" in bexI, auto)
    done
  show ?thesis
    unfolding closure_interior translation_Compl
    using interior_translation[of a "- s"]
    unfolding *
    by auto
qed

lemma frontier_translation:
  fixes a :: "'a::real_normed_vector"
  shows "frontier((\<lambda>x. a + x) ` s) = (\<lambda>x. a + x) ` (frontier s)"
  unfolding frontier_def translation_diff interior_translation closure_translation
  by auto

lemma sphere_translation:
  fixes a :: "'n::euclidean_space"
  shows "sphere (a+c) r = (+) a ` sphere c r"
apply safe
apply (rule_tac x="x-a" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma cball_translation:
  fixes a :: "'n::euclidean_space"
  shows "cball (a+c) r = (+) a ` cball c r"
apply safe
apply (rule_tac x="x-a" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done

lemma ball_translation:
  fixes a :: "'n::euclidean_space"
  shows "ball (a+c) r = (+) a ` ball c r"
apply safe
apply (rule_tac x="x-a" in image_eqI)
apply (auto simp: dist_norm algebra_simps)
done


subsection%unimportant \<open>Closure of halfspaces and hyperplanes\<close>

lemma continuous_on_closed_Collect_le:
  fixes f g :: "'a::t2_space \<Rightarrow> real"
  assumes f: "continuous_on s f" and g: "continuous_on s g" and s: "closed s"
  shows "closed {x \<in> s. f x \<le> g x}"
proof -
  have "closed ((\<lambda>x. g x - f x) -` {0..} \<inter> s)"
    using closed_real_atLeast continuous_on_diff [OF g f]
    by (simp add: continuous_on_closed_vimage [OF s])
  also have "((\<lambda>x. g x - f x) -` {0..} \<inter> s) = {x\<in>s. f x \<le> g x}"
    by auto
  finally show ?thesis .
qed

lemma continuous_at_inner: "continuous (at x) (inner a)"
  unfolding continuous_at by (intro tendsto_intros)

lemma closed_halfspace_le: "closed {x. inner a x \<le> b}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_halfspace_ge: "closed {x. inner a x \<ge> b}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_hyperplane: "closed {x. inner a x = b}"
  by (simp add: closed_Collect_eq continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_halfspace_component_le: "closed {x::'a::euclidean_space. x\<bullet>i \<le> a}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_halfspace_component_ge: "closed {x::'a::euclidean_space. x\<bullet>i \<ge> a}"
  by (simp add: closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_interval_left:
  fixes b :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. x\<bullet>i \<le> b\<bullet>i}"
  by (simp add: Collect_ball_eq closed_INT closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma closed_interval_right:
  fixes a :: "'a::euclidean_space"
  shows "closed {x::'a. \<forall>i\<in>Basis. a\<bullet>i \<le> x\<bullet>i}"
  by (simp add: Collect_ball_eq closed_INT closed_Collect_le continuous_on_inner continuous_on_const continuous_on_id)

lemma continuous_le_on_closure:
  fixes a::real
  assumes f: "continuous_on (closure s) f"
      and x: "x \<in> closure(s)"
      and xlo: "\<And>x. x \<in> s ==> f(x) \<le> a"
    shows "f(x) \<le> a"
    using image_closure_subset [OF f]
  using image_closure_subset [OF f] closed_halfspace_le [of "1::real" a] assms
  by force

lemma continuous_ge_on_closure:
  fixes a::real
  assumes f: "continuous_on (closure s) f"
      and x: "x \<in> closure(s)"
      and xlo: "\<And>x. x \<in> s ==> f(x) \<ge> a"
    shows "f(x) \<ge> a"
  using image_closure_subset [OF f] closed_halfspace_ge [of a "1::real"] assms
  by force

lemma Lim_component_le:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. f(x)\<bullet>i \<le> b) net"
  shows "l\<bullet>i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_inner[OF assms(1) tendsto_const] assms(3)])

lemma Lim_component_ge:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes "(f \<longlongrightarrow> l) net"
    and "\<not> (trivial_limit net)"
    and "eventually (\<lambda>x. b \<le> (f x)\<bullet>i) net"
  shows "b \<le> l\<bullet>i"
  by (rule tendsto_le[OF assms(2) tendsto_inner[OF assms(1) tendsto_const] tendsto_const assms(3)])

lemma Lim_component_eq:
  fixes f :: "'a \<Rightarrow> 'b::euclidean_space"
  assumes net: "(f \<longlongrightarrow> l) net" "\<not> trivial_limit net"
    and ev:"eventually (\<lambda>x. f(x)\<bullet>i = b) net"
  shows "l\<bullet>i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff]
  using Lim_component_ge[OF net, of b i]
  using Lim_component_le[OF net, of i b]
  by auto

text \<open>Limits relative to a union.\<close>

lemma eventually_within_Un:
  "eventually P (at x within (s \<union> t)) \<longleftrightarrow>
    eventually P (at x within s) \<and> eventually P (at x within t)"
  unfolding eventually_at_filter
  by (auto elim!: eventually_rev_mp)

lemma Lim_within_union:
 "(f \<longlongrightarrow> l) (at x within (s \<union> t)) \<longleftrightarrow>
  (f \<longlongrightarrow> l) (at x within s) \<and> (f \<longlongrightarrow> l) (at x within t)"
  unfolding tendsto_def
  by (auto simp: eventually_within_Un)

lemma Lim_topological:
  "(f \<longlongrightarrow> l) net \<longleftrightarrow>
    trivial_limit net \<or> (\<forall>S. open S \<longrightarrow> l \<in> S \<longrightarrow> eventually (\<lambda>x. f x \<in> S) net)"
  unfolding tendsto_def trivial_limit_eq by auto

text \<open>Continuity relative to a union.\<close>

lemma continuous_on_Un_local:
    "\<lbrakk>closedin (subtopology euclidean (s \<union> t)) s; closedin (subtopology euclidean (s \<union> t)) t;
      continuous_on s f; continuous_on t f\<rbrakk>
     \<Longrightarrow> continuous_on (s \<union> t) f"
  unfolding continuous_on closedin_limpt
  by (metis Lim_trivial_limit Lim_within_union Un_iff trivial_limit_within)

lemma continuous_on_cases_local:
     "\<lbrakk>closedin (subtopology euclidean (s \<union> t)) s; closedin (subtopology euclidean (s \<union> t)) t;
       continuous_on s f; continuous_on t g;
       \<And>x. \<lbrakk>x \<in> s \<and> \<not>P x \<or> x \<in> t \<and> P x\<rbrakk> \<Longrightarrow> f x = g x\<rbrakk>
      \<Longrightarrow> continuous_on (s \<union> t) (\<lambda>x. if P x then f x else g x)"
  by (rule continuous_on_Un_local) (auto intro: continuous_on_eq)

lemma continuous_on_cases_le:
  fixes h :: "'a :: topological_space \<Rightarrow> real"
  assumes "continuous_on {t \<in> s. h t \<le> a} f"
      and "continuous_on {t \<in> s. a \<le> h t} g"
      and h: "continuous_on s h"
      and "\<And>t. \<lbrakk>t \<in> s; h t = a\<rbrakk> \<Longrightarrow> f t = g t"
    shows "continuous_on s (\<lambda>t. if h t \<le> a then f(t) else g(t))"
proof -
  have s: "s = (s \<inter> h -` atMost a) \<union> (s \<inter> h -` atLeast a)"
    by force
  have 1: "closedin (subtopology euclidean s) (s \<inter> h -` atMost a)"
    by (rule continuous_closedin_preimage [OF h closed_atMost])
  have 2: "closedin (subtopology euclidean s) (s \<inter> h -` atLeast a)"
    by (rule continuous_closedin_preimage [OF h closed_atLeast])
  have eq: "s \<inter> h -` {..a} = {t \<in> s. h t \<le> a}" "s \<inter> h -` {a..} = {t \<in> s. a \<le> h t}"
    by auto
  show ?thesis
    apply (rule continuous_on_subset [of s, OF _ order_refl])
    apply (subst s)
    apply (rule continuous_on_cases_local)
    using 1 2 s assms apply (auto simp: eq)
    done
qed

lemma continuous_on_cases_1:
  fixes s :: "real set"
  assumes "continuous_on {t \<in> s. t \<le> a} f"
      and "continuous_on {t \<in> s. a \<le> t} g"
      and "a \<in> s \<Longrightarrow> f a = g a"
    shows "continuous_on s (\<lambda>t. if t \<le> a then f(t) else g(t))"
using assms
by (auto simp: continuous_on_id intro: continuous_on_cases_le [where h = id, simplified])

subsubsection\<open>Some more convenient intermediate-value theorem formulations\<close>

lemma connected_ivt_hyperplane:
  assumes "connected S" and xy: "x \<in> S" "y \<in> S" and b: "inner a x \<le> b" "b \<le> inner a y"
  shows "\<exists>z \<in> S. inner a z = b"
proof (rule ccontr)
  assume as:"\<not> (\<exists>z\<in>S. inner a z = b)"
  let ?A = "{x. inner a x < b}"
  let ?B = "{x. inner a x > b}"
  have "open ?A" "open ?B"
    using open_halfspace_lt and open_halfspace_gt by auto
  moreover have "?A \<inter> ?B = {}" by auto
  moreover have "S \<subseteq> ?A \<union> ?B" using as by auto
  ultimately show False
    using \<open>connected S\<close>[unfolded connected_def not_ex,
      THEN spec[where x="?A"], THEN spec[where x="?B"]]
    using xy b by auto
qed

lemma connected_ivt_component:
  fixes x::"'a::euclidean_space"
  shows "connected S \<Longrightarrow> x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x\<bullet>k \<le> a \<Longrightarrow> a \<le> y\<bullet>k \<Longrightarrow> (\<exists>z\<in>S.  z\<bullet>k = a)"
  using connected_ivt_hyperplane[of S x y "k::'a" a]
  by (auto simp: inner_commute)

lemma image_affinity_cbox: fixes m::real
  fixes a b c :: "'a::euclidean_space"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` cbox a b =
    (if cbox a b = {} then {}
     else (if 0 \<le> m then cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)
     else cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c)))"
proof (cases "m = 0")
  case True
  {
    fix x
    assume "\<forall>i\<in>Basis. x \<bullet> i \<le> c \<bullet> i" "\<forall>i\<in>Basis. c \<bullet> i \<le> x \<bullet> i"
    then have "x = c"
      by (simp add: dual_order.antisym euclidean_eqI)
  }
  moreover have "c \<in> cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)"
    unfolding True by (auto simp: cbox_sing)
  ultimately show ?thesis using True by (auto simp: cbox_def)
next
  case False
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m > 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
      by (auto simp: inner_distrib)
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m < 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i"
      by (auto simp: mult_left_mono_neg inner_distrib)
  }
  moreover
  {
    fix y
    assume "m > 0" and "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> y \<bullet> i" and "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp: pos_le_divide_eq pos_divide_le_eq mult.commute inner_distrib inner_diff_left)
      done
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i" "m < 0"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp: neg_le_divide_eq neg_divide_le_eq mult.commute inner_distrib inner_diff_left)
      done
  }
  ultimately show ?thesis using False by (auto simp: cbox_def)
qed

lemma image_smult_cbox:"(\<lambda>x. m *\<^sub>R (x::_::euclidean_space)) ` cbox a b =
  (if cbox a b = {} then {} else if 0 \<le> m then cbox (m *\<^sub>R a) (m *\<^sub>R b) else cbox (m *\<^sub>R b) (m *\<^sub>R a))"
  using image_affinity_cbox[of m 0 a b] by auto

lemma islimpt_greaterThanLessThan1:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "a islimpt {a<..<b}"
proof (rule islimptI)
  fix T
  assume "open T" "a \<in> T"
  from open_right[OF this \<open>a < b\<close>]
  obtain c where c: "a < c" "{a..<c} \<subseteq> T" by auto
  with assms dense[of a "min c b"]
  show "\<exists>y\<in>{a<..<b}. y \<in> T \<and> y \<noteq> a"
    by (metis atLeastLessThan_iff greaterThanLessThan_iff min_less_iff_conj
      not_le order.strict_implies_order subset_eq)
qed

lemma islimpt_greaterThanLessThan2:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows  "b islimpt {a<..<b}"
proof (rule islimptI)
  fix T
  assume "open T" "b \<in> T"
  from open_left[OF this \<open>a < b\<close>]
  obtain c where c: "c < b" "{c<..b} \<subseteq> T" by auto
  with assms dense[of "max a c" b]
  show "\<exists>y\<in>{a<..<b}. y \<in> T \<and> y \<noteq> b"
    by (metis greaterThanAtMost_iff greaterThanLessThan_iff max_less_iff_conj
      not_le order.strict_implies_order subset_eq)
qed

lemma closure_greaterThanLessThan[simp]:
  fixes a b::"'a::{linorder_topology, dense_order}"
  shows "a < b \<Longrightarrow> closure {a <..< b} = {a .. b}" (is "_ \<Longrightarrow> ?l = ?r")
proof
  have "?l \<subseteq> closure ?r"
    by (rule closure_mono) auto
  thus "closure {a<..<b} \<subseteq> {a..b}" by simp
qed (auto simp: closure_def order.order_iff_strict islimpt_greaterThanLessThan1
  islimpt_greaterThanLessThan2)

lemma closure_greaterThan[simp]:
  fixes a b::"'a::{no_top, linorder_topology, dense_order}"
  shows "closure {a<..} = {a..}"
proof -
  from gt_ex obtain b where "a < b" by auto
  hence "{a<..} = {a<..<b} \<union> {b..}" by auto
  also have "closure \<dots> = {a..}" using \<open>a < b\<close> unfolding closure_Un
    by auto
  finally show ?thesis .
qed

lemma closure_lessThan[simp]:
  fixes b::"'a::{no_bot, linorder_topology, dense_order}"
  shows "closure {..<b} = {..b}"
proof -
  from lt_ex obtain a where "a < b" by auto
  hence "{..<b} = {a<..<b} \<union> {..a}" by auto
  also have "closure \<dots> = {..b}" using \<open>a < b\<close> unfolding closure_Un
    by auto
  finally show ?thesis .
qed

lemma closure_atLeastLessThan[simp]:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows "closure {a ..< b} = {a .. b}"
proof -
  from assms have "{a ..< b} = {a} \<union> {a <..< b}" by auto
  also have "closure \<dots> = {a .. b}" unfolding closure_Un
    by (auto simp: assms less_imp_le)
  finally show ?thesis .
qed

lemma closure_greaterThanAtMost[simp]:
  fixes a b::"'a::{linorder_topology, dense_order}"
  assumes "a < b"
  shows "closure {a <.. b} = {a .. b}"
proof -
  from assms have "{a <.. b} = {b} \<union> {a <..< b}" by auto
  also have "closure \<dots> = {a .. b}" unfolding closure_Un
    by (auto simp: assms less_imp_le)
  finally show ?thesis .
qed


subsection \<open>Homeomorphisms\<close>

definition%important "homeomorphism s t f g \<longleftrightarrow>
  (\<forall>x\<in>s. (g(f x) = x)) \<and> (f ` s = t) \<and> continuous_on s f \<and>
  (\<forall>y\<in>t. (f(g y) = y)) \<and> (g ` t = s) \<and> continuous_on t g"

lemma homeomorphismI [intro?]:
  assumes "continuous_on S f" "continuous_on T g"
          "f ` S \<subseteq> T" "g ` T \<subseteq> S" "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x" "\<And>y. y \<in> T \<Longrightarrow> f(g y) = y"
    shows "homeomorphism S T f g"
  using assms by (force simp: homeomorphism_def)

lemma homeomorphism_translation:
  fixes a :: "'a :: real_normed_vector"
  shows "homeomorphism ((+) a ` S) S ((+) (- a)) ((+) a)"
unfolding homeomorphism_def by (auto simp: algebra_simps continuous_intros)

lemma homeomorphism_ident: "homeomorphism T T (\<lambda>a. a) (\<lambda>a. a)"
  by (rule homeomorphismI) (auto simp: continuous_on_id)

lemma homeomorphism_compose:
  assumes "homeomorphism S T f g" "homeomorphism T U h k"
    shows "homeomorphism S U (h o f) (g o k)"
  using assms
  unfolding homeomorphism_def
  by (intro conjI ballI continuous_on_compose) (auto simp: image_comp [symmetric])

lemma homeomorphism_symD: "homeomorphism S t f g \<Longrightarrow> homeomorphism t S g f"
  by (simp add: homeomorphism_def)

lemma homeomorphism_sym: "homeomorphism S t f g = homeomorphism t S g f"
  by (force simp: homeomorphism_def)

definition%important homeomorphic :: "'a::topological_space set \<Rightarrow> 'b::topological_space set \<Rightarrow> bool"
    (infixr "homeomorphic" 60)
  where "s homeomorphic t \<equiv> (\<exists>f g. homeomorphism s t f g)"

lemma homeomorphic_empty [iff]:
     "S homeomorphic {} \<longleftrightarrow> S = {}" "{} homeomorphic S \<longleftrightarrow> S = {}"
  by (auto simp: homeomorphic_def homeomorphism_def)

lemma homeomorphic_refl: "s homeomorphic s"
  unfolding homeomorphic_def homeomorphism_def
  using continuous_on_id
  apply (rule_tac x = "(\<lambda>x. x)" in exI)
  apply (rule_tac x = "(\<lambda>x. x)" in exI)
  apply blast
  done

lemma homeomorphic_sym: "s homeomorphic t \<longleftrightarrow> t homeomorphic s"
  unfolding homeomorphic_def homeomorphism_def
  by blast

lemma homeomorphic_trans [trans]:
  assumes "S homeomorphic T"
      and "T homeomorphic U"
    shows "S homeomorphic U"
  using assms
  unfolding homeomorphic_def
by (metis homeomorphism_compose)

lemma homeomorphic_minimal:
  "s homeomorphic t \<longleftrightarrow>
    (\<exists>f g. (\<forall>x\<in>s. f(x) \<in> t \<and> (g(f(x)) = x)) \<and>
           (\<forall>y\<in>t. g(y) \<in> s \<and> (f(g(y)) = y)) \<and>
           continuous_on s f \<and> continuous_on t g)"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (fastforce simp: homeomorphic_def homeomorphism_def)
next
  assume ?rhs
  then show ?lhs
    apply clarify
    unfolding homeomorphic_def homeomorphism_def
    by (metis equalityI image_subset_iff subsetI)
 qed

lemma homeomorphicI [intro?]:
   "\<lbrakk>f ` S = T; g ` T = S;
     continuous_on S f; continuous_on T g;
     \<And>x. x \<in> S \<Longrightarrow> g(f(x)) = x;
     \<And>y. y \<in> T \<Longrightarrow> f(g(y)) = y\<rbrakk> \<Longrightarrow> S homeomorphic T"
unfolding homeomorphic_def homeomorphism_def by metis

lemma homeomorphism_of_subsets:
   "\<lbrakk>homeomorphism S T f g; S' \<subseteq> S; T'' \<subseteq> T; f ` S' = T'\<rbrakk>
    \<Longrightarrow> homeomorphism S' T' f g"
apply (auto simp: homeomorphism_def elim!: continuous_on_subset)
by (metis subsetD imageI)

lemma homeomorphism_apply1: "\<lbrakk>homeomorphism S T f g; x \<in> S\<rbrakk> \<Longrightarrow> g(f x) = x"
  by (simp add: homeomorphism_def)

lemma homeomorphism_apply2: "\<lbrakk>homeomorphism S T f g; x \<in> T\<rbrakk> \<Longrightarrow> f(g x) = x"
  by (simp add: homeomorphism_def)

lemma homeomorphism_image1: "homeomorphism S T f g \<Longrightarrow> f ` S = T"
  by (simp add: homeomorphism_def)

lemma homeomorphism_image2: "homeomorphism S T f g \<Longrightarrow> g ` T = S"
  by (simp add: homeomorphism_def)

lemma homeomorphism_cont1: "homeomorphism S T f g \<Longrightarrow> continuous_on S f"
  by (simp add: homeomorphism_def)

lemma homeomorphism_cont2: "homeomorphism S T f g \<Longrightarrow> continuous_on T g"
  by (simp add: homeomorphism_def)

lemma continuous_on_no_limpt:
   "(\<And>x. \<not> x islimpt S) \<Longrightarrow> continuous_on S f"
  unfolding continuous_on_def
  by (metis UNIV_I empty_iff eventually_at_topological islimptE open_UNIV tendsto_def trivial_limit_within)

lemma continuous_on_finite:
  fixes S :: "'a::t1_space set"
  shows "finite S \<Longrightarrow> continuous_on S f"
by (metis continuous_on_no_limpt islimpt_finite)

lemma homeomorphic_finite:
  fixes S :: "'a::t1_space set" and T :: "'b::t1_space set"
  assumes "finite T"
  shows "S homeomorphic T \<longleftrightarrow> finite S \<and> finite T \<and> card S = card T" (is "?lhs = ?rhs")
proof
  assume "S homeomorphic T"
  with assms show ?rhs
    apply (auto simp: homeomorphic_def homeomorphism_def)
     apply (metis finite_imageI)
    by (metis card_image_le finite_imageI le_antisym)
next
  assume R: ?rhs
  with finite_same_card_bij obtain h where "bij_betw h S T"
    by auto
  with R show ?lhs
    apply (auto simp: homeomorphic_def homeomorphism_def continuous_on_finite)
    apply (rule_tac x=h in exI)
    apply (rule_tac x="inv_into S h" in exI)
    apply (auto simp:  bij_betw_inv_into_left bij_betw_inv_into_right bij_betw_imp_surj_on inv_into_into bij_betwE)
    apply (metis bij_betw_def bij_betw_inv_into)
    done
qed

text \<open>Relatively weak hypotheses if a set is compact.\<close>

lemma homeomorphism_compact:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes "compact s" "continuous_on s f"  "f ` s = t"  "inj_on f s"
  shows "\<exists>g. homeomorphism s t f g"
proof -
  define g where "g x = (SOME y. y\<in>s \<and> f y = x)" for x
  have g: "\<forall>x\<in>s. g (f x) = x"
    using assms(3) assms(4)[unfolded inj_on_def] unfolding g_def by auto
  {
    fix y
    assume "y \<in> t"
    then obtain x where x:"f x = y" "x\<in>s"
      using assms(3) by auto
    then have "g (f x) = x" using g by auto
    then have "f (g y) = y" unfolding x(1)[symmetric] by auto
  }
  then have g':"\<forall>x\<in>t. f (g x) = x" by auto
  moreover
  {
    fix x
    have "x\<in>s \<Longrightarrow> x \<in> g ` t"
      using g[THEN bspec[where x=x]]
      unfolding image_iff
      using assms(3)
      by (auto intro!: bexI[where x="f x"])
    moreover
    {
      assume "x\<in>g ` t"
      then obtain y where y:"y\<in>t" "g y = x" by auto
      then obtain x' where x':"x'\<in>s" "f x' = y"
        using assms(3) by auto
      then have "x \<in> s"
        unfolding g_def
        using someI2[of "\<lambda>b. b\<in>s \<and> f b = y" x' "\<lambda>x. x\<in>s"]
        unfolding y(2)[symmetric] and g_def
        by auto
    }
    ultimately have "x\<in>s \<longleftrightarrow> x \<in> g ` t" ..
  }
  then have "g ` t = s" by auto
  ultimately show ?thesis
    unfolding homeomorphism_def homeomorphic_def
    apply (rule_tac x=g in exI)
    using g and assms(3) and continuous_on_inv[OF assms(2,1), of g, unfolded assms(3)] and assms(2)
    apply auto
    done
qed

lemma homeomorphic_compact:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  shows "compact s \<Longrightarrow> continuous_on s f \<Longrightarrow> (f ` s = t) \<Longrightarrow> inj_on f s \<Longrightarrow> s homeomorphic t"
  unfolding homeomorphic_def by (metis homeomorphism_compact)

text\<open>Preservation of topological properties.\<close>

lemma homeomorphic_compactness: "s homeomorphic t \<Longrightarrow> (compact s \<longleftrightarrow> compact t)"
  unfolding homeomorphic_def homeomorphism_def
  by (metis compact_continuous_image)

text\<open>Results on translation, scaling etc.\<close>

lemma homeomorphic_scaling:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
  shows "s homeomorphic ((\<lambda>x. c *\<^sub>R x) ` s)"
  unfolding homeomorphic_minimal
  apply (rule_tac x="\<lambda>x. c *\<^sub>R x" in exI)
  apply (rule_tac x="\<lambda>x. (1 / c) *\<^sub>R x" in exI)
  using assms
  apply (auto simp: continuous_intros)
  done

lemma homeomorphic_translation:
  fixes s :: "'a::real_normed_vector set"
  shows "s homeomorphic ((\<lambda>x. a + x) ` s)"
  unfolding homeomorphic_minimal
  apply (rule_tac x="\<lambda>x. a + x" in exI)
  apply (rule_tac x="\<lambda>x. -a + x" in exI)
  using continuous_on_add [OF continuous_on_const continuous_on_id, of s a]
    continuous_on_add [OF continuous_on_const continuous_on_id, of "plus a ` s" "- a"]
  apply auto
  done

lemma homeomorphic_affinity:
  fixes s :: "'a::real_normed_vector set"
  assumes "c \<noteq> 0"
  shows "s homeomorphic ((\<lambda>x. a + c *\<^sub>R x) ` s)"
proof -
  have *: "(+) a ` (*\<^sub>R) c ` s = (\<lambda>x. a + c *\<^sub>R x) ` s" by auto
  show ?thesis
    using homeomorphic_trans
    using homeomorphic_scaling[OF assms, of s]
    using homeomorphic_translation[of "(\<lambda>x. c *\<^sub>R x) ` s" a]
    unfolding *
    by auto
qed

lemma homeomorphic_balls:
  fixes a b ::"'a::real_normed_vector"
  assumes "0 < d"  "0 < e"
  shows "(ball a d) homeomorphic  (ball b e)" (is ?th)
    and "(cball a d) homeomorphic (cball b e)" (is ?cth)
proof -
  show ?th unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    apply (auto intro!: continuous_intros
      simp: dist_commute dist_norm pos_divide_less_eq mult_strict_left_mono)
    done
  show ?cth unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    apply (auto intro!: continuous_intros
      simp: dist_commute dist_norm pos_divide_le_eq mult_strict_left_mono)
    done
qed

lemma homeomorphic_spheres:
  fixes a b ::"'a::real_normed_vector"
  assumes "0 < d"  "0 < e"
  shows "(sphere a d) homeomorphic (sphere b e)"
unfolding homeomorphic_minimal
    apply(rule_tac x="\<lambda>x. b + (e/d) *\<^sub>R (x - a)" in exI)
    apply(rule_tac x="\<lambda>x. a + (d/e) *\<^sub>R (x - b)" in exI)
    using assms
    apply (auto intro!: continuous_intros
      simp: dist_commute dist_norm pos_divide_less_eq mult_strict_left_mono)
    done

lemma homeomorphic_ball01_UNIV:
  "ball (0::'a::real_normed_vector) 1 homeomorphic (UNIV:: 'a set)"
  (is "?B homeomorphic ?U")
proof
  have "x \<in> (\<lambda>z. z /\<^sub>R (1 - norm z)) ` ball 0 1" for x::'a
    apply (rule_tac x="x /\<^sub>R (1 + norm x)" in image_eqI)
     apply (auto simp: divide_simps)
    using norm_ge_zero [of x] apply linarith+
    done
  then show "(\<lambda>z::'a. z /\<^sub>R (1 - norm z)) ` ?B = ?U"
    by blast
  have "x \<in> range (\<lambda>z. (1 / (1 + norm z)) *\<^sub>R z)" if "norm x < 1" for x::'a
    apply (rule_tac x="x /\<^sub>R (1 - norm x)" in image_eqI)
    using that apply (auto simp: divide_simps)
    done
  then show "(\<lambda>z::'a. z /\<^sub>R (1 + norm z)) ` ?U = ?B"
    by (force simp: divide_simps dest: add_less_zeroD)
  show "continuous_on (ball 0 1) (\<lambda>z. z /\<^sub>R (1 - norm z))"
    by (rule continuous_intros | force)+
  show "continuous_on UNIV (\<lambda>z. z /\<^sub>R (1 + norm z))"
    apply (intro continuous_intros)
    apply (metis le_add_same_cancel1 norm_ge_zero not_le zero_less_one)
    done
  show "\<And>x. x \<in> ball 0 1 \<Longrightarrow>
         x /\<^sub>R (1 - norm x) /\<^sub>R (1 + norm (x /\<^sub>R (1 - norm x))) = x"
    by (auto simp: divide_simps)
  show "\<And>y. y /\<^sub>R (1 + norm y) /\<^sub>R (1 - norm (y /\<^sub>R (1 + norm y))) = y"
    apply (auto simp: divide_simps)
    apply (metis le_add_same_cancel1 norm_ge_zero not_le zero_less_one)
    done
qed

proposition homeomorphic_ball_UNIV:
  fixes a ::"'a::real_normed_vector"
  assumes "0 < r" shows "ball a r homeomorphic (UNIV:: 'a set)"
  using assms homeomorphic_ball01_UNIV homeomorphic_balls(1) homeomorphic_trans zero_less_one by blast


text \<open>Connectedness is invariant under homeomorphisms.\<close>

lemma homeomorphic_connectedness:
  assumes "s homeomorphic t"
  shows "connected s \<longleftrightarrow> connected t"
using assms unfolding homeomorphic_def homeomorphism_def by (metis connected_continuous_image)


subsection%unimportant\<open>Inverse function property for open/closed maps\<close>

lemma continuous_on_inverse_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g (f x) = x"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
  shows "continuous_on T g"
proof -
  from imf injf have gTS: "g ` T = S"
    by force
  from imf injf have fU: "U \<subseteq> S \<Longrightarrow> (f ` U) = T \<inter> g -` U" for U
    by force
  show ?thesis
    by (simp add: continuous_on_open [of T g] gTS) (metis openin_imp_subset fU oo)
qed

lemma continuous_on_inverse_closed_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "\<And>x. x \<in> S \<Longrightarrow> g(f x) = x"
    and oo: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
  shows "continuous_on T g"
proof -
  from imf injf have gTS: "g ` T = S"
    by force
  from imf injf have fU: "U \<subseteq> S \<Longrightarrow> (f ` U) = T \<inter> g -` U" for U
    by force
  show ?thesis
    by (simp add: continuous_on_closed [of T g] gTS) (metis closedin_imp_subset fU oo)
qed

lemma homeomorphism_injective_open_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "inj_on f S"
    and oo: "\<And>U. openin (subtopology euclidean S) U \<Longrightarrow> openin (subtopology euclidean T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_open_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_injective_closed_map:
  assumes contf: "continuous_on S f"
    and imf: "f ` S = T"
    and injf: "inj_on f S"
    and oo: "\<And>U. closedin (subtopology euclidean S) U \<Longrightarrow> closedin (subtopology euclidean T) (f ` U)"
  obtains g where "homeomorphism S T f g"
proof
  have "continuous_on T (inv_into S f)"
    by (metis contf continuous_on_inverse_closed_map imf injf inv_into_f_f oo)
  with imf injf contf show "homeomorphism S T f (inv_into S f)"
    by (auto simp: homeomorphism_def)
qed

lemma homeomorphism_imp_open_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "openin (subtopology euclidean S) U"
  shows "openin (subtopology euclidean T) (f ` U)"
proof -
  from hom oo have [simp]: "f ` U = T \<inter> g -` U"
    using openin_subset by (fastforce simp: homeomorphism_def rev_image_eqI)
  from hom have "continuous_on T g"
    unfolding homeomorphism_def by blast
  moreover have "g ` T = S"
    by (metis hom homeomorphism_def)
  ultimately show ?thesis
    by (simp add: continuous_on_open oo)
qed

lemma homeomorphism_imp_closed_map:
  assumes hom: "homeomorphism S T f g"
    and oo: "closedin (subtopology euclidean S) U"
  shows "closedin (subtopology euclidean T) (f ` U)"
proof -
  from hom oo have [simp]: "f ` U = T \<inter> g -` U"
    using closedin_subset by (fastforce simp: homeomorphism_def rev_image_eqI)
  from hom have "continuous_on T g"
    unfolding homeomorphism_def by blast
  moreover have "g ` T = S"
    by (metis hom homeomorphism_def)
  ultimately show ?thesis
    by (simp add: continuous_on_closed oo)
qed


subsection \<open>"Isometry" (up to constant bounds) of injective linear map etc\<close>

lemma cauchy_isometric:
  assumes e: "e > 0"
    and s: "subspace s"
    and f: "bounded_linear f"
    and normf: "\<forall>x\<in>s. norm (f x) \<ge> e * norm x"
    and xs: "\<forall>n. x n \<in> s"
    and cf: "Cauchy (f \<circ> x)"
  shows "Cauchy x"
proof -
  interpret f: bounded_linear f by fact
  have "\<exists>N. \<forall>n\<ge>N. norm (x n - x N) < d" if "d > 0" for d :: real
  proof -
    from that obtain N where N: "\<forall>n\<ge>N. norm (f (x n) - f (x N)) < e * d"
      using cf[unfolded Cauchy_def o_def dist_norm, THEN spec[where x="e*d"]] e
      by auto
    have "norm (x n - x N) < d" if "n \<ge> N" for n
    proof -
      have "e * norm (x n - x N) \<le> norm (f (x n - x N))"
        using subspace_diff[OF s, of "x n" "x N"]
        using xs[THEN spec[where x=N]] and xs[THEN spec[where x=n]]
        using normf[THEN bspec[where x="x n - x N"]]
        by auto
      also have "norm (f (x n - x N)) < e * d"
        using \<open>N \<le> n\<close> N unfolding f.diff[symmetric] by auto
      finally show ?thesis
        using \<open>e>0\<close> by simp
    qed
    then show ?thesis by auto
  qed
  then show ?thesis
    by (simp add: Cauchy_altdef2 dist_norm)
qed

lemma complete_isometric_image:
  assumes "0 < e"
    and s: "subspace s"
    and f: "bounded_linear f"
    and normf: "\<forall>x\<in>s. norm(f x) \<ge> e * norm(x)"
    and cs: "complete s"
  shows "complete (f ` s)"
proof -
  have "\<exists>l\<in>f ` s. (g \<longlongrightarrow> l) sequentially"
    if as:"\<forall>n::nat. g n \<in> f ` s" and cfg:"Cauchy g" for g
  proof -
    from that obtain x where "\<forall>n. x n \<in> s \<and> g n = f (x n)"
      using choice[of "\<lambda> n xa. xa \<in> s \<and> g n = f xa"] by auto
    then have x: "\<forall>n. x n \<in> s" "\<forall>n. g n = f (x n)" by auto
    then have "f \<circ> x = g" by (simp add: fun_eq_iff)
    then obtain l where "l\<in>s" and l:"(x \<longlongrightarrow> l) sequentially"
      using cs[unfolded complete_def, THEN spec[where x=x]]
      using cauchy_isometric[OF \<open>0 < e\<close> s f normf] and cfg and x(1)
      by auto
    then show ?thesis
      using linear_continuous_at[OF f, unfolded continuous_at_sequentially, THEN spec[where x=x], of l]
      by (auto simp: \<open>f \<circ> x = g\<close>)
  qed
  then show ?thesis
    unfolding complete_def by auto
qed

proposition injective_imp_isometric:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes s: "closed s" "subspace s"
    and f: "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0"
  shows "\<exists>e>0. \<forall>x\<in>s. norm (f x) \<ge> e * norm x"
proof (cases "s \<subseteq> {0::'a}")
  case True
  have "norm x \<le> norm (f x)" if "x \<in> s" for x
  proof -
    from True that have "x = 0" by auto
    then show ?thesis by simp
  qed
  then show ?thesis
    by (auto intro!: exI[where x=1])
next
  case False
  interpret f: bounded_linear f by fact
  from False obtain a where a: "a \<noteq> 0" "a \<in> s"
    by auto
  from False have "s \<noteq> {}"
    by auto
  let ?S = "{f x| x. x \<in> s \<and> norm x = norm a}"
  let ?S' = "{x::'a. x\<in>s \<and> norm x = norm a}"
  let ?S'' = "{x::'a. norm x = norm a}"

  have "?S'' = frontier (cball 0 (norm a))"
    by (simp add: sphere_def dist_norm)
  then have "compact ?S''" by (metis compact_cball compact_frontier)
  moreover have "?S' = s \<inter> ?S''" by auto
  ultimately have "compact ?S'"
    using closed_Int_compact[of s ?S''] using s(1) by auto
  moreover have *:"f ` ?S' = ?S" by auto
  ultimately have "compact ?S"
    using compact_continuous_image[OF linear_continuous_on[OF f(1)], of ?S'] by auto
  then have "closed ?S"
    using compact_imp_closed by auto
  moreover from a have "?S \<noteq> {}" by auto
  ultimately obtain b' where "b'\<in>?S" "\<forall>y\<in>?S. norm b' \<le> norm y"
    using distance_attains_inf[of ?S 0] unfolding dist_0_norm by auto
  then obtain b where "b\<in>s"
    and ba: "norm b = norm a"
    and b: "\<forall>x\<in>{x \<in> s. norm x = norm a}. norm (f b) \<le> norm (f x)"
    unfolding *[symmetric] unfolding image_iff by auto

  let ?e = "norm (f b) / norm b"
  have "norm b > 0"
    using ba and a and norm_ge_zero by auto
  moreover have "norm (f b) > 0"
    using f(2)[THEN bspec[where x=b], OF \<open>b\<in>s\<close>]
    using \<open>norm b >0\<close> by simp
  ultimately have "0 < norm (f b) / norm b" by simp
  moreover
  have "norm (f b) / norm b * norm x \<le> norm (f x)" if "x\<in>s" for x
  proof (cases "x = 0")
    case True
    then show "norm (f b) / norm b * norm x \<le> norm (f x)"
      by auto
  next
    case False
    with \<open>a \<noteq> 0\<close> have *: "0 < norm a / norm x"
      unfolding zero_less_norm_iff[symmetric] by simp
    have "\<forall>x\<in>s. c *\<^sub>R x \<in> s" for c
      using s[unfolded subspace_def] by simp
    with \<open>x \<in> s\<close> \<open>x \<noteq> 0\<close> have "(norm a / norm x) *\<^sub>R x \<in> {x \<in> s. norm x = norm a}"
      by simp
    with \<open>x \<noteq> 0\<close> \<open>a \<noteq> 0\<close> show "norm (f b) / norm b * norm x \<le> norm (f x)"
      using b[THEN bspec[where x="(norm a / norm x) *\<^sub>R x"]]
      unfolding f.scaleR and ba
      by (auto simp: mult.commute pos_le_divide_eq pos_divide_le_eq)
  qed
  ultimately show ?thesis by auto
qed

proposition closed_injective_image_subspace:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "subspace s" "bounded_linear f" "\<forall>x\<in>s. f x = 0 \<longrightarrow> x = 0" "closed s"
  shows "closed(f ` s)"
proof -
  obtain e where "e > 0" and e: "\<forall>x\<in>s. e * norm x \<le> norm (f x)"
    using injective_imp_isometric[OF assms(4,1,2,3)] by auto
  show ?thesis
    using complete_isometric_image[OF \<open>e>0\<close> assms(1,2) e] and assms(4)
    unfolding complete_eq_closed[symmetric] by auto
qed


subsection%unimportant \<open>Some properties of a canonical subspace\<close>

lemma subspace_substandard: "subspace {x::'a::euclidean_space. (\<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0)}"
  by (auto simp: subspace_def inner_add_left)

lemma closed_substandard: "closed {x::'a::euclidean_space. \<forall>i\<in>Basis. P i \<longrightarrow> x\<bullet>i = 0}"
  (is "closed ?A")
proof -
  let ?D = "{i\<in>Basis. P i}"
  have "closed (\<Inter>i\<in>?D. {x::'a. x\<bullet>i = 0})"
    by (simp add: closed_INT closed_Collect_eq continuous_on_inner
        continuous_on_const continuous_on_id)
  also have "(\<Inter>i\<in>?D. {x::'a. x\<bullet>i = 0}) = ?A"
    by auto
  finally show "closed ?A" .
qed

lemma dim_substandard:
  assumes d: "d \<subseteq> Basis"
  shows "dim {x::'a::euclidean_space. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0} = card d" (is "dim ?A = _")
proof (rule dim_unique)
  from d show "d \<subseteq> ?A"
    by (auto simp: inner_Basis)
  from d show "independent d"
    by (rule independent_mono [OF independent_Basis])
  have "x \<in> span d" if "\<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0" for x
  proof -
    have "finite d"
      by (rule finite_subset [OF d finite_Basis])
    then have "(\<Sum>i\<in>d. (x \<bullet> i) *\<^sub>R i) \<in> span d"
      by (simp add: span_sum span_clauses)
    also have "(\<Sum>i\<in>d. (x \<bullet> i) *\<^sub>R i) = (\<Sum>i\<in>Basis. (x \<bullet> i) *\<^sub>R i)"
      by (rule sum.mono_neutral_cong_left [OF finite_Basis d]) (auto simp: that)
    finally show "x \<in> span d"
      by (simp only: euclidean_representation)
  qed
  then show "?A \<subseteq> span d" by auto
qed simp

text \<open>Hence closure and completeness of all subspaces.\<close>
lemma ex_card:
  assumes "n \<le> card A"
  shows "\<exists>S\<subseteq>A. card S = n"
proof (cases "finite A")
  case True
  from ex_bij_betw_nat_finite[OF this] obtain f where f: "bij_betw f {0..<card A} A" ..
  moreover from f \<open>n \<le> card A\<close> have "{..< n} \<subseteq> {..< card A}" "inj_on f {..< n}"
    by (auto simp: bij_betw_def intro: subset_inj_on)
  ultimately have "f ` {..< n} \<subseteq> A" "card (f ` {..< n}) = n"
    by (auto simp: bij_betw_def card_image)
  then show ?thesis by blast
next
  case False
  with \<open>n \<le> card A\<close> show ?thesis by force
qed

lemma closed_subspace:
  fixes s :: "'a::euclidean_space set"
  assumes "subspace s"
  shows "closed s"
proof -
  have "dim s \<le> card (Basis :: 'a set)"
    using dim_subset_UNIV by auto
  with ex_card[OF this] obtain d :: "'a set" where t: "card d = dim s" and d: "d \<subseteq> Basis"
    by auto
  let ?t = "{x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x\<bullet>i = 0}"
  have "\<exists>f. linear f \<and> f ` {x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} = s \<and>
      inj_on f {x::'a. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
    using dim_substandard[of d] t d assms
    by (intro subspace_isomorphism[OF subspace_substandard[of "\<lambda>i. i \<notin> d"]]) (auto simp: inner_Basis)
  then obtain f where f:
      "linear f"
      "f ` {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0} = s"
      "inj_on f {x. \<forall>i\<in>Basis. i \<notin> d \<longrightarrow> x \<bullet> i = 0}"
    by blast
  interpret f: bounded_linear f
    using f by (simp add: linear_conv_bounded_linear)
  have "x \<in> ?t \<Longrightarrow> f x = 0 \<Longrightarrow> x = 0" for x
    using f.zero d f(3)[THEN inj_onD, of x 0] by auto
  moreover have "closed ?t" by (rule closed_substandard)
  moreover have "subspace ?t" by (rule subspace_substandard)
  ultimately show ?thesis
    using closed_injective_image_subspace[of ?t f]
    unfolding f(2) using f(1) unfolding linear_conv_bounded_linear by auto
qed

lemma complete_subspace: "subspace s \<Longrightarrow> complete s"
  for s :: "'a::euclidean_space set"
  using complete_eq_closed closed_subspace by auto

lemma closed_span [iff]: "closed (span s)"
  for s :: "'a::euclidean_space set"
  by (simp add: closed_subspace subspace_span)

lemma dim_closure [simp]: "dim (closure s) = dim s" (is "?dc = ?d")
  for s :: "'a::euclidean_space set"
proof -
  have "?dc \<le> ?d"
    using closure_minimal[OF span_superset, of s]
    using closed_subspace[OF subspace_span, of s]
    using dim_subset[of "closure s" "span s"]
    by simp
  then show ?thesis
    using dim_subset[OF closure_subset, of s]
    by simp
qed


subsection%unimportant \<open>Affine transformations of intervals\<close>

lemma real_affinity_le: "0 < m \<Longrightarrow> m * x + c \<le> y \<longleftrightarrow> x \<le> inverse m * y + - (c / m)"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_le_affinity: "0 < m \<Longrightarrow> y \<le> m * x + c \<longleftrightarrow> inverse m * y + - (c / m) \<le> x"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_affinity_lt: "0 < m \<Longrightarrow> m * x + c < y \<longleftrightarrow> x < inverse m * y + - (c / m)"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_lt_affinity: "0 < m \<Longrightarrow> y < m * x + c \<longleftrightarrow> inverse m * y + - (c / m) < x"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_affinity_eq: "m \<noteq> 0 \<Longrightarrow> m * x + c = y \<longleftrightarrow> x = inverse m * y + - (c / m)"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)

lemma real_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m * x + c  \<longleftrightarrow> inverse m * y + - (c / m) = x"
  for m :: "'a::linordered_field"
  by (simp add: field_simps)


subsection \<open>Banach fixed point theorem (not really topological ...)\<close>

theorem banach_fix:
  assumes s: "complete s" "s \<noteq> {}"
    and c: "0 \<le> c" "c < 1"
    and f: "f ` s \<subseteq> s"
    and lipschitz: "\<forall>x\<in>s. \<forall>y\<in>s. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x\<in>s. f x = x"
proof -
  from c have "1 - c > 0" by simp

  from s(2) obtain z0 where z0: "z0 \<in> s" by blast
  define z where "z n = (f ^^ n) z0" for n
  with f z0 have z_in_s: "z n \<in> s" for n :: nat
    by (induct n) auto
  define d where "d = dist (z 0) (z 1)"

  have fzn: "f (z n) = z (Suc n)" for n
    by (simp add: z_def)
  have cf_z: "dist (z n) (z (Suc n)) \<le> (c ^ n) * d" for n :: nat
  proof (induct n)
    case 0
    then show ?case
      by (simp add: d_def)
  next
    case (Suc m)
    with \<open>0 \<le> c\<close> have "c * dist (z m) (z (Suc m)) \<le> c ^ Suc m * d"
      using mult_left_mono[of "dist (z m) (z (Suc m))" "c ^ m * d" c] by simp
    then show ?case
      using lipschitz[THEN bspec[where x="z m"], OF z_in_s, THEN bspec[where x="z (Suc m)"], OF z_in_s]
      by (simp add: fzn mult_le_cancel_left)
  qed

  have cf_z2: "(1 - c) * dist (z m) (z (m + n)) \<le> (c ^ m) * d * (1 - c ^ n)" for n m :: nat
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc k)
    from c have "(1 - c) * dist (z m) (z (m + Suc k)) \<le>
        (1 - c) * (dist (z m) (z (m + k)) + dist (z (m + k)) (z (Suc (m + k))))"
      by (simp add: dist_triangle)
    also from c cf_z[of "m + k"] have "\<dots> \<le> (1 - c) * (dist (z m) (z (m + k)) + c ^ (m + k) * d)"
      by simp
    also from Suc have "\<dots> \<le> c ^ m * d * (1 - c ^ k) + (1 - c) * c ^ (m + k) * d"
      by (simp add: field_simps)
    also have "\<dots> = (c ^ m) * (d * (1 - c ^ k) + (1 - c) * c ^ k * d)"
      by (simp add: power_add field_simps)
    also from c have "\<dots> \<le> (c ^ m) * d * (1 - c ^ Suc k)"
      by (simp add: field_simps)
    finally show ?case by simp
  qed

  have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (z m) (z n) < e" if "e > 0" for e
  proof (cases "d = 0")
    case True
    from \<open>1 - c > 0\<close> have "(1 - c) * x \<le> 0 \<longleftrightarrow> x \<le> 0" for x
      by (metis mult_zero_left mult.commute real_mult_le_cancel_iff1)
    with c cf_z2[of 0] True have "z n = z0" for n
      by (simp add: z_def)
    with \<open>e > 0\<close> show ?thesis by simp
  next
    case False
    with zero_le_dist[of "z 0" "z 1"] have "d > 0"
      by (metis d_def less_le)
    with \<open>1 - c > 0\<close> \<open>e > 0\<close> have "0 < e * (1 - c) / d"
      by simp
    with c obtain N where N: "c ^ N < e * (1 - c) / d"
      using real_arch_pow_inv[of "e * (1 - c) / d" c] by auto
    have *: "dist (z m) (z n) < e" if "m > n" and as: "m \<ge> N" "n \<ge> N" for m n :: nat
    proof -
      from c \<open>n \<ge> N\<close> have *: "c ^ n \<le> c ^ N"
        using power_decreasing[OF \<open>n\<ge>N\<close>, of c] by simp
      from c \<open>m > n\<close> have "1 - c ^ (m - n) > 0"
        using power_strict_mono[of c 1 "m - n"] by simp
      with \<open>d > 0\<close> \<open>0 < 1 - c\<close> have **: "d * (1 - c ^ (m - n)) / (1 - c) > 0"
        by simp
      from cf_z2[of n "m - n"] \<open>m > n\<close>
      have "dist (z m) (z n) \<le> c ^ n * d * (1 - c ^ (m - n)) / (1 - c)"
        by (simp add: pos_le_divide_eq[OF \<open>1 - c > 0\<close>] mult.commute dist_commute)
      also have "\<dots> \<le> c ^ N * d * (1 - c ^ (m - n)) / (1 - c)"
        using mult_right_mono[OF * order_less_imp_le[OF **]]
        by (simp add: mult.assoc)
      also have "\<dots> < (e * (1 - c) / d) * d * (1 - c ^ (m - n)) / (1 - c)"
        using mult_strict_right_mono[OF N **] by (auto simp: mult.assoc)
      also from c \<open>d > 0\<close> \<open>1 - c > 0\<close> have "\<dots> = e * (1 - c ^ (m - n))"
        by simp
      also from c \<open>1 - c ^ (m - n) > 0\<close> \<open>e > 0\<close> have "\<dots> \<le> e"
        using mult_right_le_one_le[of e "1 - c ^ (m - n)"] by auto
      finally show ?thesis by simp
    qed
    have "dist (z n) (z m) < e" if "N \<le> m" "N \<le> n" for m n :: nat
    proof (cases "n = m")
      case True
      with \<open>e > 0\<close> show ?thesis by simp
    next
      case False
      with *[of n m] *[of m n] and that show ?thesis
        by (auto simp: dist_commute nat_neq_iff)
    qed
    then show ?thesis by auto
  qed
  then have "Cauchy z"
    by (simp add: cauchy_def)
  then obtain x where "x\<in>s" and x:"(z \<longlongrightarrow> x) sequentially"
    using s(1)[unfolded compact_def complete_def, THEN spec[where x=z]] and z_in_s by auto

  define e where "e = dist (f x) x"
  have "e = 0"
  proof (rule ccontr)
    assume "e \<noteq> 0"
    then have "e > 0"
      unfolding e_def using zero_le_dist[of "f x" x]
      by (metis dist_eq_0_iff dist_nz e_def)
    then obtain N where N:"\<forall>n\<ge>N. dist (z n) x < e / 2"
      using x[unfolded lim_sequentially, THEN spec[where x="e/2"]] by auto
    then have N':"dist (z N) x < e / 2" by auto
    have *: "c * dist (z N) x \<le> dist (z N) x"
      unfolding mult_le_cancel_right2
      using zero_le_dist[of "z N" x] and c
      by (metis dist_eq_0_iff dist_nz order_less_asym less_le)
    have "dist (f (z N)) (f x) \<le> c * dist (z N) x"
      using lipschitz[THEN bspec[where x="z N"], THEN bspec[where x=x]]
      using z_in_s[of N] \<open>x\<in>s\<close>
      using c
      by auto
    also have "\<dots> < e / 2"
      using N' and c using * by auto
    finally show False
      unfolding fzn
      using N[THEN spec[where x="Suc N"]] and dist_triangle_half_r[of "z (Suc N)" "f x" e x]
      unfolding e_def
      by auto
  qed
  then have "f x = x" by (auto simp: e_def)
  moreover have "y = x" if "f y = y" "y \<in> s" for y
  proof -
    from \<open>x \<in> s\<close> \<open>f x = x\<close> that have "dist x y \<le> c * dist x y"
      using lipschitz[THEN bspec[where x=x], THEN bspec[where x=y]] by simp
    with c and zero_le_dist[of x y] have "dist x y = 0"
      by (simp add: mult_le_cancel_right1)
    then show ?thesis by simp
  qed
  ultimately show ?thesis
    using \<open>x\<in>s\<close> by blast
qed

lemma banach_fix_type:
  fixes f::"'a::complete_space\<Rightarrow>'a"
  assumes c:"0 \<le> c" "c < 1"
      and lipschitz:"\<forall>x. \<forall>y. dist (f x) (f y) \<le> c * dist x y"
  shows "\<exists>!x. (f x = x)"
  using assms banach_fix[OF complete_UNIV UNIV_not_empty assms(1,2) subset_UNIV, of f]
  by auto


subsection \<open>Edelstein fixed point theorem\<close>

theorem edelstein_fix:
  fixes s :: "'a::metric_space set"
  assumes s: "compact s" "s \<noteq> {}"
    and gs: "(g ` s) \<subseteq> s"
    and dist: "\<forall>x\<in>s. \<forall>y\<in>s. x \<noteq> y \<longrightarrow> dist (g x) (g y) < dist x y"
  shows "\<exists>!x\<in>s. g x = x"
proof -
  let ?D = "(\<lambda>x. (x, x)) ` s"
  have D: "compact ?D" "?D \<noteq> {}"
    by (rule compact_continuous_image)
       (auto intro!: s continuous_Pair continuous_ident simp: continuous_on_eq_continuous_within)

  have "\<And>x y e. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> 0 < e \<Longrightarrow> dist y x < e \<Longrightarrow> dist (g y) (g x) < e"
    using dist by fastforce
  then have "continuous_on s g"
    by (auto simp: continuous_on_iff)
  then have cont: "continuous_on ?D (\<lambda>x. dist ((g \<circ> fst) x) (snd x))"
    unfolding continuous_on_eq_continuous_within
    by (intro continuous_dist ballI continuous_within_compose)
       (auto intro!: continuous_fst continuous_snd continuous_ident simp: image_image)

  obtain a where "a \<in> s" and le: "\<And>x. x \<in> s \<Longrightarrow> dist (g a) a \<le> dist (g x) x"
    using continuous_attains_inf[OF D cont] by auto

  have "g a = a"
  proof (rule ccontr)
    assume "g a \<noteq> a"
    with \<open>a \<in> s\<close> gs have "dist (g (g a)) (g a) < dist (g a) a"
      by (intro dist[rule_format]) auto
    moreover have "dist (g a) a \<le> dist (g (g a)) (g a)"
      using \<open>a \<in> s\<close> gs by (intro le) auto
    ultimately show False by auto
  qed
  moreover have "\<And>x. x \<in> s \<Longrightarrow> g x = x \<Longrightarrow> x = a"
    using dist[THEN bspec[where x=a]] \<open>g a = a\<close> and \<open>a\<in>s\<close> by auto
  ultimately show "\<exists>!x\<in>s. g x = x"
    using \<open>a \<in> s\<close> by blast
qed


lemma cball_subset_cball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "cball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r < 0"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "r < 0")
    case True
    then show ?rhs by simp
  next
    case False
    then have [simp]: "r \<ge> 0" by simp
    have "norm (a - a') + r \<le> r'"
    proof (cases "a = a'")
      case True
      then show ?thesis
        using subsetD [where c = "a + r *\<^sub>R (SOME i. i \<in> Basis)", OF \<open>?lhs\<close>] subsetD [where c = a, OF \<open>?lhs\<close>]
        by (force simp: SOME_Basis dist_norm)
    next
      case False
      have "norm (a' - (a + (r / norm (a - a')) *\<^sub>R (a - a'))) = norm (a' - a - (r / norm (a - a')) *\<^sub>R (a - a'))"
        by (simp add: algebra_simps)
      also have "... = norm ((-1 - (r / norm (a - a'))) *\<^sub>R (a - a'))"
        by (simp add: algebra_simps)
      also from \<open>a \<noteq> a'\<close> have "... = \<bar>- norm (a - a') - r\<bar>"
        by (simp add: abs_mult_pos field_simps)
      finally have [simp]: "norm (a' - (a + (r / norm (a - a')) *\<^sub>R (a - a'))) = \<bar>norm (a - a') + r\<bar>"
        by linarith
      from \<open>a \<noteq> a'\<close> show ?thesis
        using subsetD [where c = "a' + (1 + r / norm(a - a')) *\<^sub>R (a - a')", OF \<open>?lhs\<close>]
        by (simp add: dist_norm scaleR_add_left)
    qed
    then show ?rhs
      by (simp add: dist_norm)
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp: ball_def dist_norm)
      (metis add.commute add_le_cancel_right dist_norm dist_triangle3 order_trans)
qed

lemma cball_subset_ball_iff: "cball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r < r' \<or> r < 0"
  (is "?lhs \<longleftrightarrow> ?rhs")
  for a :: "'a::euclidean_space"
proof
  assume ?lhs
  then show ?rhs
  proof (cases "r < 0")
    case True then
    show ?rhs by simp
  next
    case False
    then have [simp]: "r \<ge> 0" by simp
    have "norm (a - a') + r < r'"
    proof (cases "a = a'")
      case True
      then show ?thesis
        using subsetD [where c = "a + r *\<^sub>R (SOME i. i \<in> Basis)", OF \<open>?lhs\<close>] subsetD [where c = a, OF \<open>?lhs\<close>]
        by (force simp: SOME_Basis dist_norm)
    next
      case False
      have False if "norm (a - a') + r \<ge> r'"
      proof -
        from that have "\<bar>r' - norm (a - a')\<bar> \<le> r"
          by (simp split: abs_split)
            (metis \<open>0 \<le> r\<close> \<open>?lhs\<close> centre_in_cball dist_commute dist_norm less_asym mem_ball subset_eq)
        then show ?thesis
          using subsetD [where c = "a + (r' / norm(a - a') - 1) *\<^sub>R (a - a')", OF \<open>?lhs\<close>] \<open>a \<noteq> a'\<close>
          by (simp add: dist_norm field_simps)
            (simp add: diff_divide_distrib scaleR_left_diff_distrib)
      qed
      then show ?thesis by force
    qed
    then show ?rhs by (simp add: dist_norm)
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp: ball_def dist_norm)
      (metis add.commute add_le_cancel_right dist_norm dist_triangle3 le_less_trans)
qed

lemma ball_subset_cball_iff: "ball a r \<subseteq> cball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
  (is "?lhs = ?rhs")
  for a :: "'a::euclidean_space"
proof (cases "r \<le> 0")
  case True
  then show ?thesis
    using dist_not_less_zero less_le_trans by force
next
  case False
  show ?thesis
  proof
    assume ?lhs
    then have "(cball a r \<subseteq> cball a' r')"
      by (metis False closed_cball closure_ball closure_closed closure_mono not_less)
    with False show ?rhs
      by (fastforce iff: cball_subset_cball_iff)
  next
    assume ?rhs
    with False show ?lhs
      using ball_subset_cball cball_subset_cball_iff by blast
  qed
qed

lemma ball_subset_ball_iff:
  fixes a :: "'a :: euclidean_space"
  shows "ball a r \<subseteq> ball a' r' \<longleftrightarrow> dist a a' + r \<le> r' \<or> r \<le> 0"
        (is "?lhs = ?rhs")
proof (cases "r \<le> 0")
  case True then show ?thesis
    using dist_not_less_zero less_le_trans by force
next
  case False show ?thesis
  proof
    assume ?lhs
    then have "0 < r'"
      by (metis (no_types) False \<open>?lhs\<close> centre_in_ball dist_norm le_less_trans mem_ball norm_ge_zero not_less set_mp)
    then have "(cball a r \<subseteq> cball a' r')"
      by (metis False\<open>?lhs\<close> closure_ball closure_mono not_less)
    then show ?rhs
      using False cball_subset_cball_iff by fastforce
  next
  assume ?rhs then show ?lhs
    apply (auto simp: ball_def)
    apply (metis add.commute add_le_cancel_right dist_commute dist_triangle_lt not_le order_trans)
    using dist_not_less_zero order.strict_trans2 apply blast
    done
  qed
qed


lemma ball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = ball y e \<longleftrightarrow> d \<le> 0 \<and> e \<le> 0 \<or> x=y \<and> d=e"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "d \<le> 0 \<or> e \<le> 0")
    case True
      with \<open>?lhs\<close> show ?rhs
        by safe (simp_all only: ball_eq_empty [of y e, symmetric] ball_eq_empty [of x d, symmetric])
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      apply (auto simp: set_eq_subset ball_subset_ball_iff dist_norm norm_minus_commute algebra_simps)
      apply (metis add_le_same_cancel1 le_add_same_cancel1 norm_ge_zero norm_pths(2) order_trans)
      apply (metis add_increasing2 add_le_imp_le_right eq_iff norm_ge_zero)
      done
  qed
next
  assume ?rhs then show ?lhs
    by (auto simp: set_eq_subset ball_subset_ball_iff)
qed

lemma cball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = cball y e \<longleftrightarrow> d < 0 \<and> e < 0 \<or> x=y \<and> d=e"
        (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
  proof (cases "d < 0 \<or> e < 0")
    case True
      with \<open>?lhs\<close> show ?rhs
        by safe (simp_all only: cball_eq_empty [of y e, symmetric] cball_eq_empty [of x d, symmetric])
  next
    case False
    with \<open>?lhs\<close> show ?rhs
      apply (auto simp: set_eq_subset cball_subset_cball_iff dist_norm norm_minus_commute algebra_simps)
      apply (metis add_le_same_cancel1 le_add_same_cancel1 norm_ge_zero norm_pths(2) order_trans)
      apply (metis add_increasing2 add_le_imp_le_right eq_iff norm_ge_zero)
      done
  qed
next
  assume ?rhs then show ?lhs
    by (auto simp: set_eq_subset cball_subset_cball_iff)
qed

lemma ball_eq_cball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "ball x d = cball y e \<longleftrightarrow> d \<le> 0 \<and> e < 0" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    apply (auto simp: set_eq_subset ball_subset_cball_iff cball_subset_ball_iff algebra_simps)
    apply (metis add_increasing2 add_le_cancel_right add_less_same_cancel1 dist_not_less_zero less_le_trans zero_le_dist)
    apply (metis add_less_same_cancel1 dist_not_less_zero less_le_trans not_le)
    using \<open>?lhs\<close> ball_eq_empty cball_eq_empty apply blast+
    done
next
  assume ?rhs then show ?lhs by auto
qed

lemma cball_eq_ball_iff:
  fixes x :: "'a :: euclidean_space"
  shows "cball x d = ball y e \<longleftrightarrow> d < 0 \<and> e \<le> 0"
  using ball_eq_cball_iff by blast

lemma finite_ball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>ball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
proof -
  obtain e1 where "0 < e1" and e1_b:"ball p e1 \<subseteq> S"
    using open_contains_ball_eq[OF \<open>open S\<close>] assms by auto
  obtain e2 where "0 < e2" and "\<forall>x\<in>X. x \<noteq> p \<longrightarrow> e2 \<le> dist p x"
    using finite_set_avoid[OF \<open>finite X\<close>,of p] by auto
  hence "\<forall>w\<in>ball p (min e1 e2). w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)" using e1_b by auto
  thus "\<exists>e>0. \<forall>w\<in>ball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> X)" using \<open>e2>0\<close> \<open>e1>0\<close>
    apply (rule_tac x="min e1 e2" in exI)
    by auto
qed

lemma finite_cball_avoid:
  fixes S :: "'a :: euclidean_space set"
  assumes "open S" "finite X" "p \<in> S"
  shows "\<exists>e>0. \<forall>w\<in>cball p e. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
proof -
  obtain e1 where "e1>0" and e1: "\<forall>w\<in>ball p e1. w\<in>S \<and> (w\<noteq>p \<longrightarrow> w\<notin>X)"
    using finite_ball_avoid[OF assms] by auto
  define e2 where "e2 \<equiv> e1/2"
  have "e2>0" and "e2 < e1" unfolding e2_def using \<open>e1>0\<close> by auto
  then have "cball p e2 \<subseteq> ball p e1" by (subst cball_subset_ball_iff,auto)
  then show "\<exists>e>0. \<forall>w\<in>cball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> X)" using \<open>e2>0\<close> e1 by auto
qed

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

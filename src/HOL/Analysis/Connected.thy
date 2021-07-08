(*  Author:     L C Paulson, University of Cambridge
    Material split off from Topology_Euclidean_Space
*)

section \<open>Connected Components\<close>

theory Connected
  imports
    Abstract_Topology_2
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Connectedness\<close>

lemma connected_local:
 "connected S \<longleftrightarrow>
  \<not> (\<exists>e1 e2.
      openin (top_of_set S) e1 \<and>
      openin (top_of_set S) e2 \<and>
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
  (\<forall>T. openin (top_of_set S) T \<and>
     closedin (top_of_set S) T \<longrightarrow> T = {} \<or> T = S)" (is "?lhs \<longleftrightarrow> ?rhs")
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

subsection \<open>Connected components, considered as a connectedness relation or a set\<close>

definition\<^marker>\<open>tag important\<close> "connected_component S x y \<equiv> \<exists>T. connected T \<and> T \<subseteq> S \<and> x \<in> T \<and> y \<in> T"

abbreviation "connected_component_set S x \<equiv> Collect (connected_component S x)"

lemma connected_componentI:
  "connected T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> x \<in> T \<Longrightarrow> y \<in> T \<Longrightarrow> connected_component S x y"
  by (auto simp: connected_component_def)

lemma connected_component_in: "connected_component S x y \<Longrightarrow> x \<in> S \<and> y \<in> S"
  by (auto simp: connected_component_def)

lemma connected_component_refl: "x \<in> S \<Longrightarrow> connected_component S x x"
  by (auto simp: connected_component_def) (use connected_sing in blast)

lemma connected_component_refl_eq [simp]: "connected_component S x x \<longleftrightarrow> x \<in> S"
  by (auto simp: connected_component_refl) (auto simp: connected_component_def)

lemma connected_component_sym: "connected_component S x y \<Longrightarrow> connected_component S y x"
  by (auto simp: connected_component_def)

lemma connected_component_trans:
  "connected_component S x y \<Longrightarrow> connected_component S y z \<Longrightarrow> connected_component S x z"
  unfolding connected_component_def
  by (metis Int_iff Un_iff Un_subset_iff equals0D connected_Un)

lemma connected_component_of_subset:
  "connected_component S x y \<Longrightarrow> S \<subseteq> T \<Longrightarrow> connected_component T x y"
  by (auto simp: connected_component_def)

lemma connected_component_Union: "connected_component_set S x = \<Union>{T. connected T \<and> x \<in> T \<and> T \<subseteq> S}"
  by (auto simp: connected_component_def)

lemma connected_connected_component [iff]: "connected (connected_component_set S x)"
  by (auto simp: connected_component_Union intro: connected_Union)

lemma connected_iff_eq_connected_component_set:
  "connected S \<longleftrightarrow> (\<forall>x \<in> S. connected_component_set S x = S)"
proof (cases "S = {}")
  case True
  then show ?thesis by simp
next
  case False
  then obtain x where "x \<in> S" by auto
  show ?thesis
  proof
    assume "connected S"
    then show "\<forall>x \<in> S. connected_component_set S x = S"
      by (force simp: connected_component_def)
  next
    assume "\<forall>x \<in> S. connected_component_set S x = S"
    then show "connected S"
      by (metis \<open>x \<in> S\<close> connected_connected_component)
  qed
qed

lemma connected_component_subset: "connected_component_set S x \<subseteq> S"
  using connected_component_in by blast

lemma connected_component_eq_self: "connected S \<Longrightarrow> x \<in> S \<Longrightarrow> connected_component_set S x = S"
  by (simp add: connected_iff_eq_connected_component_set)

lemma connected_iff_connected_component:
  "connected S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. connected_component S x y)"
  using connected_component_in by (auto simp: connected_iff_eq_connected_component_set)

lemma connected_component_maximal:
  "x \<in> T \<Longrightarrow> connected T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> T \<subseteq> (connected_component_set S x)"
  using connected_component_eq_self connected_component_of_subset by blast

lemma connected_component_mono:
  "S \<subseteq> T \<Longrightarrow> connected_component_set S x \<subseteq> connected_component_set T x"
  by (simp add: Collect_mono connected_component_of_subset)

lemma connected_component_eq_empty [simp]: "connected_component_set S x = {} \<longleftrightarrow> x \<notin> S"
  using connected_component_refl by (fastforce simp: connected_component_in)

lemma connected_component_set_empty [simp]: "connected_component_set {} x = {}"
  using connected_component_eq_empty by blast

lemma connected_component_eq:
  "y \<in> connected_component_set S x \<Longrightarrow> (connected_component_set S y = connected_component_set S x)"
  by (metis (no_types, lifting)
      Collect_cong connected_component_sym connected_component_trans mem_Collect_eq)

lemma closed_connected_component:
  assumes S: "closed S"
  shows "closed (connected_component_set S x)"
proof (cases "x \<in> S")
  case False
  then show ?thesis
    by (metis connected_component_eq_empty closed_empty)
next
  case True
  show ?thesis
    unfolding closure_eq [symmetric]
  proof
    show "closure (connected_component_set S x) \<subseteq> connected_component_set S x"
      apply (rule connected_component_maximal)
        apply (simp add: closure_def True)
       apply (simp add: connected_imp_connected_closure)
      apply (simp add: S closure_minimal connected_component_subset)
      done
  next
    show "connected_component_set S x \<subseteq> closure (connected_component_set S x)"
      by (simp add: closure_subset)
  qed
qed

lemma connected_component_disjoint:
  "connected_component_set S a \<inter> connected_component_set S b = {} \<longleftrightarrow>
    a \<notin> connected_component_set S b"
  apply (auto simp: connected_component_eq)
  using connected_component_eq connected_component_sym
  apply blast
  done

lemma connected_component_nonoverlap:
  "connected_component_set S a \<inter> connected_component_set S b = {} \<longleftrightarrow>
    a \<notin> S \<or> b \<notin> S \<or> connected_component_set S a \<noteq> connected_component_set S b"
  apply (auto simp: connected_component_in)
  using connected_component_refl_eq
    apply blast
   apply (metis connected_component_eq mem_Collect_eq)
  apply (metis connected_component_eq mem_Collect_eq)
  done

lemma connected_component_overlap:
  "connected_component_set S a \<inter> connected_component_set S b \<noteq> {} \<longleftrightarrow>
    a \<in> S \<and> b \<in> S \<and> connected_component_set S a = connected_component_set S b"
  by (auto simp: connected_component_nonoverlap)

lemma connected_component_sym_eq: "connected_component S x y \<longleftrightarrow> connected_component S y x"
  using connected_component_sym by blast

lemma connected_component_eq_eq:
  "connected_component_set S x = connected_component_set S y \<longleftrightarrow>
    x \<notin> S \<and> y \<notin> S \<or> x \<in> S \<and> y \<in> S \<and> connected_component S x y"
  apply (cases "y \<in> S", simp)
   apply (metis connected_component_eq connected_component_eq_empty connected_component_refl_eq mem_Collect_eq)
  apply (cases "x \<in> S", simp)
   apply (metis connected_component_eq_empty)
  using connected_component_eq_empty
  apply blast
  done

lemma connected_iff_connected_component_eq:
  "connected S \<longleftrightarrow> (\<forall>x \<in> S. \<forall>y \<in> S. connected_component_set S x = connected_component_set S y)"
  by (simp add: connected_component_eq_eq connected_iff_connected_component)

lemma connected_component_idemp:
  "connected_component_set (connected_component_set S x) x = connected_component_set S x"
  apply (rule subset_antisym)
   apply (simp add: connected_component_subset)
  apply (metis connected_component_eq_empty connected_component_maximal
      connected_component_refl_eq connected_connected_component mem_Collect_eq set_eq_subset)
  done

lemma connected_component_unique:
  "\<lbrakk>x \<in> c; c \<subseteq> S; connected c;
    \<And>c'. \<lbrakk>x \<in> c'; c' \<subseteq> S; connected c'\<rbrakk> \<Longrightarrow> c' \<subseteq> c\<rbrakk>
        \<Longrightarrow> connected_component_set S x = c"
  apply (rule subset_antisym)
   apply (meson connected_component_maximal connected_component_subset connected_connected_component contra_subsetD)
  by (simp add: connected_component_maximal)

lemma joinable_connected_component_eq:
  "\<lbrakk>connected T; T \<subseteq> S;
    connected_component_set S x \<inter> T \<noteq> {};
    connected_component_set S y \<inter> T \<noteq> {}\<rbrakk>
    \<Longrightarrow> connected_component_set S x = connected_component_set S y"
apply (simp add: ex_in_conv [symmetric])
apply (rule connected_component_eq)
by (metis (no_types, opaque_lifting) connected_component_eq_eq connected_component_in connected_component_maximal subsetD mem_Collect_eq)


lemma Union_connected_component: "\<Union>(connected_component_set S ` S) = S"
  apply (rule subset_antisym)
  apply (simp add: SUP_least connected_component_subset)
  using connected_component_refl_eq
  by force


lemma complement_connected_component_unions:
    "S - connected_component_set S x =
     \<Union>(connected_component_set S ` S - {connected_component_set S x})"
  apply (subst Union_connected_component [symmetric], auto)
  apply (metis connected_component_eq_eq connected_component_in)
  by (metis connected_component_eq mem_Collect_eq)

lemma connected_component_intermediate_subset:
        "\<lbrakk>connected_component_set U a \<subseteq> T; T \<subseteq> U\<rbrakk>
        \<Longrightarrow> connected_component_set T a = connected_component_set U a"
  apply (case_tac "a \<in> U")
  apply (simp add: connected_component_maximal connected_component_mono subset_antisym)
  using connected_component_eq_empty by blast


subsection \<open>The set of connected components of a set\<close>

definition\<^marker>\<open>tag important\<close> components:: "'a::topological_space set \<Rightarrow> 'a set set"
  where "components S \<equiv> connected_component_set S ` S"

lemma components_iff: "S \<in> components U \<longleftrightarrow> (\<exists>x. x \<in> U \<and> S = connected_component_set U x)"
  by (auto simp: components_def)

lemma componentsI: "x \<in> U \<Longrightarrow> connected_component_set U x \<in> components U"
  by (auto simp: components_def)

lemma componentsE:
  assumes "S \<in> components U"
  obtains x where "x \<in> U" "S = connected_component_set U x"
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
  by (metis (no_types, opaque_lifting) components_iff connected_component_eq_eq connected_iff_connected_component)

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

lemma closedin_connected_component: "closedin (top_of_set s) (connected_component_set s x)"
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
   "C \<in> components s \<Longrightarrow> closedin (top_of_set s) C"
  using closedin_connected_component componentsE by blast


subsection\<^marker>\<open>tag unimportant\<close> \<open>Proving a function is constant on a connected set
  by proving that a level set is open\<close>

lemma continuous_levelset_openin_cases:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (top_of_set s) {x \<in> s. f x = a}
        \<Longrightarrow> (\<forall>x \<in> s. f x \<noteq> a) \<or> (\<forall>x \<in> s. f x = a)"
  unfolding connected_clopen
  using continuous_closedin_preimage_constant by auto

lemma continuous_levelset_openin:
  fixes f :: "_ \<Rightarrow> 'b::t1_space"
  shows "connected s \<Longrightarrow> continuous_on s f \<Longrightarrow>
        openin (top_of_set s) {x \<in> s. f x = a} \<Longrightarrow>
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


subsection\<^marker>\<open>tag unimportant\<close> \<open>Preservation of Connectedness\<close>

lemma homeomorphic_connectedness:
  assumes "s homeomorphic t"
  shows "connected s \<longleftrightarrow> connected t"
using assms unfolding homeomorphic_def homeomorphism_def by (metis connected_continuous_image)

lemma connected_monotone_quotient_preimage:
  assumes "connected T"
      and contf: "continuous_on S f" and fim: "f ` S = T"
      and opT: "\<And>U. U \<subseteq> T
                 \<Longrightarrow> openin (top_of_set S) (S \<inter> f -` U) \<longleftrightarrow>
                     openin (top_of_set T) U"
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
  have opeU: "openin (top_of_set T) (f ` (S \<inter> U))"
    by (metis UU \<open>open U\<close> fim image_Int_subset le_inf_iff opT openin_open_Int)
  have opeV: "openin (top_of_set T) (f ` (S \<inter> V))"
    by (metis opT fim VV \<open>open V\<close> openin_open_Int image_Int_subset inf.bounded_iff)
  have "T \<subseteq> f ` (S \<inter> U) \<union> f ` (S \<inter> V)"
    using \<open>S \<subseteq> U \<union> V\<close> fim by auto
  then show False
    using \<open>connected T\<close> disjoint opeU opeV \<open>U \<inter> S \<noteq> {}\<close> \<open>V \<inter> S \<noteq> {}\<close>
    by (auto simp: connected_openin)
qed

lemma connected_open_monotone_preimage:
  assumes contf: "continuous_on S f" and fim: "f ` S = T"
    and ST: "\<And>C. openin (top_of_set S) C \<Longrightarrow> openin (top_of_set T) (f ` C)"
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
    have "\<And>U. openin (top_of_set (S \<inter> f -` C)) U
               \<Longrightarrow> openin (top_of_set C) (f ` U)"
      using open_map_restrict [OF _ ST \<open>C \<subseteq> T\<close>] by metis
    then show "\<And>D. D \<subseteq> C
          \<Longrightarrow> openin (top_of_set (S \<inter> f -` C)) (S \<inter> f -` C \<inter> f -` D) =
              openin (top_of_set C) D"
      using open_map_imp_quotient_map [of "(S \<inter> f -` C)" f] contf' by (simp add: eqC)
  qed
qed


lemma connected_closed_monotone_preimage:
  assumes contf: "continuous_on S f" and fim: "f ` S = T"
    and ST: "\<And>C. closedin (top_of_set S) C \<Longrightarrow> closedin (top_of_set T) (f ` C)"
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
    have "\<And>U. closedin (top_of_set (S \<inter> f -` C)) U
               \<Longrightarrow> closedin (top_of_set C) (f ` U)"
      using closed_map_restrict [OF _ ST \<open>C \<subseteq> T\<close>] by metis
    then show "\<And>D. D \<subseteq> C
          \<Longrightarrow> openin (top_of_set (S \<inter> f -` C)) (S \<inter> f -` C \<inter> f -` D) =
              openin (top_of_set C) D"
      using closed_map_imp_quotient_map [of "(S \<inter> f -` C)" f] contf' by (simp add: eqC)
  qed
qed


subsection\<open>Lemmas about components\<close>

text  \<open>See Newman IV, 3.3 and 3.4.\<close>

lemma connected_Un_clopen_in_complement:
  fixes S U :: "'a::metric_space set"
  assumes "connected S" "connected U" "S \<subseteq> U" 
      and opeT: "openin (top_of_set (U - S)) T" 
      and cloT: "closedin (top_of_set (U - S)) T"
    shows "connected (S \<union> T)"
proof -
  have *: "\<lbrakk>\<And>x y. P x y \<longleftrightarrow> P y x; \<And>x y. P x y \<Longrightarrow> S \<subseteq> x \<or> S \<subseteq> y;
            \<And>x y. \<lbrakk>P x y; S \<subseteq> x\<rbrakk> \<Longrightarrow> False\<rbrakk> \<Longrightarrow> \<not>(\<exists>x y. (P x y))" for P
    by metis
  show ?thesis
    unfolding connected_closedin_eq
  proof (rule *)
    fix H1 H2
    assume H: "closedin (top_of_set (S \<union> T)) H1 \<and> 
               closedin (top_of_set (S \<union> T)) H2 \<and>
               H1 \<union> H2 = S \<union> T \<and> H1 \<inter> H2 = {} \<and> H1 \<noteq> {} \<and> H2 \<noteq> {}"
    then have clo: "closedin (top_of_set S) (S \<inter> H1)"
                   "closedin (top_of_set S) (S \<inter> H2)"
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
    assume H: "closedin (top_of_set (S \<union> T)) H1 \<and>
               closedin (top_of_set (S \<union> T)) H2 \<and>
               H1 \<union> H2 = S \<union> T \<and> H1 \<inter> H2 = {} \<and> H1 \<noteq> {} \<and> H2 \<noteq> {}" 
       and "S \<subseteq> H1"
    then have H2T: "H2 \<subseteq> T"
      by auto
    have "T \<subseteq> U"
      using Diff_iff opeT openin_imp_subset by auto
    with \<open>S \<subseteq> U\<close> have Ueq: "U = (U - S) \<union> (S \<union> T)" 
      by auto
    have "openin (top_of_set ((U - S) \<union> (S \<union> T))) H2"
    proof (rule openin_subtopology_Un)
      show "openin (top_of_set (S \<union> T)) H2"
        using \<open>H2 \<subseteq> T\<close> apply (auto simp: openin_closedin_eq)
        by (metis Diff_Diff_Int Diff_disjoint Diff_partition Diff_subset H Int_absorb1 Un_Diff)
      then show "openin (top_of_set (U - S)) H2"
        by (meson H2T Un_upper2 opeT openin_subset_trans openin_trans)
    qed
    moreover have "closedin (top_of_set ((U - S) \<union> (S \<union> T))) H2"
    proof (rule closedin_subtopology_Un)
      show "closedin (top_of_set (U - S)) H2"
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
  assume clo3: "closedin (top_of_set (U - C)) H3" 
    and clo4: "closedin (top_of_set (U - C)) H4" 
    and "H3 \<union> H4 = U - C" and "H3 \<inter> H4 = {}" and "H3 \<noteq> {}" and "H4 \<noteq> {}"
    and * [rule_format]:
    "\<forall>H1 H2. \<not> closedin (top_of_set S) H1 \<or>
                      \<not> closedin (top_of_set S) H2 \<or>
                      H1 \<union> H2 \<noteq> S \<or> H1 \<inter> H2 \<noteq> {} \<or> \<not> H1 \<noteq> {} \<or> \<not> H2 \<noteq> {}"
  then have "H3 \<subseteq> U-C" and ope3: "openin (top_of_set (U - C)) (U - C - H3)"
    and "H4 \<subseteq> U-C" and ope4: "openin (top_of_set (U - C)) (U - C - H4)"
    by (auto simp: closedin_def)
  have "C \<noteq> {}" "C \<subseteq> U-S" "connected C"
    using C in_components_nonempty in_components_subset in_components_maximal by blast+
  have cCH3: "connected (C \<union> H3)"
  proof (rule connected_Un_clopen_in_complement [OF \<open>connected C\<close> \<open>connected U\<close> _ _ clo3])
    show "openin (top_of_set (U - C)) H3"
      apply (simp add: openin_closedin_eq \<open>H3 \<subseteq> U - C\<close>)
      apply (simp add: closedin_subtopology)
      by (metis Diff_cancel Diff_triv Un_Diff clo4 \<open>H3 \<inter> H4 = {}\<close> \<open>H3 \<union> H4 = U - C\<close> closedin_closed inf_commute sup_bot.left_neutral)
  qed (use clo3 \<open>C \<subseteq> U - S\<close> in auto)
  have cCH4: "connected (C \<union> H4)"
  proof (rule connected_Un_clopen_in_complement [OF \<open>connected C\<close> \<open>connected U\<close> _ _ clo4])
    show "openin (top_of_set (U - C)) H4"
      apply (simp add: openin_closedin_eq \<open>H4 \<subseteq> U - C\<close>)
      apply (simp add: closedin_subtopology)
      by (metis Diff_cancel Int_commute Un_Diff Un_Diff_Int \<open>H3 \<inter> H4 = {}\<close> \<open>H3 \<union> H4 = U - C\<close> clo3 closedin_closed)
  qed (use clo4 \<open>C \<subseteq> U - S\<close> in auto)
  have "closedin (top_of_set S) (S \<inter> H3)" "closedin (top_of_set S) (S \<inter> H4)"
    using clo3 clo4 \<open>S \<subseteq> U\<close> \<open>C \<subseteq> U - S\<close> by (auto simp: closedin_closed)
  moreover have "S \<inter> H3 \<noteq> {}"      
    using components_maximal [OF C cCH3] \<open>C \<noteq> {}\<close> \<open>C \<subseteq> U - S\<close> \<open>H3 \<noteq> {}\<close> \<open>H3 \<subseteq> U - C\<close> by auto
  moreover have "S \<inter> H4 \<noteq> {}"
    using components_maximal [OF C cCH4] \<open>C \<noteq> {}\<close> \<open>C \<subseteq> U - S\<close> \<open>H4 \<noteq> {}\<close> \<open>H4 \<subseteq> U - C\<close> by auto
  ultimately show False
    using * [of "S \<inter> H3" "S \<inter> H4"] \<open>H3 \<inter> H4 = {}\<close> \<open>C \<subseteq> U - S\<close> \<open>H3 \<union> H4 = U - C\<close> \<open>S \<subseteq> U\<close> 
    by auto
qed


subsection\<^marker>\<open>tag unimportant\<close>\<open>Constancy of a function from a connected set into a finite, disconnected or discrete set\<close>

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


text\<open>This proof requires the existence of two separate values of the range type.\<close>
lemma finite_range_constant_imp_connected:
  assumes "\<And>f::'a::topological_space \<Rightarrow> 'b::real_normed_algebra_1.
              \<lbrakk>continuous_on S f; finite(f ` S)\<rbrakk> \<Longrightarrow> f constant_on S"
    shows "connected S"
proof -
  { fix t u
    assume clt: "closedin (top_of_set S) t"
       and clu: "closedin (top_of_set S) u"
       and tue: "t \<inter> u = {}" and tus: "t \<union> u = S"
    have conif: "continuous_on S (\<lambda>x. if x \<in> t then 0 else 1)"
      apply (subst tus [symmetric])
      apply (rule continuous_on_cases_local)
      using clt clu tue
      apply (auto simp: tus)
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

end
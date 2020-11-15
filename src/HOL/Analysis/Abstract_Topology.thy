(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light]
*)

section \<open>Operators involving abstract topology\<close>

theory Abstract_Topology
  imports
    Complex_Main
    "HOL-Library.Set_Idioms"
    "HOL-Library.FuncSet"
begin

subsection \<open>General notion of a topology as a value\<close>

definition\<^marker>\<open>tag important\<close> istopology :: "('a set \<Rightarrow> bool) \<Rightarrow> bool" where
  "istopology L \<equiv> (\<forall>S T. L S \<longrightarrow> L T \<longrightarrow> L (S \<inter> T)) \<and> (\<forall>\<K>. (\<forall>K\<in>\<K>. L K) \<longrightarrow> L (\<Union>\<K>))"

typedef\<^marker>\<open>tag important\<close> 'a topology = "{L::('a set) \<Rightarrow> bool. istopology L}"
  morphisms "openin" "topology"
  unfolding istopology_def by blast

lemma istopology_openin[intro]: "istopology(openin U)"
  using openin[of U] by blast

lemma istopology_open: "istopology open"
  by (auto simp: istopology_def)

lemma topology_inverse': "istopology U \<Longrightarrow> openin (topology U) = U"
  using topology_inverse[unfolded mem_Collect_eq] .

lemma topology_inverse_iff: "istopology U \<longleftrightarrow> openin (topology U) = U"
  using topology_inverse[of U] istopology_openin[of "topology U"] by auto

lemma topology_eq: "T1 = T2 \<longleftrightarrow> (\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S)"
proof
  assume "T1 = T2"
  then show "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S" by simp
next
  assume H: "\<forall>S. openin T1 S \<longleftrightarrow> openin T2 S"
  then have "openin T1 = openin T2" by (simp add: fun_eq_iff)
  then have "topology (openin T1) = topology (openin T2)" by simp
  then show "T1 = T2" unfolding openin_inverse .
qed


text\<open>The "universe": the union of all sets in the topology.\<close>
definition "topspace T = \<Union>{S. openin T S}"

subsubsection \<open>Main properties of open sets\<close>

proposition openin_clauses:
  fixes U :: "'a topology"
  shows
    "openin U {}"
    "\<And>S T. openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S\<inter>T)"
    "\<And>K. (\<forall>S \<in> K. openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin[of U] unfolding istopology_def by auto

lemma openin_subset: "openin U S \<Longrightarrow> S \<subseteq> topspace U"
  unfolding topspace_def by blast

lemma openin_empty[simp]: "openin U {}"
  by (rule openin_clauses)

lemma openin_Int[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<inter> T)"
  by (rule openin_clauses)

lemma openin_Union[intro]: "(\<And>S. S \<in> K \<Longrightarrow> openin U S) \<Longrightarrow> openin U (\<Union>K)"
  using openin_clauses by blast

lemma openin_Un[intro]: "openin U S \<Longrightarrow> openin U T \<Longrightarrow> openin U (S \<union> T)"
  using openin_Union[of "{S,T}" U] by auto

lemma openin_topspace[intro, simp]: "openin U (topspace U)"
  by (force simp: openin_Union topspace_def)

lemma openin_subopen: "openin U S \<longleftrightarrow> (\<forall>x \<in> S. \<exists>T. openin U T \<and> x \<in> T \<and> T \<subseteq> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs by auto
next
  assume H: ?rhs
  let ?t = "\<Union>{T. openin U T \<and> T \<subseteq> S}"
  have "openin U ?t" by (force simp: openin_Union)
  also have "?t = S" using H by auto
  finally show "openin U S" .
qed

lemma openin_INT [intro]:
  assumes "finite I"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T ((\<Inter>i \<in> I. U i) \<inter> topspace T)"
using assms by (induct, auto simp: inf_sup_aci(2) openin_Int)

lemma openin_INT2 [intro]:
  assumes "finite I" "I \<noteq> {}"
          "\<And>i. i \<in> I \<Longrightarrow> openin T (U i)"
  shows "openin T (\<Inter>i \<in> I. U i)"
proof -
  have "(\<Inter>i \<in> I. U i) \<subseteq> topspace T"
    using \<open>I \<noteq> {}\<close> openin_subset[OF assms(3)] by auto
  then show ?thesis
    using openin_INT[of _ _ U, OF assms(1) assms(3)] by (simp add: inf.absorb2 inf_commute)
qed

lemma openin_Inter [intro]:
  assumes "finite \<F>" "\<F> \<noteq> {}" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (\<Inter>\<F>)"
  by (metis (full_types) assms openin_INT2 image_ident)

lemma openin_Int_Inter:
  assumes "finite \<F>" "openin T U" "\<And>X. X \<in> \<F> \<Longrightarrow> openin T X" shows "openin T (U \<inter> \<Inter>\<F>)"
  using openin_Inter [of "insert U \<F>"] assms by auto


subsubsection \<open>Closed sets\<close>

definition\<^marker>\<open>tag important\<close> closedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool" where
"closedin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> openin U (topspace U - S)"

lemma closedin_subset: "closedin U S \<Longrightarrow> S \<subseteq> topspace U"
  by (metis closedin_def)

lemma closedin_empty[simp]: "closedin U {}"
  by (simp add: closedin_def)

lemma closedin_topspace[intro, simp]: "closedin U (topspace U)"
  by (simp add: closedin_def)

lemma closedin_Un[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<union> T)"
  by (auto simp: Diff_Un closedin_def)

lemma Diff_Inter[intro]: "A - \<Inter>S = \<Union>{A - s|s. s\<in>S}"
  by auto

lemma closedin_Union:
  assumes "finite S" "\<And>T. T \<in> S \<Longrightarrow> closedin U T"
    shows "closedin U (\<Union>S)"
  using assms by induction auto

lemma closedin_Inter[intro]:
  assumes Ke: "K \<noteq> {}"
    and Kc: "\<And>S. S \<in>K \<Longrightarrow> closedin U S"
  shows "closedin U (\<Inter>K)"
  using Ke Kc unfolding closedin_def Diff_Inter by auto

lemma closedin_INT[intro]:
  assumes "A \<noteq> {}" "\<And>x. x \<in> A \<Longrightarrow> closedin U (B x)"
  shows "closedin U (\<Inter>x\<in>A. B x)"
  using assms by blast

lemma closedin_Int[intro]: "closedin U S \<Longrightarrow> closedin U T \<Longrightarrow> closedin U (S \<inter> T)"
  using closedin_Inter[of "{S,T}" U] by auto

lemma openin_closedin_eq: "openin U S \<longleftrightarrow> S \<subseteq> topspace U \<and> closedin U (topspace U - S)"
  by (metis Diff_subset closedin_def double_diff equalityD1 openin_subset)

lemma topology_finer_closedin:
  "topspace X = topspace Y \<Longrightarrow> (\<forall>S. openin Y S \<longrightarrow> openin X S) \<longleftrightarrow> (\<forall>S. closedin Y S \<longrightarrow> closedin X S)"
  by (metis closedin_def openin_closedin_eq)

lemma openin_closedin: "S \<subseteq> topspace U \<Longrightarrow> (openin U S \<longleftrightarrow> closedin U (topspace U - S))"
  by (simp add: openin_closedin_eq)

lemma openin_diff[intro]:
  assumes oS: "openin U S"
    and cT: "closedin U T"
  shows "openin U (S - T)"
proof -
  have "S - T = S \<inter> (topspace U - T)" using openin_subset[of U S]  oS cT
    by (auto simp: topspace_def openin_subset)
  then show ?thesis using oS cT
    by (auto simp: closedin_def)
qed

lemma closedin_diff[intro]:
  assumes oS: "closedin U S"
    and cT: "openin U T"
  shows "closedin U (S - T)"
proof -
  have "S - T = S \<inter> (topspace U - T)"
    using closedin_subset[of U S] oS cT by (auto simp: topspace_def)
  then show ?thesis
    using oS cT by (auto simp: openin_closedin_eq)
qed


subsection\<open>The discrete topology\<close>

definition discrete_topology where "discrete_topology U \<equiv> topology (\<lambda>S. S \<subseteq> U)"

lemma openin_discrete_topology [simp]: "openin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U"
proof -
  have "istopology (\<lambda>S. S \<subseteq> U)"
    by (auto simp: istopology_def)
  then show ?thesis
    by (simp add: discrete_topology_def topology_inverse')
qed

lemma topspace_discrete_topology [simp]: "topspace(discrete_topology U) = U"
  by (meson openin_discrete_topology openin_subset openin_topspace order_refl subset_antisym)

lemma closedin_discrete_topology [simp]: "closedin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U"
  by (simp add: closedin_def)

lemma discrete_topology_unique:
   "discrete_topology U = X \<longleftrightarrow> topspace X = U \<and> (\<forall>x \<in> U. openin X {x})" (is "?lhs = ?rhs")
proof
  assume R: ?rhs
  then have "openin X S" if "S \<subseteq> U" for S
    using openin_subopen subsetD that by fastforce
  moreover have "x \<in> topspace X" if "openin X S" and "x \<in> S" for x S
    using openin_subset that by blast
  ultimately
  show ?lhs
    using R by (auto simp: topology_eq)
qed auto

lemma discrete_topology_unique_alt:
  "discrete_topology U = X \<longleftrightarrow> topspace X \<subseteq> U \<and> (\<forall>x \<in> U. openin X {x})"
  using openin_subset
  by (auto simp: discrete_topology_unique)

lemma subtopology_eq_discrete_topology_empty:
   "X = discrete_topology {} \<longleftrightarrow> topspace X = {}"
  using discrete_topology_unique [of "{}" X] by auto

lemma subtopology_eq_discrete_topology_sing:
   "X = discrete_topology {a} \<longleftrightarrow> topspace X = {a}"
  by (metis discrete_topology_unique openin_topspace singletonD)


subsection \<open>Subspace topology\<close>

definition\<^marker>\<open>tag important\<close> subtopology :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a topology" where
"subtopology U V = topology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"

lemma istopology_subtopology: "istopology (\<lambda>T. \<exists>S. T = S \<inter> V \<and> openin U S)"
  (is "istopology ?L")
proof -
  have "?L {}" by blast
  {
    fix A B
    assume A: "?L A" and B: "?L B"
    from A B obtain Sa and Sb where Sa: "openin U Sa" "A = Sa \<inter> V" and Sb: "openin U Sb" "B = Sb \<inter> V"
      by blast
    have "A \<inter> B = (Sa \<inter> Sb) \<inter> V" "openin U (Sa \<inter> Sb)"
      using Sa Sb by blast+
    then have "?L (A \<inter> B)" by blast
  }
  moreover
  {
    fix K
    assume K: "K \<subseteq> Collect ?L"
    have th0: "Collect ?L = (\<lambda>S. S \<inter> V) ` Collect (openin U)"
      by blast
    from K[unfolded th0 subset_image_iff]
    obtain Sk where Sk: "Sk \<subseteq> Collect (openin U)" "K = (\<lambda>S. S \<inter> V) ` Sk"
      by blast
    have "\<Union>K = (\<Union>Sk) \<inter> V"
      using Sk by auto
    moreover have "openin U (\<Union>Sk)"
      using Sk by (auto simp: subset_eq)
    ultimately have "?L (\<Union>K)" by blast
  }
  ultimately show ?thesis
    unfolding subset_eq mem_Collect_eq istopology_def by auto
qed

lemma openin_subtopology: "openin (subtopology U V) S \<longleftrightarrow> (\<exists>T. openin U T \<and> S = T \<inter> V)"
  unfolding subtopology_def topology_inverse'[OF istopology_subtopology]
  by auto

lemma openin_subtopology_Int:
   "openin X S \<Longrightarrow> openin (subtopology X T) (S \<inter> T)"
  using openin_subtopology by auto

lemma openin_subtopology_Int2:
   "openin X T \<Longrightarrow> openin (subtopology X S) (S \<inter> T)"
  using openin_subtopology by auto

lemma openin_subtopology_diff_closed:
   "\<lbrakk>S \<subseteq> topspace X; closedin X T\<rbrakk> \<Longrightarrow> openin (subtopology X S) (S - T)"
  unfolding closedin_def openin_subtopology
  by (rule_tac x="topspace X - T" in exI) auto

lemma openin_relative_to: "(openin X relative_to S) = openin (subtopology X S)"
  by (force simp: relative_to_def openin_subtopology)

lemma topspace_subtopology [simp]: "topspace (subtopology U V) = topspace U \<inter> V"
  by (auto simp: topspace_def openin_subtopology)

lemma topspace_subtopology_subset:
   "S \<subseteq> topspace X \<Longrightarrow> topspace(subtopology X S) = S"
  by (simp add: inf.absorb_iff2)

lemma closedin_subtopology: "closedin (subtopology U V) S \<longleftrightarrow> (\<exists>T. closedin U T \<and> S = T \<inter> V)"
  unfolding closedin_def topspace_subtopology
  by (auto simp: openin_subtopology)

lemma openin_subtopology_refl: "openin (subtopology U V) V \<longleftrightarrow> V \<subseteq> topspace U"
  unfolding openin_subtopology
  by auto (metis IntD1 in_mono openin_subset)

lemma subtopology_subtopology:
   "subtopology (subtopology X S) T = subtopology X (S \<inter> T)"
proof -
  have eq: "\<And>T'. (\<exists>S'. T' = S' \<inter> T \<and> (\<exists>T. openin X T \<and> S' = T \<inter> S)) = (\<exists>Sa. T' = Sa \<inter> (S \<inter> T) \<and> openin X Sa)"
    by (metis inf_assoc)
  have "subtopology (subtopology X S) T = topology (\<lambda>Ta. \<exists>Sa. Ta = Sa \<inter> T \<and> openin (subtopology X S) Sa)"
    by (simp add: subtopology_def)
  also have "\<dots> = subtopology X (S \<inter> T)"
    by (simp add: openin_subtopology eq) (simp add: subtopology_def)
  finally show ?thesis .
qed

lemma openin_subtopology_alt:
     "openin (subtopology X U) S \<longleftrightarrow> S \<in> (\<lambda>T. U \<inter> T) ` Collect (openin X)"
  by (simp add: image_iff inf_commute openin_subtopology)

lemma closedin_subtopology_alt:
     "closedin (subtopology X U) S \<longleftrightarrow> S \<in> (\<lambda>T. U \<inter> T) ` Collect (closedin X)"
  by (simp add: image_iff inf_commute closedin_subtopology)

lemma subtopology_superset:
  assumes UV: "topspace U \<subseteq> V"
  shows "subtopology U V = U"
proof -
  {
    fix S
    {
      fix T
      assume T: "openin U T" "S = T \<inter> V"
      from T openin_subset[OF T(1)] UV have eq: "S = T"
        by blast
      have "openin U S"
        unfolding eq using T by blast
    }
    moreover
    {
      assume S: "openin U S"
      then have "\<exists>T. openin U T \<and> S = T \<inter> V"
        using openin_subset[OF S] UV by auto
    }
    ultimately have "(\<exists>T. openin U T \<and> S = T \<inter> V) \<longleftrightarrow> openin U S"
      by blast
  }
  then show ?thesis
    unfolding topology_eq openin_subtopology by blast
qed

lemma subtopology_topspace[simp]: "subtopology U (topspace U) = U"
  by (simp add: subtopology_superset)

lemma subtopology_UNIV[simp]: "subtopology U UNIV = U"
  by (simp add: subtopology_superset)

lemma subtopology_restrict:
   "subtopology X (topspace X \<inter> S) = subtopology X S"
  by (metis subtopology_subtopology subtopology_topspace)

lemma openin_subtopology_empty:
   "openin (subtopology U {}) S \<longleftrightarrow> S = {}"
by (metis Int_empty_right openin_empty openin_subtopology)

lemma closedin_subtopology_empty:
   "closedin (subtopology U {}) S \<longleftrightarrow> S = {}"
by (metis Int_empty_right closedin_empty closedin_subtopology)

lemma closedin_subtopology_refl [simp]:
   "closedin (subtopology U X) X \<longleftrightarrow> X \<subseteq> topspace U"
by (metis closedin_def closedin_topspace inf.absorb_iff2 le_inf_iff topspace_subtopology)

lemma closedin_topspace_empty: "topspace T = {} \<Longrightarrow> (closedin T S \<longleftrightarrow> S = {})"
  by (simp add: closedin_def)

lemma open_in_topspace_empty:
   "topspace X = {} \<Longrightarrow> openin X S \<longleftrightarrow> S = {}"
  by (simp add: openin_closedin_eq)

lemma openin_imp_subset:
   "openin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
by (metis Int_iff openin_subtopology subsetI)

lemma closedin_imp_subset:
   "closedin (subtopology U S) T \<Longrightarrow> T \<subseteq> S"
by (simp add: closedin_def)

lemma openin_open_subtopology:
     "openin X S \<Longrightarrow> openin (subtopology X S) T \<longleftrightarrow> openin X T \<and> T \<subseteq> S"
  by (metis inf.orderE openin_Int openin_imp_subset openin_subtopology)

lemma closedin_closed_subtopology:
     "closedin X S \<Longrightarrow> (closedin (subtopology X S) T \<longleftrightarrow> closedin X T \<and> T \<subseteq> S)"
  by (metis closedin_Int closedin_imp_subset closedin_subtopology inf.orderE)

lemma openin_subtopology_Un:
    "\<lbrakk>openin (subtopology X T) S; openin (subtopology X U) S\<rbrakk>
     \<Longrightarrow> openin (subtopology X (T \<union> U)) S"
by (simp add: openin_subtopology) blast

lemma closedin_subtopology_Un:
    "\<lbrakk>closedin (subtopology X T) S; closedin (subtopology X U) S\<rbrakk>
     \<Longrightarrow> closedin (subtopology X (T \<union> U)) S"
by (simp add: closedin_subtopology) blast

lemma openin_trans_full:
   "\<lbrakk>openin (subtopology X U) S; openin X U\<rbrakk> \<Longrightarrow> openin X S"
  by (simp add: openin_open_subtopology)


subsection \<open>The canonical topology from the underlying type class\<close>

abbreviation\<^marker>\<open>tag important\<close> euclidean :: "'a::topological_space topology"
  where "euclidean \<equiv> topology open"

abbreviation top_of_set :: "'a::topological_space set \<Rightarrow> 'a topology"
  where "top_of_set \<equiv> subtopology (topology open)"

lemma open_openin: "open S \<longleftrightarrow> openin euclidean S"
  by (simp add: istopology_open topology_inverse')

declare open_openin [symmetric, simp]

lemma topspace_euclidean [simp]: "topspace euclidean = UNIV"
  by (force simp: topspace_def)

lemma topspace_euclidean_subtopology[simp]: "topspace (top_of_set S) = S"
  by (simp)

lemma closed_closedin: "closed S \<longleftrightarrow> closedin euclidean S"
  by (simp add: closed_def closedin_def Compl_eq_Diff_UNIV)

declare closed_closedin [symmetric, simp]

lemma openin_subtopology_self [simp]: "openin (top_of_set S) S"
  by (metis openin_topspace topspace_euclidean_subtopology)

subsubsection\<open>The most basic facts about the usual topology and metric on R\<close>

abbreviation euclideanreal :: "real topology"
  where "euclideanreal \<equiv> topology open"

subsection \<open>Basic "localization" results are handy for connectedness.\<close>

lemma openin_open: "openin (top_of_set U) S \<longleftrightarrow> (\<exists>T. open T \<and> (S = U \<inter> T))"
  by (auto simp: openin_subtopology)

lemma openin_Int_open:
   "\<lbrakk>openin (top_of_set U) S; open T\<rbrakk>
        \<Longrightarrow> openin (top_of_set U) (S \<inter> T)"
by (metis open_Int Int_assoc openin_open)

lemma openin_open_Int[intro]: "open S \<Longrightarrow> openin (top_of_set U) (U \<inter> S)"
  by (auto simp: openin_open)

lemma open_openin_trans[trans]:
  "open S \<Longrightarrow> open T \<Longrightarrow> T \<subseteq> S \<Longrightarrow> openin (top_of_set S) T"
  by (metis Int_absorb1  openin_open_Int)

lemma open_subset: "S \<subseteq> T \<Longrightarrow> open S \<Longrightarrow> openin (top_of_set T) S"
  by (auto simp: openin_open)

lemma closedin_closed: "closedin (top_of_set U) S \<longleftrightarrow> (\<exists>T. closed T \<and> S = U \<inter> T)"
  by (simp add: closedin_subtopology Int_ac)

lemma closedin_closed_Int: "closed S \<Longrightarrow> closedin (top_of_set U) (U \<inter> S)"
  by (metis closedin_closed)

lemma closed_subset: "S \<subseteq> T \<Longrightarrow> closed S \<Longrightarrow> closedin (top_of_set T) S"
  by (auto simp: closedin_closed)

lemma closedin_closed_subset:
 "\<lbrakk>closedin (top_of_set U) V; T \<subseteq> U; S = V \<inter> T\<rbrakk>
             \<Longrightarrow> closedin (top_of_set T) S"
  by (metis (no_types, lifting) Int_assoc Int_commute closedin_closed inf.orderE)

lemma finite_imp_closedin:
  fixes S :: "'a::t1_space set"
  shows "\<lbrakk>finite S; S \<subseteq> T\<rbrakk> \<Longrightarrow> closedin (top_of_set T) S"
    by (simp add: finite_imp_closed closed_subset)

lemma closedin_singleton [simp]:
  fixes a :: "'a::t1_space"
  shows "closedin (top_of_set U) {a} \<longleftrightarrow> a \<in> U"
using closedin_subset  by (force intro: closed_subset)

lemma openin_euclidean_subtopology_iff:
  fixes S U :: "'a::metric_space set"
  shows "openin (top_of_set U) S \<longleftrightarrow>
    S \<subseteq> U \<and> (\<forall>x\<in>S. \<exists>e>0. \<forall>x'\<in>U. dist x' x < e \<longrightarrow> x'\<in> S)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding openin_open open_dist by blast
next
  define T where "T = {x. \<exists>a\<in>S. \<exists>d>0. (\<forall>y\<in>U. dist y a < d \<longrightarrow> y \<in> S) \<and> dist x a < d}"
  have 1: "\<forall>x\<in>T. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> T"
    unfolding T_def
    apply clarsimp
    apply (rule_tac x="d - dist x a" in exI)
    by (metis add_0_left dist_commute dist_triangle_lt less_diff_eq)
  assume ?rhs then have 2: "S = U \<inter> T"
    unfolding T_def
    by auto (metis dist_self)
  from 1 2 show ?lhs
    unfolding openin_open open_dist by fast
qed

lemma connected_openin:
      "connected S \<longleftrightarrow>
       \<not>(\<exists>E1 E2. openin (top_of_set S) E1 \<and>
                 openin (top_of_set S) E2 \<and>
                 S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
  unfolding connected_def openin_open disjoint_iff_not_equal by blast

lemma connected_openin_eq:
      "connected S \<longleftrightarrow>
       \<not>(\<exists>E1 E2. openin (top_of_set S) E1 \<and>
                 openin (top_of_set S) E2 \<and>
                 E1 \<union> E2 = S \<and> E1 \<inter> E2 = {} \<and>
                 E1 \<noteq> {} \<and> E2 \<noteq> {})"
  unfolding connected_openin
  by (metis (no_types, lifting) Un_subset_iff openin_imp_subset subset_antisym)

lemma connected_closedin:
      "connected S \<longleftrightarrow>
       (\<nexists>E1 E2.
        closedin (top_of_set S) E1 \<and>
        closedin (top_of_set S) E2 \<and>
        S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
       (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs 
    by (auto simp add: connected_closed closedin_closed)
next
  assume R: ?rhs
  then show ?lhs 
  proof (clarsimp simp add: connected_closed closedin_closed)
    fix A B 
    assume s_sub: "S \<subseteq> A \<union> B" "B \<inter> S \<noteq> {}"
      and disj: "A \<inter> B \<inter> S = {}"
      and cl: "closed A" "closed B"
    have "S \<inter> (A \<union> B) = S"
      using s_sub(1) by auto
    have "S - A = B \<inter> S"
      using Diff_subset_conv Un_Diff_Int disj s_sub(1) by auto
    then have "S \<inter> A = {}"
      by (metis Diff_Diff_Int Diff_disjoint Un_Diff_Int R cl closedin_closed_Int inf_commute order_refl s_sub(2))
    then show "A \<inter> S = {}"
      by blast
  qed
qed

lemma connected_closedin_eq:
      "connected S \<longleftrightarrow>
           \<not>(\<exists>E1 E2.
                 closedin (top_of_set S) E1 \<and>
                 closedin (top_of_set S) E2 \<and>
                 E1 \<union> E2 = S \<and> E1 \<inter> E2 = {} \<and>
                 E1 \<noteq> {} \<and> E2 \<noteq> {})"
  unfolding connected_closedin
  by (metis Un_subset_iff closedin_imp_subset subset_antisym)

text \<open>These "transitivity" results are handy too\<close>

lemma openin_trans[trans]:
  "openin (top_of_set T) S \<Longrightarrow> openin (top_of_set U) T \<Longrightarrow>
    openin (top_of_set U) S"
  by (metis openin_Int_open openin_open)

lemma openin_open_trans: "openin (top_of_set T) S \<Longrightarrow> open T \<Longrightarrow> open S"
  by (auto simp: openin_open intro: openin_trans)

lemma closedin_trans[trans]:
  "closedin (top_of_set T) S \<Longrightarrow> closedin (top_of_set U) T \<Longrightarrow>
    closedin (top_of_set U) S"
  by (auto simp: closedin_closed closed_Inter Int_assoc)

lemma closedin_closed_trans: "closedin (top_of_set T) S \<Longrightarrow> closed T \<Longrightarrow> closed S"
  by (auto simp: closedin_closed intro: closedin_trans)

lemma openin_subtopology_Int_subset:
   "\<lbrakk>openin (top_of_set u) (u \<inter> S); v \<subseteq> u\<rbrakk> \<Longrightarrow> openin (top_of_set v) (v \<inter> S)"
  by (auto simp: openin_subtopology)

lemma openin_open_eq: "open s \<Longrightarrow> (openin (top_of_set s) t \<longleftrightarrow> open t \<and> t \<subseteq> s)"
  using open_subset openin_open_trans openin_subset by fastforce


subsection\<open>Derived set (set of limit points)\<close>

definition derived_set_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "derived'_set'_of" 80)
  where "X derived_set_of S \<equiv>
         {x \<in> topspace X.
                (\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y\<noteq>x. y \<in> S \<and> y \<in> T))}"

lemma derived_set_of_restrict [simp]:
   "X derived_set_of (topspace X \<inter> S) = X derived_set_of S"
  by (simp add: derived_set_of_def) (metis openin_subset subset_iff)

lemma in_derived_set_of:
   "x \<in> X derived_set_of S \<longleftrightarrow> x \<in> topspace X \<and> (\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y\<noteq>x. y \<in> S \<and> y \<in> T))"
  by (simp add: derived_set_of_def)

lemma derived_set_of_subset_topspace:
   "X derived_set_of S \<subseteq> topspace X"
  by (auto simp add: derived_set_of_def)

lemma derived_set_of_subtopology:
   "(subtopology X U) derived_set_of S = U \<inter> (X derived_set_of (U \<inter> S))"
  by (simp add: derived_set_of_def openin_subtopology) blast

lemma derived_set_of_subset_subtopology:
   "(subtopology X S) derived_set_of T \<subseteq> S"
  by (simp add: derived_set_of_subtopology)

lemma derived_set_of_empty [simp]: "X derived_set_of {} = {}"
  by (auto simp: derived_set_of_def)

lemma derived_set_of_mono:
   "S \<subseteq> T \<Longrightarrow> X derived_set_of S \<subseteq> X derived_set_of T"
  unfolding derived_set_of_def by blast

lemma derived_set_of_Un:
   "X derived_set_of (S \<union> T) = X derived_set_of S \<union> X derived_set_of T" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: in_derived_set_of) (metis IntE IntI openin_Int)
  show "?rhs \<subseteq> ?lhs"
    by (simp add: derived_set_of_mono)
qed

lemma derived_set_of_Union:
   "finite \<F> \<Longrightarrow> X derived_set_of (\<Union>\<F>) = (\<Union>S \<in> \<F>. X derived_set_of S)"
proof (induction \<F> rule: finite_induct)
  case (insert S \<F>)
  then show ?case
    by (simp add: derived_set_of_Un)
qed auto

lemma derived_set_of_topspace:
  "X derived_set_of (topspace X) = {x \<in> topspace X. \<not> openin X {x}}" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (auto simp: in_derived_set_of)
  show "?rhs \<subseteq> ?lhs"
    by (clarsimp simp: in_derived_set_of) (metis openin_closedin_eq openin_subopen singletonD subset_eq)
qed

lemma discrete_topology_unique_derived_set:
     "discrete_topology U = X \<longleftrightarrow> topspace X = U \<and> X derived_set_of U = {}"
  by (auto simp: discrete_topology_unique derived_set_of_topspace)

lemma subtopology_eq_discrete_topology_eq:
   "subtopology X U = discrete_topology U \<longleftrightarrow> U \<subseteq> topspace X \<and> U \<inter> X derived_set_of U = {}"
  using discrete_topology_unique_derived_set [of U "subtopology X U"]
  by (auto simp: eq_commute derived_set_of_subtopology)

lemma subtopology_eq_discrete_topology:
   "S \<subseteq> topspace X \<and> S \<inter> X derived_set_of S = {}
        \<Longrightarrow> subtopology X S = discrete_topology S"
  by (simp add: subtopology_eq_discrete_topology_eq)

lemma subtopology_eq_discrete_topology_gen:
   "S \<inter> X derived_set_of S = {} \<Longrightarrow> subtopology X S = discrete_topology(topspace X \<inter> S)"
  by (metis Int_lower1 derived_set_of_restrict inf_assoc inf_bot_right subtopology_eq_discrete_topology_eq subtopology_subtopology subtopology_topspace)

lemma subtopology_discrete_topology [simp]: 
  "subtopology (discrete_topology U) S = discrete_topology(U \<inter> S)"
proof -
  have "(\<lambda>T. \<exists>Sa. T = Sa \<inter> S \<and> Sa \<subseteq> U) = (\<lambda>Sa. Sa \<subseteq> U \<and> Sa \<subseteq> S)"
    by force
  then show ?thesis
    by (simp add: subtopology_def) (simp add: discrete_topology_def)
qed
lemma openin_Int_derived_set_of_subset:
   "openin X S \<Longrightarrow> S \<inter> X derived_set_of T \<subseteq> X derived_set_of (S \<inter> T)"
  by (auto simp: derived_set_of_def)

lemma openin_Int_derived_set_of_eq:
  assumes "openin X S"
  shows "S \<inter> X derived_set_of T = S \<inter> X derived_set_of (S \<inter> T)" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (simp add: assms openin_Int_derived_set_of_subset)
  show "?rhs \<subseteq> ?lhs"
    by (metis derived_set_of_mono inf_commute inf_le1 inf_mono order_refl)
qed


subsection\<open> Closure with respect to a topological space\<close>

definition closure_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr "closure'_of" 80)
  where "X closure_of S \<equiv> {x \<in> topspace X. \<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y \<in> S. y \<in> T)}"

lemma closure_of_restrict: "X closure_of S = X closure_of (topspace X \<inter> S)"
  unfolding closure_of_def
  using openin_subset by blast

lemma in_closure_of:
   "x \<in> X closure_of S \<longleftrightarrow>
    x \<in> topspace X \<and> (\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y. y \<in> S \<and> y \<in> T))"
  by (auto simp: closure_of_def)

lemma closure_of: "X closure_of S = topspace X \<inter> (S \<union> X derived_set_of S)"
  by (fastforce simp: in_closure_of in_derived_set_of)

lemma closure_of_alt: "X closure_of S = topspace X \<inter> S \<union> X derived_set_of S"
  using derived_set_of_subset_topspace [of X S]
  unfolding closure_of_def in_derived_set_of
  by safe (auto simp: in_derived_set_of)

lemma derived_set_of_subset_closure_of:
   "X derived_set_of S \<subseteq> X closure_of S"
  by (fastforce simp: closure_of_def in_derived_set_of)

lemma closure_of_subtopology:
  "(subtopology X U) closure_of S = U \<inter> (X closure_of (U \<inter> S))"
  unfolding closure_of_def topspace_subtopology openin_subtopology
  by safe (metis (full_types) IntI Int_iff inf.commute)+

lemma closure_of_empty [simp]: "X closure_of {} = {}"
  by (simp add: closure_of_alt)

lemma closure_of_topspace [simp]: "X closure_of topspace X = topspace X"
  by (simp add: closure_of)

lemma closure_of_UNIV [simp]: "X closure_of UNIV = topspace X"
  by (simp add: closure_of)

lemma closure_of_subset_topspace: "X closure_of S \<subseteq> topspace X"
  by (simp add: closure_of)

lemma closure_of_subset_subtopology: "(subtopology X S) closure_of T \<subseteq> S"
  by (simp add: closure_of_subtopology)

lemma closure_of_mono: "S \<subseteq> T \<Longrightarrow> X closure_of S \<subseteq> X closure_of T"
  by (fastforce simp add: closure_of_def)

lemma closure_of_subtopology_subset:
   "(subtopology X U) closure_of S \<subseteq> (X closure_of S)"
  unfolding closure_of_subtopology
  by clarsimp (meson closure_of_mono contra_subsetD inf.cobounded2)

lemma closure_of_subtopology_mono:
   "T \<subseteq> U \<Longrightarrow> (subtopology X T) closure_of S \<subseteq> (subtopology X U) closure_of S"
  unfolding closure_of_subtopology
  by auto (meson closure_of_mono inf_mono subset_iff)

lemma closure_of_Un [simp]: "X closure_of (S \<union> T) = X closure_of S \<union> X closure_of T"
  by (simp add: Un_assoc Un_left_commute closure_of_alt derived_set_of_Un inf_sup_distrib1)

lemma closure_of_Union:
   "finite \<F> \<Longrightarrow> X closure_of (\<Union>\<F>) = (\<Union>S \<in> \<F>. X closure_of S)"
by (induction \<F> rule: finite_induct) auto

lemma closure_of_subset: "S \<subseteq> topspace X \<Longrightarrow> S \<subseteq> X closure_of S"
  by (auto simp: closure_of_def)

lemma closure_of_subset_Int: "topspace X \<inter> S \<subseteq> X closure_of S"
  by (auto simp: closure_of_def)

lemma closure_of_subset_eq: "S \<subseteq> topspace X \<and> X closure_of S \<subseteq> S \<longleftrightarrow> closedin X S"
proof -
  have "openin X (topspace X - S)"
    if "\<And>x. \<lbrakk>x \<in> topspace X; \<forall>T. x \<in> T \<and> openin X T \<longrightarrow> S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> x \<in> S"
    apply (subst openin_subopen)
    by (metis Diff_iff Diff_mono Diff_triv inf.commute openin_subset order_refl that)
  then show ?thesis
    by (auto simp: closedin_def closure_of_def disjoint_iff_not_equal)
qed

lemma closure_of_eq: "X closure_of S = S \<longleftrightarrow> closedin X S"
proof (cases "S \<subseteq> topspace X")
  case True
  then show ?thesis
    by (metis closure_of_subset closure_of_subset_eq set_eq_subset)
next
  case False
  then show ?thesis
    using closure_of closure_of_subset_eq by fastforce
qed

lemma closedin_contains_derived_set:
   "closedin X S \<longleftrightarrow> X derived_set_of S \<subseteq> S \<and> S \<subseteq> topspace X"
proof (intro iffI conjI)
  show "closedin X S \<Longrightarrow> X derived_set_of S \<subseteq> S"
    using closure_of_eq derived_set_of_subset_closure_of by fastforce
  show "closedin X S \<Longrightarrow> S \<subseteq> topspace X"
    using closedin_subset by blast
  show "X derived_set_of S \<subseteq> S \<and> S \<subseteq> topspace X \<Longrightarrow> closedin X S"
    by (metis closure_of closure_of_eq inf.absorb_iff2 sup.orderE)
qed

lemma derived_set_subset_gen:
   "X derived_set_of S \<subseteq> S \<longleftrightarrow> closedin X (topspace X \<inter> S)"
  by (simp add: closedin_contains_derived_set derived_set_of_restrict derived_set_of_subset_topspace)

lemma derived_set_subset: "S \<subseteq> topspace X \<Longrightarrow> (X derived_set_of S \<subseteq> S \<longleftrightarrow> closedin X S)"
  by (simp add: closedin_contains_derived_set)

lemma closedin_derived_set:
     "closedin (subtopology X T) S \<longleftrightarrow>
      S \<subseteq> topspace X \<and> S \<subseteq> T \<and> (\<forall>x. x \<in> X derived_set_of S \<and> x \<in> T \<longrightarrow> x \<in> S)"
  by (auto simp: closedin_contains_derived_set derived_set_of_subtopology Int_absorb1)

lemma closedin_Int_closure_of:
     "closedin (subtopology X S) T \<longleftrightarrow> S \<inter> X closure_of T = T"
  by (metis Int_left_absorb closure_of_eq closure_of_subtopology)

lemma closure_of_closedin: "closedin X S \<Longrightarrow> X closure_of S = S"
  by (simp add: closure_of_eq)

lemma closure_of_eq_diff: "X closure_of S = topspace X - \<Union>{T. openin X T \<and> disjnt S T}"
  by (auto simp: closure_of_def disjnt_iff)

lemma closedin_closure_of [simp]: "closedin X (X closure_of S)"
  unfolding closure_of_eq_diff by blast

lemma closure_of_closure_of [simp]: "X closure_of (X closure_of S) = X closure_of S"
  by (simp add: closure_of_eq)

lemma closure_of_hull:
  assumes "S \<subseteq> topspace X" shows "X closure_of S = (closedin X) hull S"
proof (rule hull_unique [THEN sym])
  show "S \<subseteq> X closure_of S"
    by (simp add: closure_of_subset assms)
next
  show "closedin X (X closure_of S)"
    by simp
  show "\<And>T. \<lbrakk>S \<subseteq> T; closedin X T\<rbrakk> \<Longrightarrow> X closure_of S \<subseteq> T"
    by (metis closure_of_eq closure_of_mono)
qed

lemma closure_of_minimal:
   "\<lbrakk>S \<subseteq> T; closedin X T\<rbrakk> \<Longrightarrow> (X closure_of S) \<subseteq> T"
  by (metis closure_of_eq closure_of_mono)

lemma closure_of_minimal_eq:
   "\<lbrakk>S \<subseteq> topspace X; closedin X T\<rbrakk> \<Longrightarrow> (X closure_of S) \<subseteq> T \<longleftrightarrow> S \<subseteq> T"
  by (meson closure_of_minimal closure_of_subset subset_trans)

lemma closure_of_unique:
   "\<lbrakk>S \<subseteq> T; closedin X T;
     \<And>T'. \<lbrakk>S \<subseteq> T'; closedin X T'\<rbrakk> \<Longrightarrow> T \<subseteq> T'\<rbrakk>
    \<Longrightarrow> X closure_of S = T"
  by (meson closedin_closure_of closedin_subset closure_of_minimal closure_of_subset eq_iff order.trans)

lemma closure_of_eq_empty_gen: "X closure_of S = {} \<longleftrightarrow> disjnt (topspace X) S"
  unfolding disjnt_def closure_of_restrict [where S=S]
  using closure_of by fastforce

lemma closure_of_eq_empty: "S \<subseteq> topspace X \<Longrightarrow> X closure_of S = {} \<longleftrightarrow> S = {}"
  using closure_of_subset by fastforce

lemma openin_Int_closure_of_subset:
  assumes "openin X S"
  shows "S \<inter> X closure_of T \<subseteq> X closure_of (S \<inter> T)"
proof -
  have "S \<inter> X derived_set_of T = S \<inter> X derived_set_of (S \<inter> T)"
    by (meson assms openin_Int_derived_set_of_eq)
  moreover have "S \<inter> (S \<inter> T) = S \<inter> T"
    by fastforce
  ultimately show ?thesis
    by (metis closure_of_alt inf.cobounded2 inf_left_commute inf_sup_distrib1)
qed

lemma closure_of_openin_Int_closure_of:
  assumes "openin X S"
  shows "X closure_of (S \<inter> X closure_of T) = X closure_of (S \<inter> T)"
proof
  show "X closure_of (S \<inter> X closure_of T) \<subseteq> X closure_of (S \<inter> T)"
    by (simp add: assms closure_of_minimal openin_Int_closure_of_subset)
next
  show "X closure_of (S \<inter> T) \<subseteq> X closure_of (S \<inter> X closure_of T)"
    by (metis Int_lower1 Int_subset_iff assms closedin_closure_of closure_of_minimal_eq closure_of_mono inf_le2 le_infI1 openin_subset)
qed

lemma openin_Int_closure_of_eq:
  assumes "openin X S" shows "S \<inter> X closure_of T = S \<inter> X closure_of (S \<inter> T)"  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (simp add: assms openin_Int_closure_of_subset)
  show "?rhs \<subseteq> ?lhs"
    by (metis closure_of_mono inf_commute inf_le1 inf_mono order_refl)
qed

lemma openin_Int_closure_of_eq_empty:
  assumes "openin X S" shows "S \<inter> X closure_of T = {} \<longleftrightarrow> S \<inter> T = {}"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding disjoint_iff
    by (meson assms in_closure_of in_mono openin_subset)
  show "?rhs \<Longrightarrow> ?lhs"
    by (simp add: assms openin_Int_closure_of_eq)
qed

lemma closure_of_openin_Int_superset:
   "openin X S \<and> S \<subseteq> X closure_of T
        \<Longrightarrow> X closure_of (S \<inter> T) = X closure_of S"
  by (metis closure_of_openin_Int_closure_of inf.orderE)

lemma closure_of_openin_subtopology_Int_closure_of:
  assumes S: "openin (subtopology X U) S" and "T \<subseteq> U"
  shows "X closure_of (S \<inter> X closure_of T) = X closure_of (S \<inter> T)" (is "?lhs = ?rhs")
proof
  obtain S0 where S0: "openin X S0" "S = S0 \<inter> U"
    using assms by (auto simp: openin_subtopology)
  show "?lhs \<subseteq> ?rhs"
  proof -
    have "S0 \<inter> X closure_of T = S0 \<inter> X closure_of (S0 \<inter> T)"
      by (meson S0(1) openin_Int_closure_of_eq)
    moreover have "S0 \<inter> T = S0 \<inter> U \<inter> T"
      using \<open>T \<subseteq> U\<close> by fastforce
    ultimately have "S \<inter> X closure_of T \<subseteq> X closure_of (S \<inter> T)"
      using S0(2) by auto
    then show ?thesis
      by (meson closedin_closure_of closure_of_minimal)
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof -
    have "T \<inter> S \<subseteq> T \<union> X derived_set_of T"
      by force
    then show ?thesis
      by (metis Int_subset_iff S closure_of closure_of_mono inf.cobounded2 inf.coboundedI2 inf_commute openin_closedin_eq topspace_subtopology)
  qed
qed

lemma closure_of_subtopology_open:
     "openin X U \<or> S \<subseteq> U \<Longrightarrow> (subtopology X U) closure_of S = U \<inter> X closure_of S"
  by (metis closure_of_subtopology inf_absorb2 openin_Int_closure_of_eq)

lemma discrete_topology_closure_of:
     "(discrete_topology U) closure_of S = U \<inter> S"
  by (metis closedin_discrete_topology closure_of_restrict closure_of_unique discrete_topology_unique inf_sup_ord(1) order_refl)


text\<open> Interior with respect to a topological space.                             \<close>

definition interior_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr "interior'_of" 80)
  where "X interior_of S \<equiv> {x. \<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> S}"

lemma interior_of_restrict:
   "X interior_of S = X interior_of (topspace X \<inter> S)"
  using openin_subset by (auto simp: interior_of_def)

lemma interior_of_eq: "(X interior_of S = S) \<longleftrightarrow> openin X S"
  unfolding interior_of_def  using openin_subopen by blast

lemma interior_of_openin: "openin X S \<Longrightarrow> X interior_of S = S"
  by (simp add: interior_of_eq)

lemma interior_of_empty [simp]: "X interior_of {} = {}"
  by (simp add: interior_of_eq)

lemma interior_of_topspace [simp]: "X interior_of (topspace X) = topspace X"
  by (simp add: interior_of_eq)

lemma openin_interior_of [simp]: "openin X (X interior_of S)"
  unfolding interior_of_def
  using openin_subopen by fastforce

lemma interior_of_interior_of [simp]:
   "X interior_of X interior_of S = X interior_of S"
  by (simp add: interior_of_eq)

lemma interior_of_subset: "X interior_of S \<subseteq> S"
  by (auto simp: interior_of_def)

lemma interior_of_subset_closure_of: "X interior_of S \<subseteq> X closure_of S"
  by (metis closure_of_subset_Int dual_order.trans interior_of_restrict interior_of_subset)

lemma subset_interior_of_eq: "S \<subseteq> X interior_of S \<longleftrightarrow> openin X S"
  by (metis interior_of_eq interior_of_subset subset_antisym)

lemma interior_of_mono: "S \<subseteq> T \<Longrightarrow> X interior_of S \<subseteq> X interior_of T"
  by (auto simp: interior_of_def)

lemma interior_of_maximal: "\<lbrakk>T \<subseteq> S; openin X T\<rbrakk> \<Longrightarrow> T \<subseteq> X interior_of S"
  by (auto simp: interior_of_def)

lemma interior_of_maximal_eq: "openin X T \<Longrightarrow> T \<subseteq> X interior_of S \<longleftrightarrow> T \<subseteq> S"
  by (meson interior_of_maximal interior_of_subset order_trans)

lemma interior_of_unique:
   "\<lbrakk>T \<subseteq> S; openin X T; \<And>T'. \<lbrakk>T' \<subseteq> S; openin X T'\<rbrakk> \<Longrightarrow> T' \<subseteq> T\<rbrakk> \<Longrightarrow> X interior_of S = T"
  by (simp add: interior_of_maximal_eq interior_of_subset subset_antisym)

lemma interior_of_subset_topspace: "X interior_of S \<subseteq> topspace X"
  by (simp add: openin_subset)

lemma interior_of_subset_subtopology: "(subtopology X S) interior_of T \<subseteq> S"
  by (meson openin_imp_subset openin_interior_of)

lemma interior_of_Int: "X interior_of (S \<inter> T) = X interior_of S \<inter> X interior_of T"  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    by (simp add: interior_of_mono)
  show "?rhs \<subseteq> ?lhs"
    by (meson inf_mono interior_of_maximal interior_of_subset openin_Int openin_interior_of)
qed

lemma interior_of_Inter_subset: "X interior_of (\<Inter>\<F>) \<subseteq> (\<Inter>S \<in> \<F>. X interior_of S)"
  by (simp add: INT_greatest Inf_lower interior_of_mono)

lemma union_interior_of_subset:
   "X interior_of S \<union> X interior_of T \<subseteq> X interior_of (S \<union> T)"
  by (simp add: interior_of_mono)

lemma interior_of_eq_empty:
   "X interior_of S = {} \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<subseteq> S \<longrightarrow> T = {})"
  by (metis bot.extremum_uniqueI interior_of_maximal interior_of_subset openin_interior_of)

lemma interior_of_eq_empty_alt:
   "X interior_of S = {} \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<noteq> {} \<longrightarrow> T - S \<noteq> {})"
  by (auto simp: interior_of_eq_empty)

lemma interior_of_Union_openin_subsets:
   "\<Union>{T. openin X T \<and> T \<subseteq> S} = X interior_of S"
  by (rule interior_of_unique [symmetric]) auto

lemma interior_of_complement:
   "X interior_of (topspace X - S) = topspace X - X closure_of S"
  by (auto simp: interior_of_def closure_of_def)

lemma interior_of_closure_of:
   "X interior_of S = topspace X - X closure_of (topspace X - S)"
  unfolding interior_of_complement [symmetric]
  by (metis Diff_Diff_Int interior_of_restrict)

lemma closure_of_interior_of:
   "X closure_of S = topspace X - X interior_of (topspace X - S)"
  by (simp add: interior_of_complement Diff_Diff_Int closure_of)

lemma closure_of_complement: "X closure_of (topspace X - S) = topspace X - X interior_of S"
  unfolding interior_of_def closure_of_def
  by (blast dest: openin_subset)

lemma interior_of_eq_empty_complement:
  "X interior_of S = {} \<longleftrightarrow> X closure_of (topspace X - S) = topspace X"
  using interior_of_subset_topspace [of X S] closure_of_complement by fastforce

lemma closure_of_eq_topspace:
   "X closure_of S = topspace X \<longleftrightarrow> X interior_of (topspace X - S) = {}"
  using closure_of_subset_topspace [of X S] interior_of_complement by fastforce

lemma interior_of_subtopology_subset:
     "U \<inter> X interior_of S \<subseteq> (subtopology X U) interior_of S"
  by (auto simp: interior_of_def openin_subtopology)

lemma interior_of_subtopology_subsets:
   "T \<subseteq> U \<Longrightarrow> T \<inter> (subtopology X U) interior_of S \<subseteq> (subtopology X T) interior_of S"
  by (metis inf.absorb_iff2 interior_of_subtopology_subset subtopology_subtopology)

lemma interior_of_subtopology_mono:
   "\<lbrakk>S \<subseteq> T; T \<subseteq> U\<rbrakk> \<Longrightarrow> (subtopology X U) interior_of S \<subseteq> (subtopology X T) interior_of S"
  by (metis dual_order.trans inf.orderE inf_commute interior_of_subset interior_of_subtopology_subsets)

lemma interior_of_subtopology_open:
  assumes "openin X U"
  shows "(subtopology X U) interior_of S = U \<inter> X interior_of S"
proof -
  have "\<forall>A. U \<inter> X closure_of (U \<inter> A) = U \<inter> X closure_of A"
    using assms openin_Int_closure_of_eq by blast
  then have "topspace X \<inter> U - U \<inter> X closure_of (topspace X \<inter> U - S) = U \<inter> (topspace X - X closure_of (topspace X - S))"
    by (metis (no_types) Diff_Int_distrib Int_Diff inf_commute)
  then show ?thesis
    unfolding interior_of_closure_of closure_of_subtopology_open topspace_subtopology
    using openin_Int_closure_of_eq [OF assms]
    by (metis assms closure_of_subtopology_open)
qed

lemma dense_intersects_open:
   "X closure_of S = topspace X \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<noteq> {} \<longrightarrow> S \<inter> T \<noteq> {})"
proof -
  have "X closure_of S = topspace X \<longleftrightarrow> (topspace X - X interior_of (topspace X - S) = topspace X)"
    by (simp add: closure_of_interior_of)
  also have "\<dots> \<longleftrightarrow> X interior_of (topspace X - S) = {}"
    by (simp add: closure_of_complement interior_of_eq_empty_complement)
  also have "\<dots> \<longleftrightarrow> (\<forall>T. openin X T \<and> T \<noteq> {} \<longrightarrow> S \<inter> T \<noteq> {})"
    unfolding interior_of_eq_empty_alt
    using openin_subset by fastforce
  finally show ?thesis .
qed

lemma interior_of_closedin_union_empty_interior_of:
  assumes "closedin X S" and disj: "X interior_of T = {}"
  shows "X interior_of (S \<union> T) = X interior_of S"
proof -
  have "X closure_of (topspace X - T) = topspace X"
    by (metis Diff_Diff_Int disj closure_of_eq_topspace closure_of_restrict interior_of_closure_of)
  then show ?thesis
    unfolding interior_of_closure_of
    by (metis Diff_Un Diff_subset assms(1) closedin_def closure_of_openin_Int_superset)
qed

lemma interior_of_union_eq_empty:
   "closedin X S
        \<Longrightarrow> (X interior_of (S \<union> T) = {} \<longleftrightarrow>
             X interior_of S = {} \<and> X interior_of T = {})"
  by (metis interior_of_closedin_union_empty_interior_of le_sup_iff subset_empty union_interior_of_subset)

lemma discrete_topology_interior_of [simp]:
    "(discrete_topology U) interior_of S = U \<inter> S"
  by (simp add: interior_of_restrict [of _ S] interior_of_eq)


subsection \<open>Frontier with respect to topological space \<close>

definition frontier_of :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixr "frontier'_of" 80)
  where "X frontier_of S \<equiv> X closure_of S - X interior_of S"

lemma frontier_of_closures:
     "X frontier_of S = X closure_of S \<inter> X closure_of (topspace X - S)"
  by (metis Diff_Diff_Int closure_of_complement closure_of_subset_topspace double_diff frontier_of_def interior_of_subset_closure_of)


lemma interior_of_union_frontier_of [simp]:
     "X interior_of S \<union> X frontier_of S = X closure_of S"
  by (simp add: frontier_of_def interior_of_subset_closure_of subset_antisym)

lemma frontier_of_restrict: "X frontier_of S = X frontier_of (topspace X \<inter> S)"
  by (metis closure_of_restrict frontier_of_def interior_of_restrict)

lemma closedin_frontier_of: "closedin X (X frontier_of S)"
  by (simp add: closedin_Int frontier_of_closures)

lemma frontier_of_subset_topspace: "X frontier_of S \<subseteq> topspace X"
  by (simp add: closedin_frontier_of closedin_subset)

lemma frontier_of_subset_subtopology: "(subtopology X S) frontier_of T \<subseteq> S"
  by (metis (no_types) closedin_derived_set closedin_frontier_of)

lemma frontier_of_subtopology_subset:
  "U \<inter> (subtopology X U) frontier_of S \<subseteq> (X frontier_of S)"
proof -
  have "U \<inter> X interior_of S - subtopology X U interior_of S = {}"
    by (simp add: interior_of_subtopology_subset)
  moreover have "X closure_of S \<inter> subtopology X U closure_of S = subtopology X U closure_of S"
    by (meson closure_of_subtopology_subset inf.absorb_iff2)
  ultimately show ?thesis
    unfolding frontier_of_def
    by blast
qed

lemma frontier_of_subtopology_mono:
   "\<lbrakk>S \<subseteq> T; T \<subseteq> U\<rbrakk> \<Longrightarrow> (subtopology X T) frontier_of S \<subseteq> (subtopology X U) frontier_of S"
    by (simp add: frontier_of_def Diff_mono closure_of_subtopology_mono interior_of_subtopology_mono)

lemma clopenin_eq_frontier_of:
   "closedin X S \<and> openin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> X frontier_of S = {}"
proof (cases "S \<subseteq> topspace X")
  case True
  then show ?thesis
    by (metis Diff_eq_empty_iff closure_of_eq closure_of_subset_eq frontier_of_def interior_of_eq interior_of_subset interior_of_union_frontier_of sup_bot_right)
next
  case False
  then show ?thesis
    by (simp add: frontier_of_closures openin_closedin_eq)
qed

lemma frontier_of_eq_empty:
     "S \<subseteq> topspace X \<Longrightarrow> (X frontier_of S = {} \<longleftrightarrow> closedin X S \<and> openin X S)"
  by (simp add: clopenin_eq_frontier_of)

lemma frontier_of_openin:
     "openin X S \<Longrightarrow> X frontier_of S = X closure_of S - S"
  by (metis (no_types) frontier_of_def interior_of_eq)

lemma frontier_of_openin_straddle_Int:
  assumes "openin X U" "U \<inter> X frontier_of S \<noteq> {}"
  shows "U \<inter> S \<noteq> {}" "U - S \<noteq> {}"
proof -
  have "U \<inter> (X closure_of S \<inter> X closure_of (topspace X - S)) \<noteq> {}"
    using assms by (simp add: frontier_of_closures)
  then show "U \<inter> S \<noteq> {}"
    using assms openin_Int_closure_of_eq_empty by fastforce
  show "U - S \<noteq> {}"
  proof -
    have "\<exists>A. X closure_of (A - S) \<inter> U \<noteq> {}"
      using \<open>U \<inter> (X closure_of S \<inter> X closure_of (topspace X - S)) \<noteq> {}\<close> by blast
    then have "\<not> U \<subseteq> S"
      by (metis Diff_disjoint Diff_eq_empty_iff Int_Diff assms(1) inf_commute openin_Int_closure_of_eq_empty)
    then show ?thesis
      by blast
  qed
qed

lemma frontier_of_subset_closedin: "closedin X S \<Longrightarrow> (X frontier_of S) \<subseteq> S"
  using closure_of_eq frontier_of_def by fastforce

lemma frontier_of_empty [simp]: "X frontier_of {} = {}"
  by (simp add: frontier_of_def)

lemma frontier_of_topspace [simp]: "X frontier_of topspace X = {}"
  by (simp add: frontier_of_def)

lemma frontier_of_subset_eq:
  assumes "S \<subseteq> topspace X"
  shows "(X frontier_of S) \<subseteq> S \<longleftrightarrow> closedin X S"
proof
  show "X frontier_of S \<subseteq> S \<Longrightarrow> closedin X S"
    by (metis assms closure_of_subset_eq interior_of_subset interior_of_union_frontier_of le_sup_iff)
  show "closedin X S \<Longrightarrow> X frontier_of S \<subseteq> S"
    by (simp add: frontier_of_subset_closedin)
qed

lemma frontier_of_complement: "X frontier_of (topspace X - S) = X frontier_of S"
  by (metis Diff_Diff_Int closure_of_restrict frontier_of_closures inf_commute)

lemma frontier_of_disjoint_eq:
  assumes "S \<subseteq> topspace X"
  shows "((X frontier_of S) \<inter> S = {} \<longleftrightarrow> openin X S)"
proof
  assume "X frontier_of S \<inter> S = {}"
  then have "closedin X (topspace X - S)"
    using assms closure_of_subset frontier_of_def interior_of_eq interior_of_subset by fastforce
  then show "openin X S"
    using assms by (simp add: openin_closedin)
next
  show "openin X S \<Longrightarrow> X frontier_of S \<inter> S = {}"
    by (simp add: Diff_Diff_Int closedin_def frontier_of_openin inf.absorb_iff2 inf_commute)
qed

lemma frontier_of_disjoint_eq_alt:
  "S \<subseteq> (topspace X - X frontier_of S) \<longleftrightarrow> openin X S"
proof (cases "S \<subseteq> topspace X")
  case True
  show ?thesis
    using True frontier_of_disjoint_eq by auto
next
  case False
  then show ?thesis
    by (meson Diff_subset openin_subset subset_trans)
qed

lemma frontier_of_Int:
     "X frontier_of (S \<inter> T) =
      X closure_of (S \<inter> T) \<inter> (X frontier_of S \<union> X frontier_of T)"
proof -
  have *: "U \<subseteq> S \<and> U \<subseteq> T \<Longrightarrow> U \<inter> (S \<inter> A \<union> T \<inter> B) = U \<inter> (A \<union> B)" for U S T A B :: "'a set"
    by blast
  show ?thesis
    by (simp add: frontier_of_closures closure_of_mono Diff_Int * flip: closure_of_Un)
qed

lemma frontier_of_Int_subset: "X frontier_of (S \<inter> T) \<subseteq> X frontier_of S \<union> X frontier_of T"
  by (simp add: frontier_of_Int)

lemma frontier_of_Int_closedin:
  assumes "closedin X S" "closedin X T" 
  shows "X frontier_of(S \<inter> T) = X frontier_of S \<inter> T \<union> S \<inter> X frontier_of T"  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    using assms by (force simp add: frontier_of_Int closedin_Int closure_of_closedin)
  show "?rhs \<subseteq> ?lhs"
    using assms frontier_of_subset_closedin
    by (auto simp add: frontier_of_Int closedin_Int closure_of_closedin)
qed

lemma frontier_of_Un_subset: "X frontier_of(S \<union> T) \<subseteq> X frontier_of S \<union> X frontier_of T"
  by (metis Diff_Un frontier_of_Int_subset frontier_of_complement)

lemma frontier_of_Union_subset:
   "finite \<F> \<Longrightarrow> X frontier_of (\<Union>\<F>) \<subseteq> (\<Union>T \<in> \<F>. X frontier_of T)"
proof (induction \<F> rule: finite_induct)
  case (insert A \<F>)
  then show ?case
    using frontier_of_Un_subset by fastforce
qed simp

lemma frontier_of_frontier_of_subset:
     "X frontier_of (X frontier_of S) \<subseteq> X frontier_of S"
  by (simp add: closedin_frontier_of frontier_of_subset_closedin)

lemma frontier_of_subtopology_open:
     "openin X U \<Longrightarrow> (subtopology X U) frontier_of S = U \<inter> X frontier_of S"
  by (simp add: Diff_Int_distrib closure_of_subtopology_open frontier_of_def interior_of_subtopology_open)

lemma discrete_topology_frontier_of [simp]:
     "(discrete_topology U) frontier_of S = {}"
  by (simp add: Diff_eq discrete_topology_closure_of frontier_of_closures)


subsection\<open>Locally finite collections\<close>

definition locally_finite_in
  where
 "locally_finite_in X \<A> \<longleftrightarrow>
        (\<Union>\<A> \<subseteq> topspace X) \<and>
        (\<forall>x \<in> topspace X. \<exists>V. openin X V \<and> x \<in> V \<and> finite {U \<in> \<A>. U \<inter> V \<noteq> {}})"

lemma finite_imp_locally_finite_in:
   "\<lbrakk>finite \<A>; \<Union>\<A> \<subseteq> topspace X\<rbrakk> \<Longrightarrow> locally_finite_in X \<A>"
  by (auto simp: locally_finite_in_def)

lemma locally_finite_in_subset:
  assumes "locally_finite_in X \<A>" "\<B> \<subseteq> \<A>"
  shows "locally_finite_in X \<B>"
proof -
  have "finite (\<A> \<inter> {U. U \<inter> V \<noteq> {}}) \<Longrightarrow> finite (\<B> \<inter> {U. U \<inter> V \<noteq> {}})" for V
    by (meson \<open>\<B> \<subseteq> \<A>\<close> finite_subset inf_le1 inf_le2 le_inf_iff subset_trans)
  then show ?thesis
    using assms unfolding locally_finite_in_def Int_def by fastforce
qed

lemma locally_finite_in_refinement:
  assumes \<A>: "locally_finite_in X \<A>" and f: "\<And>S. S \<in> \<A> \<Longrightarrow> f S \<subseteq> S"
  shows "locally_finite_in X (f ` \<A>)"
proof -
  show ?thesis
    unfolding locally_finite_in_def
  proof safe
    fix x
    assume "x \<in> topspace X"
    then obtain V where "openin X V" "x \<in> V" "finite {U \<in> \<A>. U \<inter> V \<noteq> {}}"
      using \<A> unfolding locally_finite_in_def by blast
    moreover have "{U \<in> \<A>. f U \<inter> V \<noteq> {}} \<subseteq> {U \<in> \<A>. U \<inter> V \<noteq> {}}" for V
      using f by blast
    ultimately have "finite {U \<in> \<A>. f U \<inter> V \<noteq> {}}"
      using finite_subset by blast
    moreover have "f ` {U \<in> \<A>. f U \<inter> V \<noteq> {}} = {U \<in> f ` \<A>. U \<inter> V \<noteq> {}}"
      by blast
    ultimately have "finite {U \<in> f ` \<A>. U \<inter> V \<noteq> {}}"
      by (metis (no_types, lifting) finite_imageI)
    then show "\<exists>V. openin X V \<and> x \<in> V \<and> finite {U \<in> f ` \<A>. U \<inter> V \<noteq> {}}"
      using \<open>openin X V\<close> \<open>x \<in> V\<close> by blast
  next
    show "\<And>x xa. \<lbrakk>xa \<in> \<A>; x \<in> f xa\<rbrakk> \<Longrightarrow> x \<in> topspace X"
      by (meson Sup_upper \<A> f locally_finite_in_def subset_iff)
  qed
qed

lemma locally_finite_in_subtopology:
  assumes \<A>: "locally_finite_in X \<A>" "\<Union>\<A> \<subseteq> S"
  shows "locally_finite_in (subtopology X S) \<A>"
  unfolding locally_finite_in_def
proof safe
  fix x
  assume x: "x \<in> topspace (subtopology X S)"
  then obtain V where "openin X V" "x \<in> V" and fin: "finite {U \<in> \<A>. U \<inter> V \<noteq> {}}"
    using \<A> unfolding locally_finite_in_def topspace_subtopology by blast
  show "\<exists>V. openin (subtopology X S) V \<and> x \<in> V \<and> finite {U \<in> \<A>. U \<inter> V \<noteq> {}}"
  proof (intro exI conjI)
    show "openin (subtopology X S) (S \<inter> V)"
      by (simp add: \<open>openin X V\<close> openin_subtopology_Int2)
    have "{U \<in> \<A>. U \<inter> (S \<inter> V) \<noteq> {}} \<subseteq> {U \<in> \<A>. U \<inter> V \<noteq> {}}"
      by auto
    with fin show "finite {U \<in> \<A>. U \<inter> (S \<inter> V) \<noteq> {}}"
      using finite_subset by auto
    show "x \<in> S \<inter> V"
      using x \<open>x \<in> V\<close> by (simp)
  qed
next
  show "\<And>x A. \<lbrakk>x \<in> A; A \<in> \<A>\<rbrakk> \<Longrightarrow> x \<in> topspace (subtopology X S)"
    using assms unfolding locally_finite_in_def topspace_subtopology by blast
qed


lemma closedin_locally_finite_Union:
  assumes clo: "\<And>S. S \<in> \<A> \<Longrightarrow> closedin X S" and \<A>: "locally_finite_in X \<A>"
  shows "closedin X (\<Union>\<A>)"
  using \<A> unfolding locally_finite_in_def closedin_def
proof clarify
  show "openin X (topspace X - \<Union>\<A>)"
  proof (subst openin_subopen, clarify)
    fix x
    assume "x \<in> topspace X" and "x \<notin> \<Union>\<A>"
    then obtain V where "openin X V" "x \<in> V" and fin: "finite {U \<in> \<A>. U \<inter> V \<noteq> {}}"
      using \<A> unfolding locally_finite_in_def by blast
    let ?T = "V - \<Union>{S \<in> \<A>. S \<inter> V \<noteq> {}}"
    show "\<exists>T. openin X T \<and> x \<in> T \<and> T \<subseteq> topspace X - \<Union>\<A>"
    proof (intro exI conjI)
      show "openin X ?T"
        by (metis (no_types, lifting) fin \<open>openin X V\<close> clo closedin_Union mem_Collect_eq openin_diff)
      show "x \<in> ?T"
        using \<open>x \<notin> \<Union>\<A>\<close> \<open>x \<in> V\<close> by auto
      show "?T \<subseteq> topspace X - \<Union>\<A>"
        using \<open>openin X V\<close> openin_subset by auto
    qed
  qed
qed

lemma locally_finite_in_closure:
  assumes \<A>: "locally_finite_in X \<A>"
  shows "locally_finite_in X ((\<lambda>S. X closure_of S) ` \<A>)"
  using \<A> unfolding locally_finite_in_def
proof (intro conjI; clarsimp)
  fix x A
  assume "x \<in> X closure_of A"
  then show "x \<in> topspace X"
    by (meson in_closure_of)
next
  fix x
  assume "x \<in> topspace X" and "\<Union>\<A> \<subseteq> topspace X"
  then obtain V where V: "openin X V" "x \<in> V" and fin: "finite {U \<in> \<A>. U \<inter> V \<noteq> {}}"
    using \<A> unfolding locally_finite_in_def by blast
  have eq: "{y \<in> f ` \<A>. Q y} = f ` {x. x \<in> \<A> \<and> Q(f x)}" for f Q
    by blast
  have eq2: "{A \<in> \<A>. X closure_of A \<inter> V \<noteq> {}} = {A \<in> \<A>. A \<inter> V \<noteq> {}}"
    using openin_Int_closure_of_eq_empty V  by blast
  have "finite {U \<in> (closure_of) X ` \<A>. U \<inter> V \<noteq> {}}"
    by (simp add: eq eq2 fin)
  with V show "\<exists>V. openin X V \<and> x \<in> V \<and> finite {U \<in> (closure_of) X ` \<A>. U \<inter> V \<noteq> {}}"
    by blast
qed

lemma closedin_Union_locally_finite_closure:
   "locally_finite_in X \<A> \<Longrightarrow> closedin X (\<Union>((\<lambda>S. X closure_of S) ` \<A>))"
  by (metis (mono_tags) closedin_closure_of closedin_locally_finite_Union imageE locally_finite_in_closure)

lemma closure_of_Union_subset: "\<Union>((\<lambda>S. X closure_of S) ` \<A>) \<subseteq> X closure_of (\<Union>\<A>)"
  by clarify (meson Union_upper closure_of_mono subsetD)

lemma closure_of_locally_finite_Union:
  assumes "locally_finite_in X \<A>" 
  shows "X closure_of (\<Union>\<A>) = \<Union>((\<lambda>S. X closure_of S) ` \<A>)"  
proof (rule closure_of_unique)
  show "\<Union> \<A> \<subseteq> \<Union> ((closure_of) X ` \<A>)"
    using assms by (simp add: SUP_upper2 Sup_le_iff closure_of_subset locally_finite_in_def)
  show "closedin X (\<Union> ((closure_of) X ` \<A>))"
    using assms by (simp add: closedin_Union_locally_finite_closure)
  show "\<And>T'. \<lbrakk>\<Union> \<A> \<subseteq> T'; closedin X T'\<rbrakk> \<Longrightarrow> \<Union> ((closure_of) X ` \<A>) \<subseteq> T'"
    by (simp add: Sup_le_iff closure_of_minimal)
qed


subsection\<^marker>\<open>tag important\<close> \<open>Continuous maps\<close>

text \<open>We will need to deal with continuous maps in terms of topologies and not in terms
of type classes, as defined below.\<close>

definition continuous_map where
  "continuous_map X Y f \<equiv>
     (\<forall>x \<in> topspace X. f x \<in> topspace Y) \<and>
     (\<forall>U. openin Y U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U})"

lemma continuous_map:
   "continuous_map X Y f \<longleftrightarrow>
        f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>U. openin Y U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U})"
  by (auto simp: continuous_map_def)

lemma continuous_map_image_subset_topspace:
   "continuous_map X Y f \<Longrightarrow> f ` (topspace X) \<subseteq> topspace Y"
  by (auto simp: continuous_map_def)

lemma continuous_map_on_empty: "topspace X = {} \<Longrightarrow> continuous_map X Y f"
  by (auto simp: continuous_map_def)

lemma continuous_map_closedin:
   "continuous_map X Y f \<longleftrightarrow>
         (\<forall>x \<in> topspace X. f x \<in> topspace Y) \<and>
         (\<forall>C. closedin Y C \<longrightarrow> closedin X {x \<in> topspace X. f x \<in> C})"
proof -
  have "(\<forall>U. openin Y U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U}) =
        (\<forall>C. closedin Y C \<longrightarrow> closedin X {x \<in> topspace X. f x \<in> C})"
    if "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y"
  proof -
    have eq: "{x \<in> topspace X. f x \<in> topspace Y \<and> f x \<notin> C} = (topspace X - {x \<in> topspace X. f x \<in> C})" for C
      using that by blast
    show ?thesis
    proof (intro iffI allI impI)
      fix C
      assume "\<forall>U. openin Y U \<longrightarrow> openin X {x \<in> topspace X. f x \<in> U}" and "closedin Y C"
      then have "openin X {x \<in> topspace X. f x \<in> topspace Y - C}" by blast
      then show "closedin X {x \<in> topspace X. f x \<in> C}"
        by (auto simp add: closedin_def eq)
    next
      fix U
      assume "\<forall>C. closedin Y C \<longrightarrow> closedin X {x \<in> topspace X. f x \<in> C}" and "openin Y U"
      then have "closedin X {x \<in> topspace X. f x \<in> topspace Y - U}" by blast
      then show "openin X {x \<in> topspace X. f x \<in> U}"
        by (auto simp add: openin_closedin_eq eq)
    qed
  qed
  then show ?thesis
    by (auto simp: continuous_map_def)
qed

lemma openin_continuous_map_preimage:
   "\<lbrakk>continuous_map X Y f; openin Y U\<rbrakk> \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U}"
  by (simp add: continuous_map_def)

lemma closedin_continuous_map_preimage:
   "\<lbrakk>continuous_map X Y f; closedin Y C\<rbrakk> \<Longrightarrow> closedin X {x \<in> topspace X. f x \<in> C}"
  by (simp add: continuous_map_closedin)

lemma openin_continuous_map_preimage_gen:
  assumes "continuous_map X Y f" "openin X U" "openin Y V"
  shows "openin X {x \<in> U. f x \<in> V}"
proof -
  have eq: "{x \<in> U. f x \<in> V} = U \<inter> {x \<in> topspace X. f x \<in> V}"
    using assms(2) openin_closedin_eq by fastforce
  show ?thesis
    unfolding eq
    using assms openin_continuous_map_preimage by fastforce
qed

lemma closedin_continuous_map_preimage_gen:
  assumes "continuous_map X Y f" "closedin X U" "closedin Y V"
  shows "closedin X {x \<in> U. f x \<in> V}"
proof -
  have eq: "{x \<in> U. f x \<in> V} = U \<inter> {x \<in> topspace X. f x \<in> V}"
    using assms(2) closedin_def by fastforce
  show ?thesis
    unfolding eq
    using assms closedin_continuous_map_preimage by fastforce
qed

lemma continuous_map_image_closure_subset:
  assumes "continuous_map X Y f"
  shows "f ` (X closure_of S) \<subseteq> Y closure_of f ` S"
proof -
  have *: "f ` (topspace X) \<subseteq> topspace Y"
    by (meson assms continuous_map)
  have "X closure_of T \<subseteq> {x \<in> X closure_of T. f x \<in> Y closure_of (f ` T)}" if "T \<subseteq> topspace X" for T
  proof (rule closure_of_minimal)
    show "T \<subseteq> {x \<in> X closure_of T. f x \<in> Y closure_of f ` T}"
      using closure_of_subset * that  by (fastforce simp: in_closure_of)
  next
    show "closedin X {x \<in> X closure_of T. f x \<in> Y closure_of f ` T}"
      using assms closedin_continuous_map_preimage_gen by fastforce
  qed
  then have "f ` (X closure_of (topspace X \<inter> S)) \<subseteq> Y closure_of (f ` (topspace X \<inter> S))"
    by blast
  also have "\<dots> \<subseteq> Y closure_of (topspace Y \<inter> f ` S)"
    using * by (blast intro!: closure_of_mono)
  finally have "f ` (X closure_of (topspace X \<inter> S)) \<subseteq> Y closure_of (topspace Y \<inter> f ` S)" .
  then show ?thesis
    by (metis closure_of_restrict)
qed

lemma continuous_map_subset_aux1: "continuous_map X Y f \<Longrightarrow>
       (\<forall>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
  using continuous_map_image_closure_subset by blast

lemma continuous_map_subset_aux2:
  assumes "\<forall>S. S \<subseteq> topspace X \<longrightarrow> f ` (X closure_of S) \<subseteq> Y closure_of f ` S"
  shows "continuous_map X Y f"
  unfolding continuous_map_closedin
proof (intro conjI ballI allI impI)
  fix x
  assume "x \<in> topspace X"
  then show "f x \<in> topspace Y"
    using assms closure_of_subset_topspace by fastforce
next
  fix C
  assume "closedin Y C"
  then show "closedin X {x \<in> topspace X. f x \<in> C}"
  proof (clarsimp simp flip: closure_of_subset_eq, intro conjI)
    fix x
    assume x: "x \<in> X closure_of {x \<in> topspace X. f x \<in> C}"
      and "C \<subseteq> topspace Y" and "Y closure_of C \<subseteq> C"
    show "x \<in> topspace X"
      by (meson x in_closure_of)
    have "{a \<in> topspace X. f a \<in> C} \<subseteq> topspace X"
      by simp
    moreover have "Y closure_of f ` {a \<in> topspace X. f a \<in> C} \<subseteq> C"
      by (simp add: \<open>closedin Y C\<close> closure_of_minimal image_subset_iff)
    ultimately have "f ` (X closure_of {a \<in> topspace X. f a \<in> C}) \<subseteq> C"
      using assms by blast
    then show "f x \<in> C"
      using x by auto
  qed
qed

lemma continuous_map_eq_image_closure_subset:
     "continuous_map X Y f \<longleftrightarrow> (\<forall>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
  using continuous_map_subset_aux1 continuous_map_subset_aux2 by metis

lemma continuous_map_eq_image_closure_subset_alt:
     "continuous_map X Y f \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<longrightarrow> f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
  using continuous_map_subset_aux1 continuous_map_subset_aux2 by metis

lemma continuous_map_eq_image_closure_subset_gen:
     "continuous_map X Y f \<longleftrightarrow>
        f ` (topspace X) \<subseteq> topspace Y \<and>
        (\<forall>S. f ` (X closure_of S) \<subseteq> Y closure_of f ` S)"
  using continuous_map_subset_aux1 continuous_map_subset_aux2 continuous_map_image_subset_topspace by metis

lemma continuous_map_closure_preimage_subset:
   "continuous_map X Y f
        \<Longrightarrow> X closure_of {x \<in> topspace X. f x \<in> T}
            \<subseteq> {x \<in> topspace X. f x \<in> Y closure_of T}"
  unfolding continuous_map_closedin
  by (rule closure_of_minimal) (use in_closure_of in \<open>fastforce+\<close>)


lemma continuous_map_frontier_frontier_preimage_subset:
  assumes "continuous_map X Y f"
  shows "X frontier_of {x \<in> topspace X. f x \<in> T} \<subseteq> {x \<in> topspace X. f x \<in> Y frontier_of T}"
proof -
  have eq: "topspace X - {x \<in> topspace X. f x \<in> T} = {x \<in> topspace X. f x \<in> topspace Y - T}"
    using assms unfolding continuous_map_def by blast
  have "X closure_of {x \<in> topspace X. f x \<in> T} \<subseteq> {x \<in> topspace X. f x \<in> Y closure_of T}"
    by (simp add: assms continuous_map_closure_preimage_subset)
  moreover
  have "X closure_of (topspace X - {x \<in> topspace X. f x \<in> T}) \<subseteq> {x \<in> topspace X. f x \<in> Y closure_of (topspace Y - T)}"
    using continuous_map_closure_preimage_subset [OF assms] eq by presburger
  ultimately show ?thesis
    by (auto simp: frontier_of_closures)
qed

lemma topology_finer_continuous_id:
  assumes "topspace X = topspace Y" 
  shows "(\<forall>S. openin X S \<longrightarrow> openin Y S) \<longleftrightarrow> continuous_map Y X id"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding continuous_map_def
    using assms openin_subopen openin_subset by fastforce
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding continuous_map_def
    using assms openin_subopen topspace_def by fastforce
qed

lemma continuous_map_const [simp]:
   "continuous_map X Y (\<lambda>x. C) \<longleftrightarrow> topspace X = {} \<or> C \<in> topspace Y"
proof (cases "topspace X = {}")
  case False
  show ?thesis
  proof (cases "C \<in> topspace Y")
    case True
    with openin_subopen show ?thesis
      by (auto simp: continuous_map_def)
  next
    case False
    then show ?thesis
      unfolding continuous_map_def by fastforce
  qed
qed (auto simp: continuous_map_on_empty)

declare continuous_map_const [THEN iffD2, continuous_intros]

lemma continuous_map_compose [continuous_intros]:
  assumes f: "continuous_map X X' f" and g: "continuous_map X' X'' g"
  shows "continuous_map X X'' (g \<circ> f)"
  unfolding continuous_map_def
proof (intro conjI ballI allI impI)
  fix x
  assume "x \<in> topspace X"
  then show "(g \<circ> f) x \<in> topspace X''"
    using assms unfolding continuous_map_def by force
next
  fix U
  assume "openin X'' U"
  have eq: "{x \<in> topspace X. (g \<circ> f) x \<in> U} = {x \<in> topspace X. f x \<in> {y. y \<in> topspace X' \<and> g y \<in> U}}"
    by auto (meson f continuous_map_def)
  show "openin X {x \<in> topspace X. (g \<circ> f) x \<in> U}"
    unfolding eq
    using assms unfolding continuous_map_def
    using \<open>openin X'' U\<close> by blast
qed

lemma continuous_map_eq:
  assumes "continuous_map X X' f" and "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x" shows "continuous_map X X' g"
proof -
  have eq: "{x \<in> topspace X. f x \<in> U} = {x \<in> topspace X. g x \<in> U}" for U
    using assms by auto
  show ?thesis
    using assms by (simp add: continuous_map_def eq)
qed

lemma restrict_continuous_map [simp]:
     "topspace X \<subseteq> S \<Longrightarrow> continuous_map X X' (restrict f S) \<longleftrightarrow> continuous_map X X' f"
  by (auto simp: elim!: continuous_map_eq)

lemma continuous_map_in_subtopology:
  "continuous_map X (subtopology X' S) f \<longleftrightarrow> continuous_map X X' f \<and> f ` (topspace X) \<subseteq> S"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof -
    have "\<And>A. f ` (X closure_of A) \<subseteq> subtopology X' S closure_of f ` A"
      by (meson L continuous_map_image_closure_subset)
    then show ?thesis
      by (metis (no_types) closure_of_subset_subtopology closure_of_subtopology_subset closure_of_topspace continuous_map_eq_image_closure_subset dual_order.trans)
  qed
next
  assume R: ?rhs
  then have eq: "{x \<in> topspace X. f x \<in> U} = {x \<in> topspace X. f x \<in> U \<and> f x \<in> S}" for U
    by auto
  show ?lhs
    using R
    unfolding continuous_map
    by (auto simp: openin_subtopology eq)
qed


lemma continuous_map_from_subtopology:
     "continuous_map X X' f \<Longrightarrow> continuous_map (subtopology X S) X' f"
  by (auto simp: continuous_map openin_subtopology)

lemma continuous_map_into_fulltopology:
   "continuous_map X (subtopology X' T) f \<Longrightarrow> continuous_map X X' f"
  by (auto simp: continuous_map_in_subtopology)

lemma continuous_map_into_subtopology:
   "\<lbrakk>continuous_map X X' f; f ` topspace X \<subseteq> T\<rbrakk> \<Longrightarrow> continuous_map X (subtopology X' T) f"
  by (auto simp: continuous_map_in_subtopology)

lemma continuous_map_from_subtopology_mono:
     "\<lbrakk>continuous_map (subtopology X T) X' f; S \<subseteq> T\<rbrakk>
      \<Longrightarrow> continuous_map (subtopology X S) X' f"
  by (metis inf.absorb_iff2 continuous_map_from_subtopology subtopology_subtopology)

lemma continuous_map_from_discrete_topology [simp]:
  "continuous_map (discrete_topology U) X f \<longleftrightarrow> f ` U \<subseteq> topspace X"
  by (auto simp: continuous_map_def)

lemma continuous_map_iff_continuous [simp]: "continuous_map (top_of_set S) euclidean g = continuous_on S g"
  by (fastforce simp add: continuous_map openin_subtopology continuous_on_open_invariant)

lemma continuous_map_iff_continuous2 [simp]: "continuous_map euclidean euclidean g = continuous_on UNIV g"
  by (metis continuous_map_iff_continuous subtopology_UNIV)

lemma continuous_map_openin_preimage_eq:
   "continuous_map X Y f \<longleftrightarrow>
        f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>U. openin Y U \<longrightarrow> openin X (topspace X \<inter> f -` U))"
  by (auto simp: continuous_map_def vimage_def Int_def)

lemma continuous_map_closedin_preimage_eq:
   "continuous_map X Y f \<longleftrightarrow>
        f ` (topspace X) \<subseteq> topspace Y \<and> (\<forall>U. closedin Y U \<longrightarrow> closedin X (topspace X \<inter> f -` U))"
  by (auto simp: continuous_map_closedin vimage_def Int_def)

lemma continuous_map_square_root: "continuous_map euclideanreal euclideanreal sqrt"
  by (simp add: continuous_at_imp_continuous_on isCont_real_sqrt)

lemma continuous_map_sqrt [continuous_intros]:
   "continuous_map X euclideanreal f \<Longrightarrow> continuous_map X euclideanreal (\<lambda>x. sqrt(f x))"
  by (meson continuous_map_compose continuous_map_eq continuous_map_square_root o_apply)

lemma continuous_map_id [simp, continuous_intros]: "continuous_map X X id"
  unfolding continuous_map_def  using openin_subopen topspace_def by fastforce

declare continuous_map_id [unfolded id_def, simp, continuous_intros]

lemma continuous_map_id_subt [simp]: "continuous_map (subtopology X S) X id"
  by (simp add: continuous_map_from_subtopology)

declare continuous_map_id_subt [unfolded id_def, simp]


lemma\<^marker>\<open>tag important\<close> continuous_map_alt:
   "continuous_map T1 T2 f 
    = ((\<forall>U. openin T2 U \<longrightarrow> openin T1 (f -` U \<inter> topspace T1)) \<and> f ` topspace T1 \<subseteq> topspace T2)"
  by (auto simp: continuous_map_def vimage_def image_def Collect_conj_eq inf_commute)

lemma continuous_map_open [intro]:
  "continuous_map T1 T2 f \<Longrightarrow> openin T2 U \<Longrightarrow> openin T1 (f-`U \<inter> topspace(T1))"
  unfolding continuous_map_alt by auto

lemma continuous_map_preimage_topspace [intro]:
  assumes "continuous_map T1 T2 f"
  shows "f-`(topspace T2) \<inter> topspace T1 = topspace T1"
using assms unfolding continuous_map_def by auto



subsection\<open>Open and closed maps (not a priori assumed continuous)\<close>

definition open_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "open_map X1 X2 f \<equiv> \<forall>U. openin X1 U \<longrightarrow> openin X2 (f ` U)"

definition closed_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "closed_map X1 X2 f \<equiv> \<forall>U. closedin X1 U \<longrightarrow> closedin X2 (f ` U)"

lemma open_map_imp_subset_topspace:
     "open_map X1 X2 f \<Longrightarrow> f ` (topspace X1) \<subseteq> topspace X2"
  unfolding open_map_def by (simp add: openin_subset)

lemma open_map_on_empty:
   "topspace X = {} \<Longrightarrow> open_map X Y f"
  by (metis empty_iff imageE in_mono open_map_def openin_subopen openin_subset)

lemma closed_map_on_empty:
   "topspace X = {} \<Longrightarrow> closed_map X Y f"
  by (simp add: closed_map_def closedin_topspace_empty)

lemma closed_map_const:
   "closed_map X Y (\<lambda>x. c) \<longleftrightarrow> topspace X = {} \<or> closedin Y {c}"
proof (cases "topspace X = {}")
  case True
  then show ?thesis
    by (simp add: closed_map_on_empty)
next
  case False
  then show ?thesis
    by (auto simp: closed_map_def image_constant_conv)
qed

lemma open_map_imp_subset:
    "\<lbrakk>open_map X1 X2 f; S \<subseteq> topspace X1\<rbrakk> \<Longrightarrow> f ` S \<subseteq> topspace X2"
  by (meson order_trans open_map_imp_subset_topspace subset_image_iff)

lemma topology_finer_open_id:
     "(\<forall>S. openin X S \<longrightarrow> openin X' S) \<longleftrightarrow> open_map X X' id"
  unfolding open_map_def by auto

lemma open_map_id: "open_map X X id"
  unfolding open_map_def by auto

lemma open_map_eq:
     "\<lbrakk>open_map X X' f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> open_map X X' g"
  unfolding open_map_def
  by (metis image_cong openin_subset subset_iff)

lemma open_map_inclusion_eq:
  "open_map (subtopology X S) X id \<longleftrightarrow> openin X (topspace X \<inter> S)"
proof -
  have *: "openin X (T \<inter> S)" if "openin X (S \<inter> topspace X)" "openin X T" for T
  proof -
    have "T \<subseteq> topspace X"
      using that by (simp add: openin_subset)
    with that show "openin X (T \<inter> S)"
      by (metis inf.absorb1 inf.left_commute inf_commute openin_Int)
  qed
  show ?thesis
    by (fastforce simp add: open_map_def Int_commute openin_subtopology_alt intro: *)
qed

lemma open_map_inclusion:
     "openin X S \<Longrightarrow> open_map (subtopology X S) X id"
  by (simp add: open_map_inclusion_eq openin_Int)

lemma open_map_compose:
     "\<lbrakk>open_map X X' f; open_map X' X'' g\<rbrakk> \<Longrightarrow> open_map X X'' (g \<circ> f)"
  by (metis (no_types, lifting) image_comp open_map_def)

lemma closed_map_imp_subset_topspace:
     "closed_map X1 X2 f \<Longrightarrow> f ` (topspace X1) \<subseteq> topspace X2"
  by (simp add: closed_map_def closedin_subset)

lemma closed_map_imp_subset:
     "\<lbrakk>closed_map X1 X2 f; S \<subseteq> topspace X1\<rbrakk> \<Longrightarrow> f ` S \<subseteq> topspace X2"
  using closed_map_imp_subset_topspace by blast

lemma topology_finer_closed_id:
    "(\<forall>S. closedin X S \<longrightarrow> closedin X' S) \<longleftrightarrow> closed_map X X' id"
  by (simp add: closed_map_def)

lemma closed_map_id: "closed_map X X id"
  by (simp add: closed_map_def)

lemma closed_map_eq:
   "\<lbrakk>closed_map X X' f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> closed_map X X' g"
  unfolding closed_map_def
  by (metis image_cong closedin_subset subset_iff)

lemma closed_map_compose:
    "\<lbrakk>closed_map X X' f; closed_map X' X'' g\<rbrakk> \<Longrightarrow> closed_map X X'' (g \<circ> f)"
  by (metis (no_types, lifting) closed_map_def image_comp)

lemma closed_map_inclusion_eq:
   "closed_map (subtopology X S) X id \<longleftrightarrow>
        closedin X (topspace X \<inter> S)"
proof -
  have *: "closedin X (T \<inter> S)" if "closedin X (S \<inter> topspace X)" "closedin X T" for T
  proof -
    have "T \<subseteq> topspace X"
      using that by (simp add: closedin_subset)
    with that show "closedin X (T \<inter> S)"
      by (metis inf.absorb1 inf.left_commute inf_commute closedin_Int)
  qed
  show ?thesis
    by (fastforce simp add: closed_map_def Int_commute closedin_subtopology_alt intro: *)
qed

lemma closed_map_inclusion: "closedin X S \<Longrightarrow> closed_map (subtopology X S) X id"
  by (simp add: closed_map_inclusion_eq closedin_Int)

lemma open_map_into_subtopology:
    "\<lbrakk>open_map X X' f; f ` topspace X \<subseteq> S\<rbrakk> \<Longrightarrow> open_map X (subtopology X' S) f"
  unfolding open_map_def openin_subtopology
  using openin_subset by fastforce

lemma closed_map_into_subtopology:
    "\<lbrakk>closed_map X X' f; f ` topspace X \<subseteq> S\<rbrakk> \<Longrightarrow> closed_map X (subtopology X' S) f"
  unfolding closed_map_def closedin_subtopology
  using closedin_subset by fastforce

lemma open_map_into_discrete_topology:
    "open_map X (discrete_topology U) f \<longleftrightarrow> f ` (topspace X) \<subseteq> U"
  unfolding open_map_def openin_discrete_topology using openin_subset by blast

lemma closed_map_into_discrete_topology:
    "closed_map X (discrete_topology U) f \<longleftrightarrow> f ` (topspace X) \<subseteq> U"
  unfolding closed_map_def closedin_discrete_topology using closedin_subset by blast

lemma bijective_open_imp_closed_map:
     "\<lbrakk>open_map X X' f; f ` (topspace X) = topspace X'; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> closed_map X X' f"
  unfolding open_map_def closed_map_def closedin_def
  by auto (metis Diff_subset inj_on_image_set_diff)

lemma bijective_closed_imp_open_map:
     "\<lbrakk>closed_map X X' f; f ` (topspace X) = topspace X'; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> open_map X X' f"
  unfolding closed_map_def open_map_def openin_closedin_eq
  by auto (metis Diff_subset inj_on_image_set_diff)

lemma open_map_from_subtopology:
     "\<lbrakk>open_map X X' f; openin X U\<rbrakk> \<Longrightarrow> open_map (subtopology X U) X' f"
  unfolding open_map_def openin_subtopology_alt by blast

lemma closed_map_from_subtopology:
     "\<lbrakk>closed_map X X' f; closedin X U\<rbrakk> \<Longrightarrow> closed_map (subtopology X U) X' f"
  unfolding closed_map_def closedin_subtopology_alt by blast

lemma open_map_restriction:
  assumes f: "open_map X X' f" and U: "{x \<in> topspace X. f x \<in> V} = U"
  shows "open_map (subtopology X U) (subtopology X' V) f"
  unfolding open_map_def
proof clarsimp
  fix W
  assume "openin (subtopology X U) W"
  then obtain T where "openin X T" "W = T \<inter> U"
    by (meson openin_subtopology)
  with f U have "f ` W = (f ` T) \<inter> V"
    unfolding open_map_def openin_closedin_eq by auto
  then show "openin (subtopology X' V) (f ` W)"
    by (metis \<open>openin X T\<close> f open_map_def openin_subtopology_Int)
qed

lemma closed_map_restriction:
  assumes f: "closed_map X X' f" and U: "{x \<in> topspace X. f x \<in> V} = U"
  shows "closed_map (subtopology X U) (subtopology X' V) f"
  unfolding closed_map_def
proof clarsimp
  fix W
  assume "closedin (subtopology X U) W"
  then obtain T where "closedin X T" "W = T \<inter> U"
    by (meson closedin_subtopology)
  with f U have "f ` W = (f ` T) \<inter> V"
    unfolding closed_map_def closedin_def by auto
  then show "closedin (subtopology X' V) (f ` W)"
    by (metis \<open>closedin X T\<close> closed_map_def closedin_subtopology f)
qed

subsection\<open>Quotient maps\<close>
                                      
definition quotient_map where
 "quotient_map X X' f \<longleftrightarrow>
        f ` (topspace X) = topspace X' \<and>
        (\<forall>U. U \<subseteq> topspace X' \<longrightarrow> (openin X {x. x \<in> topspace X \<and> f x \<in> U} \<longleftrightarrow> openin X' U))"

lemma quotient_map_eq:
  assumes "quotient_map X X' f" "\<And>x. x \<in> topspace X \<Longrightarrow> f x = g x"
  shows "quotient_map X X' g"
proof -
  have eq: "{x \<in> topspace X. f x \<in> U} = {x \<in> topspace X. g x \<in> U}" for U
    using assms by auto
  show ?thesis
  using assms
  unfolding quotient_map_def
  by (metis (mono_tags, lifting) eq image_cong)
qed

lemma quotient_map_compose:
  assumes f: "quotient_map X X' f" and g: "quotient_map X' X'' g"
  shows "quotient_map X X'' (g \<circ> f)"
  unfolding quotient_map_def
proof (intro conjI allI impI)
  show "(g \<circ> f) ` topspace X = topspace X''"
    using assms by (simp only: image_comp [symmetric]) (simp add: quotient_map_def)
next
  fix U''
  assume "U'' \<subseteq> topspace X''"
  define U' where "U' \<equiv> {y \<in> topspace X'. g y \<in> U''}"
  have "U' \<subseteq> topspace X'"
    by (auto simp add: U'_def)
  then have U': "openin X {x \<in> topspace X. f x \<in> U'} = openin X' U'"
    using assms unfolding quotient_map_def by simp
  have eq: "{x \<in> topspace X. f x \<in> topspace X' \<and> g (f x) \<in> U''} = {x \<in> topspace X. (g \<circ> f) x \<in> U''}"
    using f quotient_map_def by fastforce
  have "openin X {x \<in> topspace X. (g \<circ> f) x \<in> U''} = openin X {x \<in> topspace X. f x \<in> U'}"
    using assms  by (simp add: quotient_map_def U'_def eq)
  also have "\<dots> = openin X'' U''"
    using U'_def \<open>U'' \<subseteq> topspace X''\<close> U' g quotient_map_def by fastforce
  finally show "openin X {x \<in> topspace X. (g \<circ> f) x \<in> U''} = openin X'' U''" .
qed

lemma quotient_map_from_composition:
  assumes f: "continuous_map X X' f" and g: "continuous_map X' X'' g" and gf: "quotient_map X X'' (g \<circ> f)"
  shows  "quotient_map X' X'' g"
  unfolding quotient_map_def
proof (intro conjI allI impI)
  show "g ` topspace X' = topspace X''"
    using assms unfolding continuous_map_def quotient_map_def by fastforce
next
  fix U'' :: "'c set"
  assume U'': "U'' \<subseteq> topspace X''"
  have eq: "{x \<in> topspace X. g (f x) \<in> U''} = {x \<in> topspace X. f x \<in> {y. y \<in> topspace X' \<and> g y \<in> U''}}"
    using continuous_map_def f by fastforce
  show "openin X' {x \<in> topspace X'. g x \<in> U''} = openin X'' U''"
    using assms unfolding continuous_map_def quotient_map_def
    by (metis (mono_tags, lifting) Collect_cong U'' comp_apply eq)
qed

lemma quotient_imp_continuous_map:
    "quotient_map X X' f \<Longrightarrow> continuous_map X X' f"
  by (simp add: continuous_map openin_subset quotient_map_def)

lemma quotient_imp_surjective_map:
    "quotient_map X X' f \<Longrightarrow> f ` (topspace X) = topspace X'"
  by (simp add: quotient_map_def)

lemma quotient_map_closedin:
  "quotient_map X X' f \<longleftrightarrow>
        f ` (topspace X) = topspace X' \<and>
        (\<forall>U. U \<subseteq> topspace X' \<longrightarrow> (closedin X {x. x \<in> topspace X \<and> f x \<in> U} \<longleftrightarrow> closedin X' U))"
proof -
  have eq: "(topspace X - {x \<in> topspace X. f x \<in> U'}) = {x \<in> topspace X. f x \<in> topspace X' \<and> f x \<notin> U'}"
    if "f ` topspace X = topspace X'" "U' \<subseteq> topspace X'" for U'
      using that by auto
  have "(\<forall>U\<subseteq>topspace X'. openin X {x \<in> topspace X. f x \<in> U} = openin X' U) =
          (\<forall>U\<subseteq>topspace X'. closedin X {x \<in> topspace X. f x \<in> U} = closedin X' U)"
    if "f ` topspace X = topspace X'"
  proof (rule iffI; intro allI impI subsetI)
    fix U'
    assume *[rule_format]: "\<forall>U\<subseteq>topspace X'. openin X {x \<in> topspace X. f x \<in> U} = openin X' U"
      and U': "U' \<subseteq> topspace X'"
    show "closedin X {x \<in> topspace X. f x \<in> U'} = closedin X' U'"
      using U'  by (auto simp add: closedin_def simp flip: * [of "topspace X' - U'"] eq [OF that])
  next
    fix U' :: "'b set"
    assume *[rule_format]: "\<forall>U\<subseteq>topspace X'. closedin X {x \<in> topspace X. f x \<in> U} = closedin X' U"
      and U': "U' \<subseteq> topspace X'"
    show "openin X {x \<in> topspace X. f x \<in> U'} = openin X' U'"
      using U'  by (auto simp add: openin_closedin_eq simp flip: * [of "topspace X' - U'"] eq [OF that])
  qed
  then show ?thesis
    unfolding quotient_map_def by force
qed

lemma continuous_open_imp_quotient_map:
  assumes "continuous_map X X' f" and om: "open_map X X' f" and feq: "f ` (topspace X) = topspace X'"
  shows "quotient_map X X' f"
proof -
  { fix U
    assume U: "U \<subseteq> topspace X'" and "openin X {x \<in> topspace X. f x \<in> U}"
    then have ope: "openin X' (f ` {x \<in> topspace X. f x \<in> U})"
      using om unfolding open_map_def by blast
    then have "openin X' U"
      using U feq by (subst openin_subopen) force
  }
  moreover have "openin X {x \<in> topspace X. f x \<in> U}" if "U \<subseteq> topspace X'" and "openin X' U" for U
    using that assms unfolding continuous_map_def by blast
  ultimately show ?thesis
    unfolding quotient_map_def using assms by blast
qed

lemma continuous_closed_imp_quotient_map:
  assumes "continuous_map X X' f" and om: "closed_map X X' f" and feq: "f ` (topspace X) = topspace X'"
  shows "quotient_map X X' f"
proof -
  have "f ` {x \<in> topspace X. f x \<in> U} = U" if "U \<subseteq> topspace X'" for U
    using that feq by auto
  with assms show ?thesis
    unfolding quotient_map_closedin closed_map_def continuous_map_closedin by auto
qed

lemma continuous_open_quotient_map:
   "\<lbrakk>continuous_map X X' f; open_map X X' f\<rbrakk> \<Longrightarrow> quotient_map X X' f \<longleftrightarrow> f ` (topspace X) = topspace X'"
  by (meson continuous_open_imp_quotient_map quotient_map_def)

lemma continuous_closed_quotient_map:
     "\<lbrakk>continuous_map X X' f; closed_map X X' f\<rbrakk> \<Longrightarrow> quotient_map X X' f \<longleftrightarrow> f ` (topspace X) = topspace X'"
  by (meson continuous_closed_imp_quotient_map quotient_map_def)

lemma injective_quotient_map:
  assumes "inj_on f (topspace X)"
  shows "quotient_map X X' f \<longleftrightarrow>
         continuous_map X X' f \<and> open_map X X' f \<and> closed_map X X' f \<and> f ` (topspace X) = topspace X'"
         (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have "open_map X X' f"
  proof (clarsimp simp add: open_map_def)
    fix U
    assume "openin X U"
    then have "U \<subseteq> topspace X"
      by (simp add: openin_subset)
    moreover have "{x \<in> topspace X. f x \<in> f ` U} = U"
      using \<open>U \<subseteq> topspace X\<close> assms inj_onD by fastforce
    ultimately show "openin X' (f ` U)"
      using L unfolding quotient_map_def
      by (metis (no_types, lifting) Collect_cong \<open>openin X U\<close> image_mono)
  qed
  moreover have "closed_map X X' f"
  proof (clarsimp simp add: closed_map_def)
    fix U
    assume "closedin X U"
    then have "U \<subseteq> topspace X"
      by (simp add: closedin_subset)
    moreover have "{x \<in> topspace X. f x \<in> f ` U} = U"
      using \<open>U \<subseteq> topspace X\<close> assms inj_onD by fastforce
    ultimately show "closedin X' (f ` U)"
      using L unfolding quotient_map_closedin
      by (metis (no_types, lifting) Collect_cong \<open>closedin X U\<close> image_mono)
  qed
  ultimately show ?rhs
    using L by (simp add: quotient_imp_continuous_map quotient_imp_surjective_map)
next
  assume ?rhs
  then show ?lhs
    by (simp add: continuous_closed_imp_quotient_map)
qed

lemma continuous_compose_quotient_map:
  assumes f: "quotient_map X X' f" and g: "continuous_map X X'' (g \<circ> f)"
  shows "continuous_map X' X'' g"
  unfolding quotient_map_def continuous_map_def
proof (intro conjI ballI allI impI)
  show "\<And>x'. x' \<in> topspace X' \<Longrightarrow> g x' \<in> topspace X''"
    using assms unfolding quotient_map_def
    by (metis (no_types, hide_lams) continuous_map_image_subset_topspace image_comp image_subset_iff)
next
  fix U'' :: "'c set"
  assume U'': "openin X'' U''"
  have "f ` topspace X = topspace X'"
    by (simp add: f quotient_imp_surjective_map)
  then have eq: "{x \<in> topspace X. f x \<in> topspace X' \<and> g (f x) \<in> U} = {x \<in> topspace X. g (f x) \<in> U}" for U
    by auto
  have "openin X {x \<in> topspace X. f x \<in> topspace X' \<and> g (f x) \<in> U''}"
    unfolding eq using U'' g openin_continuous_map_preimage by fastforce
  then have *: "openin X {x \<in> topspace X. f x \<in> {x \<in> topspace X'. g x \<in> U''}}"
    by auto
  show "openin X' {x \<in> topspace X'. g x \<in> U''}"
    using f unfolding quotient_map_def
    by (metis (no_types) Collect_subset *)
qed

lemma continuous_compose_quotient_map_eq:
   "quotient_map X X' f \<Longrightarrow> continuous_map X X'' (g \<circ> f) \<longleftrightarrow> continuous_map X' X'' g"
  using continuous_compose_quotient_map continuous_map_compose quotient_imp_continuous_map by blast

lemma quotient_map_compose_eq:
   "quotient_map X X' f \<Longrightarrow> quotient_map X X'' (g \<circ> f) \<longleftrightarrow> quotient_map X' X'' g"
  by (meson continuous_compose_quotient_map_eq quotient_imp_continuous_map quotient_map_compose quotient_map_from_composition)

lemma quotient_map_restriction:
  assumes quo: "quotient_map X Y f" and U: "{x \<in> topspace X. f x \<in> V} = U" and disj: "openin Y V \<or> closedin Y V"
 shows "quotient_map (subtopology X U) (subtopology Y V) f"
  using disj
proof
  assume V: "openin Y V"
  with U have sub: "U \<subseteq> topspace X" "V \<subseteq> topspace Y"
    by (auto simp: openin_subset)
  have fim: "f ` topspace X = topspace Y"
     and Y: "\<And>U. U \<subseteq> topspace Y \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U} = openin Y U"
    using quo unfolding quotient_map_def by auto
  have "openin X U"
    using U V Y sub(2) by blast
  show ?thesis
    unfolding quotient_map_def
  proof (intro conjI allI impI)
    show "f ` topspace (subtopology X U) = topspace (subtopology Y V)"
      using sub U fim by (auto)
  next
    fix Y' :: "'b set"
    assume "Y' \<subseteq> topspace (subtopology Y V)"
    then have "Y' \<subseteq> topspace Y" "Y' \<subseteq> V"
      by (simp_all)
    then have eq: "{x \<in> topspace X. x \<in> U \<and> f x \<in> Y'} = {x \<in> topspace X. f x \<in> Y'}"
      using U by blast
    then show "openin (subtopology X U) {x \<in> topspace (subtopology X U). f x \<in> Y'} = openin (subtopology Y V) Y'"
      using U V Y \<open>openin X U\<close>  \<open>Y' \<subseteq> topspace Y\<close> \<open>Y' \<subseteq> V\<close>
      by (simp add: openin_open_subtopology eq) (auto simp: openin_closedin_eq)
  qed
next
  assume V: "closedin Y V"
  with U have sub: "U \<subseteq> topspace X" "V \<subseteq> topspace Y"
    by (auto simp: closedin_subset)
  have fim: "f ` topspace X = topspace Y"
     and Y: "\<And>U. U \<subseteq> topspace Y \<Longrightarrow> closedin X {x \<in> topspace X. f x \<in> U} = closedin Y U"
    using quo unfolding quotient_map_closedin by auto
  have "closedin X U"
    using U V Y sub(2) by blast
  show ?thesis
    unfolding quotient_map_closedin
  proof (intro conjI allI impI)
    show "f ` topspace (subtopology X U) = topspace (subtopology Y V)"
      using sub U fim by (auto)
  next
    fix Y' :: "'b set"
    assume "Y' \<subseteq> topspace (subtopology Y V)"
    then have "Y' \<subseteq> topspace Y" "Y' \<subseteq> V"
      by (simp_all)
    then have eq: "{x \<in> topspace X. x \<in> U \<and> f x \<in> Y'} = {x \<in> topspace X. f x \<in> Y'}"
      using U by blast
    then show "closedin (subtopology X U) {x \<in> topspace (subtopology X U). f x \<in> Y'} = closedin (subtopology Y V) Y'"
      using U V Y \<open>closedin X U\<close>  \<open>Y' \<subseteq> topspace Y\<close> \<open>Y' \<subseteq> V\<close>
      by (simp add: closedin_closed_subtopology eq) (auto simp: closedin_def)
  qed
qed

lemma quotient_map_saturated_open:
     "quotient_map X Y f \<longleftrightarrow>
        continuous_map X Y f \<and> f ` (topspace X) = topspace Y \<and>
        (\<forall>U. openin X U \<and> {x \<in> topspace X. f x \<in> f ` U} \<subseteq> U \<longrightarrow> openin Y (f ` U))"
     (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have fim: "f ` topspace X = topspace Y"
    and Y: "\<And>U. U \<subseteq> topspace Y \<Longrightarrow> openin Y U = openin X {x \<in> topspace X. f x \<in> U}"
    unfolding quotient_map_def by auto
  show ?rhs
  proof (intro conjI allI impI)
    show "continuous_map X Y f"
      by (simp add: L quotient_imp_continuous_map)
    show "f ` topspace X = topspace Y"
      by (simp add: fim)
  next
    fix U :: "'a set"
    assume U: "openin X U \<and> {x \<in> topspace X. f x \<in> f ` U} \<subseteq> U"
    then have sub:  "f ` U \<subseteq> topspace Y" and eq: "{x \<in> topspace X. f x \<in> f ` U} = U"
      using fim openin_subset by fastforce+
    show "openin Y (f ` U)"
      by (simp add: sub Y eq U)
  qed
next
  assume ?rhs
  then have YX: "\<And>U. openin Y U \<Longrightarrow> openin X {x \<in> topspace X. f x \<in> U}"
       and fim: "f ` topspace X = topspace Y"
       and XY: "\<And>U. \<lbrakk>openin X U; {x \<in> topspace X. f x \<in> f ` U} \<subseteq> U\<rbrakk> \<Longrightarrow> openin Y (f ` U)"
    by (auto simp: quotient_map_def continuous_map_def)
  show ?lhs
  proof (simp add: quotient_map_def fim, intro allI impI iffI)
    fix U :: "'b set"
    assume "U \<subseteq> topspace Y" and X: "openin X {x \<in> topspace X. f x \<in> U}"
    have feq: "f ` {x \<in> topspace X. f x \<in> U} = U"
      using \<open>U \<subseteq> topspace Y\<close> fim by auto
    show "openin Y U"
      using XY [OF X] by (simp add: feq)
  next
    fix U :: "'b set"
    assume "U \<subseteq> topspace Y" and Y: "openin Y U"
    show "openin X {x \<in> topspace X. f x \<in> U}"
      by (metis YX [OF Y])
  qed
qed

subsection\<open> Separated Sets\<close>

definition separatedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "separatedin X S T \<equiv>
           S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and>
           S \<inter> X closure_of T = {} \<and> T \<inter> X closure_of S = {}"

lemma separatedin_empty [simp]:
     "separatedin X S {} \<longleftrightarrow> S \<subseteq> topspace X"
     "separatedin X {} S \<longleftrightarrow> S \<subseteq> topspace X"
  by (simp_all add: separatedin_def)

lemma separatedin_refl [simp]:
     "separatedin X S S \<longleftrightarrow> S = {}"
proof -
  have "\<And>x. \<lbrakk>separatedin X S S; x \<in> S\<rbrakk> \<Longrightarrow> False"
    by (metis all_not_in_conv closure_of_subset inf.orderE separatedin_def)
  then show ?thesis
    by auto
qed

lemma separatedin_sym:
     "separatedin X S T \<longleftrightarrow> separatedin X T S"
  by (auto simp: separatedin_def)

lemma separatedin_imp_disjoint:
     "separatedin X S T \<Longrightarrow> disjnt S T"
  by (meson closure_of_subset disjnt_def disjnt_subset2 separatedin_def)

lemma separatedin_mono:
   "\<lbrakk>separatedin X S T; S' \<subseteq> S; T' \<subseteq> T\<rbrakk> \<Longrightarrow> separatedin X S' T'"
  unfolding separatedin_def
  using closure_of_mono by blast

lemma separatedin_open_sets:
     "\<lbrakk>openin X S; openin X T\<rbrakk> \<Longrightarrow> separatedin X S T \<longleftrightarrow> disjnt S T"
  unfolding disjnt_def separatedin_def
  by (auto simp: openin_Int_closure_of_eq_empty openin_subset)

lemma separatedin_closed_sets:
     "\<lbrakk>closedin X S; closedin X T\<rbrakk> \<Longrightarrow> separatedin X S T \<longleftrightarrow> disjnt S T"
  unfolding closure_of_eq disjnt_def separatedin_def
  by (metis closedin_def closure_of_eq inf_commute)

lemma separatedin_subtopology:
     "separatedin (subtopology X U) S T \<longleftrightarrow> S \<subseteq> U \<and> T \<subseteq> U \<and> separatedin X S T" (is "?lhs = ?rhs")
  by (auto simp: separatedin_def closure_of_subtopology Int_ac disjoint_iff elim!: inf.orderE)

lemma separatedin_discrete_topology:
     "separatedin (discrete_topology U) S T \<longleftrightarrow> S \<subseteq> U \<and> T \<subseteq> U \<and> disjnt S T"
  by (metis openin_discrete_topology separatedin_def separatedin_open_sets topspace_discrete_topology)

lemma separated_eq_distinguishable:
   "separatedin X {x} {y} \<longleftrightarrow>
        x \<in> topspace X \<and> y \<in> topspace X \<and>
        (\<exists>U. openin X U \<and> x \<in> U \<and> (y \<notin> U)) \<and>
        (\<exists>v. openin X v \<and> y \<in> v \<and> (x \<notin> v))"
  by (force simp: separatedin_def closure_of_def)

lemma separatedin_Un [simp]:
   "separatedin X S (T \<union> U) \<longleftrightarrow> separatedin X S T \<and> separatedin X S U"
   "separatedin X (S \<union> T) U \<longleftrightarrow> separatedin X S U \<and> separatedin X T U"
  by (auto simp: separatedin_def)

lemma separatedin_Union:
  "finite \<F> \<Longrightarrow> separatedin X S (\<Union>\<F>) \<longleftrightarrow> S \<subseteq> topspace X \<and> (\<forall>T \<in> \<F>. separatedin X S T)"
  "finite \<F> \<Longrightarrow> separatedin X (\<Union>\<F>) S \<longleftrightarrow> (\<forall>T \<in> \<F>. separatedin X S T) \<and> S \<subseteq> topspace X"
  by (auto simp: separatedin_def closure_of_Union)

lemma separatedin_openin_diff:
   "\<lbrakk>openin X S; openin X T\<rbrakk> \<Longrightarrow> separatedin X (S - T) (T - S)"
  unfolding separatedin_def
  by (metis Diff_Int_distrib2 Diff_disjoint Diff_empty Diff_mono empty_Diff empty_subsetI openin_Int_closure_of_eq_empty openin_subset)

lemma separatedin_closedin_diff:
  assumes "closedin X S" "closedin X T"
  shows "separatedin X (S - T) (T - S)"
proof -
  have "S - T \<subseteq> topspace X" "T - S \<subseteq> topspace X"
    using assms closedin_subset by auto
  with assms show ?thesis
    by (simp add: separatedin_def Diff_Int_distrib2 closure_of_minimal inf_absorb2)
qed

lemma separation_closedin_Un_gen:
     "separatedin X S T \<longleftrightarrow>
        S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and> disjnt S T \<and>
        closedin (subtopology X (S \<union> T)) S \<and>
        closedin (subtopology X (S \<union> T)) T"
  by (auto simp add: separatedin_def closedin_Int_closure_of disjnt_iff dest: closure_of_subset)

lemma separation_openin_Un_gen:
     "separatedin X S T \<longleftrightarrow>
        S \<subseteq> topspace X \<and> T \<subseteq> topspace X \<and> disjnt S T \<and>
        openin (subtopology X (S \<union> T)) S \<and>
        openin (subtopology X (S \<union> T)) T"
  unfolding openin_closedin_eq topspace_subtopology separation_closedin_Un_gen disjnt_def
  by (auto simp: Diff_triv Int_commute Un_Diff inf_absorb1 topspace_def)


subsection\<open>Homeomorphisms\<close>
text\<open>(1-way and 2-way versions may be useful in places)\<close>

definition homeomorphic_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
 "homeomorphic_map X Y f \<equiv> quotient_map X Y f \<and> inj_on f (topspace X)"

definition homeomorphic_maps :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where
 "homeomorphic_maps X Y f g \<equiv>
    continuous_map X Y f \<and> continuous_map Y X g \<and>
     (\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"


lemma homeomorphic_map_eq:
   "\<lbrakk>homeomorphic_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> homeomorphic_map X Y g"
  by (meson homeomorphic_map_def inj_on_cong quotient_map_eq)

lemma homeomorphic_maps_eq:
     "\<lbrakk>homeomorphic_maps X Y f g;
       \<And>x. x \<in> topspace X \<Longrightarrow> f x = f' x; \<And>y. y \<in> topspace Y \<Longrightarrow> g y = g' y\<rbrakk>
      \<Longrightarrow> homeomorphic_maps X Y f' g'"
  unfolding homeomorphic_maps_def
  by (metis continuous_map_eq continuous_map_eq_image_closure_subset_gen image_subset_iff)

lemma homeomorphic_maps_sym:
     "homeomorphic_maps X Y f g \<longleftrightarrow> homeomorphic_maps Y X g f"
  by (auto simp: homeomorphic_maps_def)

lemma homeomorphic_maps_id:
     "homeomorphic_maps X Y id id \<longleftrightarrow> Y = X"  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "topspace X = topspace Y"
    by (auto simp: homeomorphic_maps_def continuous_map_def)
  with L show ?rhs
    unfolding homeomorphic_maps_def
    by (metis topology_finer_continuous_id topology_eq)
next
  assume ?rhs
  then show ?lhs
    unfolding homeomorphic_maps_def by auto
qed

lemma homeomorphic_map_id [simp]: "homeomorphic_map X Y id \<longleftrightarrow> Y = X"
       (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have eq: "topspace X = topspace Y"
    by (auto simp: homeomorphic_map_def continuous_map_def quotient_map_def)
  then have "\<And>S. openin X S \<longrightarrow> openin Y S"
    by (meson L homeomorphic_map_def injective_quotient_map topology_finer_open_id)
  then show ?rhs
    using L unfolding homeomorphic_map_def
    by (metis eq quotient_imp_continuous_map topology_eq topology_finer_continuous_id)
next
  assume ?rhs
  then show ?lhs
    unfolding homeomorphic_map_def
    by (simp add: closed_map_id continuous_closed_imp_quotient_map)
qed

lemma homeomorphic_map_compose:
  assumes "homeomorphic_map X Y f" "homeomorphic_map Y X'' g"
  shows "homeomorphic_map X X'' (g \<circ> f)"
proof -
  have "inj_on g (f ` topspace X)"
    by (metis (no_types) assms homeomorphic_map_def quotient_imp_surjective_map)
  then show ?thesis
    using assms by (meson comp_inj_on homeomorphic_map_def quotient_map_compose_eq)
qed

lemma homeomorphic_maps_compose:
   "homeomorphic_maps X Y f h \<and>
        homeomorphic_maps Y X'' g k
        \<Longrightarrow> homeomorphic_maps X X'' (g \<circ> f) (h \<circ> k)"
  unfolding homeomorphic_maps_def
  by (auto simp: continuous_map_compose; simp add: continuous_map_def)

lemma homeomorphic_eq_everything_map:
   "homeomorphic_map X Y f \<longleftrightarrow>
        continuous_map X Y f \<and> open_map X Y f \<and> closed_map X Y f \<and>
        f ` (topspace X) = topspace Y \<and> inj_on f (topspace X)"
  unfolding homeomorphic_map_def
  by (force simp: injective_quotient_map intro: injective_quotient_map)

lemma homeomorphic_imp_continuous_map:
     "homeomorphic_map X Y f \<Longrightarrow> continuous_map X Y f"
  by (simp add: homeomorphic_eq_everything_map)

lemma homeomorphic_imp_open_map:
   "homeomorphic_map X Y f \<Longrightarrow> open_map X Y f"
  by (simp add: homeomorphic_eq_everything_map)

lemma homeomorphic_imp_closed_map:
   "homeomorphic_map X Y f \<Longrightarrow> closed_map X Y f"
  by (simp add: homeomorphic_eq_everything_map)

lemma homeomorphic_imp_surjective_map:
   "homeomorphic_map X Y f \<Longrightarrow> f ` (topspace X) = topspace Y"
  by (simp add: homeomorphic_eq_everything_map)

lemma homeomorphic_imp_injective_map:
    "homeomorphic_map X Y f \<Longrightarrow> inj_on f (topspace X)"
  by (simp add: homeomorphic_eq_everything_map)

lemma bijective_open_imp_homeomorphic_map:
   "\<lbrakk>continuous_map X Y f; open_map X Y f; f ` (topspace X) = topspace Y; inj_on f (topspace X)\<rbrakk>
        \<Longrightarrow> homeomorphic_map X Y f"
  by (simp add: homeomorphic_map_def continuous_open_imp_quotient_map)

lemma bijective_closed_imp_homeomorphic_map:
   "\<lbrakk>continuous_map X Y f; closed_map X Y f; f ` (topspace X) = topspace Y; inj_on f (topspace X)\<rbrakk>
        \<Longrightarrow> homeomorphic_map X Y f"
  by (simp add: continuous_closed_quotient_map homeomorphic_map_def)

lemma open_eq_continuous_inverse_map:
  assumes X: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y \<and> g(f x) = x"
    and Y: "\<And>y. y \<in> topspace Y \<Longrightarrow> g y \<in> topspace X \<and> f(g y) = y"
  shows "open_map X Y f \<longleftrightarrow> continuous_map Y X g"
proof -
  have eq: "{x \<in> topspace Y. g x \<in> U} = f ` U" if "openin X U" for U
    using openin_subset [OF that] by (force simp: X Y image_iff)
  show ?thesis
    by (auto simp: Y open_map_def continuous_map_def eq)
qed

lemma closed_eq_continuous_inverse_map:
  assumes X: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y \<and> g(f x) = x"
    and Y: "\<And>y. y \<in> topspace Y \<Longrightarrow> g y \<in> topspace X \<and> f(g y) = y"
  shows "closed_map X Y f \<longleftrightarrow> continuous_map Y X g"
proof -
  have eq: "{x \<in> topspace Y. g x \<in> U} = f ` U" if "closedin X U" for U
    using closedin_subset [OF that] by (force simp: X Y image_iff)
  show ?thesis
    by (auto simp: Y closed_map_def continuous_map_closedin eq)
qed

lemma homeomorphic_maps_map:
  "homeomorphic_maps X Y f g \<longleftrightarrow>
        homeomorphic_map X Y f \<and> homeomorphic_map Y X g \<and>
        (\<forall>x \<in> topspace X. g(f x) = x) \<and> (\<forall>y \<in> topspace Y. f(g y) = y)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have L: "continuous_map X Y f" "continuous_map Y X g" "\<forall>x\<in>topspace X. g (f x) = x" "\<forall>x'\<in>topspace Y. f (g x') = x'"
    by (auto simp: homeomorphic_maps_def)
  show ?rhs
  proof (intro conjI bijective_open_imp_homeomorphic_map L)
    show "open_map X Y f"
      using L using open_eq_continuous_inverse_map [of concl: X Y f g] by (simp add: continuous_map_def)
    show "open_map Y X g"
      using L using open_eq_continuous_inverse_map [of concl: Y X g f] by (simp add: continuous_map_def)
    show "f ` topspace X = topspace Y" "g ` topspace Y = topspace X"
      using L by (force simp: continuous_map_closedin)+
    show "inj_on f (topspace X)" "inj_on g (topspace Y)"
      using L unfolding inj_on_def by metis+
  qed
next
  assume ?rhs
  then show ?lhs
    by (auto simp: homeomorphic_maps_def homeomorphic_imp_continuous_map)
qed

lemma homeomorphic_maps_imp_map:
    "homeomorphic_maps X Y f g \<Longrightarrow> homeomorphic_map X Y f"
  using homeomorphic_maps_map by blast

lemma homeomorphic_map_maps:
     "homeomorphic_map X Y f \<longleftrightarrow> (\<exists>g. homeomorphic_maps X Y f g)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have L: "continuous_map X Y f" "open_map X Y f" "closed_map X Y f"
    "f ` (topspace X) = topspace Y" "inj_on f (topspace X)"
    by (auto simp: homeomorphic_eq_everything_map)
  have X: "\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y \<and> inv_into (topspace X) f (f x) = x"
    using L by auto
  have Y: "\<And>y. y \<in> topspace Y \<Longrightarrow> inv_into (topspace X) f y \<in> topspace X \<and> f (inv_into (topspace X) f y) = y"
    by (simp add: L f_inv_into_f inv_into_into)
  have "homeomorphic_maps X Y f (inv_into (topspace X) f)"
    unfolding homeomorphic_maps_def
  proof (intro conjI L)
    show "continuous_map Y X (inv_into (topspace X) f)"
      by (simp add: L X Y flip: open_eq_continuous_inverse_map [where f=f])
  next
    show "\<forall>x\<in>topspace X. inv_into (topspace X) f (f x) = x"
         "\<forall>y\<in>topspace Y. f (inv_into (topspace X) f y) = y"
      using X Y by auto
  qed
  then show ?rhs
    by metis
next
  assume ?rhs
  then show ?lhs
    using homeomorphic_maps_map by blast
qed

lemma homeomorphic_maps_involution:
   "\<lbrakk>continuous_map X X f; \<And>x. x \<in> topspace X \<Longrightarrow> f(f x) = x\<rbrakk> \<Longrightarrow> homeomorphic_maps X X f f"
  by (auto simp: homeomorphic_maps_def)

lemma homeomorphic_map_involution:
   "\<lbrakk>continuous_map X X f; \<And>x. x \<in> topspace X \<Longrightarrow> f(f x) = x\<rbrakk> \<Longrightarrow> homeomorphic_map X X f"
  using homeomorphic_maps_involution homeomorphic_maps_map by blast

lemma homeomorphic_map_openness:
  assumes hom: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "openin Y (f ` U) \<longleftrightarrow> openin X U"
proof -
  obtain g where "homeomorphic_maps X Y f g"
    using assms by (auto simp: homeomorphic_map_maps)
  then have g: "homeomorphic_map Y X g" and gf: "\<And>x. x \<in> topspace X \<Longrightarrow> g(f x) = x"
    by (auto simp: homeomorphic_maps_map)
  then have "openin X U \<Longrightarrow> openin Y (f ` U)"
    using hom homeomorphic_imp_open_map open_map_def by blast
  show "openin Y (f ` U) = openin X U"
  proof
    assume L: "openin Y (f ` U)"
    have "U = g ` (f ` U)"
      using U gf by force
    then show "openin X U"
      by (metis L homeomorphic_imp_open_map open_map_def g)
  next
    assume "openin X U"
    then show "openin Y (f ` U)"
      using hom homeomorphic_imp_open_map open_map_def by blast
  qed
qed


lemma homeomorphic_map_closedness:
  assumes hom: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "closedin Y (f ` U) \<longleftrightarrow> closedin X U"
proof -
  obtain g where "homeomorphic_maps X Y f g"
    using assms by (auto simp: homeomorphic_map_maps)
  then have g: "homeomorphic_map Y X g" and gf: "\<And>x. x \<in> topspace X \<Longrightarrow> g(f x) = x"
    by (auto simp: homeomorphic_maps_map)
  then have "closedin X U \<Longrightarrow> closedin Y (f ` U)"
    using hom homeomorphic_imp_closed_map closed_map_def by blast
  show "closedin Y (f ` U) = closedin X U"
  proof
    assume L: "closedin Y (f ` U)"
    have "U = g ` (f ` U)"
      using U gf by force
    then show "closedin X U"
      by (metis L homeomorphic_imp_closed_map closed_map_def g)
  next
    assume "closedin X U"
    then show "closedin Y (f ` U)"
      using hom homeomorphic_imp_closed_map closed_map_def by blast
  qed
qed

lemma homeomorphic_map_openness_eq:
     "homeomorphic_map X Y f \<Longrightarrow> openin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> openin Y (f ` U)"
  by (meson homeomorphic_map_openness openin_closedin_eq)

lemma homeomorphic_map_closedness_eq:
    "homeomorphic_map X Y f \<Longrightarrow> closedin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> closedin Y (f ` U)"
  by (meson closedin_subset homeomorphic_map_closedness)

lemma all_openin_homeomorphic_image:
  assumes "homeomorphic_map X Y f"
  shows "(\<forall>V. openin Y V \<longrightarrow> P V) \<longleftrightarrow> (\<forall>U. openin X U \<longrightarrow> P(f ` U))"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson assms homeomorphic_map_openness_eq)
next
  assume ?rhs
  then show ?lhs
    by (metis (no_types, lifting) assms homeomorphic_imp_surjective_map homeomorphic_map_openness openin_subset subset_image_iff)
qed

lemma all_closedin_homeomorphic_image:
  assumes "homeomorphic_map X Y f"
  shows "(\<forall>V. closedin Y V \<longrightarrow> P V) \<longleftrightarrow> (\<forall>U. closedin X U \<longrightarrow> P(f ` U))"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (meson assms homeomorphic_map_closedness_eq)
next
  assume ?rhs
  then show ?lhs
    by (metis (no_types, lifting) assms homeomorphic_imp_surjective_map homeomorphic_map_closedness closedin_subset subset_image_iff)
qed


lemma homeomorphic_map_derived_set_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y derived_set_of (f ` S) = f ` (X derived_set_of S)"
proof -
  have fim: "f ` (topspace X) = topspace Y" and inj: "inj_on f (topspace X)"
    using hom by (auto simp: homeomorphic_eq_everything_map)
  have iff: "(\<forall>T. x \<in> T \<and> openin X T \<longrightarrow> (\<exists>y. y \<noteq> x \<and> y \<in> S \<and> y \<in> T)) =
            (\<forall>T. T \<subseteq> topspace Y \<longrightarrow> f x \<in> T \<longrightarrow> openin Y T \<longrightarrow> (\<exists>y. y \<noteq> f x \<and> y \<in> f ` S \<and> y \<in> T))"
    if "x \<in> topspace X" for x
  proof -
    have \<section>: "(x \<in> T \<and> openin X T) = (T \<subseteq> topspace X \<and> f x \<in> f ` T \<and> openin Y (f ` T))" for T
      by (meson hom homeomorphic_map_openness_eq inj inj_on_image_mem_iff that)
    moreover have "(\<exists>y. y \<noteq> x \<and> y \<in> S \<and> y \<in> T) = (\<exists>y. y \<noteq> f x \<and> y \<in> f ` S \<and> y \<in> f ` T)"  (is "?lhs = ?rhs")
      if "T \<subseteq> topspace X \<and> f x \<in> f ` T \<and> openin Y (f ` T)" for T
    proof
      show "?lhs \<Longrightarrow> ?rhs"
        by (meson \<section> imageI inj inj_on_eq_iff inj_on_subset that)
      show "?rhs \<Longrightarrow> ?lhs"
        using S inj inj_onD that by fastforce
    qed
    ultimately show ?thesis
      by (auto simp flip: fim simp: all_subset_image)
  qed
  have *: "\<lbrakk>T = f ` S; \<And>x. x \<in> S \<Longrightarrow> P x \<longleftrightarrow> Q(f x)\<rbrakk> \<Longrightarrow> {y. y \<in> T \<and> Q y} = f ` {x \<in> S. P x}" for T S P Q
    by auto
  show ?thesis
    unfolding derived_set_of_def
    by (rule *) (use fim iff openin_subset in force)+
qed


lemma homeomorphic_map_closure_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y closure_of (f ` S) = f ` (X closure_of S)"
  unfolding closure_of
  using homeomorphic_imp_surjective_map [OF hom] S
  by (auto simp: in_derived_set_of homeomorphic_map_derived_set_of [OF assms])

lemma homeomorphic_map_interior_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y interior_of (f ` S) = f ` (X interior_of S)"
proof -
  { fix y
    assume "y \<in> topspace Y" and "y \<notin> Y closure_of (topspace Y - f ` S)"
    then have "y \<in> f ` (topspace X - X closure_of (topspace X - S))"
      using homeomorphic_eq_everything_map [THEN iffD1, OF hom] homeomorphic_map_closure_of [OF hom]
      by (metis DiffI Diff_subset S closure_of_subset_topspace inj_on_image_set_diff) }
  moreover
  { fix x
    assume "x \<in> topspace X"
    then have "f x \<in> topspace Y"
      using hom homeomorphic_imp_surjective_map by blast }
  moreover
  { fix x
    assume "x \<in> topspace X" and "x \<notin> X closure_of (topspace X - S)" and "f x \<in> Y closure_of (topspace Y - f ` S)"
    then have "False"
      using homeomorphic_map_closure_of [OF hom] hom
      unfolding homeomorphic_eq_everything_map
      by (metis Diff_subset S closure_of_subset_topspace inj_on_image_mem_iff inj_on_image_set_diff)
  }
  ultimately  show ?thesis
    by (auto simp: interior_of_closure_of)
qed

lemma homeomorphic_map_frontier_of:
  assumes hom: "homeomorphic_map X Y f" and S: "S \<subseteq> topspace X"
  shows "Y frontier_of (f ` S) = f ` (X frontier_of S)"
  unfolding frontier_of_def
proof (intro equalityI subsetI DiffI)
  fix y
  assume "y \<in> Y closure_of f ` S - Y interior_of f ` S"
  then show "y \<in> f ` (X closure_of S - X interior_of S)"
    using S hom homeomorphic_map_closure_of homeomorphic_map_interior_of by fastforce
next
  fix y
  assume "y \<in> f ` (X closure_of S - X interior_of S)"
  then show "y \<in> Y closure_of f ` S"
    using S hom homeomorphic_map_closure_of by fastforce
next
  fix x
  assume "x \<in> f ` (X closure_of S - X interior_of S)"
  then obtain y where y: "x = f y" "y \<in> X closure_of S" "y \<notin> X interior_of S"
    by blast
  then have "y \<in> topspace X"
    by (simp add: in_closure_of)
  then have "f y \<notin> f ` (X interior_of S)"
    by (meson hom homeomorphic_map_def inj_on_image_mem_iff interior_of_subset_topspace y(3))
  then show "x \<notin> Y interior_of f ` S"
    using S hom homeomorphic_map_interior_of y(1) by blast
qed

lemma homeomorphic_maps_subtopologies:
   "\<lbrakk>homeomorphic_maps X Y f g;  f ` (topspace X \<inter> S) = topspace Y \<inter> T\<rbrakk>
        \<Longrightarrow> homeomorphic_maps (subtopology X S) (subtopology Y T) f g"
  unfolding homeomorphic_maps_def
  by (force simp: continuous_map_from_subtopology continuous_map_in_subtopology)

lemma homeomorphic_maps_subtopologies_alt:
     "\<lbrakk>homeomorphic_maps X Y f g; f ` (topspace X \<inter> S) \<subseteq> T; g ` (topspace Y \<inter> T) \<subseteq> S\<rbrakk>
      \<Longrightarrow> homeomorphic_maps (subtopology X S) (subtopology Y T) f g"
  unfolding homeomorphic_maps_def
  by (force simp: continuous_map_from_subtopology continuous_map_in_subtopology)

lemma homeomorphic_map_subtopologies:
   "\<lbrakk>homeomorphic_map X Y f; f ` (topspace X \<inter> S) = topspace Y \<inter> T\<rbrakk>
        \<Longrightarrow> homeomorphic_map (subtopology X S) (subtopology Y T) f"
  by (meson homeomorphic_map_maps homeomorphic_maps_subtopologies)

lemma homeomorphic_map_subtopologies_alt:
  assumes hom: "homeomorphic_map X Y f" 
      and S: "\<And>x. \<lbrakk>x \<in> topspace X; f x \<in> topspace Y\<rbrakk> \<Longrightarrow> f x \<in> T \<longleftrightarrow> x \<in> S"
    shows "homeomorphic_map (subtopology X S) (subtopology Y T) f"
proof -
  have "homeomorphic_maps (subtopology X S) (subtopology Y T) f g" 
      if "homeomorphic_maps X Y f g" for g
  proof (rule homeomorphic_maps_subtopologies [OF that])
    show "f ` (topspace X \<inter> S) = topspace Y \<inter> T"
      using that S 
      apply (auto simp: homeomorphic_maps_def continuous_map_def)
      by (metis IntI image_iff)
  qed
  then show ?thesis
    using hom by (meson homeomorphic_map_maps)
qed


subsection\<open>Relation of homeomorphism between topological spaces\<close>

definition homeomorphic_space (infixr "homeomorphic'_space" 50)
  where "X homeomorphic_space Y \<equiv> \<exists>f g. homeomorphic_maps X Y f g"

lemma homeomorphic_space_refl: "X homeomorphic_space X"
  by (meson homeomorphic_maps_id homeomorphic_space_def)

lemma homeomorphic_space_sym:
   "X homeomorphic_space Y \<longleftrightarrow> Y homeomorphic_space X"
  unfolding homeomorphic_space_def by (metis homeomorphic_maps_sym)

lemma homeomorphic_space_trans [trans]:
     "\<lbrakk>X1 homeomorphic_space X2; X2 homeomorphic_space X3\<rbrakk> \<Longrightarrow> X1 homeomorphic_space X3"
  unfolding homeomorphic_space_def by (metis homeomorphic_maps_compose)

lemma homeomorphic_space:
     "X homeomorphic_space Y \<longleftrightarrow> (\<exists>f. homeomorphic_map X Y f)"
  by (simp add: homeomorphic_map_maps homeomorphic_space_def)

lemma homeomorphic_maps_imp_homeomorphic_space:
     "homeomorphic_maps X Y f g \<Longrightarrow> X homeomorphic_space Y"
  unfolding homeomorphic_space_def by metis

lemma homeomorphic_map_imp_homeomorphic_space:
     "homeomorphic_map X Y f \<Longrightarrow> X homeomorphic_space Y"
  unfolding homeomorphic_map_maps
  using homeomorphic_space_def by blast

lemma homeomorphic_empty_space:
     "X homeomorphic_space Y \<Longrightarrow> topspace X = {} \<longleftrightarrow> topspace Y = {}"
  by (metis homeomorphic_imp_surjective_map homeomorphic_space image_is_empty)

lemma homeomorphic_empty_space_eq:
  assumes "topspace X = {}"
    shows "X homeomorphic_space Y \<longleftrightarrow> topspace Y = {}"
proof -
  have "\<forall>f t. continuous_map X (t::'b topology) f"
    using assms continuous_map_on_empty by blast
  then show ?thesis
    by (metis (no_types) assms continuous_map_on_empty empty_iff homeomorphic_empty_space homeomorphic_maps_def homeomorphic_space_def)
qed

subsection\<open>Connected topological spaces\<close>

definition connected_space :: "'a topology \<Rightarrow> bool" where
  "connected_space X \<equiv>
        \<not>(\<exists>E1 E2. openin X E1 \<and> openin X E2 \<and>
                  topspace X \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"

definition connectedin :: "'a topology \<Rightarrow> 'a set \<Rightarrow> bool" where
  "connectedin X S \<equiv> S \<subseteq> topspace X \<and> connected_space (subtopology X S)"

lemma connected_spaceD:
  "\<lbrakk>connected_space X;
    openin X U; openin X V; topspace X \<subseteq> U \<union> V; U \<inter> V = {}; U \<noteq> {}; V \<noteq> {}\<rbrakk> \<Longrightarrow> False"
  by (auto simp: connected_space_def)

lemma connectedin_subset_topspace: "connectedin X S \<Longrightarrow> S \<subseteq> topspace X"
  by (simp add: connectedin_def)

lemma connectedin_topspace:
     "connectedin X (topspace X) \<longleftrightarrow> connected_space X"
  by (simp add: connectedin_def)

lemma connected_space_subtopology:
     "connectedin X S \<Longrightarrow> connected_space (subtopology X S)"
  by (simp add: connectedin_def)

lemma connectedin_subtopology:
     "connectedin (subtopology X S) T \<longleftrightarrow> connectedin X T \<and> T \<subseteq> S"
  by (force simp: connectedin_def subtopology_subtopology inf_absorb2)

lemma connected_space_eq:
     "connected_space X \<longleftrightarrow>
      (\<nexists>E1 E2. openin X E1 \<and> openin X E2 \<and> E1 \<union> E2 = topspace X \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
  unfolding connected_space_def
  by (metis openin_Un openin_subset subset_antisym)

lemma connected_space_closedin:
     "connected_space X \<longleftrightarrow>
      (\<nexists>E1 E2. closedin X E1 \<and> closedin X E2 \<and> topspace X \<subseteq> E1 \<union> E2 \<and>
               E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then have L: "\<And>E1 E2. \<lbrakk>openin X E1; E1 \<inter> E2 = {}; topspace X \<subseteq> E1 \<union> E2; openin X E2\<rbrakk> \<Longrightarrow> E1 = {} \<or> E2 = {}"
    by (simp add: connected_space_def)
  show ?rhs
    unfolding connected_space_def
  proof clarify
    fix E1 E2
    assume "closedin X E1" and "closedin X E2" and "topspace X \<subseteq> E1 \<union> E2" and "E1 \<inter> E2 = {}"
      and "E1 \<noteq> {}" and "E2 \<noteq> {}"
    have "E1 \<union> E2 = topspace X"
      by (meson Un_subset_iff \<open>closedin X E1\<close> \<open>closedin X E2\<close> \<open>topspace X \<subseteq> E1 \<union> E2\<close> closedin_def subset_antisym)
    then have "topspace X - E2 = E1"
      using \<open>E1 \<inter> E2 = {}\<close> by fastforce
    then have "topspace X = E1"
      using \<open>E1 \<noteq> {}\<close> L \<open>closedin X E1\<close> \<open>closedin X E2\<close> by blast
    then show "False"
      using \<open>E1 \<inter> E2 = {}\<close> \<open>E1 \<union> E2 = topspace X\<close> \<open>E2 \<noteq> {}\<close> by blast
  qed
next
  assume R: ?rhs
  show ?lhs
    unfolding connected_space_def
  proof clarify
    fix E1 E2
    assume "openin X E1" and "openin X E2" and "topspace X \<subseteq> E1 \<union> E2" and "E1 \<inter> E2 = {}"
      and "E1 \<noteq> {}" and "E2 \<noteq> {}"
    have "E1 \<union> E2 = topspace X"
      by (meson Un_subset_iff \<open>openin X E1\<close> \<open>openin X E2\<close> \<open>topspace X \<subseteq> E1 \<union> E2\<close> openin_closedin_eq subset_antisym)
    then have "topspace X - E2 = E1"
      using \<open>E1 \<inter> E2 = {}\<close> by fastforce
    then have "topspace X = E1"
      using \<open>E1 \<noteq> {}\<close> R \<open>openin X E1\<close> \<open>openin X E2\<close> by blast
    then show "False"
      using \<open>E1 \<inter> E2 = {}\<close> \<open>E1 \<union> E2 = topspace X\<close> \<open>E2 \<noteq> {}\<close> by blast
  qed
qed

lemma connected_space_closedin_eq:
     "connected_space X \<longleftrightarrow>
       (\<nexists>E1 E2. closedin X E1 \<and> closedin X E2 \<and>
                E1 \<union> E2 = topspace X \<and> E1 \<inter> E2 = {} \<and> E1 \<noteq> {} \<and> E2 \<noteq> {})"
  by (metis closedin_Un closedin_def connected_space_closedin subset_antisym)

lemma connected_space_clopen_in:
     "connected_space X \<longleftrightarrow>
        (\<forall>T. openin X T \<and> closedin X T \<longrightarrow> T = {} \<or> T = topspace X)"
proof -
  have eq: "openin X E1 \<and> openin X E2 \<and> E1 \<union> E2 = topspace X \<and> E1 \<inter> E2 = {} \<and> P
        \<longleftrightarrow> E2 = topspace X - E1 \<and> openin X E1 \<and> openin X E2 \<and> P" for E1 E2 P
    using openin_subset by blast
  show ?thesis
    unfolding connected_space_eq eq closedin_def
    by (auto simp: openin_closedin_eq)
qed

lemma connectedin:
     "connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
         (\<nexists>E1 E2.
             openin X E1 \<and> openin X E2 \<and>
             S \<subseteq> E1 \<union> E2 \<and> E1 \<inter> E2 \<inter> S = {} \<and> E1 \<inter> S \<noteq> {} \<and> E2 \<inter> S \<noteq> {})"  (is "?lhs = ?rhs")
proof -
  have *: "(\<exists>E1:: 'a set. \<exists>E2:: 'a set. (\<exists>T1:: 'a set. P1 T1 \<and> E1 = f1 T1) \<and> (\<exists>T2:: 'a set. P2 T2 \<and> E2 = f2 T2) \<and>
             R E1 E2) \<longleftrightarrow> (\<exists>T1 T2. P1 T1 \<and> P2 T2 \<and> R(f1 T1) (f2 T2))" for P1 f1 P2 f2 R
    by auto
  show ?thesis 
    unfolding connectedin_def connected_space_def openin_subtopology topspace_subtopology *
    by (intro conj_cong arg_cong [where f=Not] ex_cong1; blast dest!: openin_subset)
qed

lemma connectedin_iff_connected [simp]: "connectedin euclidean S \<longleftrightarrow> connected S"
  by (simp add: connected_def connectedin)

lemma connectedin_closedin:
   "connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
        \<not>(\<exists>E1 E2. closedin X E1 \<and> closedin X E2 \<and>
                  S \<subseteq> (E1 \<union> E2) \<and>
                  (E1 \<inter> E2 \<inter> S = {}) \<and>
                  \<not>(E1 \<inter> S = {}) \<and> \<not>(E2 \<inter> S = {}))"
proof -
  have *: "(\<exists>E1:: 'a set. \<exists>E2:: 'a set. (\<exists>T1:: 'a set. P1 T1 \<and> E1 = f1 T1) \<and> (\<exists>T2:: 'a set. P2 T2 \<and> E2 = f2 T2) \<and>
             R E1 E2) \<longleftrightarrow> (\<exists>T1 T2. P1 T1 \<and> P2 T2 \<and> R(f1 T1) (f2 T2))" for P1 f1 P2 f2 R
    by auto
  show ?thesis
    unfolding connectedin_def connected_space_closedin closedin_subtopology topspace_subtopology *
    by (intro conj_cong arg_cong [where f=Not] ex_cong1; blast dest!: openin_subset)
qed

lemma connectedin_empty [simp]: "connectedin X {}"
  by (simp add: connectedin)

lemma connected_space_topspace_empty:
     "topspace X = {} \<Longrightarrow> connected_space X"
  using connectedin_topspace by fastforce

lemma connectedin_sing [simp]: "connectedin X {a} \<longleftrightarrow> a \<in> topspace X"
  by (simp add: connectedin)

lemma connectedin_absolute [simp]:
  "connectedin (subtopology X S) S \<longleftrightarrow> connectedin X S"
  by (simp add: connectedin_subtopology)

lemma connectedin_Union:
  assumes \<U>: "\<And>S. S \<in> \<U> \<Longrightarrow> connectedin X S" and ne: "\<Inter>\<U> \<noteq> {}"
  shows "connectedin X (\<Union>\<U>)"
proof -
  have "\<Union>\<U> \<subseteq> topspace X"
    using \<U> by (simp add: Union_least connectedin_def)
  moreover have False
    if "openin X E1" "openin X E2" and cover: "\<Union>\<U> \<subseteq> E1 \<union> E2" and disj: "E1 \<inter> E2 \<inter> \<Union>\<U> = {}"
       and overlap1: "E1 \<inter> \<Union>\<U> \<noteq> {}" and overlap2: "E2 \<inter> \<Union>\<U> \<noteq> {}"
      for E1 E2
  proof -
    have disjS: "E1 \<inter> E2 \<inter> S = {}" if "S \<in> \<U>" for S
      using Diff_triv that disj by auto
    have coverS: "S \<subseteq> E1 \<union> E2" if "S \<in> \<U>" for S
      using that cover by blast
    have "\<U> \<noteq> {}"
      using overlap1 by blast
    obtain a where a: "\<And>U. U \<in> \<U> \<Longrightarrow> a \<in> U"
      using ne by force
    with \<open>\<U> \<noteq> {}\<close> have "a \<in> \<Union>\<U>"
      by blast
    then consider "a \<in> E1" | "a \<in> E2"
      using \<open>\<Union>\<U> \<subseteq> E1 \<union> E2\<close> by auto
    then show False
    proof cases
      case 1
      then obtain b S where "b \<in> E2" "b \<in> S" "S \<in> \<U>"
        using overlap2 by blast
      then show ?thesis
        using "1" \<open>openin X E1\<close> \<open>openin X E2\<close> disjS coverS a [OF \<open>S \<in> \<U>\<close>]  \<U>[OF \<open>S \<in> \<U>\<close>]
        unfolding connectedin
        by (meson disjoint_iff_not_equal)
    next
      case 2
      then obtain b S where "b \<in> E1" "b \<in> S" "S \<in> \<U>"
        using overlap1 by blast
      then show ?thesis
        using "2" \<open>openin X E1\<close> \<open>openin X E2\<close> disjS coverS a [OF \<open>S \<in> \<U>\<close>]  \<U>[OF \<open>S \<in> \<U>\<close>]
        unfolding connectedin
        by (meson disjoint_iff_not_equal)
    qed
  qed
  ultimately show ?thesis
    unfolding connectedin by blast
qed

lemma connectedin_Un:
     "\<lbrakk>connectedin X S; connectedin X T; S \<inter> T \<noteq> {}\<rbrakk> \<Longrightarrow> connectedin X (S \<union> T)"
  using connectedin_Union [of "{S,T}"] by auto

lemma connected_space_subconnected:
  "connected_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. \<exists>S. connectedin X S \<and> x \<in> S \<and> y \<in> S)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using connectedin_topspace by blast
next
  assume R [rule_format]: ?rhs
  have False if "openin X U" "openin X V" and disj: "U \<inter> V = {}" and cover: "topspace X \<subseteq> U \<union> V"
    and "U \<noteq> {}" "V \<noteq> {}" for U V
  proof -
    obtain u v where "u \<in> U" "v \<in> V"
      using \<open>U \<noteq> {}\<close> \<open>V \<noteq> {}\<close> by auto
    then obtain T where "u \<in> T" "v \<in> T" and T: "connectedin X T"
      using R [of u v] that
      by (meson \<open>openin X U\<close> \<open>openin X V\<close> subsetD openin_subset)
    then show False
      using that unfolding connectedin
      by (metis IntI \<open>u \<in> U\<close> \<open>v \<in> V\<close> empty_iff inf_bot_left subset_trans)
  qed
  then show ?lhs
    by (auto simp: connected_space_def)
qed

lemma connectedin_intermediate_closure_of:
  assumes "connectedin X S" "S \<subseteq> T" "T \<subseteq> X closure_of S"
  shows "connectedin X T"
proof -
  have S: "S \<subseteq> topspace X" and T: "T \<subseteq> topspace X"
    using assms by (meson closure_of_subset_topspace dual_order.trans)+
  have \<section>: "\<And>E1 E2. \<lbrakk>openin X E1; openin X E2; E1 \<inter> S = {} \<or> E2 \<inter> S = {}\<rbrakk> \<Longrightarrow> E1 \<inter> T = {} \<or> E2 \<inter> T = {}"
    using assms unfolding disjoint_iff by (meson in_closure_of subsetD)
  then show ?thesis
    using assms
    unfolding connectedin closure_of_subset_topspace S T
    by (metis Int_empty_right T dual_order.trans inf.orderE inf_left_commute)
qed

lemma connectedin_closure_of:
     "connectedin X S \<Longrightarrow> connectedin X (X closure_of S)"
  by (meson closure_of_subset connectedin_def connectedin_intermediate_closure_of subset_refl)

lemma connectedin_separation:
  "connectedin X S \<longleftrightarrow>
        S \<subseteq> topspace X \<and>
        (\<nexists>C1 C2. C1 \<union> C2 = S \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> C1 \<inter> X closure_of C2 = {} \<and> C2 \<inter> X closure_of C1 = {})" (is "?lhs = ?rhs")
  unfolding connectedin_def connected_space_closedin_eq closedin_Int_closure_of topspace_subtopology
  apply (intro conj_cong refl arg_cong [where f=Not])
  apply (intro ex_cong1 iffI, blast)
  using closure_of_subset_Int by force

lemma connectedin_eq_not_separated:
   "connectedin X S \<longleftrightarrow>
         S \<subseteq> topspace X \<and>
         (\<nexists>C1 C2. C1 \<union> C2 = S \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> separatedin X C1 C2)"
  unfolding separatedin_def by (metis connectedin_separation sup.boundedE)

lemma connectedin_eq_not_separated_subset:
  "connectedin X S \<longleftrightarrow>
      S \<subseteq> topspace X \<and> (\<nexists>C1 C2. S \<subseteq> C1 \<union> C2 \<and> S \<inter> C1 \<noteq> {} \<and> S \<inter> C2 \<noteq> {} \<and> separatedin X C1 C2)"
proof -
  have "\<forall>C1 C2. S \<subseteq> C1 \<union> C2 \<longrightarrow> S \<inter> C1 = {} \<or> S \<inter> C2 = {} \<or> \<not> separatedin X C1 C2"
    if "\<And>C1 C2. C1 \<union> C2 = S \<longrightarrow> C1 = {} \<or> C2 = {} \<or> \<not> separatedin X C1 C2"
  proof (intro allI)
    fix C1 C2
    show "S \<subseteq> C1 \<union> C2 \<longrightarrow> S \<inter> C1 = {} \<or> S \<inter> C2 = {} \<or> \<not> separatedin X C1 C2"
      using that [of "S \<inter> C1" "S \<inter> C2"]
      by (auto simp: separatedin_mono)
  qed
  then show ?thesis
    by (metis Un_Int_eq(1) Un_Int_eq(2) connectedin_eq_not_separated order_refl)
qed

lemma connected_space_eq_not_separated:
     "connected_space X \<longleftrightarrow>
      (\<nexists>C1 C2. C1 \<union> C2 = topspace X \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> separatedin X C1 C2)"
  by (simp add: connectedin_eq_not_separated flip: connectedin_topspace)

lemma connected_space_eq_not_separated_subset:
  "connected_space X \<longleftrightarrow>
    (\<nexists>C1 C2. topspace X \<subseteq> C1 \<union> C2 \<and> C1 \<noteq> {} \<and> C2 \<noteq> {} \<and> separatedin X C1 C2)"
  by (metis connected_space_eq_not_separated le_sup_iff separatedin_def subset_antisym)

lemma connectedin_subset_separated_union:
     "\<lbrakk>connectedin X C; separatedin X S T; C \<subseteq> S \<union> T\<rbrakk> \<Longrightarrow> C \<subseteq> S \<or> C \<subseteq> T"
  unfolding connectedin_eq_not_separated_subset  by blast

lemma connectedin_nonseparated_union:
  assumes "connectedin X S" "connectedin X T" "\<not>separatedin X S T"
  shows "connectedin X (S \<union> T)"
proof -
  have "\<And>C1 C2. \<lbrakk>T \<subseteq> C1 \<union> C2; S \<subseteq> C1 \<union> C2\<rbrakk> \<Longrightarrow>
           S \<inter> C1 = {} \<and> T \<inter> C1 = {} \<or> S \<inter> C2 = {} \<and> T \<inter> C2 = {} \<or> \<not> separatedin X C1 C2"
    using assms
    unfolding connectedin_eq_not_separated_subset
    by (metis (no_types, lifting) assms connectedin_subset_separated_union inf.orderE separatedin_empty(1) separatedin_mono separatedin_sym)
  then show ?thesis
    unfolding connectedin_eq_not_separated_subset
    by (simp add: assms(1) assms(2) connectedin_subset_topspace Int_Un_distrib2)
qed

lemma connected_space_closures:
     "connected_space X \<longleftrightarrow>
        (\<nexists>e1 e2. e1 \<union> e2 = topspace X \<and> X closure_of e1 \<inter> X closure_of e2 = {} \<and> e1 \<noteq> {} \<and> e2 \<noteq> {})"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    unfolding connected_space_closedin_eq
    by (metis Un_upper1 Un_upper2 closedin_closure_of closure_of_Un closure_of_eq_empty closure_of_topspace)
next
  assume ?rhs
  then show ?lhs
    unfolding connected_space_closedin_eq
    by (metis closure_of_eq)
qed

lemma connectedin_inter_frontier_of:
  assumes "connectedin X S" "S \<inter> T \<noteq> {}" "S - T \<noteq> {}"
  shows "S \<inter> X frontier_of T \<noteq> {}"
proof -
  have "S \<subseteq> topspace X" and *:
    "\<And>E1 E2. openin X E1 \<longrightarrow> openin X E2 \<longrightarrow> E1 \<inter> E2 \<inter> S = {} \<longrightarrow> S \<subseteq> E1 \<union> E2 \<longrightarrow> E1 \<inter> S = {} \<or> E2 \<inter> S = {}"
    using \<open>connectedin X S\<close> by (auto simp: connectedin)
  moreover
  have "S - (topspace X \<inter> T) \<noteq> {}"
    using assms(3) by blast
  moreover
  have "S \<inter> topspace X \<inter> T \<noteq> {}"
    using assms(1) assms(2) connectedin by fastforce
  moreover
  have False if "S \<inter> T \<noteq> {}" "S - T \<noteq> {}" "T \<subseteq> topspace X" "S \<inter> X frontier_of T = {}" for T
  proof -
    have null: "S \<inter> (X closure_of T - X interior_of T) = {}"
      using that unfolding frontier_of_def by blast
    have "X interior_of T \<inter> (topspace X - X closure_of T) \<inter> S = {}"
      by (metis Diff_disjoint inf_bot_left interior_of_Int interior_of_complement interior_of_empty)
    moreover have "S \<subseteq> X interior_of T \<union> (topspace X - X closure_of T)"
      using that \<open>S \<subseteq> topspace X\<close> null by auto
    moreover have "S \<inter> X interior_of T \<noteq> {}"
      using closure_of_subset that(1) that(3) null by fastforce
    ultimately have "S \<inter> X interior_of (topspace X - T) = {}"
      by (metis "*" inf_commute interior_of_complement openin_interior_of)
    then have "topspace (subtopology X S) \<inter> X interior_of T = S"
      using \<open>S \<subseteq> topspace X\<close> interior_of_complement null by fastforce
    then show ?thesis
      using that by (metis Diff_eq_empty_iff inf_le2 interior_of_subset subset_trans)
  qed
  ultimately show ?thesis
    by (metis Int_lower1 frontier_of_restrict inf_assoc)
qed

lemma connectedin_continuous_map_image:
  assumes f: "continuous_map X Y f" and "connectedin X S"
  shows "connectedin Y (f ` S)"
proof -
  have "S \<subseteq> topspace X" and *:
    "\<And>E1 E2. openin X E1 \<longrightarrow> openin X E2 \<longrightarrow> E1 \<inter> E2 \<inter> S = {} \<longrightarrow> S \<subseteq> E1 \<union> E2 \<longrightarrow> E1 \<inter> S = {} \<or> E2 \<inter> S = {}"
    using \<open>connectedin X S\<close> by (auto simp: connectedin)
  show ?thesis
    unfolding connectedin connected_space_def
  proof (intro conjI notI; clarify)
    show "f x \<in> topspace Y" if  "x \<in> S" for x
      using \<open>S \<subseteq> topspace X\<close> continuous_map_image_subset_topspace f that by blast
  next
    fix U V
    let ?U = "{x \<in> topspace X. f x \<in> U}"
    let ?V = "{x \<in> topspace X. f x \<in> V}"
    assume UV: "openin Y U" "openin Y V" "f ` S \<subseteq> U \<union> V" "U \<inter> V \<inter> f ` S = {}" "U \<inter> f ` S \<noteq> {}" "V \<inter> f ` S \<noteq> {}"
    then have 1: "?U \<inter> ?V \<inter> S = {}"
      by auto
    have 2: "openin X ?U" "openin X ?V"
      using \<open>openin Y U\<close> \<open>openin Y V\<close> continuous_map f by fastforce+
    show "False"
      using * [of ?U ?V] UV \<open>S \<subseteq> topspace X\<close>
      by (auto simp: 1 2)
  qed
qed

lemma homeomorphic_connected_space:
     "X homeomorphic_space Y \<Longrightarrow> connected_space X \<longleftrightarrow> connected_space Y"
  unfolding homeomorphic_space_def homeomorphic_maps_def
  by (metis connected_space_subconnected connectedin_continuous_map_image connectedin_topspace continuous_map_image_subset_topspace image_eqI image_subset_iff)

lemma homeomorphic_map_connectedness:
  assumes f: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "connectedin Y (f ` U) \<longleftrightarrow> connectedin X U"
proof -
  have 1: "f ` U \<subseteq> topspace Y \<longleftrightarrow> U \<subseteq> topspace X"
    using U f homeomorphic_imp_surjective_map by blast
  moreover have "connected_space (subtopology Y (f ` U)) \<longleftrightarrow> connected_space (subtopology X U)"
  proof (rule homeomorphic_connected_space)
    have "f ` U \<subseteq> topspace Y"
      by (simp add: U 1)
    then have "topspace Y \<inter> f ` U = f ` U"
      by (simp add: subset_antisym)
    then show "subtopology Y (f ` U) homeomorphic_space subtopology X U"
      by (metis (no_types) Int_subset_iff U f homeomorphic_map_imp_homeomorphic_space homeomorphic_map_subtopologies homeomorphic_space_sym subset_antisym subset_refl)
  qed
  ultimately show ?thesis
    by (auto simp: connectedin_def)
qed

lemma homeomorphic_map_connectedness_eq:
   "homeomorphic_map X Y f
        \<Longrightarrow> connectedin X U \<longleftrightarrow>
             U \<subseteq> topspace X \<and> connectedin Y (f ` U)"
  using homeomorphic_map_connectedness connectedin_subset_topspace by metis

lemma connectedin_discrete_topology:
   "connectedin (discrete_topology U) S \<longleftrightarrow> S \<subseteq> U \<and> (\<exists>a. S \<subseteq> {a})"
proof (cases "S \<subseteq> U")
  case True
  show ?thesis
  proof (cases "S = {}")
    case False
    moreover have "connectedin (discrete_topology U) S \<longleftrightarrow> (\<exists>a. S = {a})"
    proof
      show "connectedin (discrete_topology U) S \<Longrightarrow> \<exists>a. S = {a}"
        using False connectedin_inter_frontier_of insert_Diff by fastforce
    qed (use True in auto)
    ultimately show ?thesis
      by auto
  qed simp
next
  case False
  then show ?thesis
    by (simp add: connectedin_def)
qed

lemma connected_space_discrete_topology:
     "connected_space (discrete_topology U) \<longleftrightarrow> (\<exists>a. U \<subseteq> {a})"
  by (metis connectedin_discrete_topology connectedin_topspace order_refl topspace_discrete_topology)


subsection\<open>Compact sets\<close>

definition compactin where
 "compactin X S \<longleftrightarrow>
     S \<subseteq> topspace X \<and>
     (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> S \<subseteq> \<Union>\<U>
          \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>))"

definition compact_space where
   "compact_space X \<equiv> compactin X (topspace X)"

lemma compact_space_alt:
   "compact_space X \<longleftrightarrow>
        (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> topspace X \<subseteq> \<Union>\<U>
            \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> topspace X \<subseteq> \<Union>\<F>))"
  by (simp add: compact_space_def compactin_def)

lemma compact_space:
   "compact_space X \<longleftrightarrow>
        (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> \<Union>\<U> = topspace X
            \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> \<Union>\<F> = topspace X))"
  unfolding compact_space_alt
  using openin_subset by fastforce

lemma compactinD:
  "\<lbrakk>compactin X S; \<And>U. U \<in> \<U> \<Longrightarrow> openin X U; S \<subseteq> \<Union>\<U>\<rbrakk> \<Longrightarrow> \<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>"
  by (auto simp: compactin_def)

lemma compactin_euclidean_iff [simp]: "compactin euclidean S \<longleftrightarrow> compact S"
  by (simp add: compact_eq_Heine_Borel compactin_def) meson

lemma compactin_absolute [simp]:
   "compactin (subtopology X S) S \<longleftrightarrow> compactin X S"
proof -
  have eq: "(\<forall>U \<in> \<U>. \<exists>Y. openin X Y \<and> U = Y \<inter> S) \<longleftrightarrow> \<U> \<subseteq> (\<lambda>Y. Y \<inter> S) ` {y. openin X y}" for \<U>
    by auto
  show ?thesis
    by (auto simp: compactin_def openin_subtopology eq imp_conjL all_subset_image ex_finite_subset_image)
qed

lemma compactin_subspace: "compactin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> compact_space (subtopology X S)"
  unfolding compact_space_def topspace_subtopology
  by (metis compactin_absolute compactin_def inf.absorb2)

lemma compact_space_subtopology: "compactin X S \<Longrightarrow> compact_space (subtopology X S)"
  by (simp add: compactin_subspace)

lemma compactin_subtopology: "compactin (subtopology X S) T \<longleftrightarrow> compactin X T \<and> T \<subseteq> S"
  by (metis compactin_subspace inf.absorb_iff2 le_inf_iff subtopology_subtopology topspace_subtopology)

lemma compactin_subset_topspace: "compactin X S \<Longrightarrow> S \<subseteq> topspace X"
  by (simp add: compactin_subspace)

lemma compactin_contractive:
   "\<lbrakk>compactin X' S; topspace X' = topspace X;
     \<And>U. openin X U \<Longrightarrow> openin X' U\<rbrakk> \<Longrightarrow> compactin X S"
  by (simp add: compactin_def)

lemma finite_imp_compactin:
   "\<lbrakk>S \<subseteq> topspace X; finite S\<rbrakk> \<Longrightarrow> compactin X S"
  by (metis compactin_subspace compact_space finite_UnionD inf.absorb_iff2 order_refl topspace_subtopology)

lemma compactin_empty [iff]: "compactin X {}"
  by (simp add: finite_imp_compactin)

lemma compact_space_topspace_empty:
   "topspace X = {} \<Longrightarrow> compact_space X"
  by (simp add: compact_space_def)

lemma finite_imp_compactin_eq:
   "finite S \<Longrightarrow> (compactin X S \<longleftrightarrow> S \<subseteq> topspace X)"
  using compactin_subset_topspace finite_imp_compactin by blast

lemma compactin_sing [simp]: "compactin X {a} \<longleftrightarrow> a \<in> topspace X"
  by (simp add: finite_imp_compactin_eq)

lemma closed_compactin:
  assumes XK: "compactin X K" and "C \<subseteq> K" and XC: "closedin X C"
  shows "compactin X C"
  unfolding compactin_def
proof (intro conjI allI impI)
  show "C \<subseteq> topspace X"
    by (simp add: XC closedin_subset)
next
  fix \<U> :: "'a set set"
  assume \<U>: "Ball \<U> (openin X) \<and> C \<subseteq> \<Union>\<U>"
  have "(\<forall>U\<in>insert (topspace X - C) \<U>. openin X U)"
    using XC \<U> by blast
  moreover have "K \<subseteq> \<Union>(insert (topspace X - C) \<U>)"
    using \<U> XK compactin_subset_topspace by fastforce
  ultimately obtain \<F> where "finite \<F>" "\<F> \<subseteq> insert (topspace X - C) \<U>" "K \<subseteq> \<Union>\<F>"
    using assms unfolding compactin_def by metis
  moreover have "openin X (topspace X - C)"
    using XC by auto
  ultimately show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> C \<subseteq> \<Union>\<F>"
    using \<open>C \<subseteq> K\<close>
    by (rule_tac x="\<F> - {topspace X - C}" in exI) auto
qed

lemma closedin_compact_space:
   "\<lbrakk>compact_space X; closedin X S\<rbrakk> \<Longrightarrow> compactin X S"
  by (simp add: closed_compactin closedin_subset compact_space_def)

lemma compact_Int_closedin:
  assumes "compactin X S" "closedin X T" shows "compactin X (S \<inter> T)"
proof -
  have "compactin (subtopology X S) (S \<inter> T)"
    by (metis assms closedin_compact_space closedin_subtopology compactin_subspace inf_commute)
  then show ?thesis
    by (simp add: compactin_subtopology)
qed

lemma closed_Int_compactin: "\<lbrakk>closedin X S; compactin X T\<rbrakk> \<Longrightarrow> compactin X (S \<inter> T)"
  by (metis compact_Int_closedin inf_commute)

lemma compactin_Un:
  assumes S: "compactin X S" and T: "compactin X T" shows "compactin X (S \<union> T)"
  unfolding compactin_def
proof (intro conjI allI impI)
  show "S \<union> T \<subseteq> topspace X"
    using assms by (auto simp: compactin_def)
next
  fix \<U> :: "'a set set"
  assume \<U>: "Ball \<U> (openin X) \<and> S \<union> T \<subseteq> \<Union>\<U>"
  with S obtain \<F> where \<V>: "finite \<F>" "\<F> \<subseteq> \<U>" "S \<subseteq> \<Union>\<F>"
    unfolding compactin_def by (meson sup.bounded_iff)
  obtain \<W> where "finite \<W>" "\<W> \<subseteq> \<U>" "T \<subseteq> \<Union>\<W>"
    using \<U> T
    unfolding compactin_def by (meson sup.bounded_iff)
  with \<V> show "\<exists>\<V>. finite \<V> \<and> \<V> \<subseteq> \<U> \<and> S \<union> T \<subseteq> \<Union>\<V>"
    by (rule_tac x="\<F> \<union> \<W>" in exI) auto
qed

lemma compactin_Union:
   "\<lbrakk>finite \<F>; \<And>S. S \<in> \<F> \<Longrightarrow> compactin X S\<rbrakk> \<Longrightarrow> compactin X (\<Union>\<F>)"
by (induction rule: finite_induct) (simp_all add: compactin_Un)

lemma compactin_subtopology_imp_compact:
  assumes "compactin (subtopology X S) K" shows "compactin X K"
  using assms
proof (clarsimp simp add: compactin_def)
  fix \<U>
  define \<V> where "\<V> \<equiv> (\<lambda>U. U \<inter> S) ` \<U>"
  assume "K \<subseteq> topspace X" and "K \<subseteq> S" and "\<forall>x\<in>\<U>. openin X x" and "K \<subseteq> \<Union>\<U>"
  then have "\<forall>V \<in> \<V>. openin (subtopology X S) V" "K \<subseteq> \<Union>\<V>"
    unfolding \<V>_def by (auto simp: openin_subtopology)
  moreover
  assume "\<forall>\<U>. (\<forall>x\<in>\<U>. openin (subtopology X S) x) \<and> K \<subseteq> \<Union>\<U> \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> K \<subseteq> \<Union>\<F>)"
  ultimately obtain \<F> where "finite \<F>" "\<F> \<subseteq> \<V>" "K \<subseteq> \<Union>\<F>"
    by meson
  then have \<F>: "\<exists>U. U \<in> \<U> \<and> V = U \<inter> S" if "V \<in> \<F>" for V
    unfolding \<V>_def using that by blast
  let ?\<F> = "(\<lambda>F. @U. U \<in> \<U> \<and> F = U \<inter> S) ` \<F>"
  show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> K \<subseteq> \<Union>\<F>"
  proof (intro exI conjI)
    show "finite ?\<F>"
      using \<open>finite \<F>\<close> by blast
    show "?\<F> \<subseteq> \<U>"
      using someI_ex [OF \<F>] by blast
    show "K \<subseteq> \<Union>?\<F>"
    proof clarsimp
      fix x
      assume "x \<in> K"
      then show "\<exists>V \<in> \<F>. x \<in> (SOME U. U \<in> \<U> \<and> V = U \<inter> S)"
        using \<open>K \<subseteq> \<Union>\<F>\<close> someI_ex [OF \<F>]
        by (metis (no_types, lifting) IntD1 Union_iff subsetCE)
    qed
  qed
qed

lemma compact_imp_compactin_subtopology:
  assumes "compactin X K" "K \<subseteq> S" shows "compactin (subtopology X S) K"
  using assms
proof (clarsimp simp add: compactin_def)
  fix \<U> :: "'a set set"
  define \<V> where "\<V> \<equiv> {V. openin X V \<and> (\<exists>U \<in> \<U>. U = V \<inter> S)}"
  assume "K \<subseteq> S" and "K \<subseteq> topspace X" and "\<forall>U\<in>\<U>. openin (subtopology X S) U" and "K \<subseteq> \<Union>\<U>"
  then have "\<forall>V \<in> \<V>. openin X V" "K \<subseteq> \<Union>\<V>"
    unfolding \<V>_def by (fastforce simp: subset_eq openin_subtopology)+
  moreover
  assume "\<forall>\<U>. (\<forall>U\<in>\<U>. openin X U) \<and> K \<subseteq> \<Union>\<U> \<longrightarrow> (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> K \<subseteq> \<Union>\<F>)"
  ultimately obtain \<F> where "finite \<F>" "\<F> \<subseteq> \<V>" "K \<subseteq> \<Union>\<F>"
    by meson
  let ?\<F> = "(\<lambda>F. F \<inter> S) ` \<F>"
  show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> K \<subseteq> \<Union>\<F>"
  proof (intro exI conjI)
    show "finite ?\<F>"
      using \<open>finite \<F>\<close> by blast
    show "?\<F> \<subseteq> \<U>"
      using \<V>_def \<open>\<F> \<subseteq> \<V>\<close> by blast
    show "K \<subseteq> \<Union>?\<F>"
      using \<open>K \<subseteq> \<Union>\<F>\<close> assms(2) by auto
  qed
qed


proposition compact_space_fip:
   "compact_space X \<longleftrightarrow>
    (\<forall>\<U>. (\<forall>C\<in>\<U>. closedin X C) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> \<Inter>\<F> \<noteq> {}) \<longrightarrow> \<Inter>\<U> \<noteq> {})"
   (is "_ = ?rhs")
proof (cases "topspace X = {}")
  case True
  then show ?thesis
unfolding compact_space_def
  by (metis Sup_bot_conv(1) closedin_topspace_empty compactin_empty finite.emptyI finite_UnionD order_refl)
next
  case False
  show ?thesis
  proof safe
    fix \<U> :: "'a set set"
    assume * [rule_format]: "\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> \<Inter>\<F> \<noteq> {}"
    define \<V> where "\<V> \<equiv> (\<lambda>S. topspace X - S) ` \<U>"
    assume clo: "\<forall>C\<in>\<U>. closedin X C" and [simp]: "\<Inter>\<U> = {}"
    then have "\<forall>V \<in> \<V>. openin X V" "topspace X \<subseteq> \<Union>\<V>"
      by (auto simp: \<V>_def)
    moreover assume [unfolded compact_space_alt, rule_format, of \<V>]: "compact_space X"
    ultimately obtain \<F> where \<F>: "finite \<F>" "\<F> \<subseteq> \<U>" "topspace X \<subseteq> topspace X - \<Inter>\<F>"
      by (auto simp: ex_finite_subset_image \<V>_def)
    moreover have "\<F> \<noteq> {}"
      using \<F> \<open>topspace X \<noteq> {}\<close> by blast
    ultimately show "False"
      using * [of \<F>]
      by auto (metis Diff_iff Inter_iff clo closedin_def subsetD)
  next
    assume R [rule_format]: ?rhs
    show "compact_space X"
      unfolding compact_space_alt
    proof clarify
      fix \<U> :: "'a set set"
      define \<V> where "\<V> \<equiv> (\<lambda>S. topspace X - S) ` \<U>"
      assume "\<forall>C\<in>\<U>. openin X C" and "topspace X \<subseteq> \<Union>\<U>"
      with \<open>topspace X \<noteq> {}\<close> have *: "\<forall>V \<in> \<V>. closedin X V" "\<U> \<noteq> {}"
        by (auto simp: \<V>_def)
      show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> topspace X \<subseteq> \<Union>\<F>"
      proof (rule ccontr; simp)
        assume "\<forall>\<F>\<subseteq>\<U>. finite \<F> \<longrightarrow> \<not> topspace X \<subseteq> \<Union>\<F>"
        then have "\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<V> \<longrightarrow> \<Inter>\<F> \<noteq> {}"
          by (simp add: \<V>_def all_finite_subset_image)
        with \<open>topspace X \<subseteq> \<Union>\<U>\<close> show False
          using R [of \<V>] * by (simp add: \<V>_def)
      qed
    qed
  qed
qed

corollary compactin_fip:
  "compactin X S \<longleftrightarrow>
    S \<subseteq> topspace X \<and>
    (\<forall>\<U>. (\<forall>C\<in>\<U>. closedin X C) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}) \<longrightarrow> S \<inter> \<Inter>\<U> \<noteq> {})"
proof (cases "S = {}")
  case False
  show ?thesis
  proof (cases "S \<subseteq> topspace X")
    case True
    then have "compactin X S \<longleftrightarrow>
          (\<forall>\<U>. \<U> \<subseteq> (\<lambda>T. S \<inter> T) ` {T. closedin X T} \<longrightarrow>
           (\<forall>\<F>. finite \<F> \<longrightarrow> \<F> \<subseteq> \<U> \<longrightarrow> \<Inter>\<F> \<noteq> {}) \<longrightarrow> \<Inter>\<U> \<noteq> {})"
      by (simp add: compact_space_fip compactin_subspace closedin_subtopology image_def subset_eq Int_commute imp_conjL)
    also have "\<dots> = (\<forall>\<U>\<subseteq>Collect (closedin X). (\<forall>\<F>. finite \<F> \<longrightarrow> \<F> \<subseteq> (\<inter>) S ` \<U> \<longrightarrow> \<Inter>\<F> \<noteq> {}) \<longrightarrow> \<Inter> ((\<inter>) S ` \<U>) \<noteq> {})"
      by (simp add: all_subset_image)
    also have "\<dots> = (\<forall>\<U>. (\<forall>C\<in>\<U>. closedin X C) \<and> (\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}) \<longrightarrow> S \<inter> \<Inter>\<U> \<noteq> {})"
    proof -
      have eq: "((\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> \<Inter> ((\<inter>) S ` \<F>) \<noteq> {}) \<longrightarrow> \<Inter> ((\<inter>) S ` \<U>) \<noteq> {}) \<longleftrightarrow>
                ((\<forall>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<longrightarrow> S \<inter> \<Inter>\<F> \<noteq> {}) \<longrightarrow> S \<inter> \<Inter>\<U> \<noteq> {})"  for \<U>
        by simp (use \<open>S \<noteq> {}\<close> in blast)
      show ?thesis
        unfolding imp_conjL [symmetric] all_finite_subset_image eq by blast
    qed
    finally show ?thesis
      using True by simp
  qed (simp add: compactin_subspace)
qed force

corollary compact_space_imp_nest:
  fixes C :: "nat \<Rightarrow> 'a set"
  assumes "compact_space X" and clo: "\<And>n. closedin X (C n)"
    and ne: "\<And>n. C n \<noteq> {}" and inc: "\<And>m n. m \<le> n \<Longrightarrow> C n \<subseteq> C m"
  shows "(\<Inter>n. C n) \<noteq> {}"
proof -
  let ?\<U> = "range (\<lambda>n. \<Inter>m \<le> n. C m)"
  have "closedin X A" if "A \<in> ?\<U>" for A
    using that clo by auto
  moreover have "(\<Inter>n\<in>K. \<Inter>m \<le> n. C m) \<noteq> {}" if "finite K" for K
  proof -
    obtain n where "\<And>k. k \<in> K \<Longrightarrow> k \<le> n"
      using Max.coboundedI \<open>finite K\<close> by blast
    with inc have "C n \<subseteq> (\<Inter>n\<in>K. \<Inter>m \<le> n. C m)"
    by blast
  with ne [of n] show ?thesis
    by blast
  qed
  ultimately show ?thesis
    using \<open>compact_space X\<close> [unfolded compact_space_fip, rule_format, of ?\<U>]
    by (simp add: all_finite_subset_image INT_extend_simps UN_atMost_UNIV del: INT_simps)
qed

lemma compactin_discrete_topology:
   "compactin (discrete_topology X) S \<longleftrightarrow> S \<subseteq> X \<and> finite S" (is "?lhs = ?rhs")
proof (intro iffI conjI)
  assume L: ?lhs
  then show "S \<subseteq> X"
    by (auto simp: compactin_def)
  have *: "\<And>\<U>. Ball \<U> (openin (discrete_topology X)) \<and> S \<subseteq> \<Union>\<U> \<Longrightarrow>
        (\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>)"
    using L by (auto simp: compactin_def)
  show "finite S"
    using * [of "(\<lambda>x. {x}) ` X"] \<open>S \<subseteq> X\<close>
    by clarsimp (metis UN_singleton finite_subset_image infinite_super)
next
  assume ?rhs
  then show ?lhs
    by (simp add: finite_imp_compactin)
qed

lemma compact_space_discrete_topology: "compact_space(discrete_topology X) \<longleftrightarrow> finite X"
  by (simp add: compactin_discrete_topology compact_space_def)

lemma compact_space_imp_Bolzano_Weierstrass:
  assumes "compact_space X" "infinite S" "S \<subseteq> topspace X"
  shows "X derived_set_of S \<noteq> {}"
proof
  assume X: "X derived_set_of S = {}"
  then have "closedin X S"
    by (simp add: closedin_contains_derived_set assms)
  then have "compactin X S"
    by (rule closedin_compact_space [OF \<open>compact_space X\<close>])
  with X show False
    by (metis \<open>infinite S\<close> compactin_subspace compact_space_discrete_topology inf_bot_right subtopology_eq_discrete_topology_eq)
qed

lemma compactin_imp_Bolzano_Weierstrass:
   "\<lbrakk>compactin X S; infinite T \<and> T \<subseteq> S\<rbrakk> \<Longrightarrow> S \<inter> X derived_set_of T \<noteq> {}"
  using compact_space_imp_Bolzano_Weierstrass [of "subtopology X S"]
  by (simp add: compactin_subspace derived_set_of_subtopology inf_absorb2)

lemma compact_closure_of_imp_Bolzano_Weierstrass:
   "\<lbrakk>compactin X (X closure_of S); infinite T; T \<subseteq> S; T \<subseteq> topspace X\<rbrakk> \<Longrightarrow> X derived_set_of T \<noteq> {}"
  using closure_of_mono closure_of_subset compactin_imp_Bolzano_Weierstrass by fastforce

lemma discrete_compactin_eq_finite:
   "S \<inter> X derived_set_of S = {} \<Longrightarrow> compactin X S \<longleftrightarrow> S \<subseteq> topspace X \<and> finite S"
  by (meson compactin_imp_Bolzano_Weierstrass finite_imp_compactin_eq order_refl)

lemma discrete_compact_space_eq_finite:
   "X derived_set_of (topspace X) = {} \<Longrightarrow> (compact_space X \<longleftrightarrow> finite(topspace X))"
  by (metis compact_space_discrete_topology discrete_topology_unique_derived_set)

lemma image_compactin:
  assumes cpt: "compactin X S" and cont: "continuous_map X Y f"
  shows "compactin Y (f ` S)"
  unfolding compactin_def
proof (intro conjI allI impI)
  show "f ` S \<subseteq> topspace Y"
    using compactin_subset_topspace cont continuous_map_image_subset_topspace cpt by blast
next
  fix \<U> :: "'b set set"
  assume \<U>: "Ball \<U> (openin Y) \<and> f ` S \<subseteq> \<Union>\<U>"
  define \<V> where "\<V> \<equiv> (\<lambda>U. {x \<in> topspace X. f x \<in> U}) ` \<U>"
  have "S \<subseteq> topspace X"
    and *: "\<And>\<U>. \<lbrakk>\<forall>U\<in>\<U>. openin X U; S \<subseteq> \<Union>\<U>\<rbrakk> \<Longrightarrow> \<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> S \<subseteq> \<Union>\<F>"
    using cpt by (auto simp: compactin_def)
  obtain \<F> where \<F>: "finite \<F>" "\<F> \<subseteq> \<V>" "S \<subseteq> \<Union>\<F>"
  proof -
    have 1: "\<forall>U\<in>\<V>. openin X U"
      unfolding \<V>_def using \<U> cont[unfolded continuous_map] by blast
    have 2: "S \<subseteq> \<Union>\<V>"
      unfolding \<V>_def using compactin_subset_topspace cpt \<U> by fastforce
    show thesis
      using * [OF 1 2] that by metis
  qed
  have "\<forall>v \<in> \<V>. \<exists>U. U \<in> \<U> \<and> v = {x \<in> topspace X. f x \<in> U}"
    using \<V>_def by blast
  then obtain U where U: "\<forall>v \<in> \<V>. U v \<in> \<U> \<and> v = {x \<in> topspace X. f x \<in> U v}"
    by metis
  show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> f ` S \<subseteq> \<Union>\<F>"
  proof (intro conjI exI)
    show "finite (U ` \<F>)"
      by (simp add: \<open>finite \<F>\<close>)
  next
    show "U ` \<F> \<subseteq> \<U>"
      using \<open>\<F> \<subseteq> \<V>\<close> U by auto
  next
    show "f ` S \<subseteq> \<Union> (U ` \<F>)"
      using \<F>(2-3) U UnionE subset_eq U by fastforce
  qed
qed


lemma homeomorphic_compact_space:
  assumes "X homeomorphic_space Y"
  shows "compact_space X \<longleftrightarrow> compact_space Y"
    using homeomorphic_space_sym
    by (metis assms compact_space_def homeomorphic_eq_everything_map homeomorphic_space image_compactin)

lemma homeomorphic_map_compactness:
  assumes hom: "homeomorphic_map X Y f" and U: "U \<subseteq> topspace X"
  shows "compactin Y (f ` U) \<longleftrightarrow> compactin X U"
proof -
  have "f ` U \<subseteq> topspace Y"
    using hom U homeomorphic_imp_surjective_map by blast
  moreover have "homeomorphic_map (subtopology X U) (subtopology Y (f ` U)) f"
    using U hom homeomorphic_imp_surjective_map by (blast intro: homeomorphic_map_subtopologies)
  then have "compact_space (subtopology Y (f ` U)) = compact_space (subtopology X U)"
    using homeomorphic_compact_space homeomorphic_map_imp_homeomorphic_space by blast
  ultimately show ?thesis
    by (simp add: compactin_subspace U)
qed

lemma homeomorphic_map_compactness_eq:
   "homeomorphic_map X Y f
        \<Longrightarrow> compactin X U \<longleftrightarrow> U \<subseteq> topspace X \<and> compactin Y (f ` U)"
  by (meson compactin_subset_topspace homeomorphic_map_compactness)


subsection\<open>Embedding maps\<close>

definition embedding_map
  where "embedding_map X Y f \<equiv> homeomorphic_map X (subtopology Y (f ` (topspace X))) f"

lemma embedding_map_eq:
   "\<lbrakk>embedding_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> embedding_map X Y g"
  unfolding embedding_map_def
  by (metis homeomorphic_map_eq image_cong)

lemma embedding_map_compose:
  assumes "embedding_map X X' f" "embedding_map X' X'' g"
  shows "embedding_map X X'' (g \<circ> f)"
proof -
  have hm: "homeomorphic_map X (subtopology X' (f ` topspace X)) f" "homeomorphic_map X' (subtopology X'' (g ` topspace X')) g"
    using assms by (auto simp: embedding_map_def)
  then obtain C where "g ` topspace X' \<inter> C = (g \<circ> f) ` topspace X"
    by (metis (no_types) Int_absorb1 continuous_map_image_subset_topspace continuous_map_in_subtopology homeomorphic_eq_everything_map image_comp image_mono)
  then have "homeomorphic_map (subtopology X' (f ` topspace X)) (subtopology X'' ((g \<circ> f) ` topspace X)) g"
    by (metis hm homeomorphic_imp_surjective_map homeomorphic_map_subtopologies image_comp subtopology_subtopology topspace_subtopology)
  then show ?thesis
  unfolding embedding_map_def
  using hm(1) homeomorphic_map_compose by blast
qed

lemma surjective_embedding_map:
   "embedding_map X Y f \<and> f ` (topspace X) = topspace Y \<longleftrightarrow> homeomorphic_map X Y f"
  by (force simp: embedding_map_def homeomorphic_eq_everything_map)

lemma embedding_map_in_subtopology:
   "embedding_map X (subtopology Y S) f \<longleftrightarrow> embedding_map X Y f \<and> f ` (topspace X) \<subseteq> S"  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding embedding_map_def
    by (metis continuous_map_in_subtopology homeomorphic_imp_continuous_map inf_absorb2 subtopology_subtopology)
qed (simp add: embedding_map_def inf.absorb_iff2 subtopology_subtopology)

lemma injective_open_imp_embedding_map:
   "\<lbrakk>continuous_map X Y f; open_map X Y f; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> embedding_map X Y f"
  unfolding embedding_map_def
  by (simp add: continuous_map_in_subtopology continuous_open_quotient_map eq_iff homeomorphic_map_def open_map_imp_subset open_map_into_subtopology)

lemma injective_closed_imp_embedding_map:
  "\<lbrakk>continuous_map X Y f; closed_map X Y f; inj_on f (topspace X)\<rbrakk> \<Longrightarrow> embedding_map X Y f"
  unfolding embedding_map_def
  by (simp add: closed_map_imp_subset closed_map_into_subtopology continuous_closed_quotient_map 
                continuous_map_in_subtopology dual_order.eq_iff homeomorphic_map_def)

lemma embedding_map_imp_homeomorphic_space:
   "embedding_map X Y f \<Longrightarrow> X homeomorphic_space (subtopology Y (f ` (topspace X)))"
  unfolding embedding_map_def
  using homeomorphic_space by blast

lemma embedding_imp_closed_map:
   "\<lbrakk>embedding_map X Y f; closedin Y (f ` topspace X)\<rbrakk> \<Longrightarrow> closed_map X Y f"
  unfolding closed_map_def
  by (auto simp: closedin_closed_subtopology embedding_map_def homeomorphic_map_closedness_eq)


subsection\<open>Retraction and section maps\<close>

definition retraction_maps :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool"
  where "retraction_maps X Y f g \<equiv>
           continuous_map X Y f \<and> continuous_map Y X g \<and> (\<forall>x \<in> topspace Y. f(g x) = x)"

definition section_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "section_map X Y f \<equiv> \<exists>g. retraction_maps Y X g f"

definition retraction_map :: "'a topology \<Rightarrow> 'b topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "retraction_map X Y f \<equiv> \<exists>g. retraction_maps X Y f g"

lemma retraction_maps_eq:
   "\<lbrakk>retraction_maps X Y f g; \<And>x. x \<in> topspace X \<Longrightarrow> f x = f' x; \<And>x. x \<in> topspace Y \<Longrightarrow> g x = g' x\<rbrakk>
        \<Longrightarrow> retraction_maps X Y f' g'"
  unfolding retraction_maps_def by (metis (no_types, lifting) continuous_map_def continuous_map_eq)

lemma section_map_eq:
   "\<lbrakk>section_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> section_map X Y g"
  unfolding section_map_def using retraction_maps_eq by blast

lemma retraction_map_eq:
   "\<lbrakk>retraction_map X Y f; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> retraction_map X Y g"
  unfolding retraction_map_def using retraction_maps_eq by blast

lemma homeomorphic_imp_retraction_maps:
   "homeomorphic_maps X Y f g \<Longrightarrow> retraction_maps X Y f g"
  by (simp add: homeomorphic_maps_def retraction_maps_def)

lemma section_and_retraction_eq_homeomorphic_map:
   "section_map X Y f \<and> retraction_map X Y f \<longleftrightarrow> homeomorphic_map X Y f"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain g g' where f: "continuous_map X Y f" 
    and g: "continuous_map Y X g" "\<forall>x\<in>topspace X. g (f x) = x"
    and g': "continuous_map Y X g'" "\<forall>x\<in>topspace Y. f (g' x) = x"
    by (auto simp: retraction_map_def retraction_maps_def section_map_def)
  then have "homeomorphic_maps X Y f g"
    by (force simp add: homeomorphic_maps_def continuous_map_def)
  then show ?rhs
    using homeomorphic_map_maps by blast
next
  assume ?rhs
  then show ?lhs
    unfolding retraction_map_def section_map_def
    by (meson homeomorphic_imp_retraction_maps homeomorphic_map_maps homeomorphic_maps_sym)
qed

lemma section_imp_embedding_map:
   "section_map X Y f \<Longrightarrow> embedding_map X Y f"
  unfolding section_map_def embedding_map_def homeomorphic_map_maps retraction_maps_def homeomorphic_maps_def
  by (force simp: continuous_map_in_subtopology continuous_map_from_subtopology)

lemma retraction_imp_quotient_map:
  assumes "retraction_map X Y f"
  shows "quotient_map X Y f"
  unfolding quotient_map_def
proof (intro conjI subsetI allI impI)
  show "f ` topspace X = topspace Y"
    using assms by (force simp: retraction_map_def retraction_maps_def continuous_map_def)
next
  fix U
  assume U: "U \<subseteq> topspace Y"
  have "openin Y U"
    if "\<forall>x\<in>topspace Y. g x \<in> topspace X" "\<forall>x\<in>topspace Y. f (g x) = x"
       "openin Y {x \<in> topspace Y. g x \<in> {x \<in> topspace X. f x \<in> U}}" for g
    using openin_subopen U that by fastforce
  then show "openin X {x \<in> topspace X. f x \<in> U} = openin Y U"
    using assms by (auto simp: retraction_map_def retraction_maps_def continuous_map_def)
qed

lemma retraction_maps_compose:
   "\<lbrakk>retraction_maps X Y f f'; retraction_maps Y Z g g'\<rbrakk> \<Longrightarrow> retraction_maps X Z (g \<circ> f) (f' \<circ> g')"
  by (clarsimp simp: retraction_maps_def continuous_map_compose) (simp add: continuous_map_def)

lemma retraction_map_compose:
   "\<lbrakk>retraction_map X Y f; retraction_map Y Z g\<rbrakk> \<Longrightarrow> retraction_map X Z (g \<circ> f)"
  by (meson retraction_map_def retraction_maps_compose)

lemma section_map_compose:
   "\<lbrakk>section_map X Y f; section_map Y Z g\<rbrakk> \<Longrightarrow> section_map X Z (g \<circ> f)"
  by (meson retraction_maps_compose section_map_def)

lemma surjective_section_eq_homeomorphic_map:
   "section_map X Y f \<and> f ` (topspace X) = topspace Y \<longleftrightarrow> homeomorphic_map X Y f"
  by (meson section_and_retraction_eq_homeomorphic_map section_imp_embedding_map surjective_embedding_map)

lemma surjective_retraction_or_section_map:
   "f ` (topspace X) = topspace Y \<Longrightarrow> retraction_map X Y f \<or> section_map X Y f \<longleftrightarrow> retraction_map X Y f"
  using section_and_retraction_eq_homeomorphic_map surjective_section_eq_homeomorphic_map by fastforce

lemma retraction_imp_surjective_map:
   "retraction_map X Y f \<Longrightarrow> f ` (topspace X) = topspace Y"
  by (simp add: retraction_imp_quotient_map quotient_imp_surjective_map)

lemma section_imp_injective_map:
   "\<lbrakk>section_map X Y f; x \<in> topspace X; y \<in> topspace X\<rbrakk> \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  by (metis (mono_tags, hide_lams) retraction_maps_def section_map_def)

lemma retraction_maps_to_retract_maps:
   "retraction_maps X Y r s
        \<Longrightarrow> retraction_maps X (subtopology X (s ` (topspace Y))) (s \<circ> r) id"
  unfolding retraction_maps_def
  by (auto simp: continuous_map_compose continuous_map_into_subtopology continuous_map_from_subtopology)
subsection \<open>Continuity\<close>

lemma continuous_on_open:
  "continuous_on S f \<longleftrightarrow>
    (\<forall>T. openin (top_of_set (f ` S)) T \<longrightarrow>
      openin (top_of_set S) (S \<inter> f -` T))"
  unfolding continuous_on_open_invariant openin_open Int_def vimage_def Int_commute
  by (simp add: imp_ex imageI conj_commute eq_commute cong: conj_cong)

lemma continuous_on_closed:
  "continuous_on S f \<longleftrightarrow>
    (\<forall>T. closedin (top_of_set (f ` S)) T \<longrightarrow>
      closedin (top_of_set S) (S \<inter> f -` T))"
  unfolding continuous_on_closed_invariant closedin_closed Int_def vimage_def Int_commute
  by (simp add: imp_ex imageI conj_commute eq_commute cong: conj_cong)

lemma continuous_on_imp_closedin:
  assumes "continuous_on S f" "closedin (top_of_set (f ` S)) T"
  shows "closedin (top_of_set S) (S \<inter> f -` T)"
  using assms continuous_on_closed by blast

lemma continuous_map_subtopology_eu [simp]:
  "continuous_map (top_of_set S) (subtopology euclidean T) h \<longleftrightarrow> continuous_on S h \<and> h ` S \<subseteq> T"
  by (simp add: continuous_map_in_subtopology)

lemma continuous_map_euclidean_top_of_set:
  assumes eq: "f -` S = UNIV" and cont: "continuous_on UNIV f"
  shows "continuous_map euclidean (top_of_set S) f"
  by (simp add: cont continuous_map_into_subtopology eq image_subset_iff_subset_vimage)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Half-global and completely global cases\<close>

lemma continuous_openin_preimage_gen:
  assumes "continuous_on S f"  "open T"
  shows "openin (top_of_set S) (S \<inter> f -` T)"
proof -
  have *: "(S \<inter> f -` T) = (S \<inter> f -` (T \<inter> f ` S))"
    by auto
  have "openin (top_of_set (f ` S)) (T \<inter> f ` S)"
    using openin_open_Int[of T "f ` S", OF assms(2)] unfolding openin_open by auto
  then show ?thesis
    using assms(1)[unfolded continuous_on_open, THEN spec[where x="T \<inter> f ` S"]]
    using * by auto
qed

lemma continuous_closedin_preimage:
  assumes "continuous_on S f" and "closed T"
  shows "closedin (top_of_set S) (S \<inter> f -` T)"
proof -
  have *: "(S \<inter> f -` T) = (S \<inter> f -` (T \<inter> f ` S))"
    by auto
  have "closedin (top_of_set (f ` S)) (T \<inter> f ` S)"
    using closedin_closed_Int[of T "f ` S", OF assms(2)]
    by (simp add: Int_commute)
  then show ?thesis
    using assms(1)[unfolded continuous_on_closed, THEN spec[where x="T \<inter> f ` S"]]
    using * by auto
qed

lemma continuous_openin_preimage_eq:
   "continuous_on S f \<longleftrightarrow> (\<forall>T. open T \<longrightarrow> openin (top_of_set S) (S \<inter> f -` T))"
  by (metis Int_commute continuous_on_open_invariant open_openin openin_subtopology)

lemma continuous_closedin_preimage_eq:
   "continuous_on S f \<longleftrightarrow>
    (\<forall>T. closed T \<longrightarrow> closedin (top_of_set S) (S \<inter> f -` T))"
  by (metis Int_commute closedin_closed continuous_on_closed_invariant)

lemma continuous_open_preimage:
  assumes contf: "continuous_on S f" and "open S" "open T"
  shows "open (S \<inter> f -` T)"
proof-
  obtain U where "open U" "(S \<inter> f -` T) = S \<inter> U"
    using continuous_openin_preimage_gen[OF contf \<open>open T\<close>]
    unfolding openin_open by auto
  then show ?thesis
    using open_Int[of S U, OF \<open>open S\<close>] by auto
qed

lemma continuous_closed_preimage:
  assumes contf: "continuous_on S f" and "closed S" "closed T"
  shows "closed (S \<inter> f -` T)"
proof-
  obtain U where "closed U" "(S \<inter> f -` T) = S \<inter> U"
    using continuous_closedin_preimage[OF contf \<open>closed T\<close>]
    unfolding closedin_closed by auto
  then show ?thesis using closed_Int[of S U, OF \<open>closed S\<close>] by auto
qed

lemma continuous_open_vimage: "open S \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> open (f -` S)"
  by (metis continuous_on_eq_continuous_within open_vimage) 
 
lemma continuous_closed_vimage: "closed S \<Longrightarrow> (\<And>x. continuous (at x) f) \<Longrightarrow> closed (f -` S)"
  by (simp add: closed_vimage continuous_on_eq_continuous_within)

lemma Times_in_interior_subtopology:
  assumes "(x, y) \<in> U" "openin (top_of_set (S \<times> T)) U"
  obtains V W where "openin (top_of_set S) V" "x \<in> V"
                    "openin (top_of_set T) W" "y \<in> W" "(V \<times> W) \<subseteq> U"
proof -
  from assms obtain E where "open E" "U = S \<times> T \<inter> E" "(x, y) \<in> E" "x \<in> S" "y \<in> T"
    by (auto simp: openin_open)
  from open_prod_elim[OF \<open>open E\<close> \<open>(x, y) \<in> E\<close>]
  obtain E1 E2 where "open E1" "open E2" "(x, y) \<in> E1 \<times> E2" "E1 \<times> E2 \<subseteq> E"
    by blast
  show ?thesis
  proof
    show "openin (top_of_set S) (E1 \<inter> S)"
      "openin (top_of_set T) (E2 \<inter> T)"
      using \<open>open E1\<close> \<open>open E2\<close>
      by (auto simp: openin_open)
    show "x \<in> E1 \<inter> S" "y \<in> E2 \<inter> T"
      using \<open>(x, y) \<in> E1 \<times> E2\<close> \<open>x \<in> S\<close> \<open>y \<in> T\<close> by auto
    show "(E1 \<inter> S) \<times> (E2 \<inter> T) \<subseteq> U"
      using \<open>E1 \<times> E2 \<subseteq> E\<close> \<open>U = _\<close>
      by (auto simp: )
  qed
qed

lemma closedin_Times:
  "closedin (top_of_set S) S' \<Longrightarrow> closedin (top_of_set T) T' \<Longrightarrow>
    closedin (top_of_set (S \<times> T)) (S' \<times> T')"
  unfolding closedin_closed using closed_Times by blast

lemma openin_Times:
  "openin (top_of_set S) S' \<Longrightarrow> openin (top_of_set T) T' \<Longrightarrow>
    openin (top_of_set (S \<times> T)) (S' \<times> T')"
  unfolding openin_open using open_Times by blast

lemma openin_Times_eq:
  fixes S :: "'a::topological_space set" and T :: "'b::topological_space set"
  shows
    "openin (top_of_set (S \<times> T)) (S' \<times> T') \<longleftrightarrow>
      S' = {} \<or> T' = {} \<or> openin (top_of_set S) S' \<and> openin (top_of_set T) T'"
    (is "?lhs = ?rhs")
proof (cases "S' = {} \<or> T' = {}")
  case True
  then show ?thesis by auto
next
  case False
  then obtain x y where "x \<in> S'" "y \<in> T'"
    by blast
  show ?thesis
  proof
    assume ?lhs
    have "openin (top_of_set S) S'"
    proof (subst openin_subopen, clarify)
      show "\<exists>U. openin (top_of_set S) U \<and> x \<in> U \<and> U \<subseteq> S'" if "x \<in> S'" for x
        using that \<open>y \<in> T'\<close> Times_in_interior_subtopology [OF _ \<open>?lhs\<close>, of x y]
        by simp (metis mem_Sigma_iff subsetD subsetI)
    qed
    moreover have "openin (top_of_set T) T'"
    proof (subst openin_subopen, clarify)
      show "\<exists>U. openin (top_of_set T) U \<and> y \<in> U \<and> U \<subseteq> T'" if "y \<in> T'" for y
        using that \<open>x \<in> S'\<close> Times_in_interior_subtopology [OF _ \<open>?lhs\<close>, of x y]
        by simp (metis mem_Sigma_iff subsetD subsetI)
    qed
    ultimately show ?rhs
      by simp
  next
    assume ?rhs
    with False show ?lhs
      by (simp add: openin_Times)
  qed
qed

lemma Lim_transform_within_openin:
  assumes f: "(f \<longlongrightarrow> l) (at a within T)"
    and "openin (top_of_set T) S" "a \<in> S"
    and eq: "\<And>x. \<lbrakk>x \<in> S; x \<noteq> a\<rbrakk> \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) (at a within T)"
proof -
  have "\<forall>\<^sub>F x in at a within T. x \<in> T \<and> x \<noteq> a"
    by (simp add: eventually_at_filter)
  moreover
  from \<open>openin _ _\<close> obtain U where "open U" "S = T \<inter> U"
    by (auto simp: openin_open)
  then have "a \<in> U" using \<open>a \<in> S\<close> by auto
  from topological_tendstoD[OF tendsto_ident_at \<open>open U\<close> \<open>a \<in> U\<close>]
  have "\<forall>\<^sub>F x in at a within T. x \<in> U" by auto
  ultimately
  have "\<forall>\<^sub>F x in at a within T. f x = g x"
    by eventually_elim (auto simp: \<open>S = _\<close> eq)
  with f show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma continuous_on_open_gen:
  assumes "f ` S \<subseteq> T"
    shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. openin (top_of_set T) U
                  \<longrightarrow> openin (top_of_set S) (S \<inter> f -` U))"
     (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (clarsimp simp add: continuous_openin_preimage_eq openin_open)
      (metis Int_assoc assms image_subset_iff_subset_vimage inf.absorb_iff1)
next
  assume R [rule_format]: ?rhs
  show ?lhs
  proof (clarsimp simp add: continuous_openin_preimage_eq)
    fix U::"'a set"
    assume "open U"
    then have "openin (top_of_set S) (S \<inter> f -` (U \<inter> T))"
      by (metis R inf_commute openin_open)
    then show "openin (top_of_set S) (S \<inter> f -` U)"
      by (metis Int_assoc Int_commute assms image_subset_iff_subset_vimage inf.absorb_iff2 vimage_Int)
  qed
qed

lemma continuous_openin_preimage:
  "\<lbrakk>continuous_on S f; f ` S \<subseteq> T; openin (top_of_set T) U\<rbrakk>
        \<Longrightarrow> openin (top_of_set S) (S \<inter> f -` U)"
  by (simp add: continuous_on_open_gen)

lemma continuous_on_closed_gen:
  assumes "f ` S \<subseteq> T"
  shows "continuous_on S f \<longleftrightarrow>
             (\<forall>U. closedin (top_of_set T) U
                  \<longrightarrow> closedin (top_of_set S) (S \<inter> f -` U))"
    (is "?lhs = ?rhs")
proof -
  have *: "U \<subseteq> T \<Longrightarrow> S \<inter> f -` (T - U) = S - (S \<inter> f -` U)" for U
    using assms by blast
  show ?thesis
  proof
    assume L: ?lhs
    show ?rhs
    proof clarify
      fix U
      assume "closedin (top_of_set T) U"
      then show "closedin (top_of_set S) (S \<inter> f -` U)"
        using L unfolding continuous_on_open_gen [OF assms]
        by (metis * closedin_def inf_le1 topspace_euclidean_subtopology)
    qed
  next
    assume R [rule_format]: ?rhs
    show ?lhs
      unfolding continuous_on_open_gen [OF assms]
      by (metis * R inf_le1 openin_closedin_eq topspace_euclidean_subtopology)
  qed
qed

lemma continuous_closedin_preimage_gen:
  assumes "continuous_on S f" "f ` S \<subseteq> T" "closedin (top_of_set T) U"
    shows "closedin (top_of_set S) (S \<inter> f -` U)"
using assms continuous_on_closed_gen by blast

lemma continuous_transform_within_openin:
  assumes "continuous (at a within T) f"
    and "openin (top_of_set T) S" "a \<in> S"
    and eq: "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  shows "continuous (at a within T) g"
  using assms by (simp add: Lim_transform_within_openin continuous_within)


subsection\<^marker>\<open>tag important\<close> \<open>The topology generated by some (open) subsets\<close>

text \<open>In the definition below of a generated topology, the \<open>Empty\<close> case is not necessary,
as it follows from \<open>UN\<close> taking for \<open>K\<close> the empty set. However, it is convenient to have,
and is never a problem in proofs, so I prefer to write it down explicitly.

We do not require \<open>UNIV\<close> to be an open set, as this will not be the case in applications. (We are
thinking of a topology on a subset of \<open>UNIV\<close>, the remaining part of \<open>UNIV\<close> being irrelevant.)\<close>

inductive generate_topology_on for S where
  Empty: "generate_topology_on S {}"
| Int: "generate_topology_on S a \<Longrightarrow> generate_topology_on S b \<Longrightarrow> generate_topology_on S (a \<inter> b)"
| UN: "(\<And>k. k \<in> K \<Longrightarrow> generate_topology_on S k) \<Longrightarrow> generate_topology_on S (\<Union>K)"
| Basis: "s \<in> S \<Longrightarrow> generate_topology_on S s"

lemma istopology_generate_topology_on:
  "istopology (generate_topology_on S)"
unfolding istopology_def by (auto intro: generate_topology_on.intros)

text \<open>The basic property of the topology generated by a set \<open>S\<close> is that it is the
smallest topology containing all the elements of \<open>S\<close>:\<close>

lemma generate_topology_on_coarsest:
  assumes T: "istopology T" "\<And>s. s \<in> S \<Longrightarrow> T s"
          and gen: "generate_topology_on S s0"
  shows "T s0"
  using gen 
by (induct rule: generate_topology_on.induct) (use T in \<open>auto simp: istopology_def\<close>)

abbreviation\<^marker>\<open>tag unimportant\<close> topology_generated_by::"('a set set) \<Rightarrow> ('a topology)"
  where "topology_generated_by S \<equiv> topology (generate_topology_on S)"

lemma openin_topology_generated_by_iff:
  "openin (topology_generated_by S) s \<longleftrightarrow> generate_topology_on S s"
  using topology_inverse'[OF istopology_generate_topology_on[of S]] by simp

lemma openin_topology_generated_by:
  "openin (topology_generated_by S) s \<Longrightarrow> generate_topology_on S s"
using openin_topology_generated_by_iff by auto

lemma topology_generated_by_topspace [simp]:
  "topspace (topology_generated_by S) = (\<Union>S)"
proof
  {
    fix s assume "openin (topology_generated_by S) s"
    then have "generate_topology_on S s" by (rule openin_topology_generated_by)
    then have "s \<subseteq> (\<Union>S)" by (induct, auto)
  }
  then show "topspace (topology_generated_by S) \<subseteq> (\<Union>S)"
    unfolding topspace_def by auto
next
  have "generate_topology_on S (\<Union>S)"
    using generate_topology_on.UN[OF generate_topology_on.Basis, of S S] by simp
  then show "(\<Union>S) \<subseteq> topspace (topology_generated_by S)"
    unfolding topspace_def using openin_topology_generated_by_iff by auto
qed

lemma topology_generated_by_Basis:
  "s \<in> S \<Longrightarrow> openin (topology_generated_by S) s"
  by (simp only: openin_topology_generated_by_iff, auto simp: generate_topology_on.Basis)

lemma generate_topology_on_Inter:
  "\<lbrakk>finite \<F>; \<And>K. K \<in> \<F> \<Longrightarrow> generate_topology_on \<S> K; \<F> \<noteq> {}\<rbrakk> \<Longrightarrow> generate_topology_on \<S> (\<Inter>\<F>)"
  by (induction \<F> rule: finite_induct; force intro: generate_topology_on.intros)

subsection\<open>Topology bases and sub-bases\<close>

lemma istopology_base_alt:
   "istopology (arbitrary union_of P) \<longleftrightarrow>
    (\<forall>S T. (arbitrary union_of P) S \<and> (arbitrary union_of P) T
           \<longrightarrow> (arbitrary union_of P) (S \<inter> T))"
  by (simp add: istopology_def) (blast intro: arbitrary_union_of_Union)

lemma istopology_base_eq:
   "istopology (arbitrary union_of P) \<longleftrightarrow>
    (\<forall>S T. P S \<and> P T \<longrightarrow> (arbitrary union_of P) (S \<inter> T))"
  by (simp add: istopology_base_alt arbitrary_union_of_Int_eq)

lemma istopology_base:
   "(\<And>S T. \<lbrakk>P S; P T\<rbrakk> \<Longrightarrow> P(S \<inter> T)) \<Longrightarrow> istopology (arbitrary union_of P)"
  by (simp add: arbitrary_def istopology_base_eq union_of_inc)

lemma openin_topology_base_unique:
   "openin X = arbitrary union_of P \<longleftrightarrow>
        (\<forall>V. P V \<longrightarrow> openin X V) \<and> (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> (\<exists>V. P V \<and> x \<in> V \<and> V \<subseteq> U))"
   (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (auto simp: union_of_def arbitrary_def)
next
  assume R: ?rhs
  then have *: "\<exists>\<U>\<subseteq>Collect P. \<Union>\<U> = S" if "openin X S" for S
    using that by (rule_tac x="{V. P V \<and> V \<subseteq> S}" in exI) fastforce
  from R show ?lhs
    by (fastforce simp add: union_of_def arbitrary_def intro: *)
qed

lemma topology_base_unique:
  assumes "\<And>S. P S \<Longrightarrow> openin X S"
          "\<And>U x. \<lbrakk>openin X U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>B. P B \<and> x \<in> B \<and> B \<subseteq> U"
  shows   "topology (arbitrary union_of P) = X"
proof -
  have "X = topology (openin X)"
    by (simp add: openin_inverse)
  also from assms have "openin X = arbitrary union_of P"
    by (subst openin_topology_base_unique) auto
  finally show ?thesis ..
qed

lemma topology_bases_eq_aux:
   "\<lbrakk>(arbitrary union_of P) S;
     \<And>U x. \<lbrakk>P U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>V. Q V \<and> x \<in> V \<and> V \<subseteq> U\<rbrakk>
        \<Longrightarrow> (arbitrary union_of Q) S"
  by (metis arbitrary_union_of_alt arbitrary_union_of_idempot)

lemma topology_bases_eq:
   "\<lbrakk>\<And>U x. \<lbrakk>P U; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>V. Q V \<and> x \<in> V \<and> V \<subseteq> U;
    \<And>V x. \<lbrakk>Q V; x \<in> V\<rbrakk> \<Longrightarrow> \<exists>U. P U \<and> x \<in> U \<and> U \<subseteq> V\<rbrakk>
        \<Longrightarrow> topology (arbitrary union_of P) =
            topology (arbitrary union_of Q)"
  by (fastforce intro:  arg_cong [where f=topology]  elim: topology_bases_eq_aux)

lemma istopology_subbase:
   "istopology (arbitrary union_of (finite intersection_of P relative_to S))"
  by (simp add: finite_intersection_of_Int istopology_base relative_to_Int)

lemma openin_subbase:
  "openin (topology (arbitrary union_of (finite intersection_of B relative_to U))) S
   \<longleftrightarrow> (arbitrary union_of (finite intersection_of B relative_to U)) S"
  by (simp add: istopology_subbase topology_inverse')

lemma topspace_subbase [simp]:
   "topspace(topology (arbitrary union_of (finite intersection_of B relative_to U))) = U" (is "?lhs = _")
proof
  show "?lhs \<subseteq> U"
    by (metis arbitrary_union_of_relative_to openin_subbase openin_topspace relative_to_imp_subset)
  show "U \<subseteq> ?lhs"
    by (metis arbitrary_union_of_inc finite_intersection_of_empty inf.orderE istopology_subbase 
              openin_subset relative_to_inc subset_UNIV topology_inverse')
qed

lemma minimal_topology_subbase:
  assumes X: "\<And>S. P S \<Longrightarrow> openin X S" and "openin X U"
  and S: "openin(topology(arbitrary union_of (finite intersection_of P relative_to U))) S"
shows "openin X S"
proof -
  have "(arbitrary union_of (finite intersection_of P relative_to U)) S"
    using S openin_subbase by blast
  with X \<open>openin X U\<close> show ?thesis
    by (force simp add: union_of_def intersection_of_def relative_to_def intro: openin_Int_Inter)
qed

lemma istopology_subbase_UNIV:
   "istopology (arbitrary union_of (finite intersection_of P))"
  by (simp add: istopology_base finite_intersection_of_Int)


lemma generate_topology_on_eq:
  "generate_topology_on S = arbitrary union_of finite' intersection_of (\<lambda>x. x \<in> S)" (is "?lhs = ?rhs")
proof (intro ext iffI)
  fix A
  assume "?lhs A"
  then show "?rhs A"
  proof induction
    case (Int a b)
    then show ?case
      by (metis (mono_tags, lifting) istopology_base_alt finite'_intersection_of_Int istopology_base)
  next
    case (UN K)
    then show ?case
      by (simp add: arbitrary_union_of_Union)
  next
    case (Basis s)
    then show ?case
      by (simp add: Sup_upper arbitrary_union_of_inc finite'_intersection_of_inc relative_to_subset)
  qed auto
next
  fix A
  assume "?rhs A"
  then obtain \<U> where \<U>: "\<And>T. T \<in> \<U> \<Longrightarrow> \<exists>\<F>. finite' \<F> \<and> \<F> \<subseteq> S \<and> \<Inter>\<F> = T" and eq: "A = \<Union>\<U>"
    unfolding union_of_def intersection_of_def by auto
  show "?lhs A"
    unfolding eq
  proof (rule generate_topology_on.UN)
    fix T
    assume "T \<in> \<U>"
    with \<U> obtain \<F> where "finite' \<F>" "\<F> \<subseteq> S" "\<Inter>\<F> = T"
      by blast
    have "generate_topology_on S (\<Inter>\<F>)"
    proof (rule generate_topology_on_Inter)
      show "finite \<F>" "\<F> \<noteq> {}"
        by (auto simp: \<open>finite' \<F>\<close>)
      show "\<And>K. K \<in> \<F> \<Longrightarrow> generate_topology_on S K"
        by (metis \<open>\<F> \<subseteq> S\<close> generate_topology_on.simps subset_iff)
    qed
    then show "generate_topology_on S T"
      using \<open>\<Inter>\<F> = T\<close> by blast
  qed
qed

lemma continuous_on_generated_topo_iff:
  "continuous_map T1 (topology_generated_by S) f \<longleftrightarrow>
      ((\<forall>U. U \<in> S \<longrightarrow> openin T1 (f-`U \<inter> topspace(T1))) \<and> (f`(topspace T1) \<subseteq> (\<Union> S)))"
unfolding continuous_map_alt topology_generated_by_topspace
proof (auto simp add: topology_generated_by_Basis)
  assume H: "\<forall>U. U \<in> S \<longrightarrow> openin T1 (f -` U \<inter> topspace T1)"
  fix U assume "openin (topology_generated_by S) U"
  then have "generate_topology_on S U" by (rule openin_topology_generated_by)
  then show "openin T1 (f -` U \<inter> topspace T1)"
  proof (induct)
    fix a b
    assume H: "openin T1 (f -` a \<inter> topspace T1)" "openin T1 (f -` b \<inter> topspace T1)"
    have "f -` (a \<inter> b) \<inter> topspace T1 = (f-`a \<inter> topspace T1) \<inter> (f-`b \<inter> topspace T1)"
      by auto
    then show "openin T1 (f -` (a \<inter> b) \<inter> topspace T1)" using H by auto
  next
    fix K
    assume H: "openin T1 (f -` k \<inter> topspace T1)" if "k\<in> K" for k
    define L where "L = {f -` k \<inter> topspace T1|k. k \<in> K}"
    have *: "openin T1 l" if "l \<in>L" for l using that H unfolding L_def by auto
    have "openin T1 (\<Union>L)" using openin_Union[OF *] by simp
    moreover have "(\<Union>L) = (f -` \<Union>K \<inter> topspace T1)" unfolding L_def by auto
    ultimately show "openin T1 (f -` \<Union>K \<inter> topspace T1)" by simp
  qed (auto simp add: H)
qed

lemma continuous_on_generated_topo:
  assumes "\<And>U. U \<in>S \<Longrightarrow> openin T1 (f-`U \<inter> topspace(T1))"
          "f`(topspace T1) \<subseteq> (\<Union> S)"
  shows "continuous_map T1 (topology_generated_by S) f"
  using assms continuous_on_generated_topo_iff by blast


subsection\<^marker>\<open>tag important\<close> \<open>Pullback topology\<close>

text \<open>Pulling back a topology by map gives again a topology. \<open>subtopology\<close> is
a special case of this notion, pulling back by the identity. We introduce the general notion as
we will need it to define the strong operator topology on the space of continuous linear operators,
by pulling back the product topology on the space of all functions.\<close>

text \<open>\<open>pullback_topology A f T\<close> is the pullback of the topology \<open>T\<close> by the map \<open>f\<close> on
the set \<open>A\<close>.\<close>

definition\<^marker>\<open>tag important\<close> pullback_topology::"('a set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b topology) \<Rightarrow> ('a topology)"
  where "pullback_topology A f T = topology (\<lambda>S. \<exists>U. openin T U \<and> S = f-`U \<inter> A)"

lemma istopology_pullback_topology:
  "istopology (\<lambda>S. \<exists>U. openin T U \<and> S = f-`U \<inter> A)"
  unfolding istopology_def proof (auto)
  fix K assume "\<forall>S\<in>K. \<exists>U. openin T U \<and> S = f -` U \<inter> A"
  then have "\<exists>U. \<forall>S\<in>K. openin T (U S) \<and> S = f-`(U S) \<inter> A"
    by (rule bchoice)
  then obtain U where U: "\<forall>S\<in>K. openin T (U S) \<and> S = f-`(U S) \<inter> A"
    by blast
  define V where "V = (\<Union>S\<in>K. U S)"
  have "openin T V" "\<Union>K = f -` V \<inter> A" unfolding V_def using U by auto
  then show "\<exists>V. openin T V \<and> \<Union>K = f -` V \<inter> A" by auto
qed

lemma openin_pullback_topology:
  "openin (pullback_topology A f T) S \<longleftrightarrow> (\<exists>U. openin T U \<and> S = f-`U \<inter> A)"
unfolding pullback_topology_def topology_inverse'[OF istopology_pullback_topology] by auto

lemma topspace_pullback_topology:
  "topspace (pullback_topology A f T) = f-`(topspace T) \<inter> A"
by (auto simp add: topspace_def openin_pullback_topology)

proposition continuous_map_pullback [intro]:
  assumes "continuous_map T1 T2 g"
  shows "continuous_map (pullback_topology A f T1) T2 (g o f)"
unfolding continuous_map_alt
proof (auto)
  fix U::"'b set" assume "openin T2 U"
  then have "openin T1 (g-`U \<inter> topspace T1)"
    using assms unfolding continuous_map_alt by auto
  have "(g o f)-`U \<inter> topspace (pullback_topology A f T1) = (g o f)-`U \<inter> A \<inter> f-`(topspace T1)"
    unfolding topspace_pullback_topology by auto
  also have "... = f-`(g-`U \<inter> topspace T1) \<inter> A "
    by auto
  also have "openin (pullback_topology A f T1) (...)"
    unfolding openin_pullback_topology using \<open>openin T1 (g-`U \<inter> topspace T1)\<close> by auto
  finally show "openin (pullback_topology A f T1) ((g \<circ> f) -` U \<inter> topspace (pullback_topology A f T1))"
    by auto
next
  fix x assume "x \<in> topspace (pullback_topology A f T1)"
  then have "f x \<in> topspace T1"
    unfolding topspace_pullback_topology by auto
  then show "g (f x) \<in> topspace T2"
    using assms unfolding continuous_map_def by auto
qed

proposition continuous_map_pullback' [intro]:
  assumes "continuous_map T1 T2 (f o g)" "topspace T1 \<subseteq> g-`A"
  shows "continuous_map T1 (pullback_topology A f T2) g"
unfolding continuous_map_alt
proof (auto)
  fix U assume "openin (pullback_topology A f T2) U"
  then have "\<exists>V. openin T2 V \<and> U = f-`V \<inter> A"
    unfolding openin_pullback_topology by auto
  then obtain V where "openin T2 V" "U = f-`V \<inter> A"
    by blast
  then have "g -` U \<inter> topspace T1 = g-`(f-`V \<inter> A) \<inter> topspace T1"
    by blast
  also have "... = (f o g)-`V \<inter> (g-`A \<inter> topspace T1)"
    by auto
  also have "... = (f o g)-`V \<inter> topspace T1"
    using assms(2) by auto
  also have "openin T1 (...)"
    using assms(1) \<open>openin T2 V\<close> by auto
  finally show "openin T1 (g -` U \<inter> topspace T1)" by simp
next
  fix x assume "x \<in> topspace T1"
  have "(f o g) x \<in> topspace T2"
    using assms(1) \<open>x \<in> topspace T1\<close> unfolding continuous_map_def by auto
  then have "g x \<in> f-`(topspace T2)"
    unfolding comp_def by blast
  moreover have "g x \<in> A" using assms(2) \<open>x \<in> topspace T1\<close> by blast
  ultimately show "g x \<in> topspace (pullback_topology A f T2)"
    unfolding topspace_pullback_topology by blast
qed
subsection\<open>Proper maps (not a priori assumed continuous) \<close>

definition proper_map
  where
 "proper_map X Y f \<equiv>
        closed_map X Y f \<and> (\<forall>y \<in> topspace Y. compactin X {x \<in> topspace X. f x = y})"

lemma proper_imp_closed_map:
   "proper_map X Y f \<Longrightarrow> closed_map X Y f"
  by (simp add: proper_map_def)

lemma proper_map_imp_subset_topspace:
   "proper_map X Y f \<Longrightarrow> f ` (topspace X) \<subseteq> topspace Y"
  by (simp add: closed_map_imp_subset_topspace proper_map_def)

lemma closed_injective_imp_proper_map:
  assumes f: "closed_map X Y f" and inj: "inj_on f (topspace X)"
  shows "proper_map X Y f"
  unfolding proper_map_def
proof (clarsimp simp: f)
  show "compactin X {x \<in> topspace X. f x = y}"
    if "y \<in> topspace Y" for y
  proof -
    have "{x \<in> topspace X. f x = y} = {} \<or> (\<exists>a \<in> topspace X. {x \<in> topspace X. f x = y} = {a})"
      using inj_on_eq_iff [OF inj] by auto
    then show ?thesis
      using that by (metis (no_types, lifting) compactin_empty compactin_sing)
  qed
qed

lemma injective_imp_proper_eq_closed_map:
   "inj_on f (topspace X) \<Longrightarrow> (proper_map X Y f \<longleftrightarrow> closed_map X Y f)"
  using closed_injective_imp_proper_map proper_imp_closed_map by blast

lemma homeomorphic_imp_proper_map:
   "homeomorphic_map X Y f \<Longrightarrow> proper_map X Y f"
  by (simp add: closed_injective_imp_proper_map homeomorphic_eq_everything_map)

lemma compactin_proper_map_preimage:
  assumes f: "proper_map X Y f" and "compactin Y K"
  shows "compactin X {x. x \<in> topspace X \<and> f x \<in> K}"
proof -
  have "f ` (topspace X) \<subseteq> topspace Y"
    by (simp add: f proper_map_imp_subset_topspace)
  have *: "\<And>y. y \<in> topspace Y \<Longrightarrow> compactin X {x \<in> topspace X. f x = y}"
    using f by (auto simp: proper_map_def)
  show ?thesis
    unfolding compactin_def
  proof clarsimp
    show "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> \<U> \<and> {x \<in> topspace X. f x \<in> K} \<subseteq> \<Union>\<F>"
      if \<U>: "\<forall>U\<in>\<U>. openin X U" and sub: "{x \<in> topspace X. f x \<in> K} \<subseteq> \<Union>\<U>"
      for \<U>
    proof -
      have "\<forall>y \<in> K. \<exists>\<V>. finite \<V> \<and> \<V> \<subseteq> \<U>  \<and> {x \<in> topspace X. f x = y} \<subseteq> \<Union>\<V>"
      proof
        fix y
        assume "y \<in> K"
        then have "compactin X {x \<in> topspace X. f x = y}"
          by (metis "*" \<open>compactin Y K\<close> compactin_subspace subsetD)
        with \<open>y \<in> K\<close> show "\<exists>\<V>. finite \<V> \<and> \<V> \<subseteq> \<U>  \<and> {x \<in> topspace X. f x = y} \<subseteq> \<Union>\<V>"
          unfolding compactin_def using \<U> sub by fastforce
      qed
      then obtain \<V> where \<V>: "\<And>y. y \<in> K \<Longrightarrow> finite (\<V> y) \<and> \<V> y \<subseteq> \<U>  \<and> {x \<in> topspace X. f x = y} \<subseteq> \<Union>(\<V> y)"
        by (metis (full_types))
      define F where "F \<equiv> \<lambda>y. topspace Y - f ` (topspace X - \<Union>(\<V> y))"
      have "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> F ` K \<and> K \<subseteq> \<Union>\<F>"
      proof (rule compactinD [OF \<open>compactin Y K\<close>])
        have "\<And>x. x \<in> K \<Longrightarrow> closedin Y (f ` (topspace X - \<Union>(\<V> x)))"
          using f unfolding proper_map_def closed_map_def
          by (meson \<U> \<V> openin_Union openin_closedin_eq subsetD)
        then show "openin Y U" if "U \<in> F ` K" for U
          using that by (auto simp: F_def)
        show "K \<subseteq> \<Union>(F ` K)"
          using \<V> \<open>compactin Y K\<close> unfolding F_def compactin_def by fastforce
      qed
      then obtain J where "finite J" "J \<subseteq> K" and J: "K \<subseteq> \<Union>(F ` J)"
        by (auto simp: ex_finite_subset_image)
      show ?thesis
        unfolding F_def
      proof (intro exI conjI)
        show "finite (\<Union>(\<V> ` J))"
          using \<V> \<open>J \<subseteq> K\<close> \<open>finite J\<close> by blast
        show "\<Union>(\<V> ` J) \<subseteq> \<U>"
          using \<V> \<open>J \<subseteq> K\<close> by blast
        show "{x \<in> topspace X. f x \<in> K} \<subseteq> \<Union>(\<Union>(\<V> ` J))"
          using J \<open>J \<subseteq> K\<close> unfolding F_def by auto
      qed
    qed
  qed
qed


lemma compact_space_proper_map_preimage:
  assumes f: "proper_map X Y f" and fim: "f ` (topspace X) = topspace Y" and "compact_space Y"
  shows "compact_space X"
proof -
  have eq: "topspace X = {x \<in> topspace X. f x \<in> topspace Y}"
    using fim by blast
  moreover have "compactin Y (topspace Y)"
    using \<open>compact_space Y\<close> compact_space_def by auto
  ultimately show ?thesis
    unfolding compact_space_def
    using eq f compactin_proper_map_preimage by fastforce
qed

lemma proper_map_alt:
   "proper_map X Y f \<longleftrightarrow>
    closed_map X Y f \<and> (\<forall>K. compactin Y K \<longrightarrow> compactin X {x. x \<in> topspace X \<and> f x \<in> K})"
  proof (intro iffI conjI allI impI)
  show "compactin X {x \<in> topspace X. f x \<in> K}"
    if "proper_map X Y f" and "compactin Y K" for K
    using that by (simp add: compactin_proper_map_preimage)
  show "proper_map X Y f"
    if f: "closed_map X Y f \<and> (\<forall>K. compactin Y K \<longrightarrow> compactin X {x \<in> topspace X. f x \<in> K})"
  proof -
    have "compactin X {x \<in> topspace X. f x = y}" if "y \<in> topspace Y" for y
    proof -
      have "compactin X {x \<in> topspace X. f x \<in> {y}}"
        using f compactin_sing that by fastforce
      then show ?thesis
        by auto
    qed
    with f show ?thesis
      by (auto simp: proper_map_def)
  qed
qed (simp add: proper_imp_closed_map)

lemma proper_map_on_empty:
   "topspace X = {} \<Longrightarrow> proper_map X Y f"
  by (auto simp: proper_map_def closed_map_on_empty)

lemma proper_map_id [simp]:
   "proper_map X X id"
proof (clarsimp simp: proper_map_alt closed_map_id)
  fix K
  assume K: "compactin X K"
  then have "{a \<in> topspace X. a \<in> K} = K"
    by (simp add: compactin_subspace subset_antisym subset_iff)
  then show "compactin X {a \<in> topspace X. a \<in> K}"
    using K by auto
qed

lemma proper_map_compose:
  assumes "proper_map X Y f" "proper_map Y Z g"
  shows "proper_map X Z (g \<circ> f)"
proof -
  have "closed_map X Y f" and f: "\<And>K. compactin Y K \<Longrightarrow> compactin X {x \<in> topspace X. f x \<in> K}"
    and "closed_map Y Z g" and g: "\<And>K. compactin Z K \<Longrightarrow> compactin Y {x \<in> topspace Y. g x \<in> K}"
    using assms by (auto simp: proper_map_alt)
  show ?thesis
    unfolding proper_map_alt
  proof (intro conjI allI impI)
    show "closed_map X Z (g \<circ> f)"
      using \<open>closed_map X Y f\<close> \<open>closed_map Y Z g\<close> closed_map_compose by blast
    have "{x \<in> topspace X. g (f x) \<in> K} = {x \<in> topspace X. f x \<in> {b \<in> topspace Y. g b \<in> K}}" for K
      using \<open>closed_map X Y f\<close> closed_map_imp_subset_topspace by blast
    then show "compactin X {x \<in> topspace X. (g \<circ> f) x \<in> K}"
      if "compactin Z K" for K
      using f [OF g [OF that]] by auto
  qed
qed

lemma proper_map_const:
   "proper_map X Y (\<lambda>x. c) \<longleftrightarrow> compact_space X \<and> (topspace X = {} \<or> closedin Y {c})"
proof (cases "topspace X = {}")
  case True
  then show ?thesis
    by (simp add: compact_space_topspace_empty proper_map_on_empty)
next
  case False
  have *: "compactin X {x \<in> topspace X. c = y}" if "compact_space X" for y
  proof (cases "c = y")
    case True
    then show ?thesis
      using compact_space_def \<open>compact_space X\<close> by auto
  qed auto
  then show ?thesis
    using closed_compactin closedin_subset
    by (force simp: False proper_map_def closed_map_const compact_space_def)
qed

lemma proper_map_inclusion:
   "s \<subseteq> topspace X
        \<Longrightarrow> proper_map (subtopology X s) X id \<longleftrightarrow> closedin X s \<and> (\<forall>k. compactin X k \<longrightarrow> compactin X (s \<inter> k))"
  by (auto simp: proper_map_alt closed_map_inclusion_eq inf.absorb_iff2 Collect_conj_eq compactin_subtopology intro: closed_Int_compactin)


subsection\<open>Perfect maps (proper, continuous and surjective)\<close>

definition perfect_map 
  where "perfect_map X Y f \<equiv> continuous_map X Y f \<and> proper_map X Y f \<and> f ` (topspace X) = topspace Y"

lemma homeomorphic_imp_perfect_map:
   "homeomorphic_map X Y f \<Longrightarrow> perfect_map X Y f"
  by (simp add: homeomorphic_eq_everything_map homeomorphic_imp_proper_map perfect_map_def)

lemma perfect_imp_quotient_map:
   "perfect_map X Y f \<Longrightarrow> quotient_map X Y f"
  by (simp add: continuous_closed_imp_quotient_map perfect_map_def proper_map_def)

lemma homeomorphic_eq_injective_perfect_map:
   "homeomorphic_map X Y f \<longleftrightarrow> perfect_map X Y f \<and> inj_on f (topspace X)"
  using homeomorphic_imp_perfect_map homeomorphic_map_def perfect_imp_quotient_map by blast

lemma perfect_injective_eq_homeomorphic_map:
   "perfect_map X Y f \<and> inj_on f (topspace X) \<longleftrightarrow> homeomorphic_map X Y f"
  by (simp add: homeomorphic_eq_injective_perfect_map)

lemma perfect_map_id [simp]: "perfect_map X X id"
  by (simp add: homeomorphic_imp_perfect_map)

lemma perfect_map_compose:
   "\<lbrakk>perfect_map X Y f; perfect_map Y Z g\<rbrakk> \<Longrightarrow> perfect_map X Z (g \<circ> f)"
  by (meson continuous_map_compose perfect_imp_quotient_map perfect_map_def proper_map_compose quotient_map_compose_eq quotient_map_def)

lemma perfect_imp_continuous_map:
   "perfect_map X Y f \<Longrightarrow> continuous_map X Y f"
  using perfect_map_def by blast

lemma perfect_imp_closed_map:
   "perfect_map X Y f \<Longrightarrow> closed_map X Y f"
  by (simp add: perfect_map_def proper_map_def)

lemma perfect_imp_proper_map:
   "perfect_map X Y f \<Longrightarrow> proper_map X Y f"
  by (simp add: perfect_map_def)

lemma perfect_imp_surjective_map:
   "perfect_map X Y f \<Longrightarrow> f ` (topspace X) = topspace Y"
  by (simp add: perfect_map_def)

end

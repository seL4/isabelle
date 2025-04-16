section\<open>Disjoint sum of arbitarily many spaces\<close>

theory Sum_Topology
  imports Abstract_Topology
begin


definition sum_topology :: "('a \<Rightarrow> 'b topology) \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) topology" where
  "sum_topology X I \<equiv>
    topology (\<lambda>U. U \<subseteq> Sigma I (topspace \<circ> X) \<and> (\<forall>i \<in> I. openin (X i) {x. (i,x) \<in> U}))"

lemma is_sum_topology: "istopology (\<lambda>U. U \<subseteq> Sigma I (topspace \<circ> X) \<and> (\<forall>i\<in>I. openin (X i) {x. (i, x) \<in> U}))"
proof -
  have 1: "{x. (i, x) \<in> S \<inter> T} = {x. (i, x) \<in> S} \<inter> {x::'b. (i, x) \<in> T}" for S T and i::'a
    by auto
  have 2: "{x. (i, x) \<in> \<Union> \<K>} = (\<Union>K\<in>\<K>. {x::'b. (i, x) \<in> K})" for \<K> and i::'a
    by auto
  show ?thesis
    unfolding istopology_def 1 2 by blast
qed

lemma openin_sum_topology:
   "openin (sum_topology X I) U \<longleftrightarrow>
        U \<subseteq> Sigma I (topspace \<circ> X) \<and> (\<forall>i \<in> I. openin (X i) {x. (i,x) \<in> U})"
  by (auto simp: sum_topology_def is_sum_topology)

lemma openin_disjoint_union:
   "openin (sum_topology X I) (Sigma I U) \<longleftrightarrow> (\<forall>i \<in> I. openin (X i) (U i))"
  using openin_subset by (force simp: openin_sum_topology)

lemma topspace_sum_topology [simp]:
   "topspace(sum_topology X I) = Sigma I (topspace \<circ> X)"
  by (metis comp_apply openin_disjoint_union openin_subset openin_sum_topology openin_topspace subset_antisym)

lemma openin_sum_topology_alt:
   "openin (sum_topology X I) U \<longleftrightarrow> (\<exists>T. U = Sigma I T \<and> (\<forall>i \<in> I. openin (X i) (T i)))"
  by (bestsimp simp: openin_sum_topology dest: openin_subset)

lemma forall_openin_sum_topology:
   "(\<forall>U. openin (sum_topology X I) U \<longrightarrow> P U) \<longleftrightarrow> (\<forall>T. (\<forall>i \<in> I. openin (X i) (T i)) \<longrightarrow> P(Sigma I T))"
  by (auto simp: openin_sum_topology_alt)

lemma exists_openin_sum_topology:
   "(\<exists>U. openin (sum_topology X I) U \<and> P U) \<longleftrightarrow>
    (\<exists>T. (\<forall>i \<in> I. openin (X i) (T i)) \<and> P(Sigma I T))"
  by (auto simp: openin_sum_topology_alt)

lemma closedin_sum_topology:
   "closedin (sum_topology X I) U \<longleftrightarrow> U \<subseteq> Sigma I (topspace \<circ> X) \<and> (\<forall>i \<in> I. closedin (X i) {x. (i,x) \<in> U})"
     (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have U: "U \<subseteq> Sigma I (topspace \<circ> X)"
    using closedin_subset by fastforce
  then have "\<forall>i\<in>I. {x. (i, x) \<in> U} \<subseteq> topspace (X i)"
    by fastforce
  moreover have "openin (X i) (topspace (X i) - {x. (i, x) \<in> U})" if "i\<in>I" for i
    apply (subst openin_subopen)
    using L that unfolding closedin_def openin_sum_topology
    by (bestsimp simp: o_def subset_iff)
  ultimately show ?rhs
    by (simp add: U closedin_def)
next
  assume R: ?rhs
  then have "openin (X i) {x. (i, x) \<in> topspace (sum_topology X I) - U}" if "i\<in>I" for i
    apply (subst openin_subopen)
    using that unfolding closedin_def openin_sum_topology
    by (bestsimp simp: o_def subset_iff)
  then show ?lhs
    by (simp add: R closedin_def openin_sum_topology)
qed

lemma closedin_disjoint_union:
   "closedin (sum_topology X I) (Sigma I U) \<longleftrightarrow> (\<forall>i \<in> I. closedin (X i) (U i))"
  using closedin_subset by (force simp: closedin_sum_topology)

lemma closedin_sum_topology_alt:
   "closedin (sum_topology X I) U \<longleftrightarrow> (\<exists>T. U = Sigma I T \<and> (\<forall>i \<in> I. closedin (X i) (T i)))"
  using closedin_subset unfolding closedin_sum_topology by auto blast

lemma forall_closedin_sum_topology:
   "(\<forall>U. closedin (sum_topology X I) U \<longrightarrow> P U) \<longleftrightarrow>
        (\<forall>t. (\<forall>i \<in> I. closedin (X i) (t i)) \<longrightarrow> P(Sigma I t))"
  by (metis closedin_sum_topology_alt)

lemma exists_closedin_sum_topology:
   "(\<exists>U. closedin (sum_topology X I) U \<and> P U) \<longleftrightarrow>
    (\<exists>T. (\<forall>i \<in> I. closedin (X i) (T i)) \<and> P(Sigma I T))"
  by (simp add: closedin_sum_topology_alt) blast

lemma open_map_component_injection:
   "i \<in> I \<Longrightarrow> open_map (X i) (sum_topology X I) (\<lambda>x. (i,x))"
  unfolding open_map_def openin_sum_topology
  using openin_subset openin_subopen by (force simp: image_iff)

lemma closed_map_component_injection:
  assumes "i \<in> I"
  shows "closed_map(X i) (sum_topology X I) (\<lambda>x. (i,x))"
proof -
  have "closedin (X j) {x. j = i \<and> x \<in> U}"
    if "\<And>U S. closedin U S \<Longrightarrow> S \<subseteq> topspace U" and "closedin (X i) U" and "j \<in> I" for U j
    using that by (cases "j=i") auto
  then show ?thesis
    using closedin_subset assms by (force simp: closed_map_def closedin_sum_topology image_iff)
qed

lemma continuous_map_component_injection:
   "i \<in> I \<Longrightarrow> continuous_map(X i) (sum_topology X I) (\<lambda>x. (i,x))"
  by (auto simp: continuous_map_def openin_sum_topology Collect_conj_eq openin_Int)

lemma subtopology_sum_topology:
  "subtopology (sum_topology X I) (Sigma I S) =
        sum_topology (\<lambda>i. subtopology (X i) (S i)) I"
  unfolding topology_eq
proof (intro strip iffI)
  fix T
  assume *: "openin (subtopology (sum_topology X I) (Sigma I S)) T"
  then obtain U where U: "\<forall>i\<in>I. openin (X i) (U i) \<and> T = Sigma I U \<inter> Sigma I S" 
    by (auto simp: openin_subtopology openin_sum_topology_alt)
  have "T = (SIGMA i:I. U i \<inter> S i)"
  proof
    show "T \<subseteq> (SIGMA i:I. U i \<inter> S i)"
      by (metis "*" SigmaE Sigma_Int_distrib2 U openin_imp_subset subset_iff)
    show "(SIGMA i:I. U i \<inter> S i) \<subseteq> T"
      using U by fastforce
  qed
  then show "openin (sum_topology (\<lambda>i. subtopology (X i) (S i)) I) T"
    by (simp add: U openin_disjoint_union openin_subtopology_Int)
next
  fix T
  assume *: "openin (sum_topology (\<lambda>i. subtopology (X i) (S i)) I) T"
  then obtain U where "\<forall>i\<in>I. \<exists>T. openin (X i) T \<and> U i = T \<inter> S i" and Teq: "T = Sigma I U"
    by (auto simp: openin_subtopology openin_sum_topology_alt)
  then obtain B where "\<And>i. i\<in>I \<Longrightarrow> openin (X i) (B i) \<and> U i = B i \<inter> S i"
    by metis
  then show "openin (subtopology (sum_topology X I) (Sigma I S)) T"
    by (auto simp: openin_subtopology openin_sum_topology_alt Teq)
qed

lemma embedding_map_component_injection:
   "i \<in> I \<Longrightarrow> embedding_map (X i) (sum_topology X I) (\<lambda>x. (i,x))"
  by (metis injective_open_imp_embedding_map continuous_map_component_injection
            open_map_component_injection inj_onI prod.inject)

lemma topological_property_of_sum_component:
  assumes major: "P (sum_topology X I)"
    and minor: "\<And>X S. \<lbrakk>P X; closedin X S; openin X S\<rbrakk> \<Longrightarrow> P(subtopology X S)"
    and PQ:  "\<And>X Y. X homeomorphic_space Y \<Longrightarrow> (P X \<longleftrightarrow> Q Y)"
  shows "(\<forall>i \<in> I. Q(X i))"
proof -
  have "Q(X i)" if "i \<in> I" for i
  proof -
    have "closed_map (X i) (sum_topology X I) (Pair i)"
      by (simp add: closed_map_component_injection that)
    moreover have "open_map (X i) (sum_topology X I) (Pair i)"
      by (simp add: open_map_component_injection that)
    ultimately have "P(subtopology (sum_topology X I) (Pair i ` topspace (X i)))"
      by (simp add: closed_map_def major minor open_map_def)
    then show ?thesis
      by (metis PQ embedding_map_component_injection embedding_map_imp_homeomorphic_space homeomorphic_space_sym that)
  qed
  then show ?thesis by metis
qed

end

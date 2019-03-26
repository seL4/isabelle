section\<open>T1 spaces with equivalences to many naturally "nice" properties. \<close>

theory T1_Spaces
imports Product_Topology 
begin

definition t1_space where
 "t1_space X \<equiv> \<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x\<noteq>y \<longrightarrow> (\<exists>U. openin X U \<and> x \<in> U \<and> y \<notin> U)"

lemma t1_space_expansive:
   "\<lbrakk>topspace Y = topspace X; \<And>U. openin X U \<Longrightarrow> openin Y U\<rbrakk> \<Longrightarrow> t1_space X \<Longrightarrow> t1_space Y"
  by (metis t1_space_def)

lemma t1_space_alt:
   "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<forall>y \<in> topspace X. x\<noteq>y \<longrightarrow> (\<exists>U. closedin X U \<and> x \<in> U \<and> y \<notin> U))"
 by (metis DiffE DiffI closedin_def openin_closedin_eq t1_space_def)

lemma t1_space_empty: "topspace X = {} \<Longrightarrow> t1_space X"
  by (simp add: t1_space_def)

lemma t1_space_derived_set_of_singleton:
  "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. X derived_set_of {x} = {})"
  apply (simp add: t1_space_def derived_set_of_def, safe)
   apply (metis openin_topspace)
  by force

lemma t1_space_derived_set_of_finite:
   "t1_space X \<longleftrightarrow> (\<forall>S. finite S \<longrightarrow> X derived_set_of S = {})"
proof (intro iffI allI impI)
  fix S :: "'a set"
  assume "finite S"
  then have fin: "finite ((\<lambda>x. {x}) ` (topspace X \<inter> S))"
    by blast
  assume "t1_space X"
  then have "X derived_set_of (\<Union>x \<in> topspace X \<inter> S. {x}) = {}"
    unfolding derived_set_of_Union [OF fin]
    by (auto simp: t1_space_derived_set_of_singleton)
  then have "X derived_set_of (topspace X \<inter> S) = {}"
    by simp
  then show "X derived_set_of S = {}"
    by simp
qed (auto simp: t1_space_derived_set_of_singleton)

lemma t1_space_closedin_singleton:
   "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. closedin X {x})"
  apply (rule iffI)
  apply (simp add: closedin_contains_derived_set t1_space_derived_set_of_singleton)
  using t1_space_alt by auto

lemma closedin_t1_singleton:
   "\<lbrakk>t1_space X; a \<in> topspace X\<rbrakk> \<Longrightarrow> closedin X {a}"
  by (simp add: t1_space_closedin_singleton)

lemma t1_space_closedin_finite:
   "t1_space X \<longleftrightarrow> (\<forall>S. finite S \<and> S \<subseteq> topspace X \<longrightarrow> closedin X S)"
  apply (rule iffI)
  apply (simp add: closedin_contains_derived_set t1_space_derived_set_of_finite)
  by (simp add: t1_space_closedin_singleton)

lemma closure_of_singleton:
   "t1_space X \<Longrightarrow> X closure_of {a} = (if a \<in> topspace X then {a} else {})"
  by (simp add: closure_of_eq t1_space_closedin_singleton closure_of_eq_empty_gen)

lemma separated_in_singleton:
  assumes "t1_space X"
  shows "separatedin X {a} S \<longleftrightarrow> a \<in> topspace X \<and> S \<subseteq> topspace X \<and> (a \<notin> X closure_of S)"
        "separatedin X S {a} \<longleftrightarrow> a \<in> topspace X \<and> S \<subseteq> topspace X \<and> (a \<notin> X closure_of S)"
  unfolding separatedin_def
  using assms closure_of closure_of_singleton by fastforce+

lemma t1_space_openin_delete:
   "t1_space X \<longleftrightarrow> (\<forall>U x. openin X U \<and> x \<in> U \<longrightarrow> openin X (U - {x}))"
  apply (rule iffI)
  apply (meson closedin_t1_singleton in_mono openin_diff openin_subset)
  by (simp add: closedin_def t1_space_closedin_singleton)

lemma t1_space_openin_delete_alt:
   "t1_space X \<longleftrightarrow> (\<forall>U x. openin X U \<longrightarrow> openin X (U - {x}))"
  by (metis Diff_empty Diff_insert0 t1_space_openin_delete)


lemma t1_space_singleton_Inter_open:
      "t1_space X \<longleftrightarrow> (\<forall>x \<in> topspace X. \<Inter>{U. openin X U \<and> x \<in> U} = {x})"  (is "?P=?Q")
  and t1_space_Inter_open_supersets:
     "t1_space X \<longleftrightarrow> (\<forall>S. S \<subseteq> topspace X \<longrightarrow> \<Inter>{U. openin X U \<and> S \<subseteq> U} = S)" (is "?P=?R")
proof -
  have "?R \<Longrightarrow> ?Q"
    apply clarify
    apply (drule_tac x="{x}" in spec, simp)
    done
  moreover have "?Q \<Longrightarrow> ?P"
    apply (clarsimp simp add: t1_space_def)
    apply (drule_tac x=x in bspec)
     apply (simp_all add: set_eq_iff)
    by (metis (no_types, lifting))
  moreover have "?P \<Longrightarrow> ?R"
  proof (clarsimp simp add: t1_space_closedin_singleton, rule subset_antisym)
    fix S
    assume S: "\<forall>x\<in>topspace X. closedin X {x}" "S \<subseteq> topspace X"
    then show "\<Inter> {U. openin X U \<and> S \<subseteq> U} \<subseteq> S"
      apply clarsimp
      by (metis Diff_insert_absorb Set.set_insert closedin_def openin_topspace subset_insert)
  qed force
  ultimately show "?P=?Q" "?P=?R"
    by auto
qed

lemma t1_space_derived_set_of_infinite_openin:
   "t1_space X \<longleftrightarrow>
        (\<forall>S. X derived_set_of S =
             {x \<in> topspace X. \<forall>U. x \<in> U \<and> openin X U \<longrightarrow> infinite(S \<inter> U)})"
         (is "_ = ?rhs")
proof
  assume "t1_space X"
  show ?rhs
  proof safe
    fix S x U
    assume "x \<in> X derived_set_of S" "x \<in> U" "openin X U" "finite (S \<inter> U)"
    with \<open>t1_space X\<close> show "False"
      apply (simp add: t1_space_derived_set_of_finite)
      by (metis IntI empty_iff empty_subsetI inf_commute openin_Int_derived_set_of_subset subset_antisym)
  next
    fix S x
    have eq: "(\<exists>y. (y \<noteq> x) \<and> y \<in> S \<and> y \<in> T) \<longleftrightarrow> ~((S \<inter> T) \<subseteq> {x})" for x S T
      by blast
    assume "x \<in> topspace X" "\<forall>U. x \<in> U \<and> openin X U \<longrightarrow> infinite (S \<inter> U)"
    then show "x \<in> X derived_set_of S"
      apply (clarsimp simp add: derived_set_of_def eq)
      by (meson finite.emptyI finite.insertI finite_subset)
  qed (auto simp: in_derived_set_of)
qed (auto simp: t1_space_derived_set_of_singleton)

lemma finite_t1_space_imp_discrete_topology:
   "\<lbrakk>topspace X = U; finite U; t1_space X\<rbrakk> \<Longrightarrow> X = discrete_topology U"
  by (metis discrete_topology_unique_derived_set t1_space_derived_set_of_finite)

lemma t1_space_subtopology: "t1_space X \<Longrightarrow> t1_space(subtopology X U)"
  by (simp add: derived_set_of_subtopology t1_space_derived_set_of_finite)

lemma closedin_derived_set_of_gen:
   "t1_space X \<Longrightarrow> closedin X (X derived_set_of S)"
  apply (clarsimp simp add: in_derived_set_of closedin_contains_derived_set derived_set_of_subset_topspace)
  by (metis DiffD2 insert_Diff insert_iff t1_space_openin_delete)

lemma derived_set_of_derived_set_subset_gen:
   "t1_space X \<Longrightarrow> X derived_set_of (X derived_set_of S) \<subseteq> X derived_set_of S"
  by (meson closedin_contains_derived_set closedin_derived_set_of_gen)

lemma subtopology_eq_discrete_topology_gen_finite:
   "\<lbrakk>t1_space X; finite S\<rbrakk> \<Longrightarrow> subtopology X S = discrete_topology(topspace X \<inter> S)"
  by (simp add: subtopology_eq_discrete_topology_gen t1_space_derived_set_of_finite)

lemma subtopology_eq_discrete_topology_finite:
   "\<lbrakk>t1_space X; S \<subseteq> topspace X; finite S\<rbrakk>
        \<Longrightarrow> subtopology X S = discrete_topology S"
  by (simp add: subtopology_eq_discrete_topology_eq t1_space_derived_set_of_finite)

lemma t1_space_closed_map_image:
   "\<lbrakk>closed_map X Y f; f ` (topspace X) = topspace Y; t1_space X\<rbrakk> \<Longrightarrow> t1_space Y"
  by (metis closed_map_def finite_subset_image t1_space_closedin_finite)

lemma homeomorphic_t1_space: "X homeomorphic_space Y \<Longrightarrow> (t1_space X \<longleftrightarrow> t1_space Y)"
  apply (clarsimp simp add: homeomorphic_space_def)
  by (meson homeomorphic_eq_everything_map homeomorphic_maps_map t1_space_closed_map_image)

proposition t1_space_product_topology:
   "t1_space (product_topology X I)
\<longleftrightarrow> topspace(product_topology X I) = {} \<or> (\<forall>i \<in> I. t1_space (X i))"
proof (cases "topspace(product_topology X I) = {}")
  case True
  then show ?thesis
    using True t1_space_empty by blast
next
  case False
  then obtain f where f: "f \<in> (\<Pi>\<^sub>E i\<in>I. topspace(X i))"
    by fastforce
  have "t1_space (product_topology X I) \<longleftrightarrow> (\<forall>i\<in>I. t1_space (X i))"
  proof (intro iffI ballI)
    show "t1_space (X i)" if "t1_space (product_topology X I)" and "i \<in> I" for i
    proof -
      have clo: "\<And>h. h \<in> (\<Pi>\<^sub>E i\<in>I. topspace (X i)) \<Longrightarrow> closedin (product_topology X I) {h}"
        using that by (simp add: t1_space_closedin_singleton)
      show ?thesis
        unfolding t1_space_closedin_singleton
      proof clarify
        show "closedin (X i) {xi}" if "xi \<in> topspace (X i)" for xi
          using clo [of "\<lambda>j \<in> I. if i=j then xi else f j"] f that \<open>i \<in> I\<close>
          by (fastforce simp add: closedin_product_topology_singleton)
      qed
    qed
  next
  next
    show "t1_space (product_topology X I)" if "\<forall>i\<in>I. t1_space (X i)"
      using that
      by (simp add: t1_space_closedin_singleton Ball_def PiE_iff closedin_product_topology_singleton)
  qed
  then show ?thesis
    using False by blast
qed

lemma t1_space_prod_topology:
   "t1_space(prod_topology X Y) \<longleftrightarrow> topspace(prod_topology X Y) = {} \<or> t1_space X \<and> t1_space Y"
proof (cases "topspace (prod_topology X Y) = {}")
  case True then show ?thesis
  by (auto simp: t1_space_empty)
next
  case False
  have eq: "{(x,y)} = {x} \<times> {y}" for x y
    by simp
  have "t1_space (prod_topology X Y) \<longleftrightarrow> (t1_space X \<and> t1_space Y)"
    using False
    by (force simp: t1_space_closedin_singleton closedin_prod_Times_iff eq simp del: insert_Times_insert)
  with False show ?thesis
    by simp
qed

end

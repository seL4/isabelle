section\<open>Lindel\"of spaces\<close>

theory Lindelof_Spaces
imports T1_Spaces
begin

definition Lindelof_space where
  "Lindelof_space X \<equiv>
        \<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> \<Union>\<U> = topspace X
            \<longrightarrow> (\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> \<Union>\<V> = topspace X)"

lemma Lindelof_spaceD:
  "\<lbrakk>Lindelof_space X; \<And>U. U \<in> \<U> \<Longrightarrow> openin X U; \<Union>\<U> = topspace X\<rbrakk>
  \<Longrightarrow> \<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> \<Union>\<V> = topspace X"
  by (auto simp: Lindelof_space_def)

lemma Lindelof_space_alt:
   "Lindelof_space X \<longleftrightarrow>
        (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> topspace X \<subseteq> \<Union>\<U>
             \<longrightarrow> (\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> topspace X \<subseteq> \<Union>\<V>))"
  unfolding Lindelof_space_def
  using openin_subset by fastforce

lemma compact_imp_Lindelof_space:
   "compact_space X \<Longrightarrow> Lindelof_space X"
  unfolding Lindelof_space_def compact_space
  by (meson uncountable_infinite)

lemma Lindelof_space_topspace_empty:
   "topspace X = {} \<Longrightarrow> Lindelof_space X"
  using compact_imp_Lindelof_space compact_space_topspace_empty by blast

lemma Lindelof_space_Union:
  assumes \<U>: "countable \<U>" and lin: "\<And>U. U \<in> \<U> \<Longrightarrow> Lindelof_space (subtopology X U)"
  shows "Lindelof_space (subtopology X (\<Union>\<U>))"
proof -
  have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> \<Union>\<U> \<inter> \<Union>\<V> = topspace X \<inter> \<Union>\<U>"
    if \<F>: "\<F> \<subseteq> Collect (openin X)" and UF: "\<Union>\<U> \<inter> \<Union>\<F> = topspace X \<inter> \<Union>\<U>"
    for \<F>
  proof -
    have "\<And>U. \<lbrakk>U \<in> \<U>; U \<inter> \<Union>\<F> = topspace X \<inter> U\<rbrakk>
               \<Longrightarrow> \<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<F> \<and> U \<inter> \<Union>\<V> = topspace X \<inter> U"
      using lin \<F>
      unfolding Lindelof_space_def openin_subtopology_alt Ball_def subset_iff [symmetric]
      by (simp add: all_subset_image imp_conjL ex_countable_subset_image)
    then obtain g where g: "\<And>U. \<lbrakk>U \<in> \<U>; U \<inter> \<Union>\<F> = topspace X \<inter> U\<rbrakk>
                               \<Longrightarrow> countable (g U) \<and> (g U) \<subseteq> \<F> \<and> U \<inter> \<Union>(g U) = topspace X \<inter> U"
      by metis
    show ?thesis
    proof (intro exI conjI)
      show "countable (\<Union>(g ` \<U>))"
        using Int_commute UF g  by (fastforce intro: countable_UN [OF \<U>])
      show "\<Union>(g ` \<U>) \<subseteq> \<F>"
        using g UF by blast
      show "\<Union>\<U> \<inter> \<Union>(\<Union>(g ` \<U>)) = topspace X \<inter> \<Union>\<U>"
      proof
        show "\<Union>\<U> \<inter> \<Union>(\<Union>(g ` \<U>)) \<subseteq> topspace X \<inter> \<Union>\<U>"
          using g UF by blast
        show "topspace X \<inter> \<Union>\<U> \<subseteq> \<Union>\<U> \<inter> \<Union>(\<Union>(g ` \<U>))"
        proof clarsimp
          show "\<exists>y\<in>\<U>. \<exists>W\<in>g y. x \<in> W"
            if "x \<in> topspace X" "x \<in> V" "V \<in> \<U>" for x V
          proof -
            have "V \<inter> \<Union>\<F> = topspace X \<inter> V"
              using UF \<open>V \<in> \<U>\<close> by blast
            with that g [OF \<open>V \<in> \<U>\<close>]  show ?thesis by blast
          qed
        qed
      qed
    qed
  qed
  then show ?thesis
      unfolding Lindelof_space_def openin_subtopology_alt Ball_def subset_iff [symmetric]
      by (simp add: all_subset_image imp_conjL ex_countable_subset_image)
qed

lemma countable_imp_Lindelof_space:
  assumes "countable(topspace X)"
  shows "Lindelof_space X"
proof -
  have "Lindelof_space (subtopology X (\<Union>x \<in> topspace X. {x}))"
  proof (rule Lindelof_space_Union)
    show "countable ((\<lambda>x. {x}) ` topspace X)"
      using assms by blast
    show "Lindelof_space (subtopology X U)"
      if "U \<in> (\<lambda>x. {x}) ` topspace X" for U
    proof -
      have "compactin X U"
        using that by force
      then show ?thesis
        by (meson compact_imp_Lindelof_space compact_space_subtopology)
    qed
  qed
  then show ?thesis
    by simp
qed
lemma Lindelof_space_subtopology:
   "Lindelof_space(subtopology X S) \<longleftrightarrow>
        (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> topspace X \<inter> S \<subseteq> \<Union>\<U>
            \<longrightarrow> (\<exists>V. countable V \<and> V \<subseteq> \<U> \<and> topspace X \<inter> S \<subseteq> \<Union>V))"
proof -
  have *: "(S \<inter> \<Union>\<U> = topspace X \<inter> S) = (topspace X \<inter> S \<subseteq> \<Union>\<U>)"
    if "\<And>x. x \<in> \<U> \<Longrightarrow> openin X x" for \<U>
    by (blast dest: openin_subset [OF that])
  moreover have "(\<V> \<subseteq> \<U> \<and> S \<inter> \<Union>\<V> = topspace X \<inter> S) = (\<V> \<subseteq> \<U> \<and> topspace X \<inter> S \<subseteq> \<Union>\<V>)"
    if "\<forall>x. x \<in> \<U> \<longrightarrow> openin X x" "topspace X \<inter> S \<subseteq> \<Union>\<U>" "countable \<V>" for \<U> \<V>
    using that * by blast
  ultimately show ?thesis
    unfolding Lindelof_space_def openin_subtopology_alt Ball_def
    apply (simp add: all_subset_image imp_conjL ex_countable_subset_image flip: subset_iff)
    apply (intro all_cong1 imp_cong ex_cong, auto)
    done
qed

lemma Lindelof_space_subtopology_subset:
   "S \<subseteq> topspace X
        \<Longrightarrow> (Lindelof_space(subtopology X S) \<longleftrightarrow>
             (\<forall>\<U>. (\<forall>U \<in> \<U>. openin X U) \<and> S \<subseteq> \<Union>\<U>
                 \<longrightarrow> (\<exists>V. countable V \<and> V \<subseteq> \<U> \<and> S \<subseteq> \<Union>V)))"
  by (metis Lindelof_space_subtopology topspace_subtopology topspace_subtopology_subset)

lemma Lindelof_space_closedin_subtopology:
  assumes X: "Lindelof_space X" and clo: "closedin X S"
  shows "Lindelof_space (subtopology X S)"
proof -
  have "S \<subseteq> topspace X"
    by (simp add: clo closedin_subset)
  then show ?thesis
  proof (clarsimp simp add: Lindelof_space_subtopology_subset)
    show "\<exists>V. countable V \<and> V \<subseteq> \<F> \<and> S \<subseteq> \<Union>V"
      if "\<forall>U\<in>\<F>. openin X U" and "S \<subseteq> \<Union>\<F>" for \<F>
    proof -
      have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> insert (topspace X - S) \<F> \<and> \<Union>\<V> = topspace X"
      proof (rule Lindelof_spaceD [OF X, of "insert (topspace X - S) \<F>"])
        show "openin X U"
          if "U \<in> insert (topspace X - S) \<F>" for U
          using that \<open>\<forall>U\<in>\<F>. openin X U\<close> clo by blast
        show "\<Union>(insert (topspace X - S) \<F>) = topspace X"
          apply auto
          apply (meson in_mono openin_closedin_eq that(1))
          using UnionE \<open>S \<subseteq> \<Union>\<F>\<close> by auto
      qed
      then obtain \<V> where "countable \<V>" "\<V> \<subseteq> insert (topspace X - S) \<F>" "\<Union>\<V> = topspace X"
        by metis
      with \<open>S \<subseteq> topspace X\<close>
      show ?thesis
        by (rule_tac x="(\<V> - {topspace X - S})" in exI) auto
    qed
  qed
qed

lemma Lindelof_space_continuous_map_image:
  assumes X: "Lindelof_space X" and f: "continuous_map X Y f" and fim: "f ` (topspace X) = topspace Y"
  shows "Lindelof_space Y"
proof -
  have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> \<Union>\<V> = topspace Y"
    if \<U>: "\<And>U. U \<in> \<U> \<Longrightarrow> openin Y U" and UU: "\<Union>\<U> = topspace Y" for \<U>
  proof -
    define \<V> where "\<V> \<equiv> (\<lambda>U. {x \<in> topspace X. f x \<in> U}) ` \<U>"
    have "\<And>V. V \<in> \<V> \<Longrightarrow> openin X V"
      unfolding \<V>_def using \<U> continuous_map f by fastforce
    moreover have "\<Union>\<V> = topspace X"
      unfolding \<V>_def using UU fim by fastforce
    ultimately have "\<exists>\<W>. countable \<W> \<and> \<W> \<subseteq> \<V> \<and> \<Union>\<W> = topspace X"
      using X by (simp add: Lindelof_space_def)
    then obtain \<C> where "countable \<C>" "\<C> \<subseteq> \<U>" and \<C>: "(\<Union>U\<in>\<C>. {x \<in> topspace X. f x \<in> U}) = topspace X"
      by (metis (no_types, lifting) \<V>_def countable_subset_image)
    moreover have "\<Union>\<C> = topspace Y"
    proof
      show "\<Union>\<C> \<subseteq> topspace Y"
        using UU \<C> \<open>\<C> \<subseteq> \<U>\<close> by fastforce
      have "y \<in> \<Union>\<C>" if "y \<in> topspace Y" for y
      proof -
        obtain x where "x \<in> topspace X" "y = f x"
          using that fim by (metis \<open>y \<in> topspace Y\<close> imageE)
        with \<C> show ?thesis by auto
      qed
      then show "topspace Y \<subseteq> \<Union>\<C>" by blast
    qed
    ultimately show ?thesis
      by blast
  qed
  then show ?thesis
    unfolding Lindelof_space_def
    by auto
qed

lemma Lindelof_space_quotient_map_image:
   "\<lbrakk>quotient_map X Y q; Lindelof_space X\<rbrakk> \<Longrightarrow> Lindelof_space Y"
  by (meson Lindelof_space_continuous_map_image quotient_imp_continuous_map quotient_imp_surjective_map)

lemma Lindelof_space_retraction_map_image:
   "\<lbrakk>retraction_map X Y r; Lindelof_space X\<rbrakk> \<Longrightarrow> Lindelof_space Y"
  using Abstract_Topology.retraction_imp_quotient_map Lindelof_space_quotient_map_image by blast

lemma locally_finite_cover_of_Lindelof_space:
  assumes X: "Lindelof_space X" and UU: "topspace X \<subseteq> \<Union>\<U>" and fin: "locally_finite_in X \<U>"
  shows "countable \<U>"
proof -
  have UU_eq: "\<Union>\<U> = topspace X"
    by (meson UU fin locally_finite_in_def subset_antisym)
  obtain T where T: "\<And>x. x \<in> topspace X \<Longrightarrow> openin X (T x) \<and> x \<in> T x \<and> finite {U \<in> \<U>. U \<inter> T x \<noteq> {}}"
    using fin unfolding locally_finite_in_def by metis
  then obtain I where "countable I" "I \<subseteq> topspace X" and I: "topspace X \<subseteq> \<Union>(T ` I)"
    using X unfolding Lindelof_space_alt
    by (drule_tac x="image T (topspace X)" in spec) (auto simp: ex_countable_subset_image)
  show ?thesis
  proof (rule countable_subset)
    have "\<And>i. i \<in> I \<Longrightarrow> countable {U \<in> \<U>. U \<inter> T i \<noteq> {}}"
      using T
      by (meson \<open>I \<subseteq> topspace X\<close> in_mono uncountable_infinite)
    then show "countable (insert {} (\<Union>i\<in>I. {U \<in> \<U>. U \<inter> T i \<noteq> {}}))"
      by (simp add: \<open>countable I\<close>)
  qed (use UU_eq I in auto)
qed


lemma Lindelof_space_proper_map_preimage:
  assumes f: "proper_map X Y f" and Y: "Lindelof_space Y"
  shows "Lindelof_space X"
proof (clarsimp simp: Lindelof_space_alt)
  show "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<U> \<and> topspace X \<subseteq> \<Union>\<V>"
    if \<U>: "\<forall>U\<in>\<U>. openin X U" and sub_UU: "topspace X \<subseteq> \<Union>\<U>" for \<U>
  proof -
    have "\<exists>\<V>. finite \<V> \<and> \<V> \<subseteq> \<U> \<and> {x \<in> topspace X. f x = y} \<subseteq> \<Union>\<V>" if "y \<in> topspace Y" for y
    proof (rule compactinD)
      show "compactin X {x \<in> topspace X. f x = y}"
        using f proper_map_def that by fastforce
    qed (use sub_UU \<U> in auto)
    then obtain \<V> where \<V>: "\<And>y. y \<in> topspace Y \<Longrightarrow> finite (\<V> y) \<and> \<V> y \<subseteq> \<U> \<and> {x \<in> topspace X. f x = y} \<subseteq> \<Union>(\<V> y)"
      by meson
    define \<W> where "\<W> \<equiv> (\<lambda>y. topspace Y - image f (topspace X - \<Union>(\<V> y))) ` topspace Y"
    have "\<forall>U \<in> \<W>. openin Y U"
      using f \<U> \<V> unfolding \<W>_def proper_map_def closed_map_def
      by (simp add: closedin_diff openin_Union openin_diff subset_iff)
    moreover have "topspace Y \<subseteq> \<Union>\<W>"
      using \<V> unfolding \<W>_def by clarsimp fastforce
    ultimately have "\<exists>\<V>. countable \<V> \<and> \<V> \<subseteq> \<W> \<and> topspace Y \<subseteq> \<Union>\<V>"
      using Y by (simp add: Lindelof_space_alt)
    then obtain I where "countable I" "I \<subseteq> topspace Y"
      and I: "topspace Y \<subseteq> (\<Union>i\<in>I. topspace Y - f ` (topspace X - \<Union>(\<V> i)))"
      unfolding \<W>_def ex_countable_subset_image by metis
    show ?thesis
    proof (intro exI conjI)
      have "\<And>i. i \<in> I \<Longrightarrow> countable (\<V> i)"
        by (meson \<V> \<open>I \<subseteq> topspace Y\<close> in_mono uncountable_infinite)
      with \<open>countable I\<close> show "countable (\<Union>(\<V> ` I))"
        by auto
      show "\<Union>(\<V> ` I) \<subseteq> \<U>"
        using \<V> \<open>I \<subseteq> topspace Y\<close> by fastforce
      show "topspace X \<subseteq> \<Union>(\<Union>(\<V> ` I))"
      proof
        show "x \<in> \<Union> (\<Union> (\<V> ` I))" if "x \<in> topspace X" for x
        proof -
          have "f x \<in> topspace Y"
            by (meson f image_subset_iff proper_map_imp_subset_topspace that)
          then show ?thesis
            using that I by auto
        qed
      qed
    qed
  qed
qed

lemma Lindelof_space_perfect_map_image:
   "\<lbrakk>Lindelof_space X; perfect_map X Y f\<rbrakk> \<Longrightarrow> Lindelof_space Y"
  using Lindelof_space_quotient_map_image perfect_imp_quotient_map by blast

lemma Lindelof_space_perfect_map_image_eq:
   "perfect_map X Y f \<Longrightarrow> Lindelof_space X \<longleftrightarrow> Lindelof_space Y"
  using Lindelof_space_perfect_map_image Lindelof_space_proper_map_preimage perfect_map_def by blast

end


(*  Author:     L C Paulson, University of Cambridge [ported from HOL Light, metric.ml] *)

section \<open>$F$-Sigma and $G$-Delta sets in a Topological Space\<close>

text \<open>An $F$-sigma set is a countable union of closed sets; a $G$-delta set is the dual.\<close>

theory FSigma
  imports Abstract_Topology
begin


definition fsigma_in 
  where "fsigma_in X \<equiv> countable union_of closedin X"

definition gdelta_in 
  where "gdelta_in X \<equiv> (countable intersection_of openin X) relative_to topspace X"

lemma fsigma_in_ascending:
   "fsigma_in X S \<longleftrightarrow> (\<exists>C. (\<forall>n. closedin X (C n)) \<and> (\<forall>n. C n \<subseteq> C(Suc n)) \<and> \<Union> (range C) = S)"
  unfolding fsigma_in_def
  by (metis closedin_Un countable_union_of_ascending closedin_empty)

lemma gdelta_in_alt:
   "gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> (countable intersection_of openin X) S"
proof -
  have "(countable intersection_of openin X) (topspace X)"
    by (simp add: countable_intersection_of_inc)
  then show ?thesis
    unfolding gdelta_in_def
    by (metis countable_intersection_of_inter relative_to_def relative_to_imp_subset relative_to_subset_inc)
qed

lemma fsigma_in_subset: "fsigma_in X S \<Longrightarrow> S \<subseteq> topspace X"
  using closedin_subset by (fastforce simp: fsigma_in_def union_of_def subset_iff)

lemma gdelta_in_subset: "gdelta_in X S \<Longrightarrow> S \<subseteq> topspace X"
  by (simp add: gdelta_in_alt)

lemma closed_imp_fsigma_in: "closedin X S \<Longrightarrow> fsigma_in X S"
  by (simp add: countable_union_of_inc fsigma_in_def)

lemma open_imp_gdelta_in: "openin X S \<Longrightarrow> gdelta_in X S"
  by (simp add: countable_intersection_of_inc gdelta_in_alt openin_subset)

lemma fsigma_in_empty [iff]: "fsigma_in X {}"
  by (simp add: closed_imp_fsigma_in)

lemma gdelta_in_empty [iff]: "gdelta_in X {}"
  by (simp add: open_imp_gdelta_in)

lemma fsigma_in_topspace [iff]: "fsigma_in X (topspace X)"
  by (simp add: closed_imp_fsigma_in)

lemma gdelta_in_topspace [iff]: "gdelta_in X (topspace X)"
  by (simp add: open_imp_gdelta_in)

lemma fsigma_in_Union:
   "\<lbrakk>countable T; \<And>S. S \<in> T \<Longrightarrow> fsigma_in X S\<rbrakk> \<Longrightarrow> fsigma_in X (\<Union> T)"
  by (simp add: countable_union_of_Union fsigma_in_def)

lemma fsigma_in_Un:
   "\<lbrakk>fsigma_in X S; fsigma_in X T\<rbrakk> \<Longrightarrow> fsigma_in X (S \<union> T)"
  by (simp add: countable_union_of_Un fsigma_in_def)

lemma fsigma_in_Int:
   "\<lbrakk>fsigma_in X S; fsigma_in X T\<rbrakk> \<Longrightarrow> fsigma_in X (S \<inter> T)"
  by (simp add: closedin_Int countable_union_of_Int fsigma_in_def)

lemma gdelta_in_Inter:
   "\<lbrakk>countable T; T\<noteq>{}; \<And>S. S \<in> T \<Longrightarrow> gdelta_in X S\<rbrakk> \<Longrightarrow> gdelta_in X (\<Inter> T)"
  by (simp add: Inf_less_eq countable_intersection_of_Inter gdelta_in_alt)

lemma gdelta_in_Int:
   "\<lbrakk>gdelta_in X S; gdelta_in X T\<rbrakk> \<Longrightarrow> gdelta_in X (S \<inter> T)"
  by (simp add: countable_intersection_of_inter gdelta_in_alt le_infI2)

lemma gdelta_in_Un:
   "\<lbrakk>gdelta_in X S; gdelta_in X T\<rbrakk> \<Longrightarrow> gdelta_in X (S \<union> T)"
  by (simp add: countable_intersection_of_union gdelta_in_alt openin_Un)

lemma fsigma_in_diff:
  assumes "fsigma_in X S" "gdelta_in X T"
  shows "fsigma_in X (S - T)"
proof -
  have [simp]: "S - (S \<inter> T) = S - T" for S T :: "'a set"
    by auto
  have [simp]: "topspace X - \<Inter>\<T> = (\<Union>T\<in>\<T>. topspace X - T)" for \<T>
    by auto
  have "\<And>\<T>. \<lbrakk>countable \<T>; \<T> \<subseteq> Collect (openin X)\<rbrakk> \<Longrightarrow>
             (countable union_of closedin X) (\<Union> ((-) (topspace X) ` \<T>))"
    by (metis Ball_Collect countable_union_of_UN countable_union_of_inc openin_closedin_eq)
  then have "\<forall>S. gdelta_in X S \<longrightarrow> fsigma_in X (topspace X - S)"
    by (simp add: fsigma_in_def gdelta_in_def all_relative_to all_intersection_of del: UN_simps)
  then show ?thesis
    by (metis Diff_Int2 Diff_Int_distrib2 assms fsigma_in_Int fsigma_in_subset inf.absorb_iff2)
qed

lemma gdelta_in_diff:
  assumes "gdelta_in X S" "fsigma_in X T"
  shows "gdelta_in X (S - T)"
proof -
  have [simp]: "topspace X - \<Union>\<T> = topspace X \<inter> (\<Inter>T\<in>\<T>. topspace X - T)" for \<T>
    by auto
  have "\<And>\<T>. \<lbrakk>countable \<T>; \<T> \<subseteq> Collect (closedin X)\<rbrakk>
         \<Longrightarrow> (countable intersection_of openin X relative_to topspace X)
              (topspace X \<inter> \<Inter> ((-) (topspace X) ` \<T>))"
    by (metis Ball_Collect closedin_def countable_intersection_of_INT countable_intersection_of_inc relative_to_inc)
  then have "\<forall>S. fsigma_in X S \<longrightarrow> gdelta_in X (topspace X - S)"
    by (simp add: fsigma_in_def gdelta_in_def all_union_of del: INT_simps)
  then show ?thesis
    by (metis Diff_Int2 Diff_Int_distrib2 assms gdelta_in_Int gdelta_in_alt inf.orderE inf_commute)
qed

lemma gdelta_in_fsigma_in:
   "gdelta_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> fsigma_in X (topspace X - S)"
  by (metis double_diff fsigma_in_diff fsigma_in_topspace gdelta_in_alt gdelta_in_diff gdelta_in_topspace)

lemma fsigma_in_gdelta_in:
   "fsigma_in X S \<longleftrightarrow> S \<subseteq> topspace X \<and> gdelta_in X (topspace X - S)"
  by (metis Diff_Diff_Int fsigma_in_subset gdelta_in_fsigma_in inf.absorb_iff2)

lemma gdelta_in_descending:
   "gdelta_in X S \<longleftrightarrow> (\<exists>C. (\<forall>n. openin X (C n)) \<and> (\<forall>n. C(Suc n) \<subseteq> C n) \<and> \<Inter>(range C) = S)" (is "?lhs=?rhs")
proof
  assume ?lhs
  then obtain C where C: "S \<subseteq> topspace X" "\<And>n. closedin X (C n)" 
                         "\<And>n. C n \<subseteq> C(Suc n)" "\<Union>(range C) = topspace X - S"
    by (meson fsigma_in_ascending gdelta_in_fsigma_in)
  define D where "D \<equiv> \<lambda>n. topspace X - C n"
  have "\<And>n. openin X (D n) \<and> D (Suc n) \<subseteq> D n"
    by (simp add: Diff_mono C D_def openin_diff)
  moreover have "\<Inter>(range D) = S"
    by (simp add: Diff_Diff_Int Int_absorb1 C D_def)
  ultimately show ?rhs
    by metis
next
  assume ?rhs
  then obtain C where "S \<subseteq> topspace X" 
                and C: "\<And>n. openin X (C n)" "\<And>n. C(Suc n) \<subseteq> C n" "\<Inter>(range C) = S"
    using openin_subset by fastforce
  define D where "D \<equiv> \<lambda>n. topspace X - C n"
  have "\<And>n. closedin X (D n) \<and> D n \<subseteq> D(Suc n)"
    by (simp add: Diff_mono C closedin_diff D_def)
  moreover have "\<Union>(range D) = topspace X - S"
    using C D_def by blast
  ultimately show ?lhs
    by (metis \<open>S \<subseteq> topspace X\<close> fsigma_in_ascending gdelta_in_fsigma_in)
qed

lemma homeomorphic_map_fsigmaness:
  assumes f: "homeomorphic_map X Y f" and "U \<subseteq> topspace X"
  shows "fsigma_in Y (f ` U) \<longleftrightarrow> fsigma_in X U"  (is "?lhs=?rhs")
proof -
  obtain g where g: "homeomorphic_maps X Y f g" and g: "homeomorphic_map Y X g"
    and 1: "(\<forall>x \<in> topspace X. g(f x) = x)" and 2: "(\<forall>y \<in> topspace Y. f(g y) = y)"
    using assms homeomorphic_map_maps by (metis homeomorphic_maps_map)
  show ?thesis
  proof
    assume ?lhs
    then obtain \<V> where "countable \<V>" and \<V>: "\<V> \<subseteq> Collect (closedin Y)" "\<Union>\<V> = f`U"
      by (force simp: fsigma_in_def union_of_def)
    define \<U> where "\<U> \<equiv> image (image g) \<V>"
    have "countable \<U>"
      using \<U>_def \<open>countable \<V>\<close> by blast
    moreover have "\<U> \<subseteq> Collect (closedin X)"
      using f g homeomorphic_map_closedness_eq \<V> unfolding \<U>_def by blast
    moreover have "\<Union>\<U> \<subseteq> U"
      unfolding \<U>_def  by (smt (verit) assms 1 \<V> image_Union image_iff in_mono subsetI)
    moreover have "U \<subseteq> \<Union>\<U>"
      unfolding \<U>_def using assms \<V>
      by (smt (verit, del_insts) "1" imageI image_Union subset_iff)
    ultimately show ?rhs
      by (metis fsigma_in_def subset_antisym union_of_def)
  next
    assume ?rhs
    then obtain \<V> where "countable \<V>" and \<V>: "\<V> \<subseteq> Collect (closedin X)" "\<Union>\<V> = U"
      by (auto simp: fsigma_in_def union_of_def)
    define \<U> where "\<U> \<equiv> image (image f) \<V>"
    have "countable \<U>"
      using \<U>_def \<open>countable \<V>\<close> by blast
    moreover have "\<U> \<subseteq> Collect (closedin Y)"
      using f g homeomorphic_map_closedness_eq \<V> unfolding \<U>_def by blast
    moreover have "\<Union>\<U> = f`U"
      unfolding \<U>_def using \<V> by blast
    ultimately show ?lhs
      by (metis fsigma_in_def union_of_def)
  qed
qed

lemma homeomorphic_map_fsigmaness_eq:
   "homeomorphic_map X Y f
        \<Longrightarrow> (fsigma_in X U \<longleftrightarrow> U \<subseteq> topspace X \<and> fsigma_in Y (f ` U))"
  by (metis fsigma_in_subset homeomorphic_map_fsigmaness)

lemma homeomorphic_map_gdeltaness:
  assumes "homeomorphic_map X Y f" "U \<subseteq> topspace X"
  shows "gdelta_in Y (f ` U) \<longleftrightarrow> gdelta_in X U"
proof -
  have "topspace Y - f ` U = f ` (topspace X - U)"
    by (metis (no_types, lifting) Diff_subset assms homeomorphic_eq_everything_map inj_on_image_set_diff)
  then show ?thesis
    using assms homeomorphic_imp_surjective_map
    by (fastforce simp: gdelta_in_fsigma_in homeomorphic_map_fsigmaness_eq)
qed

lemma homeomorphic_map_gdeltaness_eq:
   "homeomorphic_map X Y f
    \<Longrightarrow> gdelta_in X U \<longleftrightarrow> U \<subseteq> topspace X \<and> gdelta_in Y (f ` U)"
  by (meson gdelta_in_subset homeomorphic_map_gdeltaness)

lemma fsigma_in_relative_to:
   "(fsigma_in X relative_to S) = fsigma_in (subtopology X S)"
  by (simp add: fsigma_in_def countable_union_of_relative_to closedin_relative_to)

lemma fsigma_in_subtopology:
   "fsigma_in (subtopology X U) S \<longleftrightarrow> (\<exists>T. fsigma_in X T \<and> S = T \<inter> U)"
  by (metis fsigma_in_relative_to inf_commute relative_to_def)

lemma gdelta_in_relative_to:
   "(gdelta_in X relative_to S) = gdelta_in (subtopology X S)"
  apply (simp add: gdelta_in_def)
  by (metis countable_intersection_of_relative_to openin_relative_to subtopology_restrict)

lemma gdelta_in_subtopology:
   "gdelta_in (subtopology X U) S \<longleftrightarrow> (\<exists>T. gdelta_in X T \<and> S = T \<inter> U)"
  by (metis gdelta_in_relative_to inf_commute relative_to_def)

lemma fsigma_in_fsigma_subtopology:
   "fsigma_in X S \<Longrightarrow> (fsigma_in (subtopology X S) T \<longleftrightarrow> fsigma_in X T \<and> T \<subseteq> S)"
  by (metis fsigma_in_Int fsigma_in_gdelta_in fsigma_in_subtopology inf.orderE topspace_subtopology_subset)

lemma gdelta_in_gdelta_subtopology:
   "gdelta_in X S \<Longrightarrow> (gdelta_in (subtopology X S) T \<longleftrightarrow> gdelta_in X T \<and> T \<subseteq> S)"
  by (metis gdelta_in_Int gdelta_in_subset gdelta_in_subtopology inf.orderE topspace_subtopology_subset)

end

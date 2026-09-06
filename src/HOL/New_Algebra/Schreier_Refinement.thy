theory Schreier_Refinement
  imports Series_Refinement
begin

section \<open>The Schreier refinement theorem\<close>

text \<open>
  The factors of a refinement are read row by row.  The following elementary
  lemmas turn a rectangular list of entries into finite sums of singleton
  multisets; this makes transposition of the refinement matrix explicit in the
  final proof.
\<close>

lemma mset_map_upt:
  "mset (List.map f [0..<n]) = (\<Sum>i<n. {#f i#})"
  by (induction n) (simp_all add: sum.lessThan_Suc)

lemma mset_concat_map_upt:
  "mset (concat (List.map (\<lambda>i. List.map (f i) [0..<n]) [0..<m])) =
    (\<Sum>i<m. \<Sum>j<n. {#f i j#})"
proof (induction m)
  case 0
  show ?case by simp
next
  case (Suc m)
  have row: "mset (List.map (f m) [0..<n]) = (\<Sum>j<n. {#f m j#})"
    by (rule mset_map_upt)
  have "mset (concat (List.map (\<lambda>i. List.map (f i) [0..<n]) [0..<Suc m])) =
      mset (concat (List.map (\<lambda>i. List.map (f i) [0..<n]) [0..<m])) +
        mset (List.map (f m) [0..<n])"
    by simp
  also have "... = (\<Sum>i<m. \<Sum>j<n. {#f i j#}) +
      (\<Sum>j<n. {#f m j#})"
    by (rule arg_cong2[OF Suc.IH row])
  also have "... = (\<Sum>i<Suc m. \<Sum>j<n. {#f i j#})"
    by (simp add: sum.lessThan_Suc)
  finally show ?case .
qed

lemma length_concat_map_upt:
  "length (concat (List.map (\<lambda>i. List.map (f i) [0..<n]) [0..<m])) =
    m * n"
  by (induction m) (simp_all add: algebra_simps)

text \<open>
  At the endpoints of a refinement row, one factor in a subgroup product is
  either trivial or the whole carrier.  For intermediate terms, intersecting
  the carrier with another ambient subgroup and multiplying by a normal
  subgroup again gives an ambient subgroup.  These generic facts keep the row
  proofs below independent of quotient representations.
\<close>

lemma subgroup_product_with_trivial_left:
  assumes K: "Subgroup K G composition unit"
  shows "(case_prod composition) ` ({unit} \<times> K) = K"
proof -
  interpret K: Subgroup K G composition unit by fact
  have K_monoid: "Monoid K composition unit"
    by (rule K.sub.Monoid_axioms)
  show ?thesis
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> (case_prod composition) ` ({unit} \<times> K)"
    then obtain k where k: "k \<in> K" and x: "x = composition unit k"
      by auto
    then show "x \<in> K" using Monoid.left_unit[OF K_monoid k] by simp
  next
    fix x
    assume x: "x \<in> K"
    show "x \<in> (case_prod composition) ` ({unit} \<times> K)"
    proof (rule image_eqI[where x="(unit, x)"])
      show "x = case_prod composition (unit, x)"
        using Monoid.left_unit[OF K_monoid x] by simp
      show "(unit, x) \<in> {unit} \<times> K" using x by simp
    qed
  qed
qed

lemma subgroup_product_with_carrier_left:
  assumes K: "Subgroup K H composition unit"
  shows "(case_prod composition) ` (H \<times> K) = H"
proof -
  have K_submonoid: "Submonoid K H composition unit"
    by (rule Subgroup.axioms(1)[OF K])
  have H_monoid: "Monoid H composition unit"
    by (rule Submonoid.axioms(1)[OF K_submonoid])
  have K_subset: "K \<subseteq> H"
    by (rule Submonoid.subset[OF K_submonoid])
  have unit_K: "unit \<in> K"
    by (rule Submonoid.sub_unit_closed[OF K_submonoid])
  show ?thesis
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> (case_prod composition) ` (H \<times> K)"
    then obtain h k where h: "h \<in> H" and k: "k \<in> K"
      and x: "x = composition h k" by auto
    show "x \<in> H"
      unfolding x
      by (rule Monoid.composition_closed[OF H_monoid h K_subset[THEN subsetD, OF k]])
  next
    fix x
    assume x: "x \<in> H"
    show "x \<in> (case_prod composition) ` (H \<times> K)"
    proof (rule image_eqI[where x="(x, unit)"])
      show "x = case_prod composition (x, unit)"
        using Monoid.right_unit[OF H_monoid x] by simp
      show "(x, unit) \<in> H \<times> K"
        using x unit_K by simp
    qed
  qed
qed

lemma intersection_normal_product_subgroup:
  assumes G: "Group G composition unit"
    and N: "normal_subgroup K H composition unit"
    and H: "Subgroup H G composition unit"
    and L: "Subgroup L G composition unit"
  shows "Subgroup ((case_prod composition) ` ((H \<inter> L) \<times> K))
    G composition unit"
proof -
  interpret N: normal_subgroup K H composition unit by fact
  have intersection_G: "Subgroup (H \<inter> L) G composition unit"
    by (rule Group.subgroup_intersection[OF G H L])
  have intersection_H: "Subgroup (H \<inter> L) H composition unit"
    by (rule subgroup_restrict[OF intersection_G H]) simp
  have intersection_group:
      "subgroup_of_group (H \<inter> L) H composition unit"
    by (rule subgroup_of_groupI[OF intersection_H N.Group_axioms])
  have product:
      "normal_subgroup_product K (H \<inter> L) H composition unit"
    by (rule normal_subgroup_product.intro[OF N intersection_group])
  have product_subgroup:
      "Subgroup (normal_subgroup_product.HK K (H \<inter> L) composition)
        H composition unit"
    by (rule normal_subgroup_product.HK_subgroup[OF product])
  have "Subgroup ((case_prod composition) ` ((H \<inter> L) \<times> K))
      H composition unit"
    using product_subgroup
    by (simp only: normal_subgroup_product.HK_def[OF product])
  then show ?thesis by (rule subgroup_transitive[OF _ H])
qed

context normal_series_pair
begin

text \<open>
  For every pair of valid step indices, the assumptions of
  @{locale series_refinement_cell} follow directly from the two series.  We
  construct the locale predicate without interpreting it, so clients can
  reuse the proved cell API without re-elaborating the Zassenhaus locale.
\<close>
lemma series_refinement_cellI:
  assumes i: "i < m" and j: "j < n"
  shows "series_refinement_cell G (\<cdot>) \<one> A m B n i j"
proof (rule series_refinement_cell.intro)
  show "normal_series_pair G (\<cdot>) \<one> A m B n"
  proof (rule normal_series_pair.intro)
    show "normal_series G (\<cdot>) \<one> A m"
      by (rule A.normal_series_axioms)
    show "normal_series G (\<cdot>) \<one> B n"
      by (rule B.normal_series_axioms)
  qed
  show "series_refinement_cell_axioms m n i j"
    by (rule series_refinement_cell_axioms.intro[OF i j])
qed

subsection \<open>Refinement rows\<close>

text \<open>
  The left row at index @{term i} runs from @{term "A i"} to
  @{term "A (Suc i)"}; the right row at index @{term j} runs from
  @{term "B j"} to @{term "B (Suc j)"}.  Thus concatenating rows in increasing
  outer index refines the original series.  The normal-chain theorems verify
  every intermediate subgroup and adjacent normality condition.
\<close>

lemma left_refinement_start:
  assumes i: "i < m"
  shows "left_refinement_term i 0 = A i"
proof -
  interpret ASi: Subgroup "A (Suc i)" G "(\<cdot>)" \<one>
    by (rule A.term_subgroup) (use i in simp)
  have intersection: "A (Suc i) \<inter> B 0 = {\<one>}"
    using B.bottom ASi.sub_unit_closed by auto
  show ?thesis
    unfolding left_refinement_term_def intersection
    by (rule subgroup_product_with_trivial_left[OF A.term_subgroup])
      (use i in simp)
qed

lemma left_refinement_end:
  assumes i: "i < m"
  shows "left_refinement_term i n = A (Suc i)"
proof -
  interpret ASi: Subgroup "A (Suc i)" G "(\<cdot>)" \<one>
    by (rule A.term_subgroup) (use i in simp)
  have intersection: "A (Suc i) \<inter> B n = A (Suc i)"
    using B.top ASi.subset by auto
  show ?thesis
    unfolding left_refinement_term_def intersection
    by (rule subgroup_product_with_carrier_left[OF A.normal_step_subgroup[OF i]])
qed

lemma right_refinement_start:
  assumes j: "j < n"
  shows "right_refinement_term j 0 = B j"
proof -
  interpret BSj: Subgroup "B (Suc j)" G "(\<cdot>)" \<one>
    by (rule B.term_subgroup) (use j in simp)
  have intersection: "B (Suc j) \<inter> A 0 = {\<one>}"
    using A.bottom BSj.sub_unit_closed by auto
  show ?thesis
    unfolding right_refinement_term_def intersection
    by (rule subgroup_product_with_trivial_left[OF B.term_subgroup])
      (use j in simp)
qed

lemma right_refinement_end:
  assumes j: "j < n"
  shows "right_refinement_term j m = B (Suc j)"
proof -
  interpret BSj: Subgroup "B (Suc j)" G "(\<cdot>)" \<one>
    by (rule B.term_subgroup) (use j in simp)
  have intersection: "B (Suc j) \<inter> A m = B (Suc j)"
    using A.top BSj.subset by auto
  show ?thesis
    unfolding right_refinement_term_def intersection
    by (rule subgroup_product_with_carrier_left[OF B.normal_step_subgroup[OF j]])
qed

lemma left_refinement_step:
  assumes i: "i < m" and j: "j < n"
  shows "normal_subgroup (left_refinement_term i j)
      (left_refinement_term i (Suc j)) (\<cdot>) \<one>"
proof -
  have C: "series_refinement_cell G (\<cdot>) \<one> A m B n i j"
    by (rule series_refinement_cellI[OF i j])
  show ?thesis
    by (rule series_refinement_cell.left_refinement_normal[OF C])
qed

lemma left_refinement_term_subgroup:
  assumes i: "i < m" and j: "j \<le> n"
  shows "Subgroup (left_refinement_term i j) G (\<cdot>) \<one>"
  unfolding left_refinement_term_def
  by (rule intersection_normal_product_subgroup[OF A.G.Group_axioms
        A.normal_step[OF i] A.term_subgroup B.term_subgroup])
    (use i j in simp_all)

lemma right_refinement_step:
  assumes i: "i < m" and j: "j < n"
  shows "normal_subgroup (right_refinement_term j i)
      (right_refinement_term j (Suc i)) (\<cdot>) \<one>"
proof -
  have C: "series_refinement_cell G (\<cdot>) \<one> A m B n i j"
    by (rule series_refinement_cellI[OF i j])
  show ?thesis
    by (rule series_refinement_cell.right_refinement_normal[OF C])
qed

lemma right_refinement_term_subgroup:
  assumes i: "i \<le> m" and j: "j < n"
  shows "Subgroup (right_refinement_term j i) G (\<cdot>) \<one>"
  unfolding right_refinement_term_def
  by (rule intersection_normal_product_subgroup[OF A.G.Group_axioms
        B.normal_step[OF j] B.term_subgroup A.term_subgroup])
    (use i j in simp_all)

lemma left_refinement_row:
  assumes i: "i < m"
  shows "normal_chain G (\<cdot>) \<one> (left_refinement_term i) n"
proof (intro normal_chain.intro)
  show "Group G (\<cdot>) \<one>" by (rule A.G.Group_axioms)
  show "normal_chain_axioms G (\<cdot>) \<one> (left_refinement_term i) n"
  proof (rule normal_chain_axioms.intro)
    show "\<And>j. j \<le> n \<Longrightarrow>
        Subgroup (left_refinement_term i j) G (\<cdot>) \<one>"
      by (rule left_refinement_term_subgroup[OF i])
    show "\<And>j. j < n \<Longrightarrow>
        normal_subgroup (left_refinement_term i j)
          (left_refinement_term i (Suc j)) (\<cdot>) \<one>"
      by (rule left_refinement_step[OF i])
  qed
qed

lemma right_refinement_row:
  assumes j: "j < n"
  shows "normal_chain G (\<cdot>) \<one> (right_refinement_term j) m"
proof (intro normal_chain.intro)
  show "Group G (\<cdot>) \<one>" by (rule A.G.Group_axioms)
  show "normal_chain_axioms G (\<cdot>) \<one> (right_refinement_term j) m"
  proof (rule normal_chain_axioms.intro)
    show "\<And>i. i \<le> m \<Longrightarrow>
        Subgroup (right_refinement_term j i) G (\<cdot>) \<one>"
      by (rule right_refinement_term_subgroup[OF _ j])
    show "\<And>i. i < m \<Longrightarrow>
        normal_subgroup (right_refinement_term j i)
          (right_refinement_term j (Suc i)) (\<cdot>) \<one>"
      by (rule right_refinement_step[OF _ j])
  qed
qed

subsection \<open>Factor-class refinements\<close>

text \<open>
  The two lists below flatten the left and right refinement rows in row-major
  order.  Each entry is the native isomorphism class of the corresponding
  normal-chain factor; repeated or trivial factors are retained.
\<close>

definition left_refinement_factor_class ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a set group_iso_class"
  where
    "left_refinement_factor_class i j =
      normal_factor_class (left_refinement_term i j)
        (left_refinement_term i (Suc j)) (\<cdot>) \<one>"

definition right_refinement_factor_class ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a set group_iso_class"
  where
    "right_refinement_factor_class j i =
      normal_factor_class (right_refinement_term j i)
        (right_refinement_term j (Suc i)) (\<cdot>) \<one>"

definition left_refinement_factor_classes :: "'a set group_iso_class list"
  where
    "left_refinement_factor_classes =
      concat (List.map
        (\<lambda>i. List.map (left_refinement_factor_class i) [0..<n]) [0..<m])"

definition right_refinement_factor_classes :: "'a set group_iso_class list"
  where
    "right_refinement_factor_classes =
      concat (List.map
        (\<lambda>j. List.map (right_refinement_factor_class j) [0..<m]) [0..<n])"

lemma length_left_refinement_factor_classes:
  "length left_refinement_factor_classes = m * n"
  unfolding left_refinement_factor_classes_def by (rule length_concat_map_upt)

lemma length_right_refinement_factor_classes:
  "length right_refinement_factor_classes = n * m"
  unfolding right_refinement_factor_classes_def by (rule length_concat_map_upt)

lemma refinement_factor_class_eq:
  assumes i: "i < m" and j: "j < n"
  shows "left_refinement_factor_class i j =
    right_refinement_factor_class j i"
proof -
  have C: "series_refinement_cell G (\<cdot>) \<one> A m B n i j"
    by (rule series_refinement_cellI[OF i j])
  show ?thesis
    unfolding left_refinement_factor_class_def right_refinement_factor_class_def
    by (rule series_refinement_cell.refinement_cell_factor_class_eq[OF C])
qed

text \<open>
  The two row-major factor lists need not have the same order.  Their
  multisets agree: transposing the refinement matrix sends the factor at
  position @{term "(i, j)"} to the isomorphic factor at @{term "(j, i)"}.
  This is the native, factor-class form of the Schreier refinement theorem.
\<close>
theorem schreier_refinement:
  "mset left_refinement_factor_classes =
    mset right_refinement_factor_classes"
proof -
  have transpose:
      "(\<Sum>i<m. \<Sum>j<n. {#left_refinement_factor_class i j#}) =
        (\<Sum>i<m. \<Sum>j<n. {#right_refinement_factor_class j i#})"
    by (intro sum.cong) (auto simp: refinement_factor_class_eq)
  have swap:
      "(\<Sum>i<m. \<Sum>j<n. {#right_refinement_factor_class j i#}) =
        (\<Sum>j<n. \<Sum>i<m. {#right_refinement_factor_class j i#})"
    by (rule sum.swap)
  show ?thesis
    unfolding left_refinement_factor_classes_def right_refinement_factor_classes_def
      mset_concat_map_upt
    by (rule trans[OF transpose swap])
qed

end

end

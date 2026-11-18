section \<open>Composition Series, Jordan-Hoelder Uniqueness, and Solvability\<close>

theory Composition_Factors_Solvable
  imports Simple_Factor_Chain Solvable_Transfer
begin

section \<open>Maximal normal subgroups\<close>

text \<open>
  A maximal normal subgroup is proper and admits no proper normal enlargement.
  Stating maximality with non-strict inclusion makes the locale convenient to
  consume in finite-choice and composition-series arguments.
\<close>
locale maximal_normal_subgroup =
  N: normal_subgroup K G "(\<cdot>)" \<one>
  for K and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes proper: "K \<noteq> G"
    and maximal:
      "\<And>L. normal_subgroup L G (\<cdot>) \<one> \<Longrightarrow> K \<subseteq> L \<Longrightarrow>
        L = K \<or> L = G"
begin

lemma strict:
  "K \<subset> G"
  using N.subset proper by blast

end


subsection \<open>The simple-quotient characterisation\<close>

text \<open>
  The quotient of a group by a proper normal subgroup is simple exactly when
  the subgroup is maximal normal.  The forward correspondence uses the
  quotient endpoint characterisations developed for simple factors; the
  reverse direction is precisely normal-subgroup rigidity inside a simple
  factor.
\<close>
theorem maximal_normal_subgroup_iff_simple_factor_group:
  "maximal_normal_subgroup K G composition unit \<longleftrightarrow>
    simple_factor_group K G composition unit"
proof
  assume maximal: "maximal_normal_subgroup K G composition unit"
  interpret maximal: maximal_normal_subgroup K G composition unit by fact

  have quotient_nontrivial:
      "maximal.N.Factor_Group \<noteq> {maximal.N.Class unit}"
  proof
    assume quotient_trivial:
        "maximal.N.Factor_Group = {maximal.N.Class unit}"
    have subgroup_top:
        "subgroup_of_group G G composition unit"
      by (rule subgroup_of_groupI[OF maximal.N.group_self_subgroup
            maximal.N.Group_axioms])
    interpret corr: normal_subgroup_in_subgroup K G G composition unit
    proof (rule normal_subgroup_in_subgroup.intro)
      show "normal_subgroup K G composition unit"
        by (rule maximal.N.normal_subgroup_axioms)
      show "subgroup_of_group G G composition unit" by fact
      show "normal_subgroup_in_subgroup_axioms K G"
        by (rule normal_subgroup_in_subgroup_axioms.intro[OF maximal.N.subset])
    qed
    have "corr.Fract_H_K = {maximal.N.Class unit}"
      using corr.Fract_H_K_eq_top_iff quotient_trivial by simp
    then have "G = K"
      using corr.Fract_H_K_eq_bottom_iff by blast
    then show False using maximal.proper by blast
  qed

  have quotient_normal_cases:
      "Q = {maximal.N.Class unit} \<or> Q = maximal.N.Factor_Group"
    if Q_normal:
      "normal_subgroup Q maximal.N.Factor_Group
        maximal.N.quotient_composition (maximal.N.Class unit)"
    for Q
  proof -
    interpret Q: normal_subgroup Q maximal.N.Factor_Group
      maximal.N.quotient_composition "maximal.N.Class unit"
      by (rule Q_normal)
    define L where
      "L = {g \<in> G. maximal.N.Class g \<in> Q}"

    have L_subgroup: "Subgroup L G composition unit"
    proof (rule maximal.N.subgroupI)
      show "L \<subseteq> G" unfolding L_def by blast
    next
      show "unit \<in> L"
        unfolding L_def using Q.sub_unit_closed maximal.N.unit_closed by simp
    next
      fix g h
      assume g: "g \<in> L" and h: "h \<in> L"
      have classes:
          "maximal.N.quotient_composition (maximal.N.Class g)
            (maximal.N.Class h) \<in> Q"
        using g h unfolding L_def by (intro Q.sub_composition_closed) auto
      show "composition g h \<in> L"
        using g h classes unfolding L_def
        by (simp add: maximal.N.Class_commutes_with_composition)
    next
      fix g
      assume "g \<in> L"
      then show "maximal.N.invertible g"
        unfolding L_def by auto
    next
      fix g
      assume g: "g \<in> L"
      have g_G: "g \<in> G" and class_g: "maximal.N.Class g \<in> Q"
        using g unfolding L_def by auto
      have "maximal.N.quotient.inverse (maximal.N.Class g) \<in> Q"
        by (rule Q.submonoid_inverse_closed[OF
              Q.sub.invertible[OF class_g] class_g])
      then show "maximal.N.inverse g \<in> L"
        using g_G unfolding L_def
        by (simp add: maximal.N.Class_commutes_with_inverse)
    qed
    have L_group: "subgroup_of_group L G composition unit"
      by (rule subgroup_of_groupI[OF L_subgroup maximal.N.Group_axioms])
    interpret L: subgroup_of_group L G composition unit by (rule L_group)
    have L_normal: "normal_subgroup L G composition unit"
    proof
      fix g l
      assume g: "g \<in> G" and l: "l \<in> L"
      have class_g: "maximal.N.Class g \<in> maximal.N.Factor_Group"
        by (rule maximal.N.Class_in_Partition[OF g])
      have inverse_g: "maximal.N.inverse g \<in> G"
        by (rule maximal.N.invertible_inverse_closed[OF
              maximal.N.invertible[OF g] g])
      have l_G: "l \<in> G"
        using l unfolding L_def by simp
      have class_l: "maximal.N.Class l \<in> Q"
        using l unfolding L_def by simp
      have quotient_conjugate:
          "maximal.N.quotient_composition
            (maximal.N.quotient_composition
              (maximal.N.quotient.inverse (maximal.N.Class g))
              (maximal.N.Class l))
            (maximal.N.Class g) \<in> Q"
        by (rule Q.normal[OF class_g class_l])
      show "composition (composition (maximal.N.inverse g) l) g \<in> L"
        using g inverse_g l_G quotient_conjugate
        unfolding L_def
        by (simp add: maximal.N.Class_commutes_with_composition
            maximal.N.Class_commutes_with_inverse)
    qed
    have K_subset_L: "K \<subseteq> L"
    proof
      fix k
      assume k: "k \<in> K"
      have "maximal.N.Class k = maximal.N.Class unit"
      proof (rule maximal.N.Class_eq)
        show "(k, unit) \<in> maximal.N.Congruence"
        proof (rule maximal.N.CongruenceI)
          show "k = composition unit k"
            by (rule maximal.N.left_unit[OF maximal.N.sub[OF k], symmetric])
          show "k \<in> G" by (rule maximal.N.sub[OF k])
          show "unit \<in> G" by (rule maximal.N.unit_closed)
          show "k \<in> K" by fact
        qed
      qed
      then show "k \<in> L"
        unfolding L_def using k maximal.N.sub Q.sub_unit_closed by simp
    qed

    interpret corr: normal_subgroup_in_subgroup K L G composition unit
    proof (rule normal_subgroup_in_subgroup.intro)
      show "normal_subgroup K G composition unit"
        by (rule maximal.N.normal_subgroup_axioms)
      show "subgroup_of_group L G composition unit" by fact
      show "normal_subgroup_in_subgroup_axioms K L"
        by (rule normal_subgroup_in_subgroup_axioms.intro[OF K_subset_L])
    qed
    have corr_eq_Q: "corr.Fract_H_K = Q"
    proof (rule equalityI)
      show "corr.Fract_H_K \<subseteq> Q"
      proof
        fix A
        assume "A \<in> corr.Fract_H_K"
        then obtain l where l: "l \<in> L" and A_eq: "A = maximal.N.Class l"
          by (rule corr.Fract_H_K_memE)
        show "A \<in> Q"
          using l A_eq unfolding L_def by simp
      qed
    next
      show "Q \<subseteq> corr.Fract_H_K"
      proof
        fix A
        assume A: "A \<in> Q"
        then have "A \<in> maximal.N.Factor_Group" by (rule Q.sub)
        then obtain g where g: "g \<in> G" and A_eq: "A = maximal.N.Class g"
          using maximal.N.representant_exists by blast
        have "g \<in> L" using A A_eq g unfolding L_def by simp
        then show "A \<in> corr.Fract_H_K"
          unfolding corr.Fract_H_K_def A_eq by blast
      qed
    qed

    have "L = K \<or> L = G"
      by (rule maximal.maximal[OF L_normal K_subset_L])
    then show ?thesis
      using corr_eq_Q corr.Fract_H_K_eq_bottom_iff
        corr.Fract_H_K_eq_top_iff
      by blast
  qed

  show "simple_factor_group K G composition unit"
  proof (intro simple_factor_group.intro)
    show "normal_subgroup K G composition unit"
      by (rule maximal.N.normal_subgroup_axioms)
  next
    show "Simple_Group maximal.N.Factor_Group
        maximal.N.quotient_composition (maximal.N.Class unit)"
    proof (unfold_locales)
      show "maximal.N.Factor_Group \<noteq> {maximal.N.Class unit}"
        by (rule quotient_nontrivial)
    next
      show "\<And>Q. normal_subgroup Q maximal.N.Factor_Group
          maximal.N.quotient_composition (maximal.N.Class unit) \<Longrightarrow>
        Q = {maximal.N.Class unit} \<or> Q = maximal.N.Factor_Group"
        by (rule quotient_normal_cases)
    qed
  qed
next
  assume factor: "simple_factor_group K G composition unit"
  interpret factor: simple_factor_group K G composition unit by fact
  show "maximal_normal_subgroup K G composition unit"
  proof (unfold_locales)
    show "K \<noteq> G" by (rule factor.proper)
  next
    fix L
    assume normal: "normal_subgroup L G composition unit"
      and contained: "K \<subseteq> L"
    show "L = K \<or> L = G"
      by (rule simple_factor_intermediate_normal[OF factor contained normal])
  qed
qed


subsection \<open>Existence in finite groups\<close>

text \<open>
  In a finite group, every proper normal subgroup lies below a maximal normal
  subgroup.  Finiteness is used only to select a maximal member of the finite
  set of proper normal enlargements; the selected subgroup is therefore also
  suitable for induction on the carrier cardinality.
\<close>
theorem finite_maximal_normal_subgroup_above:
  assumes G: "Group G composition unit"
    and finite_G: "finite G"
    and K_normal: "normal_subgroup K G composition unit"
    and K_proper: "K \<noteq> G"
  obtains M where
    "maximal_normal_subgroup M G composition unit" "K \<subseteq> M"
proof -
  let ?candidates =
    "{L. normal_subgroup L G composition unit \<and> K \<subseteq> L \<and> L \<noteq> G}"
  interpret K: normal_subgroup K G composition unit by (rule K_normal)
  have candidates_finite: "finite ?candidates"
  proof (rule finite_subset[OF _ finite_Pow_iff[THEN iffD2, OF finite_G]])
    show "?candidates \<subseteq> Pow G"
    proof
      fix L
      assume "L \<in> ?candidates"
      then have "normal_subgroup L G composition unit" by simp
      then interpret L: normal_subgroup L G composition unit .
      show "L \<in> Pow G" using L.subset by simp
    qed
  qed
  have K_candidate: "K \<in> ?candidates"
    using K_normal K_proper by simp
  have candidates_nonempty: "?candidates \<noteq> {}"
    using K_candidate by blast
  obtain M where M_candidate: "M \<in> ?candidates"
    and M_maximal:
      "\<forall>L \<in> ?candidates. M \<subseteq> L \<longrightarrow> M = L"
    using finite_has_maximal[OF candidates_finite candidates_nonempty]
    by auto
  have M_normal: "normal_subgroup M G composition unit"
    and K_subset_M: "K \<subseteq> M" and M_proper: "M \<noteq> G"
    using M_candidate by auto
  have M_is_maximal: "maximal_normal_subgroup M G composition unit"
  proof (rule maximal_normal_subgroup.intro[OF M_normal])
    show "maximal_normal_subgroup_axioms M G composition unit"
    proof
      show "M \<noteq> G" by fact
    next
      fix L
      assume L_normal: "normal_subgroup L G composition unit"
        and M_subset_L: "M \<subseteq> L"
      show "L = M \<or> L = G"
      proof (cases "L = G")
        case True
        then show ?thesis by simp
      next
        case False
        have "L \<in> ?candidates"
          using L_normal K_subset_M M_subset_L False by auto
        then have "M = L" using M_maximal M_subset_L by blast
        then show ?thesis by simp
      qed
    qed
  qed
  show ?thesis by (rule that[OF M_is_maximal K_subset_M])
qed

corollary finite_nontrivial_group_has_maximal_normal_subgroup:
  assumes G: "Group G composition unit"
    and finite_G: "finite G" and nontrivial: "G \<noteq> {unit}"
  obtains M where "maximal_normal_subgroup M G composition unit"
proof -
  interpret G: Group G composition unit by (rule G)
  have trivial_normal: "normal_subgroup {unit} G composition unit"
    by (rule G.trivial_normal_subgroup)
  have trivial_proper: "{unit} \<noteq> G"
    using nontrivial by blast
  obtain M where M_maximal: "maximal_normal_subgroup M G composition unit"
    and "{unit} \<subseteq> M"
    using finite_maximal_normal_subgroup_above[OF
        G finite_G trivial_normal trivial_proper] .
  show ?thesis by (rule that[OF M_maximal])
qed

section \<open>Composition series of finite groups\<close>

text \<open>
  A composition series for a normal subgroup can be extended by one simple
  factor.  The old terms retain their indices and the new ambient group is
  placed at the successor of the old length.  Keeping this construction
  separate makes the finite-cardinality induction below reusable.
\<close>
definition extend_composition_series ::
    "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set"
  where
    "extend_composition_series H n G i = (if i \<le> n then H i else G)"

lemma extend_composition_series_old [simp]:
  "i \<le> n \<Longrightarrow> extend_composition_series H n G i = H i"
  by (simp add: extend_composition_series_def)

lemma extend_composition_series_top [simp]:
  "extend_composition_series H n G (Suc n) = G"
  by (simp add: extend_composition_series_def)

theorem composition_series_extend_simple_factor:
  assumes series: "composition_series K composition unit H n"
    and factor: "simple_factor_group K G composition unit"
  shows "composition_series G composition unit
    (extend_composition_series H n G) (Suc n)"
proof -
  interpret series: composition_series K composition unit H n
    by (rule series)
  interpret factor: simple_factor_group K G composition unit
    by (rule factor)
  show ?thesis
  proof (intro composition_series.intro)
    show "normal_series G composition unit
        (extend_composition_series H n G) (Suc n)"
    proof (intro normal_series.intro)
      show "Group G composition unit" by (rule factor.N.Group_axioms)
    next
      show "normal_series_axioms G composition unit
          (extend_composition_series H n G) (Suc n)"
      proof (intro normal_series_axioms.intro)
        show "extend_composition_series H n G 0 = {unit}"
          using series.bottom by simp
      next
        show "extend_composition_series H n G (Suc n) = G" by simp
      next
        fix i
        assume i: "i \<le> Suc n"
        show "Subgroup (extend_composition_series H n G i) G composition unit"
        proof (cases "i \<le> n")
          case True
          have old: "Subgroup (H i) K composition unit"
            by (rule series.term_subgroup[OF True])
          show ?thesis
            using subgroup_transitive[OF old factor.N.Subgroup_axioms] True
            by simp
        next
          case False
          then have "i = Suc n" using i by arith
          then show ?thesis
            by (simp add: factor.N.group_self_subgroup)
        qed
      next
        fix i
        assume i: "i < Suc n"
        show "normal_subgroup (extend_composition_series H n G i)
            (extend_composition_series H n G (Suc i)) composition unit"
        proof (cases "i < n")
          case True
          then show ?thesis
            using series.normal_step[OF True] by simp
        next
          case False
          then have "i = n" using i by arith
          then show ?thesis
            using series.top factor.N.normal_subgroup_axioms by simp
        qed
      qed
    qed
  next
    show "composition_series_axioms composition unit
        (extend_composition_series H n G) (Suc n)"
    proof (intro composition_series_axioms.intro)
      fix i
      assume i: "i < Suc n"
      show "simple_factor_group (extend_composition_series H n G i)
          (extend_composition_series H n G (Suc i)) composition unit"
      proof (cases "i < n")
        case True
        then show ?thesis
          using series.factor_simple[OF True] by simp
        next
          case False
          then have "i = n" using i by arith
          then show ?thesis using series.top factor by simp
      qed
    qed
  qed
qed


subsection \<open>Existence\<close>

text \<open>
  Every finite group has a composition series.  For a nontrivial group, choose
  a maximal normal subgroup.  Its quotient is simple, while its proper carrier
  has smaller cardinality, so the induction hypothesis supplies the prefix.
\<close>
theorem finite_group_has_composition_series_ex:
  assumes G: "Group G composition unit" and finite_G: "finite G"
  shows "\<exists>H n. composition_series G composition unit H n"
  using G finite_G
proof (induction "card G" arbitrary: G composition unit rule: less_induct)
  case less
  interpret G: Group G composition unit by (rule less.prems(1))
  show ?case
  proof (cases "G = {unit}")
    case True
    have "composition_series G composition unit (\<lambda>_. G) 0"
    proof (intro composition_series.intro normal_series.intro)
      show "Group G composition unit" by (rule G.Group_axioms)
    next
      show "normal_series_axioms G composition unit (\<lambda>_. G) 0"
        using True G.group_self_subgroup
        by unfold_locales auto
    next
      show "composition_series_axioms composition unit (\<lambda>_. G) 0"
      proof (rule composition_series_axioms.intro)
        fix i :: nat
        assume "i < 0"
        then show "simple_factor_group ((\<lambda>_. G) i)
            ((\<lambda>_. G) (Suc i)) composition unit"
          by simp
      qed
    qed
    then show ?thesis by blast
  next
    case False
    obtain M where maximal: "maximal_normal_subgroup M G composition unit"
      using finite_nontrivial_group_has_maximal_normal_subgroup[OF
          G.Group_axioms less.prems(2) False] .
    interpret maximal: maximal_normal_subgroup M G composition unit
      by (rule maximal)
    have finite_M: "finite M"
      by (rule finite_subset[OF maximal.N.subset less.prems(2)])
    have card_M_less: "card M < card G"
      by (rule psubset_card_mono[OF less.prems(2) maximal.strict])
    have M_group: "Group M composition unit"
      by (rule subgroup_imp_Group[OF maximal.N.Subgroup_axioms])
    obtain H n where prefix: "composition_series M composition unit H n"
      using less.hyps[OF card_M_less M_group finite_M] by blast
    have factor: "simple_factor_group M G composition unit"
      by (rule iffD1[OF maximal_normal_subgroup_iff_simple_factor_group maximal])
    have "composition_series G composition unit
        (extend_composition_series H n G) (Suc n)"
      by (rule composition_series_extend_simple_factor[OF prefix factor])
    then show ?thesis by blast
  qed
qed

corollary finite_group_has_composition_series:
  assumes G: "Group G composition unit" and finite_G: "finite G"
  obtains H n where "composition_series G composition unit H n"
  using finite_group_has_composition_series_ex[OF G finite_G] that by blast

section \<open>The Jordan--Hölder theorem\<close>

text \<open>
  Two composition series of the same set-based group form a normal-series
  pair, while simplicity of their factors supplies the additional rigidity
  needed to collapse each Schreier refinement row.  Keeping these assumptions
  in one locale makes the final comparison symmetric and explicit.
\<close>
locale composition_series_pair =
  normal_series_pair G "(\<cdot>)" \<one> A m B n +
  A_comp: composition_series G "(\<cdot>)" \<one> A m +
  B_comp: composition_series G "(\<cdot>)" \<one> B n
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and A :: "nat \<Rightarrow> 'a set" and m
    and B :: "nat \<Rightarrow> 'a set" and n
begin

text \<open>
  Each refinement row spans one simple composition factor.  The generic
  simple-factor chain theorem therefore leaves exactly that factor after
  deleting repetitions.
\<close>
lemma left_refinement_row_reduction:
  assumes i: "i < m"
  shows "nontrivial_factor_multiset (List.map (left_refinement_factor_class i) [0..<n]) =
         {#A.series_factor_class i#}"
proof -
  have "reduced_normal_chain_factor_multiset (left_refinement_term i) n (\<cdot>) \<one> =
        {#normal_factor_class (A i) (A (Suc i)) (\<cdot>) \<one>#}"
    using A_comp.factor_simple_step i left_refinement_end left_refinement_row left_refinement_start
    by (metis simple_factor_chain_reduction)
  then show ?thesis
    unfolding reduced_normal_chain_factor_multiset_def
      normal_chain_factor_classes_def left_refinement_factor_class_def
      A.series_factor_class_eq_normal_factor_class
    by simp
qed

lemma right_refinement_row_reduction:
  assumes j: "j < n"
  shows "nontrivial_factor_multiset (List.map (right_refinement_factor_class j) [0..<m]) =
         {#B.series_factor_class j#}"
proof -
  have "reduced_normal_chain_factor_multiset (right_refinement_term j) m (\<cdot>) \<one> =
        {#normal_factor_class (B j) (B (Suc j)) (\<cdot>) \<one>#}"
    using B_comp.factor_simple_step j right_refinement_end right_refinement_row right_refinement_start
    by (metis simple_factor_chain_reduction)
  then show ?thesis
    unfolding reduced_normal_chain_factor_multiset_def
      normal_chain_factor_classes_def right_refinement_factor_class_def
      B.series_factor_class_eq_normal_factor_class
    by simp
qed

lemma left_reduced_refinement_eq_series_factor_multiset:
  "left_reduced_refinement_factor_multiset = A.series_factor_multiset"
proof -
  have "left_reduced_refinement_factor_multiset =
      (\<Sum>i<m. nontrivial_factor_multiset (List.map (left_refinement_factor_class i) [0..<n]))"
    by (simp add: left_reduced_refinement_factor_multiset_def left_refinement_factor_classes_def
        nontrivial_factor_multiset_concat_map_upt)
  also have "... = (\<Sum>i<m. {#A.series_factor_class i#})"
    using left_refinement_row_reduction by auto
  also have "... = A.series_factor_multiset"
    using A.series_factor_classes_def A.series_factor_multiset_def by (metis mset_map_upt)
  finally show ?thesis .
qed

lemma right_reduced_refinement_eq_series_factor_multiset:
  "right_reduced_refinement_factor_multiset = B.series_factor_multiset"
proof -
  have "right_reduced_refinement_factor_multiset =
      (\<Sum>j<n. nontrivial_factor_multiset (List.map (right_refinement_factor_class j) [0..<m]))"
    by (simp add: nontrivial_factor_multiset_concat_map_upt right_reduced_refinement_factor_multiset_def
        right_refinement_factor_classes_def)
  also have "... = (\<Sum>j<n. {#B.series_factor_class j#})"
    using right_refinement_row_reduction by auto
  also have "... = B.series_factor_multiset"
    using B.series_factor_classes_def B.series_factor_multiset_def by (metis mset_map_upt)
  finally show ?thesis .
qed

text \<open>
  The factor-class multiset of a composition series is independent of the
  series.  Equality is obtained by identifying each original series with its
  reduced Schreier refinement and applying the reduced refinement theorem.
\<close>
theorem jordan_hoelder:
  "A.series_factor_multiset = B.series_factor_multiset"
  using left_reduced_refinement_eq_series_factor_multiset reduced_schreier_refinement
    right_reduced_refinement_eq_series_factor_multiset by presburger

corollary jordan_hoelder_length: "m = n"
  using A.size_series_factor_multiset B.size_series_factor_multiset jordan_hoelder by argo

end

section \<open>Solvability and composition factors\<close>

subsection \<open>Auxiliary group-theoretic bridges\<close>

text \<open>
  The kernel of the canonical quotient map is the normal subgroup itself.
  Although this is implicit in the quotient construction, an explicit lemma
  is useful whenever a theorem is phrased using the generic homomorphism
  kernel, as is the solvable-extension theorem.
\<close>
lemma (in normal_subgroup) quotient_map_group_epimorphism:
  "group_epimorphism Class G (\<cdot>) unit
    Factor_Group quotient_composition (Class unit)"
proof (rule group_epimorphism.intro)
  show "group_homomorphism Class G (\<cdot>) unit
      Factor_Group quotient_composition (Class unit)"
  proof (rule group_homomorphism.intro)
    show "Monoid_homomorphism Class G (\<cdot>) unit
        Factor_Group quotient_composition (Class unit)"
      by (rule natural.Monoid_homomorphism_axioms)
    show "Group G (\<cdot>) unit" by (rule Group_axioms)
    show "Group Factor_Group quotient_composition (Class unit)"
      by (rule quotient.Group_axioms)
  qed
  show "Monoid_epimorphism Class G (\<cdot>) unit
      Factor_Group quotient_composition (Class unit)"
    by (rule Monoid_epimorphism.intro[OF
          natural.Monoid_homomorphism_axioms natural.surjective_map_axioms])
qed

lemma (in normal_subgroup) quotient_map_kernel:
  "group_homomorphism.Ker Class G (Class unit) = K"
proof -
  interpret quotient_map: group_epimorphism Class G "(\<cdot>)" unit
    Factor_Group quotient_composition "Class unit"
    by (rule quotient_map_group_epimorphism)
  show ?thesis
  proof (rule equalityI)
    show "quotient_map.Ker \<subseteq> K"
    proof
      fix x
      assume x: "x \<in> quotient_map.Ker"
      have x_G: "x \<in> G" by (rule quotient_map.Ker_closed[OF x])
      have class_eq: "Class x = Class unit"
        by (rule quotient_map.Ker_image[OF x])
      have "x \<in> Class x" by (rule Class_self[OF x_G])
      then have "x \<in> Class unit" using class_eq by simp
      then show "x \<in> K" using Class_unit_normal_subgroup by simp
    qed
  next
    show "K \<subseteq> quotient_map.Ker"
    proof
      fix k
      assume k: "k \<in> K"
      have class_eq: "Class k = Class unit"
      proof (rule Class_eq)
        show "(k, unit) \<in> Congruence"
        proof (rule CongruenceI)
          show "k = unit \<cdot> k" by (rule left_unit[OF sub[OF k], symmetric])
          show "k \<in> G" by (rule sub[OF k])
          show "unit \<in> G" by (rule unit_closed)
          show "k \<in> K" by fact
        qed
      qed
      show "k \<in> quotient_map.Ker"
        by (rule quotient_map.Ker_memI[OF class_eq sub[OF k]])
    qed
  qed
qed

text \<open>
  A simple group is solvable exactly when it is abelian.  The nontrivial
  direction uses simplicity on the derived subgroup: if that subgroup were
  the whole carrier, every term of the derived series would remain the whole
  carrier, contradicting solvability.
\<close>
theorem simple_group_solvable_iff_abelian:
  assumes simple: "Simple_Group G composition unit"
  shows "Group.solvable G composition unit \<longleftrightarrow>
    Abelian_Group G composition unit"
proof -
  interpret simple: Simple_Group G composition unit by (rule simple)
  show ?thesis
  proof
    assume solvable: "simple.solvable"
    have derived_cases: "simple.derived = {unit} \<or> simple.derived = G"
      by (rule simple.normal_subgroup_eq_trivial_or_top[OF simple.derived_normal])
    have derived_not_top: "simple.derived \<noteq> G"
    proof
      assume derived_top: "simple.derived = G"
      have series_top: "simple.derivedSeries i = G" for i
      proof (induction i)
        case 0
        show ?case by simp
      next
        case (Suc i)
        have "simple.commutator_subgroup G G = G"
          using derived_top unfolding simple.derived_def .
        then show ?case using Suc.IH by simp
      qed
      obtain i where "simple.derivedSeries i = {unit}"
        using solvable unfolding simple.solvable_def by blast
      then show False using series_top[of i] simple.nontrivial by simp
    qed
    have derived_bottom: "simple.derived = {unit}"
      using derived_cases derived_not_top by blast
    have commutative: "commutative_monoid G composition unit"
    proof (rule commutative_monoid.intro[OF simple.Monoid_axioms])
      show "commutative_monoid_axioms G composition"
      proof
        fix a b
        assume a: "a \<in> G" and b: "b \<in> G"
        have commutator_in: "simple.commutator_elt a b \<in> simple.derived"
          unfolding simple.derived_def
          by (rule simple.commutator_gen_mem[OF a b subset_refl subset_refl])
        have commutator_unit: "simple.commutator_elt a b = unit"
          using commutator_in derived_bottom by simp
        have conjugate_G:
            "composition (composition a b) (simple.inverse a) \<in> G"
          using a b by simp
        have conjugate_inverse:
            "composition (composition (composition a b) (simple.inverse a))
              (simple.inverse b) = unit"
          using commutator_unit unfolding simple.commutator_elt_def .
        have conjugate_eq:
            "composition (composition a b) (simple.inverse a) = b"
        proof (rule simple.inverse_unique[where u="simple.inverse b"])
          show "composition (simple.inverse b) b = unit" using b by simp
          show "composition (composition (composition a b) (simple.inverse a))
              (simple.inverse b) = unit" by (rule conjugate_inverse)
          show "simple.inverse b \<in> G" using b by simp
          show "composition (composition a b) (simple.inverse a) \<in> G"
            by (rule conjugate_G)
          show "b \<in> G" by fact
        qed
        show "composition a b = composition b a"
          using conjugate_eq simple.commute_iff_inverse[OF a b] by simp
      qed
    qed
    show "Abelian_Group G composition unit"
      by (rule Abelian_Group.intro[OF simple.Group_axioms commutative])
  next
    assume abelian: "Abelian_Group G composition unit"
    interpret abelian: Abelian_Group G composition unit by (rule abelian)
    show "simple.solvable"
      by (rule simple.abelian_imp_solvable[OF
            abelian.commutative_monoid_axioms])
  qed
qed


subsection \<open>The factor criterion\<close>

context composition_series
begin

definition abelian_factors :: bool
  where
    "abelian_factors \<longleftrightarrow> (\<forall>i<n.
      Abelian_Group (fst (series_factor i))
        (fst (snd (series_factor i))) (snd (snd (series_factor i))))"

lemma abelian_factorsI:
  assumes "\<And>i. i < n \<Longrightarrow> Abelian_Group (fst (series_factor i))
    (fst (snd (series_factor i))) (snd (snd (series_factor i)))"
  shows abelian_factors
  using assms unfolding abelian_factors_def by blast

lemma abelian_factorsD:
  assumes abelian: abelian_factors and i: "i < n"
  shows "Abelian_Group (fst (series_factor i))
    (fst (snd (series_factor i))) (snd (snd (series_factor i)))"
  using abelian i unfolding abelian_factors_def by blast

text \<open>
  Solvability is equivalent to abelianness of every composition factor.  The
  forward implication passes solvability to each subgroup and then to its
  quotient.  The reverse implication reconstructs solvability one extension
  at a time along the series.
\<close>
theorem solvable_iff_abelian_factors:
  "G.solvable \<longleftrightarrow> abelian_factors"
proof
  assume solvable: "G.solvable"
  show abelian_factors
    unfolding abelian_factors_def
  proof (intro allI impI)
    fix i
    assume i: "i < n"
    interpret step: simple_factor_group "H i" "H (Suc i)" "(\<cdot>)" unit
      by (rule factor_simple[OF i])
    have numerator_subgroup: "Subgroup (H (Suc i)) G (\<cdot>) unit"
      by (rule term_subgroup) (use i in simp)
    have numerator_solvable: "Group.solvable (H (Suc i)) (\<cdot>) unit"
      by (rule G.solvable_subgroup[OF numerator_subgroup solvable])
    interpret quotient_map: group_epimorphism step.N.Class "H (Suc i)"
      "(\<cdot>)" unit step.N.Factor_Group step.N.quotient_composition
      "step.N.Class unit"
      by (rule step.N.quotient_map_group_epimorphism)
    have quotient_solvable: "step.N.quotient.solvable"
      by (rule quotient_map.solvable_image_epi[OF numerator_solvable])
    have quotient_abelian:
        "Abelian_Group step.N.Factor_Group step.N.quotient_composition
          (step.N.Class unit)"
      by (rule iffD1[OF simple_group_solvable_iff_abelian[
            OF step.factor_group_is_simple] quotient_solvable])
    show "Abelian_Group (fst (series_factor i))
        (fst (snd (series_factor i))) (snd (snd (series_factor i)))"
      using quotient_abelian unfolding series_factor_def by simp
  qed
next
  assume factors: abelian_factors
  have term_solvable:
      "i \<le> n \<Longrightarrow> Group.solvable (H i) (\<cdot>) unit" for i
  proof (induction i)
    case 0
    interpret trivial: Group "H 0" "(\<cdot>)" unit
      by (rule subgroup_imp_Group[OF term_subgroup[OF zero_le]])
    have H0: "H 0 = {unit}" by (rule bottom)
    have derived0: "trivial.derivedSeries 0 = {unit}"
      by (rule trans[OF trivial.derivedSeries.simps(1) H0])
    show ?case
      unfolding trivial.solvable_def using derived0 by blast
  next
    case (Suc i)
    have i: "i < n" using Suc.prems by simp
    interpret step: simple_factor_group "H i" "H (Suc i)" "(\<cdot>)" unit
      by (rule factor_simple[OF i])
    interpret quotient_map: group_epimorphism step.N.Class "H (Suc i)"
      "(\<cdot>)" unit step.N.Factor_Group step.N.quotient_composition
      "step.N.Class unit"
      by (rule step.N.quotient_map_group_epimorphism)
    have kernel_eq: "quotient_map.Ker = H i"
      by (rule step.N.quotient_map_kernel)
    have kernel_solvable:
        "Group.solvable quotient_map.Ker (\<cdot>) unit"
      using Suc.IH[OF less_imp_le[OF i]] kernel_eq by simp
    have factor_abelian:
        "Abelian_Group step.N.Factor_Group step.N.quotient_composition
          (step.N.Class unit)"
      using abelian_factorsD[OF factors i]
      unfolding series_factor_def by simp
    interpret factor_abelian:
      Abelian_Group step.N.Factor_Group step.N.quotient_composition
        "step.N.Class unit"
      by (rule factor_abelian)
    have factor_solvable: "step.N.quotient.solvable"
      by (rule step.N.quotient.abelian_imp_solvable[OF
            factor_abelian.commutative_monoid_axioms])
    show ?case
      by (rule quotient_map.solvable_extension[OF
            kernel_solvable factor_solvable])
  qed
  show "G.solvable"
    using term_solvable[OF order_refl] top by simp
qed

end


subsection \<open>Independence and finite-group formulations\<close>

context composition_series_pair
begin

text \<open>
  The Jordan--Hölder theorem identifies the complete factor multisets.  For
  abelianness, the solvability criterion gives the corresponding invariance
  immediately, without choosing isomorphisms between matched factors.
\<close>
corollary abelian_factors_iff:
  "A_comp.abelian_factors \<longleftrightarrow> B_comp.abelian_factors"
  using A_comp.solvable_iff_abelian_factors
    B_comp.solvable_iff_abelian_factors by blast

end

text \<open>
  For finite groups the existential and universal formulations are both
  available because a composition series always exists.  The universal form
  makes independence of the chosen series explicit.
\<close>
theorem finite_group_solvable_iff_has_composition_series_with_abelian_factors:
  assumes G: "Group G composition unit" and finite_G: "finite G"
  shows "Group.solvable G composition unit \<longleftrightarrow>
    (\<exists>H n. composition_series G composition unit H n \<and>
      composition_series.abelian_factors composition unit H n)"
proof
  assume solvable: "Group.solvable G composition unit"
  obtain H n where series: "composition_series G composition unit H n"
    using finite_group_has_composition_series[OF G finite_G] .
  interpret series: composition_series G composition unit H n by (rule series)
  have "series.abelian_factors"
    using solvable series.solvable_iff_abelian_factors by blast
  then show "\<exists>H n. composition_series G composition unit H n \<and>
      composition_series.abelian_factors composition unit H n"
    using series by blast
next
  assume "\<exists>H n. composition_series G composition unit H n \<and>
      composition_series.abelian_factors composition unit H n"
  then obtain H n where series: "composition_series G composition unit H n"
    and factors: "composition_series.abelian_factors composition unit H n"
    by blast
  interpret series: composition_series G composition unit H n by (rule series)
  show "Group.solvable G composition unit"
    using factors series.solvable_iff_abelian_factors by blast
qed

theorem finite_group_solvable_iff_all_composition_series_have_abelian_factors:
  assumes G: "Group G composition unit" and finite_G: "finite G"
  shows "Group.solvable G composition unit \<longleftrightarrow>
    (\<forall>H n. composition_series G composition unit H n \<longrightarrow>
      composition_series.abelian_factors composition unit H n)"
proof
  assume solvable: "Group.solvable G composition unit"
  show "\<forall>H n. composition_series G composition unit H n \<longrightarrow>
      composition_series.abelian_factors composition unit H n"
  proof (intro allI impI)
    fix H n
    assume series: "composition_series G composition unit H n"
    interpret series: composition_series G composition unit H n by (rule series)
    show "series.abelian_factors"
      using solvable series.solvable_iff_abelian_factors by blast
  qed
next
  assume all_series:
    "\<forall>H n. composition_series G composition unit H n \<longrightarrow>
      composition_series.abelian_factors composition unit H n"
  obtain H n where series: "composition_series G composition unit H n"
    using finite_group_has_composition_series[OF G finite_G] .
  interpret series: composition_series G composition unit H n by (rule series)
  have "series.abelian_factors" using all_series series by blast
  then show "Group.solvable G composition unit"
    using series.solvable_iff_abelian_factors by blast
qed

text \<open>Read the other way, the criterion says an abelian group has only abelian composition factors:
  an abelian group is solvable, and solvability is equivalent to all factors being abelian.\<close>
lemma abelian_group_composition_factors_abelian:
  assumes ab: "Abelian_Group G comp e"
    and series: "composition_series G comp e H m"
  shows "composition_series.abelian_factors comp e H m"
proof -
  interpret ab: Abelian_Group G comp e by (rule ab)
  interpret S: composition_series G comp e H m by (rule series)
  \<comment> \<open>@{thm [source] Group.abelian_imp_solvable} wants the \<^emph>\<open>commutative monoid\<close> component, which an
    abelian group supplies as one of its axioms.\<close>
  have "Group.solvable G comp e"
    by (rule ab.abelian_imp_solvable) (rule ab.commutative_monoid_axioms)
  then show ?thesis using S.solvable_iff_abelian_factors by blast
qed

end

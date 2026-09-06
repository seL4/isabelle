theory Maximal_Normal_Subgroup
  imports Simple_Factor_Chain
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

end

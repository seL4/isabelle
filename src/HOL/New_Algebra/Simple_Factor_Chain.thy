section \<open>Composition series, etc.\<close>

theory Simple_Factor_Chain
  imports Schreier_Refinement Normal_Series
begin

subsection \<open>Simple groups\<close>

text \<open>
  A simple group is a non-trivial group whose only normal subgroups are the
  trivial subgroup and the whole group.\<close>

locale Simple_Group = Group G "(\<cdot>)" \<one>
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes nontrivial: "G \<noteq> {\<one>}"
    and normal_subgroup_eq_trivial_or_top:
      "\<And>K. normal_subgroup K G (\<cdot>) \<one> \<Longrightarrow> K = {\<one>} \<or> K = G"
begin

text \<open>Simple groups have no proper non-trivial normal subgroups.\<close>

lemma proper_normal_subgroup_is_trivial:
  assumes K: "normal_subgroup K G (\<cdot>) \<one>" and proper: "K \<noteq> G"
  shows "K = {\<one>}"
  using normal_subgroup_eq_trivial_or_top[OF K] proper by blast

lemma nontrivial_normal_subgroup_is_top:
  assumes K: "normal_subgroup K G (\<cdot>) \<one>" and K_nontrivial: "K \<noteq> {\<one>}"
  shows "K = G"
  using normal_subgroup_eq_trivial_or_top[OF K] K_nontrivial by blast

end

text \<open>
  A simple factor group is the quotient associated with a normal subgroup whose
  factor group is simple.  Naming this local construction keeps the quotient
  operations attached to the existing @{locale normal_subgroup} interpretation.
\<close>

locale simple_factor_group =
  N: normal_subgroup K H "(\<cdot>)" \<one> +
  Q: Simple_Group N.Factor_Group N.quotient_composition "N.Class \<one>"
  for K and H and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

lemma factor_group_is_simple:
  "Simple_Group N.Factor_Group N.quotient_composition (N.Class \<one>)"
  by (rule Q.Simple_Group_axioms)

lemma factor_group_nontrivial:
  "N.Factor_Group \<noteq> {N.Class \<one>}"
  by (rule Q.nontrivial)

lemma proper:
  "K \<noteq> H"
  using N.Factor_Group_eq_singleton_iff Q.nontrivial by blast

end

text \<open>
  A composition series is a finite normal series whose successive factor groups
  are simple.  The indexed representation is inherited from @{locale normal_series}.
\<close>

locale composition_series = normal_series +
  assumes factor_simple: "\<And>i. i < n \<Longrightarrow> simple_factor_group (H i) (H (Suc i)) (\<cdot>) \<one>"

begin

lemma factor_simple_step:
  assumes i: "i < n"
  shows "simple_factor_group (H i) (H (Suc i)) (\<cdot>) \<one>"
  by (rule factor_simple[OF i])

lemma series_factor_simple:
  assumes i: "i < n"
  shows "Simple_Group (fst (series_factor i))
          (fst (snd (series_factor i))) (snd (snd (series_factor i)))"
  using factor_simple_step i series_factor_def simple_factor_group_def by fastforce

lemma series_factors_nth_simple:
  assumes i: "i < n"
  shows "Simple_Group (fst (series_factors ! i))
      (fst (snd (series_factors ! i))) (snd (snd (series_factors ! i)))"
  using series_factors_nth[OF i] series_factor_simple[OF i] by simp

lemma composition_step_strict:
  assumes i: "i < n"
  shows "H i \<noteq> H (Suc i)"
  using factor_simple_step i by (metis simple_factor_group.proper)

text \<open>Every prefix of a composition series is again a composition series.\<close>

lemma prefix_composition_series:
  assumes k: "k \<le> n"
  shows "composition_series (H k) (\<cdot>) \<one> H k"
proof (intro composition_series.intro composition_series_axioms.intro prefix_normal_series[OF k])
qed (use factor_simple_step k in auto)

text \<open>A composition series has positive length exactly when its group is nontrivial.\<close>

lemma zero_length_iff_trivial: "n = 0 \<longleftrightarrow> G = {\<one>}"
proof
  show "n = 0 \<Longrightarrow> G = {\<one>}"
    by (rule zero_length_implies_trivial)
next
  assume G_trivial: "G = {\<one>}"
  show "n = 0"
  proof (rule ccontr)
    assume n_nonzero: "n \<noteq> 0"
    interpret H1: Subgroup "H (Suc 0)" G "(\<cdot>)" \<one>
      using term_subgroup n_nonzero by auto
    have "H (Suc 0) \<subseteq> {\<one>}"
      using H1.subset G_trivial by simp
    then show False
      using bottom composition_step_strict n_nonzero by fastforce
  qed
qed

end

subsection \<open>Normal chains inside a simple factor\<close>

text \<open>
  The subgroup correspondence detects the bottom and top subgroups of a
  quotient without choosing representatives.  These two characterisations
  are the order-theoretic part of the correspondence needed below.
\<close>
context normal_subgroup_in_subgroup
begin

lemma Fract_H_K_eq_bottom_iff:
  "Fract_H_K = {K.Class \<one>} \<longleftrightarrow> H = K"
proof
  assume quotient: "Fract_H_K = {K.Class \<one>}"
  show "H = K"
  proof (rule equalityI)
    show "H \<subseteq> K"
    proof
      fix h
      assume h: "h \<in> H"
      have "K.Class h \<in> Fract_H_K" by (rule Class_H_closed[OF h])
      then have class_eq: "K.Class h = K.Class \<one>"
        using quotient by simp
      have "h \<in> K.Class h" by (rule K.Class_self[OF H.sub[OF h]])
      then show "h \<in> K"
        using class_eq K.Class_unit_normal_subgroup by simp
    qed
    show "K \<subseteq> H" by (rule K_contained)
  qed
next
  assume HK: "H = K"
  show "Fract_H_K = {K.Class \<one>}"
  proof (rule equalityI)
    show "Fract_H_K \<subseteq> {K.Class \<one>}"
    proof
      fix A
      assume "A \<in> Fract_H_K"
      then obtain h where h: "h \<in> H" and A: "A = K.Class h"
        by (rule Fract_H_K_memE)
      have hK: "h \<in> K" using h HK by simp
      have class_eq: "K.Class h = K.Class \<one>"
      proof (rule K.Class_eq)
        show "(h, \<one>) \<in> K.Congruence"
        proof (rule K.CongruenceI)
          show "h = \<one> \<cdot> h" by (rule K.left_unit[OF K.sub[OF hK], symmetric])
          show "h \<in> G" by (rule K.sub[OF hK])
          show "\<one> \<in> G" by (rule K.unit_closed)
          show "h \<in> K" by fact
        qed
      qed
      show "A \<in> {K.Class \<one>}" using A class_eq by simp
    qed
    show "{K.Class \<one>} \<subseteq> Fract_H_K"
      by (simp add: Fract_H_K_unit_closed)
  qed
qed

lemma Fract_H_K_eq_top_iff:
  "Fract_H_K = K.Factor_Group \<longleftrightarrow> H = G"
proof
  assume quotient: "Fract_H_K = K.Factor_Group"
  show "H = G"
  proof (rule equalityI)
    show "H \<subseteq> G" by (rule H.subset)
    show "G \<subseteq> H"
    proof
      fix g
      assume g: "g \<in> G"
      have "K.Class g \<in> K.Factor_Group"
        by (rule K.Class_in_Partition[OF g])
      then have "K.Class g \<in> Fract_H_K" using quotient by simp
      then have "K.Class g \<subseteq> H" by (rule Fract_H_K_into_subset_H)
      moreover have "g \<in> K.Class g" by (rule K.Class_self[OF g])
      ultimately show "g \<in> H" by blast
    qed
  qed
next
  assume HG: "H = G"
  show "Fract_H_K = K.Factor_Group"
  proof (rule equalityI)
    show "Fract_H_K \<subseteq> K.Factor_Group"
      by (rule Fract_H_K_subset)
    show "K.Factor_Group \<subseteq> Fract_H_K"
    proof
      fix A
      assume "A \<in> K.Factor_Group"
      then obtain g where g: "g \<in> G" and A: "A = K.Class g"
        using K.representant_exists by blast
      have "g \<in> H" using g HG by simp
      then show "A \<in> Fract_H_K" unfolding A by (rule Class_H_closed)
    qed
  qed
qed

end

text \<open>
  An intermediate subgroup that is normal in the numerator of a simple
  factor is necessarily one of the endpoints.  The proof passes to the
  quotient using the existing correspondence theorem and then reflects the
  two possible quotient subgroups back to the original carrier sets.
\<close>
lemma simple_factor_intermediate_normal:
  assumes factor: "simple_factor_group K H composition unit"
    and contained: "K \<subseteq> L"
    and normal: "normal_subgroup L H composition unit"
  shows "L = K \<or> L = H"
proof -
  interpret factor: simple_factor_group K H composition unit by fact
  interpret normal: normal_subgroup L H composition unit by fact
  have Subgroup: "subgroup_of_group L H composition unit"
    by (rule subgroup_of_groupI[OF
          normal.Subgroup_axioms factor.N.Group_axioms])
  interpret corr: normal_subgroup_in_subgroup K L H composition unit
  proof (rule normal_subgroup_in_subgroup.intro)
    show "normal_subgroup K H composition unit"
      by (rule factor.N.normal_subgroup_axioms)
    show "subgroup_of_group L H composition unit" by (rule Subgroup)
    show "normal_subgroup_in_subgroup_axioms K L"
      by (rule normal_subgroup_in_subgroup_axioms.intro[OF contained])
  qed
  have quotient_normal:
      "normal_subgroup corr.Fract_H_K factor.N.Factor_Group
        factor.N.quotient_composition (factor.N.Class unit)"
    by (rule iffD1[OF corr.normal_iff normal])
  have "corr.Fract_H_K = {factor.N.Class unit} \<or>
      corr.Fract_H_K = factor.N.Factor_Group"
    by (rule factor.Q.normal_subgroup_eq_trivial_or_top[OF quotient_normal])
  then show ?thesis
    using corr.Fract_H_K_eq_bottom_iff corr.Fract_H_K_eq_top_iff by blast
qed

definition normal_chain_factor_classes ::
    "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      'a set monoid_iso_class list"
  where
    "normal_chain_factor_classes C n composition unit =
      List.map
        (\<lambda>i. normal_factor_class (C i) (C (Suc i)) composition unit)
        [0..<n]"

definition reduced_normal_chain_factor_multiset ::
    "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      'a set monoid_iso_class multiset"
  where
    "reduced_normal_chain_factor_multiset C n composition unit =
      nontrivial_factor_multiset
        (normal_chain_factor_classes C n composition unit)"

lemma length_normal_chain_factor_classes:
  "length (normal_chain_factor_classes C n composition unit) = n"
  unfolding normal_chain_factor_classes_def by simp

text \<open>
  A finite normal chain between the endpoints of a simple factor has exactly
  one nontrivial factor.  Repetitions may occur on either side of that strict
  step, but filtering the canonical trivial class leaves the original factor
  class with multiplicity one.
\<close>
theorem simple_factor_chain_reduction:
  assumes chain: "normal_chain G composition unit C n"
    and factor: "simple_factor_group K H composition unit"
    and bottom: "C 0 = K"
    and top: "C n = H"
  shows "reduced_normal_chain_factor_multiset C n composition unit =
    {#normal_factor_class K H composition unit#}"
  using chain factor bottom top
proof (induction n arbitrary: C)
  case 0
  then show ?case by (metis simple_factor_group.proper)
next
  case (Suc n)
  interpret C: normal_chain G composition unit C "Suc n" by fact
  interpret factor: simple_factor_group K H composition unit by fact

  have last_normal: "normal_subgroup (C n) H composition unit"
    using C.normal_step[of n] Suc.prems(4) by simp
  have K_subset_last: "K \<subseteq> C n"
    using C.chain_mono[of 0 n] Suc.prems(3) by simp
  have last_cases: "C n = K \<or> C n = H"
    by (rule simple_factor_intermediate_normal[
          OF Suc.prems(2) K_subset_last last_normal])

  have factors_suc:
      "normal_chain_factor_classes C (Suc n) composition unit =
        normal_chain_factor_classes C n composition unit @
          [normal_factor_class (C n) (C (Suc n)) composition unit]"
    unfolding normal_chain_factor_classes_def by simp

  show ?case
  proof (rule disjE[OF last_cases])
    assume 1: "C n = K"
    have earlier_terms: "C i = K" if "i \<le> n" for i
    proof (rule equalityI)
      show "C i \<subseteq> K"
        using C.chain_mono[of i n] that 1 by simp
      show "K \<subseteq> C i"
        using C.chain_mono[of 0 i] that Suc.prems(3) by simp
    qed
    have earlier_trivial:
        "normal_factor_class (C i) (C (Suc i)) composition unit =
          trivial_monoid_iso_class" if "i < n" for i
    proof -
      have step: "normal_subgroup (C i) (C (Suc i)) composition unit"
        by (rule C.normal_step) (use that in simp)
      show ?thesis
        using earlier_terms[of i] earlier_terms[of "Suc i"] that
          normal_factor_class_eq_trivial_iff[OF step]
        by simp
    qed
    have prefix_classes:
        "normal_chain_factor_classes C n composition unit =
          List.map (\<lambda>_. trivial_monoid_iso_class) [0..<n]"
      unfolding normal_chain_factor_classes_def
      by (rule map_cong) (auto intro: earlier_trivial)
    have reduced_prefix:
        "nontrivial_factor_multiset
          (normal_chain_factor_classes C n composition unit) = {#}"
      unfolding prefix_classes nontrivial_factor_multiset_def
      by (induction n) simp_all
    have last_class:
        "normal_factor_class (C n) (C (Suc n)) composition unit =
          normal_factor_class K H composition unit"
      using 1 Suc.prems(4) by simp
    show ?thesis
      unfolding reduced_normal_chain_factor_multiset_def factors_suc
      using reduced_prefix last_class factor.proper
        normal_factor_class_eq_trivial_iff[OF factor.N.normal_subgroup_axioms]
      by simp
  next
    assume 2: "C n = H"
    have prefix: "normal_chain G composition unit C n"
      by (rule C.prefix_normal_chain) simp
    have reduced_prefix:
        "reduced_normal_chain_factor_multiset C n composition unit =
          {#normal_factor_class K H composition unit#}"
      by (rule Suc.IH[OF prefix Suc.prems(2) Suc.prems(3) 2])
    have last_trivial:
        "normal_factor_class (C n) (C (Suc n)) composition unit =
          trivial_monoid_iso_class"
      using 2 Suc.prems(4)
        normal_factor_class_eq_trivial_iff[OF C.normal_step[of n]] by simp
    show ?thesis
      using reduced_prefix last_trivial
      unfolding reduced_normal_chain_factor_multiset_def factors_suc
      by simp
  qed
qed

end

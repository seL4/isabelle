theory Simple_Factor_Chain
  imports Reduced_Schreier_Refinement Composition_Series
begin

section \<open>Normal chains inside a simple factor\<close>

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
      'a set group_iso_class list"
  where
    "normal_chain_factor_classes C n composition unit =
      List.map
        (\<lambda>i. normal_factor_class (C i) (C (Suc i)) composition unit)
        [0..<n]"

definition reduced_normal_chain_factor_multiset ::
    "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      'a set group_iso_class multiset"
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
          trivial_group_iso_class" if "i < n" for i
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
          List.map (\<lambda>_. trivial_group_iso_class) [0..<n]"
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
          trivial_group_iso_class"
      using 2 Suc.prems(4)
        normal_factor_class_eq_trivial_iff[OF C.normal_step[of n]] by simp
    show ?thesis
      using reduced_prefix last_trivial
      unfolding reduced_normal_chain_factor_multiset_def factors_suc
      by simp
  qed
qed

end

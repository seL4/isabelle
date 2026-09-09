theory Composition_Factors_Solvable
  imports Finite_Composition_Series Jordan_Hoelder_Uniqueness Solvable_Transfer
begin

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

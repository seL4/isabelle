theory Normal_Chain
  imports Composition_Factor_Classes
begin

section \<open>Finite relative normal chains\<close>

text \<open>
  A refinement of one step in a normal series starts at an intermediate
  subgroup rather than at the trivial subgroup.  The following locale records
  exactly the structure shared by such relative chains: finitely many
  subgroups of one ambient group, with each term normal in its successor.
  Endpoints are deliberately left unconstrained.
\<close>

definition normal_factor ::
    "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      ('a set set \<times> ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) \<times> 'a set)"
  where
    "normal_factor K H composition unit =
      (normal_subgroup.Factor_Group K H composition unit,
       Monoid_congruence.quotient_composition H composition
         (normal_subgroup.Congruence K H composition unit),
       Equivalence.Class H
         (normal_subgroup.Congruence K H composition unit) unit)"

definition normal_factor_class ::
    "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow>
      'a set group_iso_class"
  where
    "normal_factor_class K H composition unit =
      group_iso_class_of (group_structure (normal_factor K H composition unit))"

text \<open>
  A normal factor is a group whenever its denominator is normal in its
  numerator.  Equality of factor classes can therefore be discharged by an
  ordinary group isomorphism between the corresponding quotient triples.
\<close>
lemma normal_factor_group:
  assumes "normal_subgroup K H composition unit"
  shows "Group (fst (normal_factor K H composition unit))
      (fst (snd (normal_factor K H composition unit)))
      (snd (snd (normal_factor K H composition unit)))"
proof -
  interpret N: normal_subgroup K H composition unit by fact
  show ?thesis
    unfolding normal_factor_def
    using N.quotient.Group_axioms by simp
qed

lemma normal_factor_class_eq_iff:
  assumes KH: "normal_subgroup K H composition unit"
    and LM: "normal_subgroup L M composition unit"
  shows "normal_factor_class K H composition unit =
      normal_factor_class L M composition unit \<longleftrightarrow>
      normal_factor K H composition unit \<cong>\<^sub>G
        normal_factor L M composition unit"
  unfolding normal_factor_class_def
  by (rule group_iso_class_of_group_structure_eq_iff[OF
        normal_factor_group[OF KH] normal_factor_group[OF LM]])

text \<open>
  A normal factor is trivial precisely when its denominator and numerator
  coincide.  The quotient-level argument is proved once in
  \<open>Factor_Group_eq_singleton_iff\<close>; the carrier lemma below exposes it
  through the packaged factor triple, independently of the representative
  chosen for the trivial isomorphism class.
\<close>
lemma normal_factor_carrier_eq_singleton_iff:
  assumes N: "normal_subgroup K H composition unit"
  shows "fst (normal_factor K H composition unit) =
      {snd (snd (normal_factor K H composition unit))} \<longleftrightarrow> K = H"
proof -
  interpret N: normal_subgroup K H composition unit by fact
  show ?thesis
    unfolding normal_factor_def
    by (simp only: prod.sel) (rule N.Factor_Group_eq_singleton_iff)
qed

lemma normal_factor_class_eq_trivial_iff:
  assumes N: "normal_subgroup K H composition unit"
  shows "normal_factor_class K H composition unit =
      trivial_group_iso_class \<longleftrightarrow> K = H"
proof -
  have factor_group:
      "Group (fst (normal_factor K H composition unit))
        (fst (snd (normal_factor K H composition unit)))
        (snd (snd (normal_factor K H composition unit)))"
    by (rule normal_factor_group[OF N])
  have class_iff:
      "group_iso_class_of (group_structure
          (fst (normal_factor K H composition unit),
           fst (snd (normal_factor K H composition unit)),
           snd (snd (normal_factor K H composition unit)))) =
          trivial_group_iso_class \<longleftrightarrow>
      fst (normal_factor K H composition unit) =
        {snd (snd (normal_factor K H composition unit))}"
    by (rule group_iso_class_eq_trivial_iff[OF factor_group])
  show ?thesis
    unfolding normal_factor_class_def
    using class_iff normal_factor_carrier_eq_singleton_iff[OF N]
    by (simp add: surjective_pairing)
qed

locale normal_chain =
  G: Group G "(\<cdot>)" \<one>
  for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  fixes C :: "nat \<Rightarrow> 'a set" and n :: nat
  assumes term_subgroup:
      "\<And>i. i \<le> n \<Longrightarrow> Subgroup (C i) G (\<cdot>) \<one>"
    and normal_step:
      "\<And>i. i < n \<Longrightarrow> normal_subgroup (C i) (C (Suc i)) (\<cdot>) \<one>"
begin

lemma step_subset:
  assumes "i < n"
  shows "C i \<subseteq> C (Suc i)"
proof -
  interpret step: normal_subgroup "C i" "C (Suc i)" "(\<cdot>)" \<one>
    by (rule normal_step[OF assms])
  show ?thesis by (rule step.subset)
qed

lemma chain_mono:
  fixes i j :: nat
  assumes ij: "i \<le> j" and jn: "j \<le> n"
  shows "C i \<subseteq> C j"
  using ij
proof (induction rule: inc_induct)
  case base
  show "C j \<subseteq> C j" by simp
next
  case (step k)
  have k_lt_n: "k < n"
    by (rule less_le_trans[OF step(2) jn])
  show ?case
    by (rule subset_trans[OF step_subset[OF k_lt_n] step(3)])
qed

definition chain_factor_class :: "nat \<Rightarrow> 'a set group_iso_class"
  where
    "chain_factor_class i =
      normal_factor_class (C i) (C (Suc i)) (\<cdot>) \<one>"

lemma prefix_normal_chain:
  assumes "k \<le> n"
  shows "normal_chain G (\<cdot>) \<one> C k"
proof (intro normal_chain.intro)
  show "Group G (\<cdot>) \<one>" by (rule G.Group_axioms)
next
  show "normal_chain_axioms G (\<cdot>) \<one> C k"
  proof (rule normal_chain_axioms.intro)
    show "\<And>i. i \<le> k \<Longrightarrow> Subgroup (C i) G (\<cdot>) \<one>"
      by (meson assms le_trans term_subgroup)
    show "\<And>i. i < k \<Longrightarrow> normal_subgroup (C i) (C (Suc i)) (\<cdot>) \<one>"
      by (meson assms less_le_trans normal_step)
  qed
qed

end

sublocale normal_series \<subseteq> chain: normal_chain G "(\<cdot>)" \<one> H n
proof (rule normal_chain.intro)
  show "Group G (\<cdot>) \<one>" by (rule G.Group_axioms)
  show "normal_chain_axioms G (\<cdot>) \<one> H n"
  proof (rule normal_chain_axioms.intro)
    show "\<And>i. i \<le> n \<Longrightarrow> Subgroup (H i) G (\<cdot>) \<one>"
      by (rule term_subgroup)
    show "\<And>i. i < n \<Longrightarrow> normal_subgroup (H i) (H (Suc i)) (\<cdot>) \<one>"
      by (rule normal_step)
  qed
qed

context normal_series
begin

lemma series_factor_eq_normal_factor:
  "series_factor i = normal_factor (H i) (H (Suc i)) (\<cdot>) \<one>"
  unfolding series_factor_def normal_factor_def by rule

lemma series_factor_class_eq_normal_factor_class:
  "series_factor_class i =
    normal_factor_class (H i) (H (Suc i)) (\<cdot>) \<one>"
  unfolding series_factor_class_def normal_factor_class_def
  by (simp add: series_factor_eq_normal_factor)

end

end

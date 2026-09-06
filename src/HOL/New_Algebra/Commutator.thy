section \<open>Commutators and the Derived Subgroup\<close>

theory Commutator
  imports Sylow_Theorems
begin

text \<open>
  The commutator of two elements, the commutator subgroup of two subsets, and the
  derived (commutator) subgroup of a group.  These underlie the derived series and
  the notion of a solvable group.  (Custom notation is deferred; we use plain
  constant names while developing the theory.)
\<close>

context Group
begin

text \<open>The commutator of two elements.\<close>
definition commutator_elt :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "commutator_elt a b = a \<cdot> b \<cdot> inverse a \<cdot> inverse b"

text \<open>Membership rule for commutators.  Declared @{attribute simp} only: as an
  @{attribute intro} rule it back-chains on \<^emph>\<open>every\<close> carrier-membership goal
  (\<open>?x \<in> G\<close> via \<open>?x = commutator_elt ?a ?b\<close>), which interacts badly with large
  introduction-rule sets and can loop.\<close>
lemma commutator_elt_closed [simp]:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> commutator_elt a b \<in> G"
  unfolding commutator_elt_def by simp

text \<open>The commutator subgroup of two subsets of the carrier.\<close>
definition commutator_subgroup :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "commutator_subgroup H K = \<langle>{ commutator_elt h k | h k. h \<in> H \<and> k \<in> K }\<rangle>"

text \<open>The derived subgroup of the whole group.\<close>
definition derived :: "'a set"
  where "derived = commutator_subgroup G G"

lemma commutator_subgroup_is_subgroup:
  "Subgroup (commutator_subgroup H K) G (\<cdot>) \<one>"
  unfolding commutator_subgroup_def by (rule Gen_is_subgroup)

lemma commutator_subgroup_subset:
  "commutator_subgroup H K \<subseteq> G"
  unfolding commutator_subgroup_def by (rule Gen_subset_carrier)

lemma derived_is_subgroup: "Subgroup derived G (\<cdot>) \<one>"
  unfolding derived_def by (rule commutator_subgroup_is_subgroup)

lemma derived_subset: "derived \<subseteq> G"
  unfolding derived_def by (rule commutator_subgroup_subset)

text \<open>Generators of the commutator subgroup are commutators.\<close>
lemma commutator_gen_mem:
  "\<lbrakk> h \<in> H; k \<in> K; H \<subseteq> G; K \<subseteq> G \<rbrakk> \<Longrightarrow> commutator_elt h k \<in> commutator_subgroup H K"
    unfolding commutator_subgroup_def using Gen_incl by force

text \<open>Conjugation distributes over a commutator.\<close>
lemma conjugation_commutator:
  assumes "g \<in> G" "a \<in> G" "b \<in> G"
  shows "conjugation g (commutator_elt a b) = commutator_elt (conjugation g a) (conjugation g b)"
  using assms by (simp add: conjugation_hom commutator_elt_def flip: conjugation_inverse)

text \<open>The derived subgroup is normal.\<close>
lemma derived_normal: "normal_subgroup derived G (\<cdot>) \<one>"
proof -
  interpret D: Subgroup derived G "(\<cdot>)" \<one> by (rule derived_is_subgroup)
  interpret DG: subgroup_of_group derived G "(\<cdot>)" \<one>
    by (simp add: D.Subgroup_axioms Group_axioms subgroup_of_group_def)
  show ?thesis
  proof
    fix g k assume g: "g \<in> G" and k: "k \<in> derived"
    have ig: "inverse g \<in> G" using g by simp
    have conj_in: "conjugation (inverse g) x \<in> derived"
      if "x \<in> generate ({ commutator_elt a b | a b. a \<in> G \<and> b \<in> G } \<inter> G)" for x
      using that
    proof induction
      case unit then show ?case
        using conjugation_def by auto
    next
      case (incl x) 
      then obtain a b where xab: "x = commutator_elt a b" and ab: "a \<in> G" "b \<in> G" by auto
      have "conjugation (inverse g) x =
              commutator_elt (conjugation (inverse g) a) (conjugation (inverse g) b)"
        using ig ab xab by (simp add: conjugation_commutator)
      moreover have "conjugation (inverse g) a \<in> G" "conjugation (inverse g) b \<in> G"
        using ig ab by (auto simp: conjugation_closed)
      ultimately show ?case
        by (metis commutator_gen_mem derived_def set_eq_subset)
    next
      case (comp x y)
      have xy: "x \<in> G" "y \<in> G" using comp.hyps generate_subset_carrier by auto
      with conjugation_hom[OF xy] comp.IH D.sub_composition_closed
      show ?case by metis
    next
      case (inv x)
      have xG: "x \<in> G" using inv.hyps generate_subset_carrier by auto
      have "conjugation (inverse g) (inverse x) = inverse (conjugation (inverse g) x)"
        using conjugation_inverse[OF xG] .
      then show ?case using inv.IH D.submonoid_inverse_closed D.sub.invertible by simp
    qed
    have "inverse g \<cdot> k \<cdot> g = conjugation (inverse g) k"
      using g k derived_subset
      by (auto simp: conjugation_def associative invertible_inverse_inverse subsetD)
    moreover have "k \<in> generate ({ commutator_elt a b | a b. a \<in> G \<and> b \<in> G } \<inter> G)"
      using k unfolding derived_def commutator_subgroup_def Gen_def .
    ultimately show "inverse g \<cdot> k \<cdot> g \<in> derived"
      using conj_in by simp
  qed
qed

text \<open>The commutator subgroup is monotone in both arguments.\<close>
lemma commutator_subgroup_mono:
  assumes "A \<subseteq> A'" "B \<subseteq> B'"
  shows "commutator_subgroup A B \<subseteq> commutator_subgroup A' B'"
  unfolding commutator_subgroup_def Gen_def
  using assms by (intro generate_mono) blast

text \<open>A commutator computed inside a subgroup (with the restricted operation) equals the
  ambient commutator.  A locality property of @{const commutator_elt}.\<close>
lemma commutator_elt_subgroup_eq:
  assumes H: "Subgroup H G (\<cdot>) \<one>" and ab: "a \<in> H" "b \<in> H"
  shows "Group.commutator_elt H (\<cdot>) \<one> a b = commutator_elt a b"
proof -
  interpret S: Subgroup H G "(\<cdot>)" \<one> by (rule H)
  show ?thesis
    by (simp add: assms S.sub.commutator_elt_def commutator_elt_def)
  also have "\<dots> = commutator_elt a b" by (simp add: commutator_elt_def)
qed

text \<open>The commutator subgroup computed inside a subgroup is contained in the ambient one.\<close>
lemma commutator_subgroup_subgroup_subset:
  assumes H: "Subgroup H G (\<cdot>) \<one>" and AB: "A \<subseteq> H" "B \<subseteq> H"
  shows "Group.commutator_subgroup H (\<cdot>) \<one> A B \<subseteq> commutator_subgroup A B"
proof -
  interpret S: Subgroup H G "(\<cdot>)" \<one> by (rule H)
  have AG: "A \<subseteq> G" "B \<subseteq> G" using AB S.subset by auto
  have genset: "({ Group.commutator_elt H (\<cdot>) \<one> h k | h k. h \<in> A \<and> k \<in> B } \<inter> H)
                  \<subseteq> { commutator_elt h k | h k. h \<in> A \<and> k \<in> B }"
    using assms commutator_elt_subgroup_eq by blast
  have absorb: "{ commutator_elt h k | h k. h \<in> A \<and> k \<in> B } \<inter> G
                  = { commutator_elt h k | h k. h \<in> A \<and> k \<in> B }"
    using AG by (force simp: commutator_elt_closed)
  have "Group.commutator_subgroup H (\<cdot>) \<one> A B
          = Group.generate H (\<cdot>) \<one> ({ Group.commutator_elt H (\<cdot>) \<one> h k | h k. h \<in> A \<and> k \<in> B } \<inter> H)"
    by (simp add: S.sub.commutator_subgroup_def S.sub.Gen_def)
  also have "\<dots> \<subseteq> generate ({ Group.commutator_elt H (\<cdot>) \<one> h k | h k. h \<in> A \<and> k \<in> B } \<inter> H)"
    by (rule generate_subgroup_subset[OF H])
  also have "\<dots> \<subseteq> generate { commutator_elt h k | h k. h \<in> A \<and> k \<in> B }"
    using genset by (rule generate_mono)
  also have "\<dots> = commutator_subgroup A B"
    by (simp add: commutator_subgroup_def Gen_def absorb)
  finally show ?thesis .
qed

text \<open>Generation is \<^emph>\<open>absolute\<close> for a subgroup: for @{term "S \<subseteq> H"}, the subgroup generated by
  @{term S} inside @{term G} coincides with the one generated inside @{term H} (the reverse
  inclusion to @{thm [source] generate_subgroup_subset}).  The @{term H}-generated set is a
  subgroup of @{term G} containing @{term S}, so the minimal such (@{const generate}) is contained
  in it.\<close>
lemma generate_subgroup_superset:
  assumes H: "Subgroup H G (\<cdot>) \<one>" and S: "S \<subseteq> H"
  shows "generate S \<subseteq> Group.generate H (\<cdot>) \<one> S"
proof (rule generate_minimal)
  interpret S': Subgroup H G "(\<cdot>)" \<one> by (rule H)
  have "Subgroup (Group.generate H (\<cdot>) \<one> S) H (\<cdot>) \<one>" by (rule S'.sub.generate_is_subgroup)
  then show "Subgroup (Group.generate H (\<cdot>) \<one> S) G (\<cdot>) \<one>"
    using H by (rule subgroup_transitive)
  have "S \<subseteq> Group.generate H (\<cdot>) \<one> S" using S S'.sub.generate_incl by auto
  then show "S \<inter> G \<subseteq> Group.generate H (\<cdot>) \<one> S" by blast
qed

text \<open>The commutator subgroup of subsets of @{term H} computed in @{term G} is contained in the one
  computed in @{term H} (the reverse of @{thm [source] commutator_subgroup_subgroup_subset}; the two
  are in fact equal).\<close>
lemma commutator_subgroup_subset_subgroup:
  assumes H: "Subgroup H G (\<cdot>) \<one>" and AB: "A \<subseteq> H" "B \<subseteq> H"
  shows "commutator_subgroup A B \<subseteq> Group.commutator_subgroup H (\<cdot>) \<one> A B"
proof -
  interpret S: Subgroup H G "(\<cdot>)" \<one> by (rule H)
  have AG: "A \<subseteq> G" "B \<subseteq> G" using AB S.subset by auto
  \<comment> \<open>The commutator generators computed in @{term H} coincide with the ambient ones and lie in @{term H}.\<close>
  have absorb: "{ commutator_elt h k | h k. h \<in> A \<and> k \<in> B } \<inter> G
                = { commutator_elt h k | h k. h \<in> A \<and> k \<in> B }"
    using AG by (force simp: commutator_elt_closed)
  have "commutator_subgroup A B = generate ({ commutator_elt h k | h k. h \<in> A \<and> k \<in> B })"
    by (simp add: commutator_subgroup_def Gen_def absorb)
  also have "\<dots> \<subseteq> generate ({ Group.commutator_elt H (\<cdot>) \<one> h k | h k. h \<in> A \<and> k \<in> B } \<inter> H)"
    using assms by (intro generate_mono) (force simp: commutator_elt_def S.sub.commutator_elt_def)
  also have "\<dots> \<subseteq> Group.generate H (\<cdot>) \<one> ({ Group.commutator_elt H (\<cdot>) \<one> h k | h k. h \<in> A \<and> k \<in> B } \<inter> H)"
    by (rule generate_subgroup_superset[OF H]) auto
  also have "\<dots> = Group.commutator_subgroup H (\<cdot>) \<one> A B"
    by (simp add: S.sub.commutator_subgroup_def S.sub.Gen_def)
  finally show ?thesis .
qed

end (* Group *)

end

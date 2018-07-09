(*  Title:      HOL/Algebra/Group_Action.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Group_Action
imports Bij Coset Congruence
begin

section \<open>Group Actions\<close>

locale group_action =
  fixes G (structure) and E and \<phi>
  assumes group_hom: "group_hom G (BijGroup E) \<phi>"

definition
  orbit :: "[_, 'a \<Rightarrow> 'b \<Rightarrow> 'b, 'b] \<Rightarrow> 'b set"
  where "orbit G \<phi> x = {(\<phi> g) x | g. g \<in> carrier G}"

definition
  orbits :: "[_, 'b set, 'a \<Rightarrow> 'b \<Rightarrow> 'b] \<Rightarrow> ('b set) set"
  where "orbits G E \<phi> = {orbit G \<phi> x | x. x \<in> E}"

definition
  stabilizer :: "[_, 'a \<Rightarrow> 'b \<Rightarrow> 'b, 'b] \<Rightarrow> 'a set"
  where "stabilizer G \<phi> x = {g \<in> carrier G. (\<phi> g) x = x}"

definition
  invariants :: "['b set, 'a \<Rightarrow> 'b \<Rightarrow> 'b, 'a] \<Rightarrow> 'b set"
  where "invariants E \<phi> g = {x \<in> E. (\<phi> g) x = x}"

definition
  normalizer :: "[_, 'a set] \<Rightarrow> 'a set"
  where "normalizer G H =
         stabilizer G (\<lambda>g. \<lambda>H \<in> {H. H \<subseteq> carrier G}. g <#\<^bsub>G\<^esub> H #>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> g)) H"

locale faithful_action = group_action +
  assumes faithful: "inj_on \<phi> (carrier G)"

locale transitive_action = group_action +
  assumes unique_orbit: "\<lbrakk> x \<in> E; y \<in> E \<rbrakk> \<Longrightarrow> \<exists>g \<in> carrier G. (\<phi> g) x = y"



subsection \<open>Prelimineries\<close>

text \<open>Some simple lemmas to make group action's properties more explicit\<close>

lemma (in group_action) id_eq_one: "(\<lambda>x \<in> E. x) = \<phi> \<one>"
  by (metis BijGroup_def group_hom group_hom.hom_one select_convs(2))

lemma (in group_action) bij_prop0:
  "\<And> g. g \<in> carrier G \<Longrightarrow> (\<phi> g) \<in> Bij E"
  by (metis BijGroup_def group_hom group_hom.hom_closed partial_object.select_convs(1))

lemma (in group_action) surj_prop:
  "\<And> g. g \<in> carrier G \<Longrightarrow> (\<phi> g) ` E = E"
  using bij_prop0 by (simp add: Bij_def bij_betw_def)

lemma (in group_action) inj_prop:
  "\<And> g. g \<in> carrier G \<Longrightarrow> inj_on (\<phi> g) E"
  using bij_prop0 by (simp add: Bij_def bij_betw_def)

lemma (in group_action) bij_prop1:
  "\<And> g y. \<lbrakk> g \<in> carrier G; y \<in> E \<rbrakk> \<Longrightarrow>  \<exists>!x \<in> E. (\<phi> g) x = y"
proof -
  fix g y assume "g \<in> carrier G" "y \<in> E"
  hence "\<exists>x \<in> E. (\<phi> g) x = y"
    using surj_prop by force
  moreover have "\<And> x1 x2. \<lbrakk> x1 \<in> E; x2 \<in> E \<rbrakk> \<Longrightarrow> (\<phi> g) x1 = (\<phi> g) x2 \<Longrightarrow> x1 = x2"
    using inj_prop by (meson \<open>g \<in> carrier G\<close> inj_on_eq_iff)
  ultimately show "\<exists>!x \<in> E. (\<phi> g) x = y"
    by blast
qed

lemma (in group_action) composition_rule:
  assumes "x \<in> E" "g1 \<in> carrier G" "g2 \<in> carrier G"
  shows "\<phi> (g1 \<otimes> g2) x = (\<phi> g1) (\<phi> g2 x)"
proof -
  have "\<phi> (g1 \<otimes> g2) x = ((\<phi> g1) \<otimes>\<^bsub>BijGroup E\<^esub> (\<phi> g2)) x"
    using assms(2) assms(3) group_hom group_hom.hom_mult by fastforce
  also have " ... = (compose E (\<phi> g1) (\<phi> g2)) x"
    unfolding BijGroup_def by (simp add: assms bij_prop0)
  finally show "\<phi> (g1 \<otimes> g2) x = (\<phi> g1) (\<phi> g2 x)"
    by (simp add: assms(1) compose_eq)
qed

lemma (in group_action) element_image:
  assumes "g \<in> carrier G" and "x \<in> E" and "(\<phi> g) x = y"
  shows "y \<in> E"
  using surj_prop assms by blast



subsection \<open>Orbits\<close>

text\<open>We prove here that orbits form an equivalence relation\<close>

lemma (in group_action) orbit_sym_aux:
  assumes "g \<in> carrier G"
    and "x \<in> E"
    and "(\<phi> g) x = y"
  shows "(\<phi> (inv g)) y = x"
proof -
  interpret group G
    using group_hom group_hom.axioms(1) by auto
  have "y \<in> E"
    using element_image assms by simp
  have "inv g \<in> carrier G"
    by (simp add: assms(1))

  have "(\<phi> (inv g)) y = (\<phi> (inv g)) ((\<phi> g) x)"
    using assms(3) by simp
  also have " ... = compose E (\<phi> (inv g)) (\<phi> g) x"
    by (simp add: assms(2) compose_eq)
  also have " ... = ((\<phi> (inv g)) \<otimes>\<^bsub>BijGroup E\<^esub> (\<phi> g)) x"
    by (simp add: BijGroup_def assms(1) bij_prop0)
  also have " ... = (\<phi> ((inv g) \<otimes> g)) x"
    by (metis \<open>inv g \<in> carrier G\<close> assms(1) group_hom group_hom.hom_mult)
  finally show "(\<phi> (inv g)) y = x"
    by (metis assms(1) assms(2) id_eq_one l_inv restrict_apply)
qed

lemma (in group_action) orbit_refl:
  "x \<in> E \<Longrightarrow> x \<in> orbit G \<phi> x"
proof -
  assume "x \<in> E" hence "(\<phi> \<one>) x = x"
    using id_eq_one by (metis restrict_apply')
  thus "x \<in> orbit G \<phi> x" unfolding orbit_def
    using group.is_monoid group_hom group_hom.axioms(1) by force 
qed

lemma (in group_action) orbit_sym:
  assumes "x \<in> E" and "y \<in> E" and "y \<in> orbit G \<phi> x"
  shows "x \<in> orbit G \<phi> y"
proof -
  have "\<exists> g \<in> carrier G. (\<phi> g) x = y"
    using assms by (auto simp: orbit_def)
  then obtain g where g: "g \<in> carrier G \<and> (\<phi> g) x = y" by blast
  hence "(\<phi> (inv g)) y = x"
    using orbit_sym_aux by (simp add: assms(1))
  thus ?thesis
    using g group_hom group_hom.axioms(1) orbit_def by fastforce 
qed

lemma (in group_action) orbit_trans:
  assumes "x \<in> E" "y \<in> E" "z \<in> E"
    and "y \<in> orbit G \<phi> x" "z \<in> orbit G \<phi> y" 
  shows "z \<in> orbit G \<phi> x"
proof -
  interpret group G
    using group_hom group_hom.axioms(1) by auto
  obtain g1 where g1: "g1 \<in> carrier G \<and> (\<phi> g1) x = y" 
    using assms by (auto simp: orbit_def)
  obtain g2 where g2: "g2 \<in> carrier G \<and> (\<phi> g2) y = z" 
    using assms by (auto simp: orbit_def)  
  have "(\<phi> (g2 \<otimes> g1)) x = ((\<phi> g2) \<otimes>\<^bsub>BijGroup E\<^esub> (\<phi> g1)) x"
    using g1 g2 group_hom group_hom.hom_mult by fastforce
  also have " ... = (\<phi> g2) ((\<phi> g1) x)"
    using composition_rule assms(1) calculation g1 g2 by auto
  finally have "(\<phi> (g2 \<otimes> g1)) x = z"
    by (simp add: g1 g2)
  thus ?thesis
    using g1 g2 orbit_def by force 
qed

lemma (in group_action) orbits_as_classes:
  "classes\<^bsub>\<lparr> carrier = E, eq = \<lambda>x. \<lambda>y. y \<in> orbit G \<phi> x \<rparr>\<^esub> = orbits G E \<phi>"
  unfolding eq_classes_def eq_class_of_def orbits_def orbit_def 
  using element_image by auto

theorem (in group_action) orbit_partition:
  "partition E (orbits G E \<phi>)"
proof -
  have "equivalence \<lparr> carrier = E, eq = \<lambda>x. \<lambda>y. y \<in> orbit G \<phi> x \<rparr>"
  unfolding equivalence_def apply simp
  using orbit_refl orbit_sym orbit_trans by blast
  thus ?thesis using equivalence.partition_from_equivalence orbits_as_classes by fastforce
qed

corollary (in group_action) orbits_coverture:
  "\<Union> (orbits G E \<phi>) = E"
  using partition.partition_coverture[OF orbit_partition] by simp

corollary (in group_action) disjoint_union:
  assumes "orb1 \<in> (orbits G E \<phi>)" "orb2 \<in> (orbits G E \<phi>)"
  shows "(orb1 = orb2) \<or> (orb1 \<inter> orb2) = {}"
  using partition.disjoint_union[OF orbit_partition] assms by auto

corollary (in group_action) disjoint_sum:
  assumes "finite E"
  shows "(\<Sum>orb\<in>(orbits G E \<phi>). \<Sum>x\<in>orb. f x) = (\<Sum>x\<in>E. f x)"
  using partition.disjoint_sum[OF orbit_partition] assms by auto


subsubsection \<open>Transitive Actions\<close>

text \<open>Transitive actions have only one orbit\<close>

lemma (in transitive_action) all_equivalent:
  "\<lbrakk> x \<in> E; y \<in> E \<rbrakk> \<Longrightarrow> x .=\<^bsub>\<lparr>carrier = E, eq = \<lambda>x y. y \<in> orbit G \<phi> x\<rparr>\<^esub> y"
proof -
  assume "x \<in> E" "y \<in> E"
  hence "\<exists> g \<in> carrier G. (\<phi> g) x = y"
    using unique_orbit  by blast
  hence "y \<in> orbit G \<phi> x"
    using orbit_def by fastforce
  thus "x .=\<^bsub>\<lparr>carrier = E, eq = \<lambda>x y. y \<in> orbit G \<phi> x\<rparr>\<^esub> y" by simp
qed

proposition (in transitive_action) one_orbit:
  assumes "E \<noteq> {}"
  shows "card (orbits G E \<phi>) = 1"
proof -
  have "orbits G E \<phi> \<noteq> {}"
    using assms orbits_coverture by auto
  moreover have "\<And> orb1 orb2. \<lbrakk> orb1 \<in> (orbits G E \<phi>); orb2 \<in> (orbits G E \<phi>) \<rbrakk> \<Longrightarrow> orb1 = orb2"
  proof -
    fix orb1 orb2 assume orb1: "orb1 \<in> (orbits G E \<phi>)"
                     and orb2: "orb2 \<in> (orbits G E \<phi>)"
    then obtain x y where x: "orb1 = orbit G \<phi> x" and x_E: "x \<in> E" 
                      and y: "orb2 = orbit G \<phi> y" and y_E: "y \<in> E"
      unfolding orbits_def by blast
    hence "x \<in> orbit G \<phi> y" using all_equivalent by auto
    hence "orb1 \<inter> orb2 \<noteq> {}" using x y x_E orbit_refl by auto
    thus "orb1 = orb2" using disjoint_union[of orb1 orb2] orb1 orb2 by auto
  qed
  ultimately show "card (orbits G E \<phi>) = 1"
    by (meson is_singletonI' is_singleton_altdef)
qed



subsection \<open>Stabilizers\<close>

text \<open>We show that stabilizers are subgroups from the acting group\<close>

lemma (in group_action) stabilizer_subset:
  "stabilizer G \<phi> x \<subseteq> carrier G"
  by (metis (no_types, lifting) mem_Collect_eq stabilizer_def subsetI)

lemma (in group_action) stabilizer_m_closed:
  assumes "x \<in> E" "g1 \<in> (stabilizer G \<phi> x)" "g2 \<in> (stabilizer G \<phi> x)"
  shows "(g1 \<otimes> g2) \<in> (stabilizer G \<phi> x)"
proof -
  interpret group G
    using group_hom group_hom.axioms(1) by auto
  
  have "\<phi> g1 x = x"
    using assms stabilizer_def by fastforce
  moreover have "\<phi> g2 x = x"
    using assms stabilizer_def by fastforce
  moreover have g1: "g1 \<in> carrier G"
    by (meson assms contra_subsetD stabilizer_subset)
  moreover have g2: "g2 \<in> carrier G"
    by (meson assms contra_subsetD stabilizer_subset)
  ultimately have "\<phi> (g1 \<otimes> g2) x = x"
    using composition_rule assms by simp

  thus ?thesis
    by (simp add: g1 g2 stabilizer_def) 
qed

lemma (in group_action) stabilizer_one_closed:
  assumes "x \<in> E"
  shows "\<one> \<in> (stabilizer G \<phi> x)"
proof -
  have "\<phi> \<one> x = x"
    by (metis assms id_eq_one restrict_apply')
  thus ?thesis
    using group_def group_hom group_hom.axioms(1) stabilizer_def by fastforce
qed

lemma (in group_action) stabilizer_m_inv_closed:
  assumes "x \<in> E" "g \<in> (stabilizer G \<phi> x)"
  shows "(inv g) \<in> (stabilizer G \<phi> x)"
proof -
  interpret group G
    using group_hom group_hom.axioms(1) by auto

  have "\<phi> g x = x"
    using assms(2) stabilizer_def by fastforce
  moreover have g: "g \<in> carrier G"
    using assms(2) stabilizer_subset by blast
  moreover have inv_g: "inv g \<in> carrier G"
    by (simp add: g)
  ultimately have "\<phi> (inv g) x = x"
    using assms(1) orbit_sym_aux by blast

  thus ?thesis by (simp add: inv_g stabilizer_def) 
qed

theorem (in group_action) stabilizer_subgroup:
  assumes "x \<in> E"
  shows "subgroup (stabilizer G \<phi> x) G"
  unfolding subgroup_def
  using stabilizer_subset stabilizer_m_closed stabilizer_one_closed
        stabilizer_m_inv_closed assms by simp



subsection \<open>The Orbit-Stabilizer Theorem\<close>

text \<open>In this subsection, we prove the Orbit-Stabilizer theorem.
      Our approach is to show the existence of a bijection between
      "rcosets (stabilizer G phi x)" and "orbit G phi x". Then we use
      Lagrange's theorem to find the cardinal of the first set.\<close>

subsubsection \<open>Rcosets - Supporting Lemmas\<close>

corollary (in group_action) stab_rcosets_not_empty:
  assumes "x \<in> E" "R \<in> rcosets (stabilizer G \<phi> x)"
  shows "R \<noteq> {}"
  using subgroup.rcosets_non_empty[OF stabilizer_subgroup[OF assms(1)] assms(2)] by simp

corollary (in group_action) diff_stabilizes:
  assumes "x \<in> E" "R \<in> rcosets (stabilizer G \<phi> x)"
  shows "\<And>g1 g2. \<lbrakk> g1 \<in> R; g2 \<in> R \<rbrakk> \<Longrightarrow> g1 \<otimes> (inv g2) \<in> stabilizer G \<phi> x"
  using group.diff_neutralizes[of G "stabilizer G \<phi> x" R] stabilizer_subgroup[OF assms(1)]
        assms(2) group_hom group_hom.axioms(1) by blast


subsubsection \<open>Bijection Between Rcosets and an Orbit - Definition and Supporting Lemmas\<close>

(* This definition could be easier if lcosets were available, and it's indeed a considerable
   modification at Coset theory, since we could derive it easily from the definition of rcosets
   following the same idea we use here: f: rcosets \<rightarrow> lcosets, s.t. f R = (\<lambda>g. inv g) ` R
   is a bijection. *)

definition
  orb_stab_fun :: "[_, ('a \<Rightarrow> 'b \<Rightarrow> 'b), 'a set, 'b] \<Rightarrow> 'b"
  where "orb_stab_fun G \<phi> R x = (\<phi> (inv\<^bsub>G\<^esub> (SOME h. h \<in> R))) x"

lemma (in group_action) orbit_stab_fun_is_well_defined0:
  assumes "x \<in> E" "R \<in> rcosets (stabilizer G \<phi> x)"
  shows "\<And>g1 g2. \<lbrakk> g1 \<in> R; g2 \<in> R \<rbrakk> \<Longrightarrow> (\<phi> (inv g1)) x = (\<phi> (inv g2)) x"
proof -
  fix g1 g2 assume g1: "g1 \<in> R" and g2: "g2 \<in> R"
  have R_carr: "R \<subseteq> carrier G"
    using subgroup.rcosets_carrier[OF stabilizer_subgroup[OF assms(1)]]
          assms(2) group_hom group_hom.axioms(1) by auto
  from R_carr have g1_carr: "g1 \<in> carrier G" using g1 by blast
  from R_carr have g2_carr: "g2 \<in> carrier G" using g2 by blast

  have "g1 \<otimes> (inv g2) \<in> stabilizer G \<phi> x"
    using diff_stabilizes[of x R g1 g2] assms g1 g2 by blast
  hence "\<phi> (g1 \<otimes> (inv g2)) x = x"
    by (simp add: stabilizer_def)
  hence "(\<phi> (inv g1)) x = (\<phi> (inv g1)) (\<phi> (g1 \<otimes> (inv g2)) x)" by simp
  also have " ... = \<phi> ((inv g1) \<otimes> (g1 \<otimes> (inv g2))) x"
    using group_def assms(1) composition_rule g1_carr g2_carr
          group_hom group_hom.axioms(1) monoid.m_closed by fastforce
  also have " ... = \<phi> (((inv g1) \<otimes> g1) \<otimes> (inv g2)) x"
    using group_def g1_carr g2_carr group_hom group_hom.axioms(1) monoid.m_assoc by fastforce
  finally show "(\<phi> (inv g1)) x = (\<phi> (inv g2)) x"
    using group_def g1_carr g2_carr group.l_inv group_hom group_hom.axioms(1) by fastforce
qed

lemma (in group_action) orbit_stab_fun_is_well_defined1:
  assumes "x \<in> E" "R \<in> rcosets (stabilizer G \<phi> x)"
  shows "\<And>g. g \<in> R \<Longrightarrow> (\<phi> (inv (SOME h. h \<in> R))) x = (\<phi> (inv g)) x"
  by (meson assms orbit_stab_fun_is_well_defined0 someI_ex)

lemma (in group_action) orbit_stab_fun_is_inj:
  assumes "x \<in> E"
    and "R1 \<in> rcosets (stabilizer G \<phi> x)"
    and "R2 \<in> rcosets (stabilizer G \<phi> x)"
    and "\<phi> (inv (SOME h. h \<in> R1)) x = \<phi> (inv (SOME h. h \<in> R2)) x"
  shows "R1 = R2"
proof -
  have "(\<exists>g1. g1 \<in> R1) \<and> (\<exists>g2. g2 \<in> R2)"
    using assms(1-3) stab_rcosets_not_empty by auto
  then obtain g1 g2 where g1: "g1 \<in> R1" and g2: "g2 \<in> R2" by blast
  hence g12_carr: "g1 \<in> carrier G \<and> g2 \<in> carrier G"
    using subgroup.rcosets_carrier assms(1-3) group_hom
          group_hom.axioms(1) stabilizer_subgroup by blast

  then obtain r1 r2 where r1: "r1 \<in> carrier G" "R1 = (stabilizer G \<phi> x) #> r1"
                      and r2: "r2 \<in> carrier G" "R2 = (stabilizer G \<phi> x) #> r2"
    using assms(1-3) unfolding RCOSETS_def by blast
  then obtain s1 s2 where s1: "s1 \<in> (stabilizer G \<phi> x)" "g1 = s1 \<otimes> r1"
                      and s2: "s2 \<in> (stabilizer G \<phi> x)" "g2 = s2 \<otimes> r2"
    using g1 g2 unfolding r_coset_def by blast

  have "\<phi> (inv g1) x = \<phi> (inv (SOME h. h \<in> R1)) x"
    using orbit_stab_fun_is_well_defined1[OF assms(1) assms(2) g1] by simp
  also have " ... = \<phi> (inv (SOME h. h \<in> R2)) x"
    using assms(4) by simp
  finally have "\<phi> (inv g1) x = \<phi> (inv g2) x"
    using orbit_stab_fun_is_well_defined1[OF assms(1) assms(3) g2] by simp

  hence "\<phi> g2 (\<phi> (inv g1) x) = \<phi> g2 (\<phi> (inv g2) x)" by simp
  also have " ... = \<phi> (g2 \<otimes> (inv g2)) x"
    using assms(1) composition_rule g12_carr group_hom group_hom.axioms(1) by fastforce
  finally have "\<phi> g2 (\<phi> (inv g1) x) = x"
    using g12_carr assms(1) group.r_inv group_hom group_hom.axioms(1)
          id_eq_one restrict_apply by metis
  hence "\<phi> (g2 \<otimes> (inv g1)) x = x"
    using assms(1) composition_rule g12_carr group_hom group_hom.axioms(1) by fastforce
  hence "g2 \<otimes> (inv g1) \<in> (stabilizer G \<phi> x)"
    using g12_carr group.subgroup_self group_hom group_hom.axioms(1)
          mem_Collect_eq stabilizer_def subgroup_def by (metis (mono_tags, lifting))
  then obtain s where s: "s \<in> (stabilizer G \<phi> x)" "s = g2 \<otimes> (inv g1)" by blast

  let ?h = "s \<otimes> g1"
  have "?h = s \<otimes> (s1 \<otimes> r1)" by (simp add: s1)
  hence "?h = (s \<otimes> s1) \<otimes> r1"
    using stabilizer_subgroup[OF assms(1)] group_def group_hom
          group_hom.axioms(1) monoid.m_assoc r1 s s1 subgroup.mem_carrier by fastforce
  hence inR1: "?h \<in> (stabilizer G \<phi> x) #> r1" unfolding r_coset_def
    using stabilizer_subgroup[OF assms(1)] assms(1) s s1 stabilizer_m_closed by auto

  have "?h = g2" using s stabilizer_subgroup[OF assms(1)] g12_carr group.inv_solve_right
                       group_hom group_hom.axioms(1) subgroup.mem_carrier by metis
  hence inR2: "?h \<in> (stabilizer G \<phi> x) #> r2"
    using g2 r2 by blast

  have "R1 \<inter> R2 \<noteq> {}" using inR1 inR2 r1 r2 by blast
  thus ?thesis using stabilizer_subgroup group.rcos_disjoint[of G "stabilizer G \<phi> x" R1 R2]
                     assms group_hom group_hom.axioms(1) by blast
qed

lemma (in group_action) orbit_stab_fun_is_surj:
  assumes "x \<in> E" "y \<in> orbit G \<phi> x"
  shows "\<exists>R \<in> rcosets (stabilizer G \<phi> x). \<phi> (inv (SOME h. h \<in> R)) x = y"
proof -
  have "\<exists>g \<in> carrier G. (\<phi> g) x = y"
    using assms(2) unfolding orbit_def by blast
  then obtain g where g: "g \<in> carrier G \<and> (\<phi> g) x = y" by blast
  
  let ?R = "(stabilizer G \<phi> x) #> (inv g)"
  have R: "?R \<in> rcosets (stabilizer G \<phi> x)"
    unfolding RCOSETS_def using g group_hom group_hom.axioms(1) by fastforce
  moreover have "\<one> \<otimes> (inv g) \<in> ?R"
    unfolding r_coset_def using assms(1) stabilizer_one_closed by auto
  ultimately have "\<phi> (inv (SOME h. h \<in> ?R)) x = \<phi> (inv (\<one> \<otimes> (inv g))) x"
    using orbit_stab_fun_is_well_defined1[OF assms(1)] by simp
  also have " ... = (\<phi> g) x"
    using group_def g group_hom group_hom.axioms(1) monoid.l_one by fastforce
  finally have "\<phi> (inv (SOME h. h \<in> ?R)) x = y"
    using g by simp
  thus ?thesis using R by blast 
qed

proposition (in group_action) orbit_stab_fun_is_bij:
  assumes "x \<in> E"
  shows "bij_betw (\<lambda>R. (\<phi> (inv (SOME h. h \<in> R))) x) (rcosets (stabilizer G \<phi> x)) (orbit G \<phi> x)"
  unfolding bij_betw_def
proof
  show "inj_on (\<lambda>R. \<phi> (inv (SOME h. h \<in> R)) x) (rcosets stabilizer G \<phi> x)"
    using orbit_stab_fun_is_inj[OF assms(1)] by (simp add: inj_on_def)
next
  have "\<And>R. R \<in> (rcosets stabilizer G \<phi> x) \<Longrightarrow> \<phi> (inv (SOME h. h \<in> R)) x \<in> orbit G \<phi> x "
  proof -
    fix R assume R: "R \<in> (rcosets stabilizer G \<phi> x)"
    then obtain g where g: "g \<in> R"
      using assms stab_rcosets_not_empty by auto
    hence "\<phi> (inv (SOME h. h \<in> R)) x = \<phi> (inv g) x"
      using R  assms orbit_stab_fun_is_well_defined1 by blast
    thus "\<phi> (inv (SOME h. h \<in> R)) x \<in> orbit G \<phi> x" unfolding orbit_def
      using subgroup.rcosets_carrier group_hom group_hom.axioms(1)
            g R assms stabilizer_subgroup by fastforce
  qed
  moreover have "orbit G \<phi> x \<subseteq> (\<lambda>R. \<phi> (inv (SOME h. h \<in> R)) x) ` (rcosets stabilizer G \<phi> x)"
    using assms orbit_stab_fun_is_surj by fastforce
  ultimately show "(\<lambda>R. \<phi> (inv (SOME h. h \<in> R)) x) ` (rcosets stabilizer G \<phi> x) = orbit G \<phi> x "
    using assms set_eq_subset by blast
qed


subsubsection \<open>The Theorem\<close>

theorem (in group_action) orbit_stabilizer_theorem:
  assumes "x \<in> E"
  shows "card (orbit G \<phi> x) * card (stabilizer G \<phi> x) = order G"
proof -
  have "card (rcosets stabilizer G \<phi> x) = card (orbit G \<phi> x)"
    using orbit_stab_fun_is_bij[OF assms(1)] bij_betw_same_card by blast
  moreover have "card (rcosets stabilizer G \<phi> x) * card (stabilizer G \<phi> x) = order G"
    using stabilizer_subgroup assms group.lagrange group_hom group_hom.axioms(1) by blast
  ultimately show ?thesis by auto
qed



subsection \<open>The Burnside's Lemma\<close>

subsubsection \<open>Sums and Cardinals\<close>

lemma card_as_sums:
  assumes "A = {x \<in> B. P x}" "finite B"
  shows "card A = (\<Sum>x\<in>B. (if P x then 1 else 0))"
proof -
  have "A \<subseteq> B" using assms(1) by blast
  have "card A = (\<Sum>x\<in>A. 1)" by simp
  also have " ... = (\<Sum>x\<in>A. (if P x then 1 else 0))"
    by (simp add: assms(1))
  also have " ... = (\<Sum>x\<in>A. (if P x then 1 else 0)) + (\<Sum>x\<in>(B - A). (if P x then 1 else 0))"
    using assms(1) by auto
  finally show "card A = (\<Sum>x\<in>B. (if P x then 1 else 0))"
    using \<open>A \<subseteq> B\<close> add.commute assms(2) sum.subset_diff by metis
qed

lemma sum_invertion:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> (\<Sum>x\<in>A. \<Sum>y\<in>B. f x y) = (\<Sum>y\<in>B. \<Sum>x\<in>A. f x y)"
proof (induct set: finite)
  case empty thus ?case by simp
next
  case (insert x A')
  have "(\<Sum>x\<in>insert x A'. \<Sum>y\<in>B. f x y) = (\<Sum>y\<in>B. f x y) + (\<Sum>x\<in>A'. \<Sum>y\<in>B. f x y)"
    by (simp add: insert.hyps)
  also have " ... = (\<Sum>y\<in>B. f x y) + (\<Sum>y\<in>B. \<Sum>x\<in>A'. f x y)"
    using insert.hyps by (simp add: insert.prems)
  also have " ... = (\<Sum>y\<in>B. (f x y) + (\<Sum>x\<in>A'. f x y))"
    by (simp add: sum.distrib)
  finally have "(\<Sum>x\<in>insert x A'. \<Sum>y\<in>B. f x y) = (\<Sum>y\<in>B. \<Sum>x\<in>insert x A'. f x y)"
    using sum.swap by blast
  thus ?case by simp
qed

lemma (in group_action) card_stablizer_sum:
  assumes "finite (carrier G)" "orb \<in> (orbits G E \<phi>)"
  shows "(\<Sum>x \<in> orb. card (stabilizer G \<phi> x)) = order G"
proof -
  obtain x where x:"x \<in> E" and orb:"orb = orbit G \<phi> x"
    using assms(2) unfolding orbits_def by blast
  have "\<And>y. y \<in> orb \<Longrightarrow> card (stabilizer G \<phi> x) = card (stabilizer G \<phi> y)"
  proof -
    fix y assume "y \<in> orb"
    hence y: "y \<in> E \<and> y \<in> orbit G \<phi> x"
      using x orb assms(2) orbits_coverture by auto 
    hence same_orbit: "(orbit G \<phi> x) = (orbit G \<phi> y)"
      using disjoint_union[of "orbit G \<phi> x" "orbit G \<phi> y"] orbit_refl x
      unfolding orbits_def by auto
    have "card (orbit G \<phi> x) * card (stabilizer G \<phi> x) =
          card (orbit G \<phi> y) * card (stabilizer G \<phi> y)"
      using y assms(1) x orbit_stabilizer_theorem by simp
    hence "card (orbit G \<phi> x) * card (stabilizer G \<phi> x) =
           card (orbit G \<phi> x) * card (stabilizer G \<phi> y)" using same_orbit by simp
    moreover have "orbit G \<phi> x \<noteq> {} \<and> finite (orbit G \<phi> x)"
      using y orbit_def[of G \<phi> x] assms(1) by auto
    hence "card (orbit G \<phi> x) > 0"
      by (simp add: card_gt_0_iff)
    ultimately show "card (stabilizer G \<phi> x) = card (stabilizer G \<phi> y)" by auto
  qed
  hence "(\<Sum>x \<in> orb. card (stabilizer G \<phi> x)) = (\<Sum>y \<in> orb. card (stabilizer G \<phi> x))" by auto
  also have " ... = card (stabilizer G \<phi> x) * (\<Sum>y \<in> orb. 1)" by simp
  also have " ... = card (stabilizer G \<phi> x) * card (orbit G \<phi> x)"
    using orb by auto
  finally show "(\<Sum>x \<in> orb. card (stabilizer G \<phi> x)) = order G"
    by (metis mult.commute orbit_stabilizer_theorem x)
qed


subsubsection \<open>The Lemma\<close>

theorem (in group_action) burnside:
  assumes "finite (carrier G)" "finite E"
  shows "card (orbits G E \<phi>) * order G = (\<Sum>g \<in> carrier G. card(invariants E \<phi> g))"
proof -
  have "(\<Sum>g \<in> carrier G. card(invariants E \<phi> g)) =
        (\<Sum>g \<in> carrier G. \<Sum>x \<in> E. (if (\<phi> g) x = x then 1 else 0))"
    by (simp add: assms(2) card_as_sums invariants_def)
  also have " ... = (\<Sum>x \<in> E. \<Sum>g \<in> carrier G. (if (\<phi> g) x = x then 1 else 0))"
    using sum_invertion[where ?f = "\<lambda> g x. (if (\<phi> g) x = x then 1 else 0)"] assms by auto
  also have " ... = (\<Sum>x \<in> E. card (stabilizer G \<phi> x))"
    by (simp add: assms(1) card_as_sums stabilizer_def)
  also have " ... = (\<Sum>orbit \<in> (orbits G E \<phi>). \<Sum>x \<in> orbit. card (stabilizer G \<phi> x))"
    using disjoint_sum orbits_coverture assms(2) by metis
  also have " ... = (\<Sum>orbit \<in> (orbits G E \<phi>). order G)"
    by (simp add: assms(1) card_stablizer_sum)
  finally have "(\<Sum>g \<in> carrier G. card(invariants E \<phi> g)) = card (orbits G E \<phi>) * order G" by simp
  thus ?thesis by simp
qed



subsection \<open>Action by Conjugation\<close>


subsubsection \<open>Action Over Itself\<close>

text \<open>A Group Acts by Conjugation Over Itself\<close>

lemma (in group) conjugation_is_inj:
  assumes "g \<in> carrier G" "h1 \<in> carrier G" "h2 \<in> carrier G"
    and "g \<otimes> h1 \<otimes> (inv g) = g \<otimes> h2 \<otimes> (inv g)"
    shows "h1 = h2"
  using assms by auto

lemma (in group) conjugation_is_surj:
  assumes "g \<in> carrier G" "h \<in> carrier G"
  shows "g \<otimes> ((inv g) \<otimes> h \<otimes> g) \<otimes> (inv g) = h"
  using assms m_assoc inv_closed inv_inv m_closed monoid_axioms r_inv r_one
  by metis

lemma (in group) conjugation_is_bij:
  assumes "g \<in> carrier G"
  shows "bij_betw (\<lambda>h \<in> carrier G. g \<otimes> h \<otimes> (inv g)) (carrier G) (carrier G)"
         (is "bij_betw ?\<phi> (carrier G) (carrier G)")
  unfolding bij_betw_def
proof
  show "inj_on ?\<phi> (carrier G)"
    using conjugation_is_inj by (simp add: assms inj_on_def) 
next
  have S: "\<And> h. h \<in> carrier G \<Longrightarrow> (inv g) \<otimes> h \<otimes> g \<in> carrier G"
    using assms by blast
  have "\<And> h. h \<in> carrier G \<Longrightarrow> ?\<phi> ((inv g) \<otimes> h \<otimes> g) = h"
    using assms by (simp add: conjugation_is_surj)
  hence "carrier G \<subseteq> ?\<phi> ` carrier G"
    using S image_iff by fastforce
  moreover have "\<And> h. h \<in> carrier G \<Longrightarrow> ?\<phi> h \<in> carrier G"
    using assms by simp
  hence "?\<phi> ` carrier G \<subseteq> carrier G" by blast
  ultimately show "?\<phi> ` carrier G = carrier G" by blast
qed

lemma(in group) conjugation_is_hom:
  "(\<lambda>g. \<lambda>h \<in> carrier G. g \<otimes> h \<otimes> inv g) \<in> hom G (BijGroup (carrier G))"
  unfolding hom_def
proof -
  let ?\<psi> = "\<lambda>g. \<lambda>h. g \<otimes> h \<otimes> inv g"
  let ?\<phi> = "\<lambda>g. restrict (?\<psi> g) (carrier G)"

  (* First, we prove that ?\<phi>: G \<rightarrow> Bij(G) is well defined *)
  have Step0: "\<And> g. g \<in> carrier G \<Longrightarrow> (?\<phi> g) \<in> Bij (carrier G)"
    using Bij_def conjugation_is_bij by fastforce
  hence Step1: "?\<phi>: carrier G \<rightarrow> carrier (BijGroup (carrier G))"
    unfolding BijGroup_def by simp

  (* Second, we prove that ?\<phi> is a homomorphism *)
  have "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
                  (\<And> h. h \<in> carrier G \<Longrightarrow> ?\<psi> (g1 \<otimes> g2) h = (?\<phi> g1) ((?\<phi> g2) h))"
  proof -
    fix g1 g2 h assume g1: "g1 \<in> carrier G" and g2: "g2 \<in> carrier G" and h: "h \<in> carrier G"
    have "inv (g1 \<otimes> g2) = (inv g2) \<otimes> (inv g1)"
      using g1 g2 by (simp add: inv_mult_group)
    thus "?\<psi> (g1 \<otimes> g2) h  = (?\<phi> g1) ((?\<phi> g2) h)"
      by (simp add: g1 g2 h m_assoc)
  qed
  hence "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
         (\<lambda> h \<in> carrier G. ?\<psi> (g1 \<otimes> g2) h) = (\<lambda> h \<in> carrier G. (?\<phi> g1) ((?\<phi> g2) h))" by auto
  hence Step2: "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
                ?\<phi> (g1 \<otimes> g2) = (?\<phi> g1) \<otimes>\<^bsub>BijGroup (carrier G)\<^esub> (?\<phi> g2)"
    unfolding BijGroup_def by (simp add: Step0 compose_def)

  (* Finally, we combine both results to prove the lemma *)
  thus "?\<phi> \<in> {h: carrier G \<rightarrow> carrier (BijGroup (carrier G)).
              (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes> y) = h x \<otimes>\<^bsub>BijGroup (carrier G)\<^esub> h y)}"
    using Step1 Step2 by auto
qed

theorem (in group) action_by_conjugation:
  "group_action G (carrier G) (\<lambda>g. (\<lambda>h \<in> carrier G. g \<otimes> h \<otimes> (inv g)))"
  unfolding group_action_def group_hom_def using conjugation_is_hom
  by (simp add: group_BijGroup group_hom_axioms.intro is_group)


subsubsection \<open>Action Over The Set of Subgroups\<close>

text \<open>A Group Acts by Conjugation Over The Set of Subgroups\<close>

lemma (in group) subgroup_conjugation_is_inj_aux:
  assumes "g \<in> carrier G" "H1 \<subseteq> carrier G" "H2 \<subseteq> carrier G"
    and "g <# H1 #> (inv g) = g <# H2 #> (inv g)"
    shows "H1 \<subseteq> H2"
proof
  fix h1 assume h1: "h1 \<in> H1"
  hence "g \<otimes> h1 \<otimes> (inv g) \<in> g <# H1 #> (inv g)"
    unfolding l_coset_def r_coset_def using assms by blast
  hence "g \<otimes> h1 \<otimes> (inv g) \<in> g <# H2 #> (inv g)"
    using assms by auto
  hence "\<exists>h2 \<in> H2. g \<otimes> h1 \<otimes> (inv g) = g \<otimes> h2 \<otimes> (inv g)"
      unfolding l_coset_def r_coset_def by blast
  then obtain h2 where "h2 \<in> H2 \<and> g \<otimes> h1 \<otimes> (inv g) = g \<otimes> h2 \<otimes> (inv g)" by blast
  thus "h1 \<in> H2"
    using assms conjugation_is_inj h1 by blast
qed

lemma (in group) subgroup_conjugation_is_inj:
  assumes "g \<in> carrier G" "H1 \<subseteq> carrier G" "H2 \<subseteq> carrier G"
    and "g <# H1 #> (inv g) = g <# H2 #> (inv g)"
    shows "H1 = H2"
  using subgroup_conjugation_is_inj_aux assms set_eq_subset by metis

lemma (in group) subgroup_conjugation_is_surj0:
  assumes "g \<in> carrier G" "H \<subseteq> carrier G"
  shows "g <# ((inv g) <# H #> g) #> (inv g) = H"
  using coset_assoc assms coset_mult_assoc l_coset_subset_G lcos_m_assoc
  by (simp add: lcos_mult_one)

lemma (in group) subgroup_conjugation_is_surj1:
  assumes "g \<in> carrier G" "subgroup H G"
  shows "subgroup ((inv g) <# H #> g) G"
proof
  show "\<one> \<in> inv g <# H #> g"
  proof -
    have "\<one> \<in> H" by (simp add: assms(2) subgroup.one_closed)
    hence "inv g \<otimes> \<one> \<otimes> g \<in> inv g <# H #> g"
      unfolding l_coset_def r_coset_def by blast
    thus "\<one> \<in> inv g <# H #> g" using assms by simp
  qed
next
  show "inv g <# H #> g \<subseteq> carrier G"
  proof
    fix x assume "x \<in> inv g <# H #> g"
    hence "\<exists>h \<in> H. x = (inv g) \<otimes> h \<otimes> g"
      unfolding r_coset_def l_coset_def by blast
    hence "\<exists>h \<in> (carrier G). x = (inv g) \<otimes> h \<otimes> g"
      by (meson assms subgroup.mem_carrier)
    thus "x \<in> carrier G" using assms by blast
  qed
next
  show " \<And> x y. \<lbrakk> x \<in> inv g <# H #> g; y \<in> inv g <# H #> g \<rbrakk> \<Longrightarrow> x \<otimes> y \<in> inv g <# H #> g"
  proof -
    fix x y assume "x \<in> inv g <# H #> g"  "y \<in> inv g <# H #> g"
    then obtain h1 h2 where h12: "h1 \<in> H" "h2 \<in> H" and "x = (inv g) \<otimes> h1 \<otimes> g \<and> y = (inv g) \<otimes> h2 \<otimes> g"
      unfolding l_coset_def r_coset_def by blast
    hence "x \<otimes> y = ((inv g) \<otimes> h1 \<otimes> g) \<otimes> ((inv g) \<otimes> h2 \<otimes> g)" by blast
    also have "\<dots> = ((inv g) \<otimes> h1 \<otimes> (g \<otimes> inv g) \<otimes> h2 \<otimes> g)"
      using h12 assms inv_closed  m_assoc m_closed subgroup.mem_carrier [OF \<open>subgroup H G\<close>] by presburger 
    also have "\<dots> = ((inv g) \<otimes> (h1 \<otimes> h2) \<otimes> g)"
      by (simp add: h12 assms m_assoc subgroup.mem_carrier [OF \<open>subgroup H G\<close>])
    finally have "\<exists> h \<in> H. x \<otimes> y = (inv g) \<otimes> h \<otimes> g"
      by (meson assms(2) h12 subgroup_def)
    thus "x \<otimes> y \<in> inv g <# H #> g"
      unfolding l_coset_def r_coset_def by blast
  qed
next
  show "\<And>x. x \<in> inv g <# H #> g \<Longrightarrow> inv x \<in> inv g <# H #> g"
  proof -
    fix x assume "x \<in> inv g <# H #> g"
    hence "\<exists>h \<in> H. x = (inv g) \<otimes> h \<otimes> g"
      unfolding r_coset_def l_coset_def by blast
    then obtain h where h: "h \<in> H \<and> x = (inv g) \<otimes> h \<otimes> g" by blast
    hence "x \<otimes> (inv g) \<otimes> (inv h) \<otimes> g = \<one>"
      using assms m_assoc monoid_axioms by (simp add: subgroup.mem_carrier)
    hence "inv x = (inv g) \<otimes> (inv h) \<otimes> g"
      using assms h inv_mult_group m_assoc monoid_axioms by (simp add: subgroup.mem_carrier)
    moreover have "inv h \<in> H"
      by (simp add: assms h subgroup.m_inv_closed)
    ultimately show "inv x \<in> inv g <# H #> g" unfolding r_coset_def l_coset_def by blast
  qed
qed

lemma (in group) subgroup_conjugation_is_surj2:
  assumes "g \<in> carrier G" "subgroup H G"
  shows "subgroup (g <# H #> (inv g)) G"
  using subgroup_conjugation_is_surj1 by (metis assms inv_closed inv_inv)

lemma (in group) subgroup_conjugation_is_bij:
  assumes "g \<in> carrier G"
  shows "bij_betw (\<lambda>H \<in> {H. subgroup H G}. g <# H #> (inv g)) {H. subgroup H G} {H. subgroup H G}"
         (is "bij_betw ?\<phi> {H. subgroup H G} {H. subgroup H G}")
  unfolding bij_betw_def
proof
  show "inj_on ?\<phi> {H. subgroup H G}"
    using subgroup_conjugation_is_inj assms inj_on_def subgroup.subset
    by (metis (mono_tags, lifting) inj_on_restrict_eq mem_Collect_eq)
next
  have "\<And>H. H \<in> {H. subgroup H G} \<Longrightarrow> ?\<phi> ((inv g) <# H #> g) = H"
    by (simp add: assms subgroup.subset subgroup_conjugation_is_surj0
                  subgroup_conjugation_is_surj1 is_group)
  hence "\<And>H. H \<in> {H. subgroup H G} \<Longrightarrow> \<exists>H' \<in> {H. subgroup H G}. ?\<phi> H' = H"
    using assms subgroup_conjugation_is_surj1 by fastforce
  thus "?\<phi> ` {H. subgroup H G} = {H. subgroup H G}"
    using subgroup_conjugation_is_surj2 assms by auto
qed

lemma (in group) subgroup_conjugation_is_hom:
  "(\<lambda>g. \<lambda>H \<in> {H. subgroup H G}. g <# H #> (inv g)) \<in> hom G (BijGroup {H. subgroup H G})"
  unfolding hom_def
proof -
  (* We follow the exact same structure of conjugation_is_hom's proof *)
  let ?\<psi> = "\<lambda>g. \<lambda>H. g <# H #> (inv g)"
  let ?\<phi> = "\<lambda>g. restrict (?\<psi> g) {H. subgroup H G}"

  have Step0: "\<And> g. g \<in> carrier G \<Longrightarrow> (?\<phi> g) \<in> Bij {H. subgroup H G}"
    using Bij_def subgroup_conjugation_is_bij by fastforce
  hence Step1: "?\<phi>: carrier G \<rightarrow> carrier (BijGroup {H. subgroup H G})"
    unfolding BijGroup_def by simp

  have "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
                  (\<And> H. H \<in> {H. subgroup H G} \<Longrightarrow> ?\<psi> (g1 \<otimes> g2) H = (?\<phi> g1) ((?\<phi> g2) H))"
  proof -
    fix g1 g2 H assume g1: "g1 \<in> carrier G" and g2: "g2 \<in> carrier G" and H': "H \<in> {H. subgroup H G}"
    hence H: "subgroup H G" by simp
    have "(?\<phi> g1) ((?\<phi> g2) H) = g1 <# (g2 <# H #> (inv g2)) #> (inv g1)"
      by (simp add: H g2 subgroup_conjugation_is_surj2)
    also have " ... = g1 <# (g2 <# H) #> ((inv g2) \<otimes> (inv g1))"
      by (simp add: H coset_mult_assoc g1 g2 group.coset_assoc
                    is_group l_coset_subset_G subgroup.subset)
    also have " ... = g1 <# (g2 <# H) #> inv (g1 \<otimes> g2)"
      using g1 g2 by (simp add: inv_mult_group)
    finally have "(?\<phi> g1) ((?\<phi> g2) H) = ?\<psi> (g1 \<otimes> g2) H"
      by (simp add: H g1 g2 lcos_m_assoc subgroup.subset)
    thus "?\<psi> (g1 \<otimes> g2) H = (?\<phi> g1) ((?\<phi> g2) H)" by auto
  qed
  hence "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
         (\<lambda>H \<in> {H. subgroup H G}. ?\<psi> (g1 \<otimes> g2) H) = (\<lambda>H \<in> {H. subgroup H G}. (?\<phi> g1) ((?\<phi> g2) H))"
    by (meson restrict_ext)
  hence Step2: "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
                ?\<phi> (g1 \<otimes> g2) = (?\<phi> g1) \<otimes>\<^bsub>BijGroup {H. subgroup H G}\<^esub> (?\<phi> g2)"
    unfolding BijGroup_def by (simp add: Step0 compose_def)

  show "?\<phi> \<in> {h: carrier G \<rightarrow> carrier (BijGroup {H. subgroup H G}).
              \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. h (x \<otimes> y) = h x \<otimes>\<^bsub>BijGroup {H. subgroup H G}\<^esub> h y}"
    using Step1 Step2 by auto
qed

theorem (in group) action_by_conjugation_on_subgroups_set:
  "group_action G {H. subgroup H G} (\<lambda>g. \<lambda>H \<in> {H. subgroup H G}. g <# H #> (inv g))"
  unfolding group_action_def group_hom_def using subgroup_conjugation_is_hom
  by (simp add: group_BijGroup group_hom_axioms.intro is_group)


subsubsection \<open>Action Over The Power Set\<close>

text \<open>A Group Acts by Conjugation Over The Power Set\<close>

lemma (in group) subset_conjugation_is_bij:
  assumes "g \<in> carrier G"
  shows "bij_betw (\<lambda>H \<in> {H. H \<subseteq> carrier G}. g <# H #> (inv g)) {H. H \<subseteq> carrier G} {H. H \<subseteq> carrier G}"
         (is "bij_betw ?\<phi> {H. H \<subseteq> carrier G} {H. H \<subseteq> carrier G}")
  unfolding bij_betw_def
proof
  show "inj_on ?\<phi> {H. H \<subseteq> carrier G}"
    using subgroup_conjugation_is_inj assms inj_on_def
    by (metis (mono_tags, lifting) inj_on_restrict_eq mem_Collect_eq)
next
  have "\<And>H. H \<in> {H. H \<subseteq> carrier G} \<Longrightarrow> ?\<phi> ((inv g) <# H #> g) = H"
    by (simp add: assms l_coset_subset_G r_coset_subset_G subgroup_conjugation_is_surj0)
  hence "\<And>H. H \<in> {H. H \<subseteq> carrier G} \<Longrightarrow> \<exists>H' \<in> {H. H \<subseteq> carrier G}. ?\<phi> H' = H"
    by (metis assms l_coset_subset_G mem_Collect_eq r_coset_subset_G subgroup_def subgroup_self)
  hence "{H. H \<subseteq> carrier G} \<subseteq> ?\<phi> ` {H. H \<subseteq> carrier G}" by blast
  moreover have "?\<phi> ` {H. H \<subseteq> carrier G} \<subseteq> {H. H \<subseteq> carrier G}"
    by clarsimp (meson assms contra_subsetD inv_closed l_coset_subset_G r_coset_subset_G)
  ultimately show "?\<phi> ` {H. H \<subseteq> carrier G} = {H. H \<subseteq> carrier G}" by simp
qed

lemma (in group) subset_conjugation_is_hom:
  "(\<lambda>g. \<lambda>H \<in> {H. H \<subseteq> carrier G}. g <# H #> (inv g)) \<in> hom G (BijGroup {H. H \<subseteq> carrier G})"
  unfolding hom_def
proof -
  (* We follow the exact same structure of conjugation_is_hom's proof *)
  let ?\<psi> = "\<lambda>g. \<lambda>H. g <# H #> (inv g)"
  let ?\<phi> = "\<lambda>g. restrict (?\<psi> g) {H. H \<subseteq> carrier G}"

  have Step0: "\<And> g. g \<in> carrier G \<Longrightarrow> (?\<phi> g) \<in> Bij {H. H \<subseteq> carrier G}"
    using Bij_def subset_conjugation_is_bij by fastforce
  hence Step1: "?\<phi>: carrier G \<rightarrow> carrier (BijGroup {H. H \<subseteq> carrier G})"
    unfolding BijGroup_def by simp

  have "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
                  (\<And> H. H \<in> {H. H \<subseteq> carrier G} \<Longrightarrow> ?\<psi> (g1 \<otimes> g2) H = (?\<phi> g1) ((?\<phi> g2) H))"
  proof -
    fix g1 g2 H assume g1: "g1 \<in> carrier G" and g2: "g2 \<in> carrier G" and H: "H \<in> {H. H \<subseteq> carrier G}"
    hence "(?\<phi> g1) ((?\<phi> g2) H) = g1 <# (g2 <# H #> (inv g2)) #> (inv g1)"
      using l_coset_subset_G r_coset_subset_G by auto
    also have " ... = g1 <# (g2 <# H) #> ((inv g2) \<otimes> (inv g1))"
      using H coset_assoc coset_mult_assoc g1 g2 l_coset_subset_G by auto
    also have " ... = g1 <# (g2 <# H) #> inv (g1 \<otimes> g2)"
      using g1 g2 by (simp add: inv_mult_group)
    finally have "(?\<phi> g1) ((?\<phi> g2) H) = ?\<psi> (g1 \<otimes> g2) H"
      using H g1 g2 lcos_m_assoc by force
    thus "?\<psi> (g1 \<otimes> g2) H = (?\<phi> g1) ((?\<phi> g2) H)" by auto
  qed
  hence "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
         (\<lambda>H \<in> {H. H \<subseteq> carrier G}. ?\<psi> (g1 \<otimes> g2) H) = (\<lambda>H \<in> {H. H \<subseteq> carrier G}. (?\<phi> g1) ((?\<phi> g2) H))"
    by (meson restrict_ext)
  hence Step2: "\<And> g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow>
                ?\<phi> (g1 \<otimes> g2) = (?\<phi> g1) \<otimes>\<^bsub>BijGroup {H. H \<subseteq> carrier G}\<^esub> (?\<phi> g2)"
    unfolding BijGroup_def by (simp add: Step0 compose_def)

  show "?\<phi> \<in> {h: carrier G \<rightarrow> carrier (BijGroup {H. H \<subseteq> carrier G}).
              \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. h (x \<otimes> y) = h x \<otimes>\<^bsub>BijGroup {H. H \<subseteq> carrier G}\<^esub> h y}"
    using Step1 Step2 by auto
qed

theorem (in group) action_by_conjugation_on_power_set:
  "group_action G {H. H \<subseteq> carrier G} (\<lambda>g. \<lambda>H \<in> {H. H \<subseteq> carrier G}. g <# H #> (inv g))"
  unfolding group_action_def group_hom_def using subset_conjugation_is_hom
  by (simp add: group_BijGroup group_hom_axioms.intro is_group)

corollary (in group) normalizer_imp_subgroup:
  assumes "H \<subseteq> carrier G"
  shows "subgroup (normalizer G H) G"
  unfolding normalizer_def
  using group_action.stabilizer_subgroup[OF action_by_conjugation_on_power_set] assms by auto


subsection \<open>Subgroup of an Acting Group\<close>

text \<open>A Subgroup of an Acting Group Induces an Action\<close>

lemma (in group_action) induced_homomorphism:
  assumes "subgroup H G"
  shows "\<phi> \<in> hom (G \<lparr>carrier := H\<rparr>) (BijGroup E)"
  unfolding hom_def apply simp
proof -
  have S0: "H \<subseteq> carrier G" by (meson assms subgroup_def)
  hence "\<phi>: H \<rightarrow> carrier (BijGroup E)"
    by (simp add: BijGroup_def bij_prop0 subset_eq)
  thus "\<phi>: H \<rightarrow> carrier (BijGroup E) \<and> (\<forall>x \<in> H. \<forall>y \<in> H. \<phi> (x \<otimes> y) = \<phi> x \<otimes>\<^bsub>BijGroup E\<^esub> \<phi> y)"
    by (simp add: S0  group_hom group_hom.hom_mult set_rev_mp)
qed

theorem (in group_action) induced_action:
  assumes "subgroup H G"
  shows "group_action (G \<lparr>carrier := H\<rparr>) E \<phi>"
  unfolding group_action_def group_hom_def
  using induced_homomorphism assms group.subgroup_imp_group group_BijGroup
        group_hom group_hom.axioms(1) group_hom_axioms_def by blast

end

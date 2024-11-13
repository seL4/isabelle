(*  Title:      The Second Isomorphism Theorem for Groups
    Author:     Jakob von Raumer, Karlsruhe Institute of Technology
    Maintainer: Jakob von Raumer <jakob.raumer@student.kit.edu>
*)

theory SndIsomorphismGrp
imports Coset
begin

section \<open>The Second Isomorphism Theorem for Groups\<close>

text \<open>This theory provides a proof of the second isomorphism theorems for groups. 
The theorems consist of several facts about normal subgroups.\<close>

text \<open>The first lemma states that whenever we have a subgroup @{term S} and
a normal subgroup @{term H} of a group @{term G}, their intersection is normal
in @{term G}\<close>

locale second_isomorphism_grp = normal +
  fixes S:: "'a set"
  assumes subgrpS: "subgroup S G"

context second_isomorphism_grp
begin

interpretation groupS: group "G\<lparr>carrier := S\<rparr>"
  using subgrpS 
  by (metis subgroup_imp_group)

lemma normal_subgrp_intersection_normal:
  shows "S \<inter> H \<lhd> (G\<lparr>carrier := S\<rparr>)"
proof(auto simp: groupS.normal_inv_iff)
  from subgrpS is_subgroup have "\<And>x. x \<in> {S, H} \<Longrightarrow> subgroup x G" by auto
  hence "subgroup (\<Inter> {S, H}) G" using subgroups_Inter by blast
  hence "subgroup (S \<inter> H) G" by auto
  moreover have "S \<inter> H \<subseteq> S" by simp
  ultimately show "subgroup (S \<inter> H) (G\<lparr>carrier := S\<rparr>)"
    by (simp add: subgroup_incl subgrpS)
next
  fix g h
  assume g: "g \<in> S" and hH: "h \<in> H" and hS: "h \<in> S" 
  from g hH subgrpS show "g \<otimes> h \<otimes> inv\<^bsub>G\<lparr>carrier := S\<rparr>\<^esub> g \<in> H" 
    by (metis inv_op_closed2 subgroup.mem_carrier m_inv_consistent)
  from g hS subgrpS show "g \<otimes> h \<otimes> inv\<^bsub>G\<lparr>carrier := S\<rparr>\<^esub> g \<in> S" 
    by (metis subgroup.m_closed subgroup.m_inv_closed m_inv_consistent)
qed

lemma normal_set_mult_subgroup:
  shows "subgroup (H <#> S) G"
proof(rule subgroupI)
  show "H <#> S \<subseteq> carrier G" 
    by (metis setmult_subset_G subgroup.subset subgrpS subset)
next
  have "\<one> \<in> H" "\<one> \<in> S" 
    using is_subgroup subgrpS subgroup.one_closed by auto
  hence "\<one> \<otimes> \<one> \<in> H <#> S" 
    unfolding set_mult_def by blast
  thus "H <#> S \<noteq> {}" by auto
next
  fix g
  assume g: "g \<in> H <#> S"
  then obtain h s where h: "h \<in> H" and s: "s \<in> S" and ghs: "g = h \<otimes> s" unfolding set_mult_def 
    by auto
  hence "s \<in> carrier G" by (metis subgroup.mem_carrier subgrpS)
  with h ghs obtain h' where h': "h' \<in> H" and "g = s \<otimes> h'" 
    using coset_eq unfolding r_coset_def l_coset_def by auto
  with s have "inv g = (inv h') \<otimes> (inv s)" 
    by (metis inv_mult_group mem_carrier subgroup.mem_carrier subgrpS)
  moreover from h' s subgrpS have "inv h' \<in> H" "inv s \<in> S" 
    using subgroup.m_inv_closed m_inv_closed by auto
  ultimately show "inv g \<in> H <#> S" 
    unfolding set_mult_def by auto
next
  fix g g'
  assume g: "g \<in> H <#> S" and h: "g' \<in> H <#> S"
  then obtain h h' s s' where hh'ss': "h \<in> H" "h' \<in> H" "s \<in> S" "s' \<in> S" and "g = h \<otimes> s" and "g' = h' \<otimes> s'" 
    unfolding set_mult_def by auto
  hence "g \<otimes> g' = (h \<otimes> s) \<otimes> (h' \<otimes> s')" by metis
  also from hh'ss' have inG: "h \<in> carrier G" "h' \<in> carrier G" "s \<in> carrier G" "s' \<in> carrier G" 
    using subgrpS mem_carrier subgroup.mem_carrier by force+
  hence "(h \<otimes> s) \<otimes> (h' \<otimes> s') = h \<otimes> (s \<otimes> h') \<otimes> s'" 
    using m_assoc by auto
  also from hh'ss' inG obtain h'' where h'': "h'' \<in> H" and "s \<otimes> h' = h'' \<otimes> s"
    using coset_eq unfolding r_coset_def l_coset_def 
    by fastforce
  hence "h \<otimes> (s \<otimes> h') \<otimes> s' = h \<otimes> (h'' \<otimes> s) \<otimes> s'" 
    by simp
  also from h'' inG have "... = (h \<otimes> h'') \<otimes> (s \<otimes> s')" 
    using m_assoc mem_carrier by auto
  finally have "g \<otimes> g' = h \<otimes> h'' \<otimes> (s \<otimes> s')".
  moreover have "... \<in> H <#> S" 
    unfolding set_mult_def using h'' hh'ss' subgrpS subgroup.m_closed by fastforce
  ultimately show "g \<otimes> g' \<in> H <#> S" 
    by simp
qed

lemma H_contained_in_set_mult:
  shows "H \<subseteq> H <#> S"
proof 
  fix x
  assume x: "x \<in> H"
  have "x \<otimes> \<one> \<in> H <#> S" unfolding set_mult_def
    using second_isomorphism_grp.subgrpS second_isomorphism_grp_axioms subgroup.one_closed x by force
  with x show "x \<in> H <#> S" by (metis mem_carrier r_one)
qed

lemma S_contained_in_set_mult:
  shows "S \<subseteq> H <#> S"
proof
  fix s
  assume s: "s \<in> S"
  then have "\<one> \<otimes> s \<in> H <#> S" unfolding set_mult_def by force
  with s show "s \<in> H <#> S" using subgrpS subgroup.mem_carrier l_one by force
qed

lemma normal_intersection_hom:
  shows "group_hom (G\<lparr>carrier := S\<rparr>) ((G\<lparr>carrier := H <#> S\<rparr>) Mod H) (\<lambda>g. H #> g)"
proof -
  have "group ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)"
    by (simp add: H_contained_in_set_mult normal.factorgroup_is_group normal_axioms 
        normal_restrict_supergroup normal_set_mult_subgroup)
  moreover have "H #> g \<in> carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)" if g: "g \<in> S" for g
  proof -
    from g that have "g \<in> H <#> S"
      using S_contained_in_set_mult by blast
    thus "H #> g \<in> carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)" 
      unfolding FactGroup_def RCOSETS_def r_coset_def by auto
  qed
  moreover have "\<And>x y. \<lbrakk>x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> H #> x \<otimes> y = H #> x <#> (H #> y)"
    using normal.rcos_sum normal_axioms subgroup.mem_carrier subgrpS by fastforce
  ultimately show ?thesis
    by (auto simp: group_hom_def group_hom_axioms_def hom_def)
qed

lemma normal_intersection_hom_kernel:
  shows "kernel (G\<lparr>carrier := S\<rparr>) ((G\<lparr>carrier := H <#> S\<rparr>) Mod H) (\<lambda>g. H #> g) = H \<inter> S"
proof -
  have "kernel (G\<lparr>carrier := S\<rparr>) ((G\<lparr>carrier := H <#> S\<rparr>) Mod H) (\<lambda>g. H #> g)
      = {g \<in> S. H #> g = \<one>\<^bsub>(G\<lparr>carrier := H <#> S\<rparr>) Mod H\<^esub>}" 
    unfolding kernel_def by auto
  also have "... = {g \<in> S. H #> g = H}" 
    unfolding FactGroup_def by auto
  also have "... = {g \<in> S. g \<in> H}"
    by (meson coset_join1 is_group rcos_const subgroupE(1) subgroup_axioms subgrpS subset_eq)
  also have "... = H \<inter> S" by auto
  finally show ?thesis.
qed

lemma normal_intersection_hom_surj:
  shows "(\<lambda>g. H #> g) ` carrier (G\<lparr>carrier := S\<rparr>) = carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)"
proof auto
  fix g
  assume "g \<in> S"
  hence "g \<in> H <#> S" 
    using S_contained_in_set_mult by auto
  thus "H #> g \<in> carrier ((G\<lparr>carrier := H <#> S\<rparr>) Mod H)" 
    unfolding FactGroup_def RCOSETS_def r_coset_def by auto
next
  fix x
  assume "x \<in> carrier (G\<lparr>carrier := H <#> S\<rparr> Mod H)"
  then obtain h s where h: "h \<in> H" and s: "s \<in> S" and "x = H #> (h \<otimes> s)"
    unfolding FactGroup_def RCOSETS_def r_coset_def set_mult_def by auto
  hence "x = (H #> h) #> s" 
    by (metis h s coset_mult_assoc mem_carrier subgroup.mem_carrier subgrpS subset)
  also have "... = H #> s" 
    by (metis h is_group rcos_const)
  finally have "x = H #> s".
  with s show "x \<in> (#>) H ` S" 
    by simp
qed

text \<open>Finally we can prove the actual isomorphism theorem:\<close>

theorem normal_intersection_quotient_isom:
  shows "(\<lambda>X. the_elem ((\<lambda>g. H #> g) ` X)) \<in> iso ((G\<lparr>carrier := S\<rparr>) Mod (H \<inter> S)) (((G\<lparr>carrier := H <#> S\<rparr>)) Mod H)"
using normal_intersection_hom_kernel[symmetric] normal_intersection_hom normal_intersection_hom_surj
by (metis group_hom.FactGroup_iso_set)

end


corollary (in group) normal_subgroup_set_mult_closed:
  assumes "M \<lhd> G" and "N \<lhd> G"
  shows "M <#> N \<lhd> G"
proof (rule normalI)
  from assms show "subgroup (M <#> N) G"
    using second_isomorphism_grp.normal_set_mult_subgroup normal_imp_subgroup
    unfolding second_isomorphism_grp_def second_isomorphism_grp_axioms_def by force
next
  show "\<forall>x\<in>carrier G. M <#> N #> x = x <# (M <#> N)"
  proof
    fix x
    assume x: "x \<in> carrier G"
    have "M <#> N #> x = M <#> (N #> x)" 
      by (metis assms normal_inv_iff setmult_rcos_assoc subgroup.subset x)
    also have "\<dots> = M <#> (x <# N)" 
      by (metis assms(2) normal.coset_eq x)
    also have "\<dots> = (M #> x) <#> N" 
      by (metis assms normal_imp_subgroup rcos_assoc_lcos subgroup.subset x)
    also have "\<dots> = x <# (M <#> N)"
      by (simp add: assms normal.coset_eq normal_imp_subgroup setmult_lcos_assoc subgroup.subset x)
    finally show "M <#> N #> x = x <# (M <#> N)" .
  qed
qed

end

(*  Title:      HOL/Algebra/Weak_Morphisms.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Weak_Morphisms
  imports QuotRing

begin

section \<open>Weak Morphisms\<close>

text \<open>The definition of ring isomorphism, as well as the definition of group isomorphism, doesn't
      enforce any algebraic constraint to the structure of the schemes involved. This seems
      unnatural, but it turns out to be very useful: in order to prove that a scheme B satisfy
      certain algebraic constraints, it's sufficient to prove those for a scheme A and show
      the existence of an isomorphism between A and B. In this section, we explore this idea
      in a different way: given a scheme A and a function f, we build a scheme B with an
      algebraic structure of same strength as A where f is an homomorphism from A to B.\<close>


subsection \<open>Definitions\<close>

locale weak_group_morphism = normal H G for f and H and G (structure) +
  assumes inj_mod_subgroup: "\<lbrakk> a \<in> carrier G; b \<in> carrier G \<rbrakk> \<Longrightarrow> f a = f b \<longleftrightarrow> a \<otimes> (inv b) \<in> H"

locale weak_ring_morphism = ideal I R for f and I and R (structure) +
  assumes inj_mod_ideal: "\<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> f a = f b \<longleftrightarrow> a \<ominus> b \<in> I"


definition image_group :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'c) monoid_scheme \<Rightarrow> 'b monoid"
  where "image_group f G \<equiv>
           \<lparr> carrier = f ` (carrier G),
               mult = (\<lambda>a b. f ((inv_into (carrier G) f a) \<otimes>\<^bsub>G\<^esub> (inv_into (carrier G) f b))),
                one = f \<one>\<^bsub>G\<^esub> \<rparr>"

definition image_ring :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'c) ring_scheme \<Rightarrow> 'b ring"
  where "image_ring f R \<equiv> monoid.extend (image_group f R)
           \<lparr> zero = f \<zero>\<^bsub>R\<^esub>,
              add = (\<lambda>a b. f ((inv_into (carrier R) f a) \<oplus>\<^bsub>R\<^esub> (inv_into (carrier R) f b))) \<rparr>"


subsection \<open>Weak Group Morphisms\<close>

lemma image_group_carrier: "carrier (image_group f G) = f ` (carrier G)"
  unfolding image_group_def by simp

lemma image_group_one: "one (image_group f G) = f \<one>\<^bsub>G\<^esub>"
  unfolding image_group_def by simp

lemma weak_group_morphismsI:
  assumes "H \<lhd> G" and "\<And>a b. \<lbrakk> a \<in> carrier G; b \<in> carrier G \<rbrakk> \<Longrightarrow> f a = f b \<longleftrightarrow> a \<otimes>\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> b) \<in> H"
  shows "weak_group_morphism f H G"
  using assms unfolding weak_group_morphism_def weak_group_morphism_axioms_def by auto

lemma image_group_truncate:
  fixes R :: "('a, 'b) monoid_scheme"
  shows "monoid.truncate (image_group f R) = image_group f (monoid.truncate R)"
  by (simp add: image_group_def monoid.defs)

lemma image_ring_truncate: "monoid.truncate (image_ring f R) = image_group f R"
  by (simp add: image_ring_def monoid.defs)

lemma (in ring) weak_add_group_morphism:
  assumes "weak_ring_morphism f I R" shows "weak_group_morphism f I (add_monoid R)"
proof -
  have is_normal: "I \<lhd> (add_monoid R)"
    using ideal_is_normal[OF  weak_ring_morphism.axioms(1)[OF assms]] .
  show ?thesis
    using weak_group_morphism.intro[OF is_normal]
          weak_ring_morphism.inj_mod_ideal[OF assms]
    unfolding weak_group_morphism_axioms_def a_minus_def a_inv_def
    by auto
qed

lemma (in group) weak_group_morphism_range:
  assumes "weak_group_morphism f H G" and "a \<in> carrier G" shows "f ` (H #> a) = { f a }"
proof -
  interpret H: subgroup H G
    using weak_group_morphism.axioms(1)[OF assms(1)] unfolding normal_def by simp
  show ?thesis
  proof
    show "{ f a } \<subseteq> f ` (H #> a)"
      using H.one_closed assms(2) unfolding r_coset_def by force
  next
    show "f ` (H #> a) \<subseteq> { f a }"
    proof
      fix b assume "b \<in> f ` (H #> a)" then obtain h where "h \<in> H" "h \<in> carrier G" "b = f (h \<otimes> a)"
        unfolding r_coset_def using H.subset by auto
      thus "b \<in> { f a }"
        using weak_group_morphism.inj_mod_subgroup[OF assms(1)] assms(2)
        by (metis inv_solve_right m_closed singleton_iff)
    qed
  qed
qed

lemma (in group) vimage_eq_rcoset:
  assumes "weak_group_morphism f H G" and "a \<in> carrier G"
  shows "{ b \<in> carrier G. f b = f a } = H #> a" and "{ b \<in> carrier G. f b = f a } = a <# H"
proof -
  interpret H: normal H G
    using weak_group_morphism.axioms(1)[OF assms(1)] by simp
  show "{ b \<in> carrier G. f b = f a } = H #> a"
  proof
    show "H #> a \<subseteq> { b \<in> carrier G. f b = f a }"
      using r_coset_subset_G[OF H.subset assms(2)] weak_group_morphism_range[OF assms] by auto
  next
    show "{ b \<in> carrier G. f b = f a } \<subseteq> H #> a"
    proof
      fix b assume b: "b \<in> { b \<in> carrier G. f b = f a }" then obtain h where "h \<in> H" "b \<otimes> (inv a) = h"
        using weak_group_morphism.inj_mod_subgroup[OF assms(1)] assms(2) by fastforce
      thus "b \<in> H #> a"
        using H.rcos_module[OF is_group] b assms(2) by blast
    qed
  qed
  thus "{ b \<in> carrier G. f b = f a } = a <# H"
    by (simp add: assms(2) H.coset_eq)
qed

lemma (in group) weak_group_morphism_ker:
  assumes "weak_group_morphism f H G" shows "kernel G (image_group f G) f = H"
  using vimage_eq_rcoset(1)[OF assms one_closed] weak_group_morphism.axioms(1)[OF assms(1)]
  by (simp add: image_group_def kernel_def normal_def subgroup.subset)

lemma (in group) weak_group_morphism_inv_into:
  assumes "weak_group_morphism f H G" and "a \<in> carrier G"
  obtains h h' where "h  \<in> H" "inv_into (carrier G) f (f a) = h \<otimes> a"
                 and "h' \<in> H" "inv_into (carrier G) f (f a) = a \<otimes> h'"
proof -
  have "inv_into (carrier G) f (f a) \<in> { b \<in> carrier G. f b = f a }"
    using assms(2) by (auto simp add: inv_into_into f_inv_into_f)
  thus thesis
    using that vimage_eq_rcoset[OF assms] unfolding r_coset_def l_coset_def by blast
qed

proposition (in group) weak_group_morphism_is_iso:
  assumes "weak_group_morphism f H G" shows "(\<lambda>x. the_elem (f ` x)) \<in> iso (G Mod H) (image_group f G)"
proof (auto simp add: iso_def hom_def image_group_def)
  interpret H: normal H G
    using weak_group_morphism.axioms(1)[OF assms] .

  show "\<And>x. x \<in> carrier (G Mod H) \<Longrightarrow> the_elem (f ` x) \<in> f ` carrier G"
    unfolding FactGroup_def RCOSETS_def using weak_group_morphism_range[OF assms] by auto

  thus  "bij_betw (\<lambda>x. the_elem (f ` x)) (carrier (G Mod H)) (f ` carrier G)"
    unfolding bij_betw_def
  proof (auto)
    fix a assume "a \<in> carrier G"
    hence "the_elem (f ` (H #> a)) = f a" and "H #> a \<in> carrier (G Mod H)"
      using weak_group_morphism_range[OF assms] unfolding FactGroup_def RCOSETS_def by auto
    thus "f a \<in> (\<lambda>x. the_elem (f ` x)) ` carrier (G Mod H)"
      using image_iff by fastforce
  next
    show "inj_on (\<lambda>x. the_elem (f ` x)) (carrier (G Mod H))"
    proof (rule inj_onI)
      fix x y assume "x \<in> (carrier (G Mod H))" and "y \<in> (carrier (G Mod H))"
      then obtain a b where a: "a \<in> carrier G" "x = H #> a" and b: "b \<in> carrier G" "y = H #> b"
        unfolding FactGroup_def RCOSETS_def by auto
      assume "the_elem (f ` x) = the_elem (f ` y)"
      hence "a \<otimes> (inv b) \<in> H"
        using weak_group_morphism.inj_mod_subgroup[OF assms]
              weak_group_morphism_range[OF assms] a b by auto
      thus "x = y"
        using a(1) b(1) unfolding a b
        by (meson H.rcos_const H.subset group.coset_mult_inv1 is_group)
    qed
  qed

  fix x y assume "x \<in> carrier (G Mod H)" "y \<in> carrier (G Mod H)"
  then obtain a b where a: "a \<in> carrier G" "x = H #> a" and b: "b \<in> carrier G" "y = H #> b"
    unfolding FactGroup_def RCOSETS_def by auto

  show "the_elem (f ` (x <#> y)) = f (inv_into (carrier G) f (the_elem (f ` x)) \<otimes>
                                      inv_into (carrier G) f (the_elem (f ` y)))"
  proof (simp add: weak_group_morphism_range[OF assms] a b)
    obtain h1 h2
      where h1: "h1 \<in> H" "inv_into (carrier G) f (f a) = a \<otimes> h1"
        and h2: "h2 \<in> H" "inv_into (carrier G) f (f b) = h2 \<otimes> b"
      using weak_group_morphism_inv_into[OF assms] a(1) b(1) by metis
    have "the_elem (f ` ((H #> a) <#> (H #> b))) = the_elem (f ` (H #> (a \<otimes> b)))"
      by (simp add: a b H.rcos_sum)
    hence "the_elem (f ` ((H #> a) <#> (H #> b))) = f (a \<otimes> b)"
      using weak_group_morphism_range[OF assms] a(1) b(1) by auto
    moreover
    have "(a \<otimes> h1) \<otimes> (h2 \<otimes> b) = a \<otimes> (h1 \<otimes> h2 \<otimes> b)"
      by (simp add: a(1) b(1) h1(1) h2(1) H.subset m_assoc)
    hence "(a \<otimes> h1) \<otimes> (h2 \<otimes> b) \<in> a <# (H #> b)"
      using h1(1) h2(1) unfolding l_coset_def r_coset_def by auto
    hence "(a \<otimes> h1) \<otimes> (h2 \<otimes> b) \<in> (a \<otimes> b) <# H"
      by (simp add: H.subset H.coset_eq a(1) b(1) lcos_m_assoc)
    hence "f (inv_into (carrier G) f (f a) \<otimes> inv_into (carrier G) f (f b)) = f (a \<otimes> b)"
      using vimage_eq_rcoset(2)[OF assms] a(1) b(1) unfolding h1 h2 by auto
    ultimately
    show "the_elem (f ` ((H #> a) <#> (H #> b))) = f (inv_into (carrier G) f (f a) \<otimes>
                                                      inv_into (carrier G) f (f b))"
      by simp
  qed
qed

corollary (in group) image_group_is_group:
  assumes "weak_group_morphism f H G" shows "group (image_group f G)"
proof -
  interpret H: normal H G
    using weak_group_morphism.axioms(1)[OF assms] .

  have "group ((image_group f G) \<lparr> one := the_elem (f ` \<one>\<^bsub>G Mod H\<^esub>) \<rparr>)"
    using group.iso_imp_img_group[OF H.factorgroup_is_group weak_group_morphism_is_iso[OF assms]] .
  moreover have "\<one>\<^bsub>G Mod H\<^esub> = H #> \<one>"
    unfolding FactGroup_def using H.subset by force
  hence "the_elem (f ` \<one>\<^bsub>G Mod H\<^esub>) = f \<one>"
    using weak_group_morphism_range[OF assms one_closed] by simp
  ultimately show ?thesis by (simp add: image_group_def)
qed

corollary (in group) weak_group_morphism_is_hom:
  assumes "weak_group_morphism f H G" shows "f \<in> hom G (image_group f G)"
proof -
  interpret H: normal H G
    using weak_group_morphism.axioms(1)[OF assms] .

  have the_elem_hom: "(\<lambda>x. the_elem (f ` x)) \<in> hom (G Mod H) (image_group f G)"
    using weak_group_morphism_is_iso[OF assms] by (simp add: iso_def)
  have hom: "(\<lambda>x. the_elem (f ` x)) \<circ> (#>) H \<in> hom G (image_group f G)"
    using hom_trans[OF H.r_coset_hom_Mod the_elem_hom] by simp
  have restrict: "\<And>a. a \<in> carrier G \<Longrightarrow> ((\<lambda>x. the_elem (f ` x)) \<circ> (#>) H) a = f a"
    using weak_group_morphism_range[OF assms] by auto
  show ?thesis
    using hom_restrict[OF hom restrict] by simp 
qed

corollary (in group) weak_group_morphism_group_hom:
  assumes "weak_group_morphism f H G" shows "group_hom G (image_group f G) f"
  using image_group_is_group[OF assms] weak_group_morphism_is_hom[OF assms] group_axioms
  unfolding group_hom_def group_hom_axioms_def by simp


subsection \<open>Weak Ring Morphisms\<close>

lemma image_ring_carrier: "carrier (image_ring f R) = f ` (carrier R)"
  unfolding image_ring_def image_group_def by (simp add: monoid.defs)

lemma image_ring_one: "one (image_ring f R) = f \<one>\<^bsub>R\<^esub>"
  unfolding image_ring_def image_group_def by (simp add: monoid.defs)

lemma image_ring_zero: "zero (image_ring f R) = f \<zero>\<^bsub>R\<^esub>"
  unfolding image_ring_def image_group_def by (simp add: monoid.defs)

lemma weak_ring_morphismI:
  assumes "ideal I R" and "\<And>a b. \<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> f a = f b \<longleftrightarrow> a \<ominus>\<^bsub>R\<^esub> b \<in> I"
  shows "weak_ring_morphism f I R"
  using assms unfolding weak_ring_morphism_def weak_ring_morphism_axioms_def by auto

lemma (in ring) weak_ring_morphism_range:
  assumes "weak_ring_morphism f I R" and "a \<in> carrier R" shows "f ` (I +> a) = { f a }"
  using add.weak_group_morphism_range[OF weak_add_group_morphism[OF assms(1)] assms(2)]
  unfolding a_r_coset_def .

lemma (in ring) vimage_eq_a_rcoset:
  assumes "weak_ring_morphism f I R" and "a \<in> carrier R" shows "{ b \<in> carrier R. f b = f a } = I +> a"
  using add.vimage_eq_rcoset[OF weak_add_group_morphism[OF assms(1)] assms(2)]
  unfolding a_r_coset_def by simp

lemma (in ring) weak_ring_morphism_ker:
  assumes "weak_ring_morphism f I R" shows "a_kernel R (image_ring f R) f = I"
  using add.weak_group_morphism_ker[OF weak_add_group_morphism[OF assms]]
  unfolding kernel_def a_kernel_def' image_ring_def image_group_def by (simp add: monoid.defs)

lemma (in ring) weak_ring_morphism_inv_into:
  assumes "weak_ring_morphism f I R" and "a \<in> carrier R"
  obtains i where "i \<in> I" "inv_into (carrier R) f (f a) = i \<oplus> a"
  using add.weak_group_morphism_inv_into(1)[OF weak_add_group_morphism[OF assms(1)] assms(2)] by auto

proposition (in ring) weak_ring_morphism_is_iso:
  assumes "weak_ring_morphism f I R" shows "(\<lambda>x. the_elem (f ` x)) \<in> ring_iso (R Quot I) (image_ring f R)"
proof (rule ring_iso_memI)
  show "bij_betw (\<lambda>x. the_elem (f ` x)) (carrier (R Quot I)) (carrier (image_ring f R))"
   and add_hom: "\<And>x y. \<lbrakk> x \<in> carrier (R Quot I); y \<in> carrier (R Quot I) \<rbrakk> \<Longrightarrow>
              the_elem (f ` (x \<oplus>\<^bsub>R Quot I\<^esub> y)) = the_elem (f ` x) \<oplus>\<^bsub>image_ring f R\<^esub> the_elem (f ` y)"
    using add.weak_group_morphism_is_iso[OF weak_add_group_morphism[OF assms]]
    unfolding iso_def hom_def FactGroup_def FactRing_def A_RCOSETS_def set_add_def
    by (auto simp add: image_ring_def image_group_def monoid.defs)
next
  interpret I: ideal I R
    using weak_ring_morphism.axioms(1)[OF assms] .

  show "the_elem (f ` \<one>\<^bsub>R Quot I\<^esub>) = \<one>\<^bsub>image_ring f R\<^esub>"
   and "\<And>x. x \<in> carrier (R Quot I) \<Longrightarrow> the_elem (f ` x) \<in> carrier (image_ring f R)"
    using weak_ring_morphism_range[OF assms] one_closed I.Icarr
    by (auto simp add: image_ring_def image_group_def monoid.defs FactRing_def A_RCOSETS_def')

  fix x y assume "x \<in> carrier (R Quot I)" "y \<in> carrier (R Quot I)"
  then obtain a b where a: "a \<in> carrier R" "x = I +> a" and b: "b \<in> carrier R" "y = I +> b"
    unfolding FactRing_def A_RCOSETS_def' by auto
  hence prod: "x \<otimes>\<^bsub>R Quot I\<^esub> y = I +> (a \<otimes> b)"
    unfolding FactRing_def by (simp add: I.rcoset_mult_add)

  show "the_elem (f ` (x \<otimes>\<^bsub>R Quot I\<^esub> y)) = the_elem (f ` x) \<otimes>\<^bsub>image_ring f R\<^esub> the_elem (f ` y)"
    unfolding prod
  proof (simp add: weak_ring_morphism_range[OF assms] a b image_ring_def image_group_def monoid.defs)
    obtain i j
      where i: "i \<in> I" "inv_into (carrier R) f (f a) = i \<oplus> a"
        and j: "j \<in> I" "inv_into (carrier R) f (f b) = j \<oplus> b"
      using weak_ring_morphism_inv_into[OF assms] a(1) b(1) by metis
    have "i \<in> carrier R" and "j \<in> carrier R"
      using I.Icarr i(1) j(1) by auto
    hence "(i \<oplus> a) \<otimes> (j \<oplus> b) = (i \<oplus> a) \<otimes> j \<oplus> (i \<otimes> b) \<oplus> (a \<otimes> b)"
      using a(1) b(1) by algebra
    hence "(i \<oplus> a) \<otimes> (j \<oplus> b) \<in> I +> (a \<otimes> b)"
      using i(1) j(1) a(1) b(1) unfolding a_r_coset_def' 
      by (simp add: I.I_l_closed I.I_r_closed)
    thus "f (a \<otimes> b) = f (inv_into (carrier R) f (f a) \<otimes> inv_into (carrier R) f (f b))"
      unfolding i j using weak_ring_morphism_range[OF assms m_closed[OF a(1) b(1)]]
      by (metis imageI singletonD) 
  qed
qed

corollary (in ring) image_ring_zero':
  assumes "weak_ring_morphism f I R" shows "the_elem (f ` \<zero>\<^bsub>R Quot I\<^esub>) = \<zero>\<^bsub>image_ring f R\<^esub>"
proof -
  interpret I: ideal I R
    using weak_ring_morphism.axioms(1)[OF assms] .

  have "\<zero>\<^bsub>R Quot I\<^esub> = I +> \<zero>"
    unfolding FactRing_def a_r_coset_def' by force
  thus ?thesis
    using weak_ring_morphism_range[OF assms zero_closed] unfolding image_ring_zero by simp
qed

corollary (in ring) image_ring_is_ring:
  assumes "weak_ring_morphism f I R" shows "ring (image_ring f R)"
proof -
  interpret I: ideal I R
    using weak_ring_morphism.axioms(1)[OF assms] .

  have "ring ((image_ring f R) \<lparr> zero := the_elem (f ` \<zero>\<^bsub>R Quot I\<^esub>) \<rparr>)"
    using ring.ring_iso_imp_img_ring[OF I.quotient_is_ring weak_ring_morphism_is_iso[OF assms]] by simp
  thus ?thesis
    unfolding image_ring_zero'[OF assms] by simp
qed

corollary (in ring) image_ring_is_field:
  assumes "weak_ring_morphism f I R" and "field (R Quot I)" shows "field (image_ring f R)"
  using field.ring_iso_imp_img_field[OF assms(2) weak_ring_morphism_is_iso[OF assms(1)]]
  unfolding image_ring_zero'[OF assms(1)] by simp

corollary (in ring) weak_ring_morphism_is_hom:
  assumes "weak_ring_morphism f I R" shows "f \<in> ring_hom R (image_ring f R)"
proof -
  interpret I: ideal I R
    using weak_ring_morphism.axioms(1)[OF assms] .

  have the_elem_hom: "(\<lambda>x. the_elem (f ` x)) \<in> ring_hom (R Quot I) (image_ring f R)"
    using weak_ring_morphism_is_iso[OF assms] by (simp add: ring_iso_def)
  have ring_hom: "(\<lambda>x. the_elem (f ` x)) \<circ> (+>) I \<in> ring_hom R (image_ring f R)"
    using ring_hom_trans[OF I.rcos_ring_hom the_elem_hom] .
  have restrict: "\<And>a. a \<in> carrier R \<Longrightarrow> ((\<lambda>x. the_elem (f ` x)) \<circ> (+>) I) a = f a"
    using weak_ring_morphism_range[OF assms] by auto
  show ?thesis
    using ring_hom_restrict[OF ring_hom restrict] by simp
qed

corollary (in ring) weak_ring_morphism_ring_hom:
  assumes "weak_ring_morphism f I R" shows "ring_hom_ring R (image_ring f R) f"
  using ring_hom_ringI2[OF ring_axioms image_ring_is_ring[OF assms] weak_ring_morphism_is_hom[OF assms]] .


subsection \<open>Injective Functions\<close>

text \<open>If the fuction is injective, we don't need to impose any algebraic restriction to the input
      scheme in order to state an isomorphism.\<close>

lemma inj_imp_image_group_iso:
  assumes "inj_on f (carrier G)" shows "f \<in> iso G (image_group f G)"
  using assms by (auto simp add: image_group_def iso_def bij_betw_def hom_def)

lemma inj_imp_image_group_inv_iso:
  assumes "inj f" shows "Hilbert_Choice.inv f \<in> iso (image_group f G) G"
  using assms by (auto simp add: image_group_def iso_def bij_betw_def hom_def inj_on_def)

lemma inj_imp_image_ring_iso:
  assumes "inj_on f (carrier R)" shows "f \<in> ring_iso R (image_ring f R)"
  using assms by (auto simp add: image_ring_def image_group_def ring_iso_def
                                 bij_betw_def ring_hom_def monoid.defs)

lemma inj_imp_image_ring_inv_iso:
  assumes "inj f" shows "Hilbert_Choice.inv f \<in> ring_iso (image_ring f R) R"
  using assms by (auto simp add: image_ring_def image_group_def ring_iso_def
                                 bij_betw_def ring_hom_def inj_on_def monoid.defs)

lemma (in group) inj_imp_image_group_is_group:
  assumes "inj_on f (carrier G)" shows "group (image_group f G)"
  using iso_imp_img_group[OF inj_imp_image_group_iso[OF assms]] by (simp add: image_group_def)

lemma (in ring) inj_imp_image_ring_is_ring:
  assumes "inj_on f (carrier R)" shows "ring (image_ring f R)"
  using ring_iso_imp_img_ring[OF inj_imp_image_ring_iso[OF assms]]
  by (simp add: image_ring_def image_group_def monoid.defs)

lemma (in domain) inj_imp_image_ring_is_domain:
  assumes "inj_on f (carrier R)" shows "domain (image_ring f R)"
  using ring_iso_imp_img_domain[OF inj_imp_image_ring_iso[OF assms]]
  by (simp add: image_ring_def image_group_def monoid.defs)

lemma (in field) inj_imp_image_ring_is_field:
  assumes "inj_on f (carrier R)" shows "field (image_ring f R)"
  using ring_iso_imp_img_field[OF inj_imp_image_ring_iso[OF assms]]
  by (simp add: image_ring_def image_group_def monoid.defs)


section \<open>Examples\<close>

text \<open>In a lot of different contexts, the lack of dependent types make some definitions quite
      complicated. The tools developed in this theory give us a way to change the type of a
      scheme and preserve all of its algebraic properties. We show, in this section, how to
      make use of this feature in order to solve the problem mentioned above. \<close>


subsection \<open>Direct Product\<close>

abbreviation nil_monoid :: "('a list) monoid"
  where "nil_monoid \<equiv> \<lparr> carrier = { [] }, mult = (\<lambda>a b. []), one = [] \<rparr>"

definition DirProd_list :: "(('a, 'b) monoid_scheme) list \<Rightarrow> ('a list) monoid"
  where "DirProd_list Gs = foldr (\<lambda>G H. image_group (\<lambda>(x, xs). x # xs) (G \<times>\<times> H)) Gs nil_monoid"


subsubsection \<open>Basic Properties\<close>

lemma DirProd_list_carrier:
  shows "carrier (DirProd_list (G # Gs)) = (\<lambda>(x, xs). x # xs) ` (carrier G \<times> carrier (DirProd_list Gs))"
  unfolding DirProd_list_def image_group_def by auto

lemma DirProd_list_one:
  shows "one (DirProd_list Gs) = foldr (\<lambda>G tl. (one G) # tl) Gs []"
  unfolding DirProd_list_def DirProd_def image_group_def by (induct Gs) (auto)

lemma DirProd_list_carrier_mem:
  assumes "gs \<in> carrier (DirProd_list Gs)"
  shows "length gs = length Gs" and "\<And>i. i < length Gs \<Longrightarrow> (gs ! i) \<in> carrier (Gs ! i)"
proof -
  let ?same_length = "\<lambda>xs ys. length xs = length ys"
  let ?in_carrier = "\<lambda>i gs Gs. (gs ! i) \<in> carrier (Gs ! i)"
  from assms have "?same_length gs Gs \<and> (\<forall>i < length Gs. ?in_carrier i gs Gs)"
  proof (induct Gs arbitrary: gs, simp add: DirProd_list_def)
    case (Cons G Gs)
    then obtain g' gs'
      where g': "g' \<in> carrier G" and gs': "gs' \<in> carrier (DirProd_list Gs)" and gs: "gs = g' # gs'"
      unfolding DirProd_list_carrier by auto
    hence "?same_length gs (G # Gs)" and "\<And>i. i \<in> {(Suc 0)..< length (G # Gs)} \<Longrightarrow> ?in_carrier i gs (G # Gs)"
      using Cons(1) by auto
    moreover have "?in_carrier 0 gs (G # Gs)"
      unfolding gs using g' by simp
    ultimately show ?case
      by (metis atLeastLessThan_iff eq_imp_le less_Suc0 linorder_neqE_nat nat_less_le)
  qed
  thus "?same_length gs Gs" and "\<And>i. i < length Gs \<Longrightarrow> ?in_carrier i gs Gs"
    by simp+
qed

lemma DirProd_list_carrier_memI:
  assumes "length gs = length Gs" and "\<And>i. i < length Gs \<Longrightarrow> (gs ! i) \<in> carrier (Gs ! i)"
  shows "gs \<in> carrier (DirProd_list Gs)"
  using assms
proof (induct Gs arbitrary: gs, simp add: DirProd_list_def)
  case (Cons G Gs)
  then obtain g' gs' where gs: "gs = g' # gs'"
    by (metis length_Suc_conv)
  have "g' \<in> carrier G"
    using Cons(3)[of 0] unfolding gs by auto
  moreover have "gs' \<in> carrier (DirProd_list Gs)"
    using Cons unfolding gs by force
  ultimately show ?case
    unfolding DirProd_list_carrier gs by blast
qed

lemma inj_on_DirProd_carrier:
  shows "inj_on (\<lambda>(g, gs). g # gs) (carrier (G \<times>\<times> (DirProd_list Gs)))"
  unfolding DirProd_def inj_on_def by auto

lemma DirProd_list_is_group:
  assumes "\<And>i. i < length Gs \<Longrightarrow> group (Gs ! i)" shows "group (DirProd_list Gs)"
  using assms
proof (induct Gs)
  case Nil thus ?case
    unfolding DirProd_list_def by (unfold_locales, auto simp add: Units_def)
next
  case (Cons G Gs)
  hence is_group: "group (G \<times>\<times> (DirProd_list Gs))"
    using DirProd_group[of G "DirProd_list Gs"] by force
  show ?case
    using group.inj_imp_image_group_is_group[OF is_group inj_on_DirProd_carrier]
    unfolding DirProd_list_def by auto 
qed

lemma DirProd_list_iso:
  "(\<lambda>(g, gs). g # gs) \<in> iso (G \<times>\<times> (DirProd_list Gs)) (DirProd_list (G # Gs))"
  using inj_imp_image_group_iso[OF inj_on_DirProd_carrier] unfolding DirProd_list_def by auto

end
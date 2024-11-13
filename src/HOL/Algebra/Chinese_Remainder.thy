(*  Title:      HOL/Algebra/Chinese_Remainder.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Chinese_Remainder
  imports Weak_Morphisms Ideal_Product
    
begin


section \<open>Direct Product of Rings\<close>

subsection \<open>Definitions\<close>

definition RDirProd :: "('a, 'n) ring_scheme \<Rightarrow> ('b, 'm) ring_scheme \<Rightarrow> ('a \<times> 'b) ring"
  where "RDirProd R S = monoid.extend (R \<times>\<times> S)
           \<lparr> zero = one ((add_monoid R) \<times>\<times> (add_monoid S)),
              add = mult ((add_monoid R) \<times>\<times> (add_monoid S)) \<rparr> "

abbreviation nil_ring :: "('a list) ring"
  where "nil_ring \<equiv> monoid.extend nil_monoid \<lparr> zero = [], add = (\<lambda>a b. []) \<rparr>"

definition RDirProd_list :: "(('a, 'n) ring_scheme) list \<Rightarrow> ('a list) ring"
  where "RDirProd_list Rs = foldr (\<lambda>R S. image_ring (\<lambda>(a, as). a # as) (RDirProd R S)) Rs nil_ring"


subsection \<open>Basic Properties\<close>

lemma RDirProd_carrier: "carrier (RDirProd R S) = carrier R \<times> carrier S"
  unfolding RDirProd_def DirProd_def by (simp add: monoid.defs)

lemma RDirProd_add_monoid [simp]: "add_monoid (RDirProd R S) = (add_monoid R) \<times>\<times> (add_monoid S)"
  by (simp add: RDirProd_def monoid.defs)

lemma RDirProd_ring:
  assumes "ring R" and "ring S" shows "ring (RDirProd R S)"
proof -
  have "monoid (RDirProd R S)"
    using DirProd_monoid[OF assms[THEN ring.axioms(2)]] unfolding monoid_def
    by (auto simp add: DirProd_def RDirProd_def monoid.defs)
  then interpret Prod: group "add_monoid (RDirProd R S)" + monoid "RDirProd R S"
    using DirProd_group[OF assms[THEN abelian_group.a_group[OF ring.is_abelian_group]]]
    unfolding RDirProd_add_monoid by auto
  show ?thesis
    by (unfold_locales, auto simp add: RDirProd_def DirProd_def monoid.defs assms ring.ring_simprules)
qed

lemma RDirProd_iso1:
  "(\<lambda>(x, y). (y, x)) \<in> ring_iso (RDirProd R S) (RDirProd S R)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_iso2:
  "(\<lambda>(x, (y, z)). ((x, y), z)) \<in> ring_iso (RDirProd R (RDirProd S T)) (RDirProd (RDirProd R S) T)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: image_iff RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_iso3:
  "(\<lambda>((x, y), z). (x, (y, z))) \<in> ring_iso (RDirProd (RDirProd R S) T) (RDirProd R (RDirProd S T))"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: image_iff RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_iso4:
  assumes "f \<in> ring_iso R S" shows "(\<lambda>(r, t). (f r, t)) \<in> ring_iso (RDirProd R T) (RDirProd S T)"
  using assms unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: image_iff RDirProd_def DirProd_def monoid.defs)+

lemma RDirProd_iso5:
  assumes "f \<in> ring_iso S T" shows "(\<lambda>(r, s). (r, f s)) \<in> ring_iso (RDirProd R S) (RDirProd R T)"
  using ring_iso_set_trans[OF ring_iso_set_trans[OF RDirProd_iso1 RDirProd_iso4[OF assms]] RDirProd_iso1]
  by (simp add: case_prod_unfold comp_def)

lemma RDirProd_iso6:
  assumes "f \<in> ring_iso R R'" and "g \<in> ring_iso S S'"
  shows "(\<lambda>(r, s). (f r, g s)) \<in> ring_iso (RDirProd R S) (RDirProd R' S')"
  using ring_iso_set_trans[OF RDirProd_iso4[OF assms(1)] RDirProd_iso5[OF assms(2)]]
  by (simp add: case_prod_beta' comp_def)

lemma RDirProd_iso7:
  shows "(\<lambda>a. (a, [])) \<in> ring_iso R (RDirProd R nil_ring)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def
  by (auto simp add: RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_hom1:
  shows "(\<lambda>a. (a, a)) \<in> ring_hom R (RDirProd R R)"
  by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_hom2:
  assumes "f \<in> ring_hom S T"
  shows "(\<lambda>(x, y). (x, f y)) \<in> ring_hom (RDirProd R S) (RDirProd R T)"
    and "(\<lambda>(x, y). (f x, y)) \<in> ring_hom (RDirProd S R) (RDirProd T R)"
  using assms by (auto simp add: ring_hom_def RDirProd_def DirProd_def monoid.defs)

lemma RDirProd_hom3:
  assumes "f \<in> ring_hom R R'" and "g \<in> ring_hom S S'"
  shows "(\<lambda>(r, s). (f r, g s)) \<in> ring_hom (RDirProd R S) (RDirProd R' S')"
  using ring_hom_trans[OF RDirProd_hom2(2)[OF assms(1)] RDirProd_hom2(1)[OF assms(2)]]
  by (simp add: case_prod_beta' comp_def)


subsection \<open>Direct Product of a List of Rings\<close>

lemma RDirProd_list_nil [simp]: "RDirProd_list [] = nil_ring"
  unfolding RDirProd_list_def by simp

lemma nil_ring_simprules [simp]:
  "carrier nil_ring = { [] }" and "one nil_ring = []" and "zero nil_ring = []"
  by (auto simp add: monoid.defs)

lemma RDirProd_list_truncate:
  shows "monoid.truncate (RDirProd_list Rs) = DirProd_list Rs"
proof (induct Rs, simp add: RDirProd_list_def DirProd_list_def monoid.defs)
  case (Cons R Rs)
  have "monoid.truncate (RDirProd_list (R # Rs)) =
        monoid.truncate (image_ring (\<lambda>(a, as). a # as) (RDirProd R (RDirProd_list Rs)))"
    unfolding RDirProd_list_def by simp
  also have " ... = image_group (\<lambda>(a, as). a # as) (monoid.truncate (RDirProd R (RDirProd_list Rs)))"
  by (simp add: image_ring_def image_group_def monoid.defs)
  also have " ... = image_group (\<lambda>(a, as). a # as) (R \<times>\<times> (monoid.truncate (RDirProd_list Rs)))"
    by (simp add: RDirProd_def DirProd_def monoid.defs)
  also have " ... = DirProd_list (R # Rs)"
    unfolding Cons DirProd_list_def by simp
  finally show ?case .
qed

lemma RDirProd_list_carrier_def':
  shows "carrier (RDirProd_list Rs) = carrier (DirProd_list Rs)"
proof -
  have "carrier (RDirProd_list Rs) = carrier (monoid.truncate (RDirProd_list Rs))"
    by (simp add: monoid.defs)
  thus ?thesis
    unfolding RDirProd_list_truncate .
qed

lemma RDirProd_list_carrier:
  shows "carrier (RDirProd_list (G # Gs)) = (\<lambda>(x, xs). x # xs) ` (carrier G \<times> carrier (RDirProd_list Gs))"
  unfolding RDirProd_list_carrier_def' using DirProd_list_carrier .

lemma RDirProd_list_one:
  shows "one (RDirProd_list Rs) = foldr (\<lambda>R tl. (one R) # tl) Rs []"
  unfolding RDirProd_list_def RDirProd_def image_ring_def image_group_def
  by (induct Rs) (auto simp add: monoid.defs)

lemma RDirProd_list_zero:
  shows "zero (RDirProd_list Rs) = foldr (\<lambda>R tl. (zero R) # tl) Rs []"
  unfolding RDirProd_list_def RDirProd_def image_ring_def
  by (induct Rs) (auto simp add: monoid.defs)

lemma RDirProd_list_zero':
  shows "zero (RDirProd_list (R # Rs)) = (zero R) # (zero (RDirProd_list Rs))"
  unfolding RDirProd_list_zero by simp

lemma RDirProd_list_carrier_mem:
  assumes "as \<in> carrier (RDirProd_list Rs)"
  shows "length as = length Rs" and "\<And>i. i < length Rs \<Longrightarrow> (as ! i) \<in> carrier (Rs ! i)"
  using assms DirProd_list_carrier_mem unfolding RDirProd_list_carrier_def' by auto

lemma RDirProd_list_carrier_memI:
  assumes "length as = length Rs" and "\<And>i. i < length Rs \<Longrightarrow> (as ! i) \<in> carrier (Rs ! i)"
  shows "as \<in> carrier (RDirProd_list Rs)"
  using assms DirProd_list_carrier_memI unfolding RDirProd_list_carrier_def' by auto

lemma inj_on_RDirProd_carrier:
  shows "inj_on (\<lambda>(a, as). a # as) (carrier (RDirProd R (RDirProd_list Rs)))"
  unfolding RDirProd_def DirProd_def inj_on_def by auto

lemma RDirProd_list_is_ring:
  assumes "\<And>i. i < length Rs \<Longrightarrow> ring (Rs ! i)" shows "ring (RDirProd_list Rs)"
  using assms
proof (induct Rs)
  case Nil thus ?case
    unfolding RDirProd_list_def by (unfold_locales, auto simp add: monoid.defs Units_def)
next
  case (Cons R Rs)
  hence is_ring: "ring (RDirProd R (RDirProd_list Rs))"
    using RDirProd_ring[of R "RDirProd_list Rs"] by force
  show ?case
    using ring.inj_imp_image_ring_is_ring[OF is_ring inj_on_RDirProd_carrier]
    unfolding RDirProd_list_def by auto 
qed

lemma RDirProd_list_iso1:
  "(\<lambda>(a, as). a # as) \<in> ring_iso (RDirProd R (RDirProd_list Rs)) (RDirProd_list (R # Rs))"
  using inj_imp_image_ring_iso[OF inj_on_RDirProd_carrier] unfolding RDirProd_list_def by auto

lemma RDirProd_list_iso2:
  "Hilbert_Choice.inv (\<lambda>(a, as). a # as) \<in> ring_iso (RDirProd_list (R # Rs)) (RDirProd R (RDirProd_list Rs))"
  unfolding RDirProd_list_def by (auto intro: inj_imp_image_ring_inv_iso simp add: inj_def)

lemma RDirProd_list_iso3:
  "(\<lambda>a. [ a ]) \<in> ring_iso R (RDirProd_list [ R ])"
proof -
  have [simp]: "(\<lambda>a. [ a ]) = (\<lambda>(a, as). a # as) \<circ> (\<lambda>a. (a, []))" by auto
  show ?thesis
    using ring_iso_set_trans[OF RDirProd_iso7] RDirProd_list_iso1[of R "[]"]
    unfolding RDirProd_list_def by simp
qed

lemma RDirProd_list_hom1:
  "(\<lambda>(a, as). a # as) \<in> ring_hom (RDirProd R (RDirProd_list Rs)) (RDirProd_list (R # Rs))"
  using RDirProd_list_iso1 unfolding ring_iso_def by auto

lemma RDirProd_list_hom2:
  assumes "f \<in> ring_hom R S" shows "(\<lambda>a. [ f a ]) \<in> ring_hom R (RDirProd_list [ S ])"
proof -
  have hom1: "(\<lambda>a. (a, [])) \<in> ring_hom R (RDirProd R nil_ring)"
    using RDirProd_iso7 unfolding ring_iso_def by auto
  have hom2: "(\<lambda>(a, as). a # as) \<in> ring_hom (RDirProd S nil_ring) (RDirProd_list [ S ])"
    using RDirProd_list_hom1[of _ "[]"] unfolding RDirProd_list_def by auto
  have [simp]: "(\<lambda>(a, as). a # as) \<circ> ((\<lambda>(x, y). (f x, y)) \<circ> (\<lambda>a. (a, []))) = (\<lambda>a. [ f a ])" by auto
  show ?thesis
    using ring_hom_trans[OF ring_hom_trans[OF hom1 RDirProd_hom2(2)[OF assms]] hom2] by simp
qed


section \<open>Chinese Remainder Theorem\<close>

subsection \<open>Definitions\<close>

abbreviation (in ring) canonical_proj :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<times> 'a set"
  where "canonical_proj I J \<equiv> (\<lambda>a. (I +> a, J +> a))"

definition (in ring) canonical_proj_ext :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a set) list"
  where "canonical_proj_ext I n = (\<lambda>a. map (\<lambda>i. (I i) +> a) [0..< Suc n])"


subsection \<open>Chinese Remainder Simple\<close>

lemma (in ring) canonical_proj_is_surj:
  assumes "ideal I R" "ideal J R" and "I <+> J = carrier R"
  shows "(canonical_proj I J) ` carrier R = carrier (RDirProd (R Quot I) (R Quot J))"
  unfolding RDirProd_def DirProd_def FactRing_def A_RCOSETS_def'
proof (auto simp add: monoid.defs)
  have aux_lemma1: "I +> i = \<zero>\<^bsub>R Quot I\<^esub>" if "ideal I R" "i \<in> I" for I i
    using that a_rcos_zero by (simp add: FactRing_def)

  have aux_lemma2: "I +> j = \<one>\<^bsub>R Quot I\<^esub>"
    if A: "ideal I R" "i \<in> I" "j \<in> carrier R" "i \<oplus> j = \<one>"
    for I i j
  proof -
    have "(I +> i) \<oplus>\<^bsub>R Quot I\<^esub> (I +> j) = I +> \<one>"
      using ring_hom_memE(3)[OF ideal.rcos_ring_hom ideal.Icarr[OF _ A(2)] A(3)] A(1,4) by simp
    moreover have "I +> i = I"
      using abelian_subgroupI3[OF ideal.axioms(1) is_abelian_group]
      by (simp add: A(1-2) abelian_subgroup.a_rcos_const)
    moreover have "I +> j \<in> carrier (R Quot I)" and "I = \<zero>\<^bsub>R Quot I\<^esub>" and "I +> \<one> = \<one>\<^bsub>R Quot I\<^esub>"
      by (auto simp add: FactRing_def A_RCOSETS_def' A(3))
    ultimately show ?thesis
      using ring.ring_simprules(8)[OF ideal.quotient_is_ring[OF A(1)]] by simp
  qed

  interpret I: ring "R Quot I" + J: ring "R Quot J"
    using assms(1-2)[THEN ideal.quotient_is_ring] by auto

  fix a b assume a: "a \<in> carrier R" and b: "b \<in> carrier R"
  have "\<one> \<in> I <+> J"
    using assms(3) by blast
  then obtain i j where i: "i \<in> carrier R" "i \<in> I" and j: "j \<in> carrier R" "j \<in> J" and ij: "i \<oplus> j = \<one>"
    using assms(1-2)[THEN ideal.Icarr] unfolding set_add_def' by auto
  hence rcos_j: "I +> j = \<one>\<^bsub>R Quot I\<^esub>" and rcos_i: "J +> i = \<one>\<^bsub>R Quot J\<^esub>"
    using assms(1-2)[THEN aux_lemma2] a_comm by simp+

  define s where "s = (a \<otimes> j) \<oplus> (b \<otimes> i)"
  hence "s \<in> carrier R"
    using a b i j by simp

  have "I +> s = ((I +> a) \<otimes>\<^bsub>R Quot I\<^esub> (I +> j)) \<oplus>\<^bsub>R Quot I\<^esub> (I +> (b \<otimes> i))"
    using ring_hom_memE(2-3)[OF ideal.rcos_ring_hom[OF assms(1)]]
    by (simp add: a b i(1) j(1) s_def)
  moreover have "I +> a \<in> carrier (R Quot I)"
    by (auto simp add: FactRing_def A_RCOSETS_def' a)
  ultimately have "I +> s = I +> a"
    unfolding rcos_j aux_lemma1[OF assms(1) ideal.I_l_closed[OF assms(1) i(2) b]] by simp

  have "J +> s = (J +> (a \<otimes> j)) \<oplus>\<^bsub>R Quot J\<^esub> ((J +> b) \<otimes>\<^bsub>R Quot J\<^esub> (J +> i))"
    using ring_hom_memE(2-3)[OF ideal.rcos_ring_hom[OF assms(2)]]
    by (simp add: a b i(1) j(1) s_def)
  moreover have "J +> b \<in> carrier (R Quot J)"
    by (auto simp add: FactRing_def A_RCOSETS_def' b)
  ultimately have "J +> s = J +> b"
    unfolding rcos_i aux_lemma1[OF assms(2) ideal.I_l_closed[OF assms(2) j(2) a]] by simp

  from \<open>I +> s = I +> a\<close> and \<open>J +> s = J +> b\<close> and \<open>s \<in> carrier R\<close>
  show "(I +> a, J +> b) \<in> (canonical_proj I J) ` carrier R" by blast
qed

lemma (in ring) canonical_proj_ker:
  assumes "ideal I R" and "ideal J R"
  shows "a_kernel R (RDirProd (R Quot I) (R Quot J)) (canonical_proj I J) = I \<inter> J"
proof
  show "a_kernel R (RDirProd (R Quot I) (R Quot J)) (canonical_proj I J) \<subseteq> I \<inter> J"
    unfolding FactRing_def RDirProd_def DirProd_def a_kernel_def'
    by (auto simp add: assms[THEN ideal.rcos_const_imp_mem] monoid.defs)
next
  show "I \<inter> J \<subseteq> a_kernel R (RDirProd (R Quot I) (R Quot J)) (canonical_proj I J)"
  proof
    fix s assume s: "s \<in> I \<inter> J" then have "I +> s = I" and "J +> s = J"
      using abelian_subgroupI3[OF ideal.axioms(1) is_abelian_group]
      by (simp add: abelian_subgroup.a_rcos_const assms)+
    thus "s \<in> a_kernel R (RDirProd (R Quot I) (R Quot J)) (canonical_proj I J)"
      unfolding FactRing_def RDirProd_def DirProd_def a_kernel_def'
      using ideal.Icarr[OF assms(1)] s by (simp add: monoid.defs)
  qed
qed

lemma (in ring) canonical_proj_is_hom:
  assumes "ideal I R" and "ideal J R"
  shows "(canonical_proj I J) \<in> ring_hom R (RDirProd (R Quot I) (R Quot J))"
  unfolding RDirProd_def DirProd_def FactRing_def A_RCOSETS_def'
  by (auto intro!: ring_hom_memI
         simp add: assms[THEN ideal.rcoset_mult_add]
                   assms[THEN ideal.a_rcos_sum] monoid.defs)

lemma (in ring) canonical_proj_ring_hom:
  assumes "ideal I R" and "ideal J R"
  shows "ring_hom_ring R (RDirProd (R Quot I) (R Quot J)) (canonical_proj I J)"
  using ring_hom_ring.intro[OF ring_axioms RDirProd_ring[OF assms[THEN ideal.quotient_is_ring]]]
  by (simp add: ring_hom_ring_axioms_def canonical_proj_is_hom[OF assms])

theorem (in ring) chinese_remainder_simple:
  assumes "ideal I R" "ideal J R" and "I <+> J = carrier R"
  shows "R Quot (I \<inter> J) \<simeq> RDirProd (R Quot I) (R Quot J)"
  using ring_hom_ring.FactRing_iso[OF canonical_proj_ring_hom canonical_proj_is_surj]
  by (simp add: canonical_proj_ker assms)


subsection \<open>Chinese Remainder Generalized\<close>

lemma (in ring) canonical_proj_ext_zero [simp]: "(canonical_proj_ext I 0) = (\<lambda>a. [ (I 0) +> a ])"
  unfolding canonical_proj_ext_def by simp

lemma (in ring) canonical_proj_ext_tl:
  "(\<lambda>a. canonical_proj_ext I (Suc n) a) = (\<lambda>a. ((I 0) +> a) # (canonical_proj_ext (\<lambda>i. I (Suc i)) n a))"
  unfolding canonical_proj_ext_def by (induct n) (auto, metis (lifting) append.assoc append_Cons append_Nil)

lemma (in ring) canonical_proj_ext_is_hom:
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R"
  shows "(canonical_proj_ext I n) \<in> ring_hom R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))"
  using assms
proof (induct n arbitrary: I)
  case 0 thus ?case
    using RDirProd_list_hom2[OF ideal.rcos_ring_hom[of _ R]] by (simp add: canonical_proj_ext_def)
next
  let ?DirProd = "\<lambda>I n. RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..<Suc n])"
  let ?proj = "\<lambda>I n. canonical_proj_ext I n"

  case (Suc n)
  hence I: "ideal (I 0) R" by simp
  have hom: "(?proj (\<lambda>i. I (Suc i)) n) \<in> ring_hom R (?DirProd (\<lambda>i. I (Suc i)) n)"
    using Suc(1)[of "\<lambda>i. I (Suc i)"] Suc(2) by simp
  have [simp]:
    "(\<lambda>(a, as). a # as) \<circ> ((\<lambda>(r, s). (I 0 +> r, ?proj (\<lambda>i. I (Suc i)) n s)) \<circ> (\<lambda>a. (a, a))) = ?proj I (Suc n)"
    unfolding canonical_proj_ext_tl by auto
  moreover have
    "(R Quot I 0) # (map (\<lambda>i. R Quot I (Suc i)) [0..< Suc n]) = map (\<lambda>i. R Quot (I i)) [0..< Suc (Suc n)]"
    by (induct n) (auto)
  moreover show ?case
    using ring_hom_trans[OF ring_hom_trans[OF RDirProd_hom1
          RDirProd_hom3[OF ideal.rcos_ring_hom[OF I] hom]] RDirProd_list_hom1]
    unfolding calculation(2) by simp
qed

lemma (in ring) RDirProd_Quot_list_is_ring:
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R" shows "ring (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))"
proof -
  have ring_list: "\<And>i. i < Suc n \<Longrightarrow> ring ((map (\<lambda>i. R Quot I i) [0..< Suc n]) ! i)"
    using ideal.quotient_is_ring[OF assms]
    by (metis add.left_neutral diff_zero le_simps(2) nth_map_upt)
  show ?thesis
    using RDirProd_list_is_ring[OF ring_list] by simp
qed

lemma (in ring) canonical_proj_ext_ring_hom:
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R"
  shows "ring_hom_ring R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) (canonical_proj_ext I n)"
proof -
  have ring: "ring (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))"
    using RDirProd_Quot_list_is_ring[OF assms] by simp  
  show ?thesis
    using canonical_proj_ext_is_hom assms ring_hom_ring.intro[OF ring_axioms ring]
    unfolding ring_hom_ring_axioms_def by blast
qed

lemma (in ring) canonical_proj_ext_ker:
  assumes "\<And>i. i \<le> (n :: nat) \<Longrightarrow> ideal (I i) R"
  shows "a_kernel R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) (canonical_proj_ext I n) = (\<Inter>i \<le> n. I i)"
proof -
  let ?map_Quot = "\<lambda>I n. map (\<lambda>i. R Quot (I i)) [0..< Suc n]"
  let ?ker = "\<lambda>I n. a_kernel R (RDirProd_list (?map_Quot I n)) (canonical_proj_ext I n)"

  from assms show ?thesis
  proof (induct n arbitrary: I)
    case 0 then have I: "ideal (I 0) R" by simp
    show ?case
      unfolding a_kernel_def' RDirProd_list_zero canonical_proj_ext_def FactRing_def
      using ideal.rcos_const_imp_mem a_rcos_zero ideal.Icarr I by auto 
  next
    case (Suc n)
    hence I: "ideal (I 0) R" by simp
    have map_simp: "?map_Quot I (Suc n) = (R Quot I 0) # (?map_Quot (\<lambda>i. I (Suc i)) n)"
      by (induct n) (auto)
    have ker_I0: "I 0 = a_kernel R (R Quot (I 0)) (\<lambda>a. (I 0) +> a)"
      using ideal.rcos_const_imp_mem[OF I] a_rcos_zero[OF I] ideal.Icarr[OF I]
      unfolding a_kernel_def' FactRing_def by auto
    hence "?ker I (Suc n) = (?ker (\<lambda>i. I (Suc i)) n) \<inter> (I 0)"
      unfolding a_kernel_def' map_simp RDirProd_list_zero' canonical_proj_ext_tl by auto
    moreover have "?ker (\<lambda>i. I (Suc i)) n = (\<Inter>i \<le> n. I (Suc i))"
      using Suc(1)[of "\<lambda>i. I (Suc i)"] Suc(2) by auto
    ultimately show ?case
      by (auto simp add: INT_extend_simps(10) atMost_atLeast0)
         (metis atLeastAtMost_iff le_zero_eq not_less_eq_eq)
  qed
qed

lemma (in cring) canonical_proj_ext_is_surj:
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R" and "\<And>i j. \<lbrakk> i \<le> n; j \<le> n \<rbrakk> \<Longrightarrow> i \<noteq> j \<Longrightarrow> I i <+> I j = carrier R"
  shows "(canonical_proj_ext I n) ` carrier R = carrier (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))"
  using assms
proof (induct n arbitrary: I)
  case 0 show ?case
    by (auto simp add: RDirProd_list_carrier FactRing_def A_RCOSETS_def')
next
  have aux_lemma: "(\<lambda>a. (f a, g a)) ` carrier R = (f ` carrier R) \<times> (g ` carrier R)"
    if A: "ring T" "f \<in> ring_hom R S" "g \<in> ring_hom R T" "f ` carrier R \<subseteq> f ` (a_kernel R T g)"
    for S :: "'c ring" and T :: "'d ring" and f g
  proof
    show "(\<lambda>a. (f a, g a)) ` carrier R \<subseteq> (f ` carrier R) \<times> (g ` carrier R)"
      by blast
  next
    show "(f ` carrier R) \<times> (g ` carrier R) \<subseteq> (\<lambda>a. (f a, g a)) ` carrier R"
    proof
      fix t assume "t \<in> (f ` carrier R) \<times> (g ` carrier R)"
      then obtain a b where a: "a \<in> carrier R" "f a = fst t" and b: "b \<in> carrier R" "g b = snd t"
        by auto
      obtain c where c: "c \<in> a_kernel R T g" "f c = f (a \<ominus> b)"
        using A(4) minus_closed[OF a(1) b (1)] by auto
      have "f (c \<oplus> b) = f (a \<ominus> b) \<oplus>\<^bsub>S\<^esub>  f b"
        using ring_hom_memE(3)[OF A(2)] b c unfolding a_kernel_def' by auto
      hence "f (c \<oplus> b) = f a"
        using ring_hom_memE(3)[OF A(2) minus_closed[of a b], of b] a b by algebra
      moreover have "g (c \<oplus> b) = g b"
        using ring_hom_memE(1,3)[OF A(3)] b(1) c ring.ring_simprules(8)[OF A(1)]
        unfolding a_kernel_def' by auto
      ultimately have "(\<lambda>a. (f a, g a)) (c \<oplus> b) = t" and "c \<oplus> b \<in> carrier R"
        using a b c unfolding a_kernel_def' by auto
      thus "t \<in> (\<lambda>a. (f a, g a)) ` carrier R"
        by blast
    qed
  qed

  let ?map_Quot = "\<lambda>I n. map (\<lambda>i. R Quot (I i)) [0..< Suc n]"
  let ?DirProd = "\<lambda>I n. RDirProd_list (?map_Quot I n)"
  let ?proj = "\<lambda>I n. canonical_proj_ext I n"

  case (Suc n)
  interpret I: ideal "I 0" R + Inter: ideal "\<Inter>i \<le> n. I (Suc i)" R
    using i_Intersect[of "(\<lambda>i. I (Suc i)) ` {..n}"] Suc(2) by auto

  have map_simp: "?map_Quot I (Suc n) = (R Quot I 0) # (?map_Quot (\<lambda>i. I (Suc i)) n)"
    by (induct n) (auto)

  have IH: "(?proj (\<lambda>i. I (Suc i)) n) ` carrier R = carrier (?DirProd (\<lambda>i. I (Suc i)) n)"
   and ring: "ring (?DirProd (\<lambda>i. I (Suc i)) n)"
   and hom: "?proj (\<lambda>i. I (Suc i)) n \<in> ring_hom R (?DirProd (\<lambda>i. I (Suc i)) n)"
    using RDirProd_Quot_list_is_ring[of n "\<lambda>i. I (Suc i)"] Suc(1)[of "\<lambda>i. I (Suc i)"]
           canonical_proj_ext_is_hom[of n "\<lambda>i. I (Suc i)"] Suc(2-3) by auto

  have ker: "a_kernel R (?DirProd (\<lambda>i. I (Suc i)) n) (?proj (\<lambda>i. I (Suc i)) n) = (\<Inter>i \<le> n. I (Suc i))"
    using canonical_proj_ext_ker[of n "\<lambda>i. I (Suc i)"] Suc(2) by auto
  have carrier_Quot: "carrier (R Quot (I 0)) = (\<lambda>a. (I 0) +> a) ` carrier R"
    by (auto simp add: RDirProd_list_carrier FactRing_def A_RCOSETS_def')
  have ring: "ring (?DirProd (\<lambda>i. I (Suc i)) n)"
   and hom: "?proj (\<lambda>i. I (Suc i)) n \<in> ring_hom R (?DirProd (\<lambda>i. I (Suc i)) n)"
    using RDirProd_Quot_list_is_ring[of n "\<lambda>i. I (Suc i)"]
          canonical_proj_ext_is_hom[of n "\<lambda>i. I (Suc i)"] Suc(2) by auto
  have "carrier (R Quot (I 0)) \<subseteq> (\<lambda>a. (I 0) +> a) ` (\<Inter>i \<le> n. I (Suc i))"
  proof
    have "(\<Inter>i \<in> {Suc 0.. Suc n}. I i) <+> (I 0) = carrier R"
      using inter_plus_ideal_eq_carrier_arbitrary[of n I 0]
      by (simp add: Suc(2-3) atLeast1_atMost_eq_remove0)
    hence eq_carrier: "(I 0) <+> (\<Inter>i \<le> n. I (Suc i)) = carrier R"
      using set_add_comm[OF I.a_subset Inter.a_subset]
      by (metis INT_extend_simps(10) atMost_atLeast0 image_Suc_atLeastAtMost)

    fix b assume "b \<in> carrier (R Quot (I 0))"
    hence "(b, (\<Inter>i \<le> n. I (Suc i))) \<in> carrier (R Quot I 0) \<times> carrier (R Quot (\<Inter>i\<le>n. I (Suc i)))"
      using ring.ring_simprules(2)[OF Inter.quotient_is_ring] by (simp add: FactRing_def)
    then obtain s
      where "s \<in> carrier R" "(canonical_proj (I 0) (\<Inter>i \<le> n. I (Suc i))) s = (b, (\<Inter>i \<le> n. I (Suc i)))"
      using canonical_proj_is_surj[OF I.is_ideal Inter.is_ideal eq_carrier]
      unfolding RDirProd_carrier by (metis (no_types, lifting) imageE)
    hence "s \<in> (\<Inter>i \<le> n. I (Suc i))" and "(\<lambda>a. (I 0) +> a) s = b"
      using Inter.rcos_const_imp_mem by auto
    thus "b \<in> (\<lambda>a. (I 0) +> a) ` (\<Inter>i \<le> n. I (Suc i))"
      by auto
  qed
  hence "(\<lambda>a. ((I 0) +> a, ?proj (\<lambda>i. I (Suc i)) n a)) ` carrier R =
         carrier (R Quot (I 0)) \<times> carrier (?DirProd (\<lambda>i. I (Suc i)) n)"
    using aux_lemma[OF ring I.rcos_ring_hom hom] unfolding carrier_Quot ker IH by simp
  moreover show ?case
    unfolding map_simp RDirProd_list_carrier sym[OF calculation(1)] canonical_proj_ext_tl by auto 
qed

theorem (in cring) chinese_remainder:
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R" and "\<And>i j. \<lbrakk> i \<le> n; j \<le> n \<rbrakk> \<Longrightarrow> i \<noteq> j \<Longrightarrow> I i <+> I j = carrier R"
  shows "R Quot (\<Inter>i \<le> n. I i) \<simeq> RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])"
  using ring_hom_ring.FactRing_iso[OF canonical_proj_ext_ring_hom, of n I]
        canonical_proj_ext_is_surj[of n I] canonical_proj_ext_ker[of n I] assms
  by auto

end
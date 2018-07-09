(*  Title:      HOL/Algebra/Chinese_Remainder.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Chinese_Remainder
  imports QuotRing Ideal_Product
begin

section \<open>Chinese Remainder Theorem\<close>

subsection \<open>Direct Product of Rings\<close>

definition
  RDirProd :: "[ ('a, 'n) ring_scheme, ('b, 'm) ring_scheme ]  \<Rightarrow> ('a \<times> 'b) ring"
  where "RDirProd R S =
           \<lparr> carrier = carrier R \<times> carrier S,
                mult = (\<lambda>(r, s). \<lambda>(r', s'). (r \<otimes>\<^bsub>R\<^esub> r', s \<otimes>\<^bsub>S\<^esub> s')),
                 one = (\<one>\<^bsub>R\<^esub>, \<one>\<^bsub>S\<^esub>),
                zero = (\<zero>\<^bsub>R\<^esub>, \<zero>\<^bsub>S\<^esub>),
                 add = (\<lambda>(r, s). \<lambda>(r', s'). (r \<oplus>\<^bsub>R\<^esub> r', s \<oplus>\<^bsub>S\<^esub> s')) \<rparr>"

lemma RDirProd_monoid:
  assumes "ring R" and "ring S"
  shows "monoid (RDirProd R S)"
  by (rule monoidI) (auto simp add: RDirProd_def assms ring.ring_simprules ring.is_monoid)

lemma RDirProd_abelian_group:
  assumes "ring R" and "ring S"
  shows "abelian_group (RDirProd R S)"
  by (auto intro!: abelian_groupI
         simp add: RDirProd_def assms ring.ring_simprules)
     (meson assms ring.ring_simprules(3,16))+

lemma RDirProd_group:
  assumes "ring R" and "ring S"
  shows "ring (RDirProd R S)"
proof -
  show ?thesis
    apply (rule ringI)
    apply (simp_all add: assms RDirProd_abelian_group RDirProd_monoid)
    by (auto simp add: RDirProd_def assms ring.ring_simprules)
qed

lemma RDirProd_isomorphism1:
  "(\<lambda>(x, y). (y, x)) \<in> ring_iso (RDirProd R S) (RDirProd S R)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def by auto

lemma RDirProd_isomorphism2:
  "(\<lambda>(x, (y, z)). ((x, y), z)) \<in> ring_iso (RDirProd R (RDirProd S T)) (RDirProd (RDirProd R S) T)"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
  by (auto simp add: image_iff)

lemma RDirProd_isomorphism3:
  "(\<lambda>((x, y), z). (x, (y, z))) \<in> ring_iso (RDirProd (RDirProd R S) T) (RDirProd R (RDirProd S T))"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
  by (auto simp add: image_iff)

lemma RDirProd_isomorphism4:
  assumes "f \<in> ring_iso R S"
  shows "(\<lambda>(r, t). (f r, t)) \<in> ring_iso (RDirProd R T) (RDirProd S T)"
  using assms unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
  by (auto simp add: image_iff)+

lemma RDirProd_isomorphism5:
  assumes "f \<in> ring_iso S T"
  shows "(\<lambda>(r, s). (r, f s)) \<in> ring_iso (RDirProd R S) (RDirProd R T)"
  using ring_iso_set_trans[OF ring_iso_set_trans[OF RDirProd_isomorphism1[of R S]
                                                    RDirProd_isomorphism4[OF assms, of R]]
                              RDirProd_isomorphism1[of T R]]
  by (simp add: case_prod_unfold case_prod_unfold comp_def comp_def)

lemma RDirProd_isomorphism6:
  assumes "f \<in> ring_iso R R'" and "g \<in> ring_iso S S'"
  shows "(\<lambda>(r, s). (f r, g s)) \<in> ring_iso (RDirProd R S) (RDirProd R' S')"
  using ring_iso_set_trans[OF RDirProd_isomorphism4[OF assms(1)] RDirProd_isomorphism5[OF assms(2)]]
  by (simp add: case_prod_beta' comp_def)


subsection \<open>Simple Version of The Theorem\<close>

text \<open>We start by proving a simpler version of the theorem. The rest of the theory is
      dedicated to its generalization\<close>

lemma (in ideal) set_add_zero:
  assumes "i \<in> I"
  shows "I +> i = I"
  by (simp add: a_rcos_const assms)

lemma (in ideal) set_add_zero_imp_mem:
  assumes "i \<in> carrier R" "I +> i = I"
  shows "i \<in> I"
  using a_rcos_self assms(1-2) by auto

lemma (in ring) canonical_proj_is_surj:
  assumes "ideal I R" "ideal J R" "I <+> J = carrier R"
  shows "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow>
                 \<exists>a \<in> carrier R. I +> a = I +> x \<and> J +> a = J +> y"
proof -
  { fix I J i j assume A: "ideal I R" "ideal J R" "i \<in> I" "j \<in> J" "\<one> = i \<oplus> j"
    have "I +> \<one> = I +> j"
    proof -
      have "I +> \<one> = I +> (i \<oplus> j)" using A(5) by simp
      also have " ... = (I +> i) <+> (I +> j)"
        by (metis abelian_subgroup.a_rcos_sum abelian_subgroupI3 A(1-4)
            ideal.Icarr ideal.axioms(1) is_abelian_group)
      also have " ... = (I +> \<zero>) <+> (I +> j)"
        using ideal.set_add_zero[OF A(1) A(3)]
        by (simp add: A(1) additive_subgroup.a_subset ideal.axioms(1)) 
      also have " ... = I +> (\<zero> \<oplus> j)"
        by (meson A abelian_subgroup.a_rcos_sum abelian_subgroupI3
            additive_subgroup.a_Hcarr ideal.axioms(1) is_abelian_group zero_closed)
      finally show "I +> \<one> = I +> j"
        using A(2) A(4) ideal.Icarr by fastforce
    qed } note aux_lemma = this
  
  fix x y assume x: "x \<in> carrier R" and y: "y \<in> carrier R"
  
  have "\<one> \<in> I <+> J" using assms by simp
  then obtain i j where i: "i \<in> I" and j: "j \<in> J" and ij: "\<one> = i \<oplus> j"
    using set_add_def'[of R I J] by auto
  have mod_I: "I +> j = I +> \<one>" and mod_J: "J +> i = J +> \<one>"
    using aux_lemma[OF assms(1-2) i j ij] apply simp
    using aux_lemma[OF assms(2) assms(1) j i] ij
    by (metis add.m_comm assms(1) assms(2) i ideal.Icarr j)

  have "I +> ((j \<otimes> x) \<oplus> (i \<otimes> y)) = (I +> (j \<otimes> x)) <+> (I +> (i \<otimes> y))"
    by (metis abelian_subgroup.a_rcos_sum abelian_subgroupI3 assms i ideal.Icarr
        ideal.axioms(1) is_abelian_group j m_closed x y)
  also have " ... = (I +> (j \<otimes> x)) <+> (I +> \<zero>)"
    using ideal.set_add_zero[OF assms(1), of "i \<otimes> y"] i assms(1)
    by (simp add: additive_subgroup.a_subset ideal.I_r_closed ideal.axioms(1) y)
  also have " ... = I +> (j \<otimes> x)"
    by (metis abelian_subgroup.a_rcos_sum abelian_subgroupI3 additive_subgroup.a_Hcarr assms(1-2)
        ideal.axioms(1) is_abelian_group j m_closed r_zero x zero_closed)
  finally have Ix: "I +> ((j \<otimes> x) \<oplus> (i \<otimes> y)) = I +> x" using mod_I
    by (metis (full_types) assms ideal.Icarr ideal.rcoset_mult_add is_monoid j monoid.l_one one_closed x)
  have "J +> ((j \<otimes> x) \<oplus> (i \<otimes> y)) = (J +> (j \<otimes> x)) <+> (J +> (i \<otimes> y))"
    by (metis abelian_subgroup.a_rcos_sum abelian_subgroupI3 assms i ideal.Icarr
        ideal.axioms(1) is_abelian_group j m_closed x y)
  also have " ... = (J +> \<zero>) <+> (J +> (i \<otimes> y))"
    using ideal.set_add_zero[OF assms(2), of "j \<otimes> x"] j assms(2)
    by (simp add: additive_subgroup.a_subset ideal.I_r_closed ideal.axioms(1) x)
  also have " ... = J +> (i \<otimes> y)"
    by (metis a_coset_add_zero a_rcosetsI abelian_subgroup.rcosets_add_eq abelian_subgroupI3
        additive_subgroup.a_Hcarr additive_subgroup.a_subset assms i ideal.axioms(1)
        is_abelian_group m_closed y)
  finally have Jy: "J +> ((j \<otimes> x) \<oplus> (i \<otimes> y)) = J +> y" using mod_J
    by (metis (full_types) assms i ideal.Icarr ideal.rcoset_mult_add local.semiring_axioms one_closed semiring.semiring_simprules(9) y)  
  have "(j \<otimes> x) \<oplus> (i \<otimes> y) \<in> carrier R"
    by (meson x y i j assms add.m_closed additive_subgroup.a_Hcarr ideal.axioms(1) m_closed)
  thus "\<exists>a \<in> carrier R. I +> a = I +> x \<and> J +> a = J +> y" using Ix Jy by blast
qed

lemma (in ring) canonical_proj_is_hom:
  assumes "ideal I R" "ideal J R" "I <+> J = carrier R"
  shows "(\<lambda>a. (I +> a, J +> a)) \<in> ring_hom R (RDirProd (R Quot I) (R Quot J))"
proof (rule ring_hom_memI)
  fix x y assume x: "x \<in> carrier R" and y: "y \<in> carrier R"
  show "(I +> x, J +> x) \<in> carrier (RDirProd (R Quot I) (R Quot J))"
    using A_RCOSETS_def'[of R I] A_RCOSETS_def'[of R J] x
    unfolding RDirProd_def FactRing_def by auto
  show "(I +> x \<otimes> y, J +> x \<otimes> y) =
        (I +> x, J +> x) \<otimes>\<^bsub>RDirProd (R Quot I) (R Quot J)\<^esub> (I +> y, J +> y)"
    unfolding RDirProd_def FactRing_def by (simp add: assms ideal.rcoset_mult_add x y)
  show "(I +> x \<oplus> y, J +> x \<oplus> y) =
        (I +> x, J +> x) \<oplus>\<^bsub>RDirProd (R Quot I) (R Quot J)\<^esub> (I +> y, J +> y)"
    unfolding RDirProd_def FactRing_def
    by (simp add: abelian_subgroup.a_rcos_sum abelian_subgroupI3 assms ideal.axioms(1) is_abelian_group x y)
next
  show "(I +> \<one>, J +> \<one>) = \<one>\<^bsub>RDirProd (R Quot I) (R Quot J)\<^esub>"
    unfolding RDirProd_def FactRing_def by simp
qed

theorem (in ring) chinese_remainder_simple:
  assumes "ideal I R" "ideal J R" "I <+> J = carrier R"
  shows "(R Quot (I \<inter> J)) \<simeq> (RDirProd (R Quot I) (R Quot J))"
proof -
  let ?\<phi> = "\<lambda>a. (I +> a, J +> a)"

  have phi_hom: "?\<phi> \<in> ring_hom R (RDirProd (R Quot I) (R Quot J))"
    using canonical_proj_is_hom[OF assms] .

  moreover have "?\<phi> ` (carrier R) = carrier (RDirProd (R Quot I) (R Quot J))"
  proof
    show "carrier (RDirProd (R Quot I) (R Quot J)) \<subseteq> ?\<phi> ` (carrier R)"
    proof
      fix t assume "t \<in> carrier (RDirProd (R Quot I) (R Quot J))"
      then obtain x y where x: "x \<in> carrier R" and y: "y \<in> carrier R"
                        and t: "t = (I +> x, J +> y)"
        using A_RCOSETS_def'[of R I] A_RCOSETS_def'[of R J]
        unfolding RDirProd_def FactRing_def by auto
      then obtain a where "a \<in> carrier R" "I +> a = I +> x" "J +> a = J +> y"
        using canonical_proj_is_surj[OF assms x y] by blast
      hence "?\<phi> a = t" using t by simp
      thus "t \<in> (?\<phi> ` carrier R)" using \<open>a \<in> carrier R\<close> by blast
    qed
  next
    show "?\<phi> ` carrier R \<subseteq> carrier (RDirProd (R Quot I) (R Quot J))"
      using phi_hom unfolding ring_hom_def by blast
  qed

  moreover have "a_kernel R (RDirProd (R Quot I) (R Quot J)) ?\<phi> = I \<inter> J"
  proof
    show "I \<inter> J \<subseteq> a_kernel R (RDirProd (R Quot I) (R Quot J)) ?\<phi>"
    proof
      fix s assume s: "s \<in> I \<inter> J" hence "I +> s = I \<and> J +> s = J"
        by (simp add: additive_subgroup.zero_closed assms ideal.axioms(1) ideal.set_add_zero)
      thus "s \<in> a_kernel R (RDirProd (R Quot I) (R Quot J)) ?\<phi>"
        unfolding FactRing_def RDirProd_def a_kernel_def kernel_def
        using s additive_subgroup.a_Hcarr assms(1) ideal.axioms(1) by fastforce
    qed
  next
    show "a_kernel R (RDirProd (R Quot I) (R Quot J)) ?\<phi> \<subseteq> I \<inter> J"
    unfolding FactRing_def RDirProd_def a_kernel_def kernel_def apply simp
    using ideal.set_add_zero_imp_mem assms(1-2) by fastforce
  qed

  moreover have "ring (RDirProd (R Quot I) (R Quot J))"
    by (simp add: RDirProd_group assms(1) assms(2) ideal.quotient_is_ring) 

  ultimately show ?thesis
    using ring_hom_ring.FactRing_iso[of R "RDirProd (R Quot I) (R Quot J)" ?\<phi>] is_ring
    by (simp add: ring_hom_ringI2)
qed


subsection \<open>First Generalization - The Extended Canonical Projection is Surjective\<close>

lemma (in cring) canonical_proj_ext_is_surj:
  fixes n::nat
  assumes "\<And>i. i \<le> n \<Longrightarrow> x i \<in> carrier R"
      and "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R"
      and "\<And>i j. \<lbrakk> i \<le> n; j \<le> n; i \<noteq> j \<rbrakk> \<Longrightarrow> I i <+> I j = carrier R"
    shows "\<exists> a \<in> carrier R. \<forall> i \<le> n. (I i) +> a = (I i) +> (x i)" using assms
proof (induct n)
  case 0 thus ?case by blast 
next
  case (Suc n)
  then obtain a where a: "a \<in> carrier R" "\<And>i. i \<le> n \<Longrightarrow> (I i) +> a = (I i) +> (x i)"
    by force
  
  have inter_is_ideal: "ideal (\<Inter> i \<le> n. I i) R"
    by (metis (mono_tags, lifting) Suc.prems(2) atMost_iff i_Intersect imageE image_is_empty le_SucI not_empty_eq_Iic_eq_empty)
  have "(\<Inter> i \<le> n. I i) <+> I (Suc n) = carrier R"
    using inter_plus_ideal_eq_carrier Suc by simp
  then obtain b where b: "b \<in> carrier R"
                  and "(\<Inter> i \<le> n. I i) +> b = (\<Inter> i \<le> n. I i) +> \<zero>"
                  and S: "I (Suc n) +> b = I (Suc n) +> (x (Suc n) \<ominus> a)"
    using canonical_proj_is_surj[OF inter_is_ideal, of "I (Suc n)" \<zero> "x (Suc n) \<ominus> a"] Suc a by auto
  hence b_inter: "b \<in> (\<Inter> i \<le> n. I i)"
    using ideal.set_add_zero_imp_mem[OF inter_is_ideal b]
    by (metis additive_subgroup.zero_closed ideal.axioms(1) ideal.set_add_zero inter_is_ideal)
  hence eq_zero: "\<And>i. i \<le> n \<Longrightarrow> (I i) +> b = (I i) +> \<zero>"
  proof -
    fix i assume i: "i \<le> n"
    hence "b \<in> I i" using  b_inter by blast
    moreover have "ideal (I i) R" using Suc i by simp 
    ultimately show "(I i) +> b = (I i) +> \<zero>"
      by (metis b ideal.I_r_closed ideal.set_add_zero r_null zero_closed)
  qed
  
  have "(I i) +> (a \<oplus> b) = (I i) +> (x i)" if "i \<le> Suc n" for i
  proof -
    show "(I i) +> (a \<oplus> b) = (I i) +> (x i)"
      using that
    proof (cases)
      assume 1: "i \<le> n"
      hence "(I i) +> (a \<oplus> b) = ((I i) +> (x i)) <+> ((I i) +> b)"
        by (metis Suc.prems(2) a abelian_subgroup.a_rcos_sum abelian_subgroupI3 b ideal_def le_SucI ring_def)
      also have " ... = ((I i) +> (x i)) <+> ((I i) +> \<zero>)"
        using eq_zero[OF 1] by simp
      also have " ... = I i +> ((x i) \<oplus> \<zero>)"
        by (meson Suc.prems abelian_subgroup.a_rcos_sum abelian_subgroupI3 atMost_iff that ideal_def ring_def zero_closed)
      finally show "(I i) +> (a \<oplus> b) = (I i) +> (x i)"
        using Suc.prems(1) that by auto
    next
      assume "\<not> i \<le> n" hence 2: "i = Suc n" using that by simp
      hence "I i +> (a \<oplus> b) = I (Suc n) +> (a \<oplus> b)" by simp
      also have " ... = (I (Suc n) +> a) <+> (I (Suc n) +> (x (Suc n) \<ominus> a))"
        by (metis le_Suc_eq S a b Suc.prems(2)[of "Suc n"] 2 abelian_subgroup.a_rcos_sum
              abelian_subgroupI3 ideal.axioms(1) is_abelian_group)
      also have " ... = I (Suc n) +> (a \<oplus> (x (Suc n) \<ominus> a))"
        by (simp add: Suc.prems(1-2) a(1) abelian_subgroup.a_rcos_sum
                      abelian_subgroupI3 ideal.axioms(1) is_abelian_group)
      also have " ... = I (Suc n) +> (x (Suc n))"
        using a(1) Suc.prems(1)[of "Suc n"] abelian_group.minus_eq
              abelian_group.r_neg add.m_lcomm is_abelian_group by fastforce
      finally show "I i +> (a \<oplus> b) = (I i) +> (x i)" using 2 by simp
    qed
  qed
  thus ?case using a b by auto
qed


subsection \<open>Direct Product of a List of Monoid Structures\<close>

fun DirProd_list :: "(('a, 'b) monoid_scheme) list \<Rightarrow> (('a list), 'b) monoid_scheme"
  where
    "DirProd_list [] = \<lparr> carrier = {[]}, mult = (\<lambda>a b. []), one = [], \<dots> = (undefined :: 'b) \<rparr>"
  | "DirProd_list (Cons R Rs) =
      \<lparr> carrier = { r # rs | r rs. r \<in> carrier R \<and> rs \<in> carrier (DirProd_list Rs) },
           mult = (\<lambda>r1 r2. ((hd r1) \<otimes>\<^bsub>R\<^esub> (hd r2)) # ((tl r1) \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> (tl r2))),
            one = (\<one>\<^bsub>R\<^esub>) # (\<one>\<^bsub>(DirProd_list Rs)\<^esub>), \<dots> = (undefined :: 'b) \<rparr>"


lemma DirProd_list_carrier_elts:
  assumes "rs \<in> carrier (DirProd_list Rs)"
    shows "length rs = length Rs" using assms
proof (induct Rs arbitrary: rs rule: DirProd_list.induct)
  case 1 thus ?case by simp
next
  case (2 R Rs)
  then obtain r' rs' where "r' \<in> carrier R" "rs' \<in> carrier (DirProd_list Rs)"
                       and "rs = r' # rs'" by auto
  thus ?case by (simp add: "2.hyps"(1))
qed

lemma DirProd_list_in_carrierI:
  assumes "\<And>i. i < length rs \<Longrightarrow> rs ! i \<in> carrier (Rs ! i)"
    and "length rs = length Rs"
  shows "rs \<in> carrier (DirProd_list Rs)" using assms
proof (induct Rs arbitrary: rs rule: DirProd_list.induct)
  case 1 thus ?case by simp
next
  case (2 R Rs)
  then obtain r' rs' where rs: "r' \<in> carrier R" "rs = r' # rs'"
    by (metis Suc_length_conv lessThan_iff nth_Cons_0 zero_less_Suc)
  hence "rs' \<in> carrier (DirProd_list Rs)"
    using "2.hyps"(1) "2.prems"(1) "2.prems"(2) by force
  thus ?case by (simp add: rs)
qed

lemma DirProd_list_in_carrierE:
  assumes "rs \<in> carrier (DirProd_list Rs)"
  shows "\<And>i. i < length rs \<Longrightarrow> rs ! i \<in> carrier (Rs ! i)" using assms
proof (induct Rs arbitrary: rs rule: DirProd_list.induct)
  case 1 thus ?case by simp 
next
  case (2 R Rs)
  then obtain r' rs' where  r': " r' \<in> carrier R"
                       and rs': "rs' \<in> carrier (DirProd_list Rs)"
                       and  rs: "rs = r' # rs'" by auto
  hence "\<And>i. i \<in> {..<(length rs')} \<Longrightarrow> rs' ! i \<in> carrier (Rs ! i)"
    using "2.hyps"(1) by blast
  hence "\<And>i. i \<in> {(Suc 0 :: nat)..<(length rs)} \<Longrightarrow> rs ! i \<in> carrier ((R # Rs) ! i)"
    by (simp add: less_eq_Suc_le rs)
  moreover have "i = 0 \<Longrightarrow> rs ! i \<in> carrier ((R # Rs) ! i)"
    using r' rs r' by simp
  ultimately show ?case
    using "2.prems"(1) by fastforce   
qed

lemma DirProd_list_m_closed:
  assumes "r1 \<in> carrier (DirProd_list Rs)" "r2 \<in> carrier (DirProd_list Rs)"
    and "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r2 \<in> carrier (DirProd_list Rs)" using assms
proof (induct Rs arbitrary: r1 r2 rule: DirProd_list.induct)
  case 1 thus ?case by simp 
next
  case (2 R Rs)
  then obtain r1' rs1' r2' rs2'
    where r12': "r1' \<in> carrier R" "r2' \<in> carrier R"
      and "rs1' \<in> carrier (DirProd_list Rs)"
      and "rs2' \<in> carrier (DirProd_list Rs)"
      and r1: "r1 = r1' # rs1'"
      and r2: "r2 = r2' # rs2'" by auto
  moreover have "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
    using "2.prems"(3) by force
  ultimately have "rs1' \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> rs2' \<in> carrier (DirProd_list Rs)"
    using "2.hyps"(1) by blast
  moreover have "monoid R"
    using "2.prems"(3) by force
  hence "r1' \<otimes>\<^bsub>R\<^esub> r2' \<in> carrier R"
    by (simp add: r12' monoid.m_closed)
  ultimately show ?case by (simp add: r1 r2)
qed

lemma DirProd_list_m_output:
  assumes "r1 \<in> carrier (DirProd_list Rs)" "r2 \<in> carrier (DirProd_list Rs)"
  shows "\<And>i. i < length Rs \<Longrightarrow>
             (r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r2) ! i = (r1 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r2 ! i)" using assms
proof (induct Rs arbitrary: r1 r2 rule: DirProd_list.induct)
  case 1 thus ?case by simp 
next
  case (2 R Rs)
  hence "\<And>i. i \<in> {(Suc 0)..<(length (R # Rs))} \<Longrightarrow>
             (r1 \<otimes>\<^bsub>(DirProd_list (R # Rs))\<^esub> r2) ! i = (r1 ! i) \<otimes>\<^bsub>((R # Rs) ! i)\<^esub> (r2 ! i)"
    using "2"(5) "2"(6) by auto
  moreover have "(r1 \<otimes>\<^bsub>(DirProd_list (R # Rs))\<^esub> r2) ! 0 = (r1 ! 0) \<otimes>\<^bsub>R\<^esub> (r2 ! 0)"
    using "2.prems"(2) "2.prems"(3) by auto
  ultimately show ?case
    by (metis "2.prems"(1) atLeastLessThan_iff le_0_eq lessThan_iff not_less_eq_eq nth_Cons')  
qed

lemma DirProd_list_m_comm:
  assumes "r1 \<in> carrier (DirProd_list Rs)" "r2 \<in> carrier (DirProd_list Rs)"
    and "\<And>i. i < length Rs \<Longrightarrow> comm_monoid (Rs ! i)"
  shows "r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r2 = r2 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r1"
  apply (rule nth_equalityI) apply auto
proof -
  show "length (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2) = length (r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1)"
    by (metis DirProd_list_carrier_elts DirProd_list_m_closed Group.comm_monoid.axioms(1) assms)

  fix i assume "i < length (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2)"
  hence i: "i < length Rs"
    by (metis DirProd_list_carrier_elts DirProd_list_m_closed Group.comm_monoid.axioms(1) assms)
  have "(r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2) ! i = (r1 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r2 ! i)"
    using i DirProd_list_m_output[OF assms(1-2)] by simp
  also have " ... = (r2 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r1 ! i)"
    by (metis DirProd_list_carrier_elts DirProd_list_in_carrierE assms comm_monoid.m_comm i lessThan_iff)
  also have " ... = (r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) ! i"
    using i DirProd_list_m_output[OF assms(2) assms(1)] by simp
  finally show "(r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2) ! i = (r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) ! i" .
qed

lemma DirProd_list_m_assoc:
  assumes "r1 \<in> carrier (DirProd_list Rs)"
      and "r2 \<in> carrier (DirProd_list Rs)"
      and "r3 \<in> carrier (DirProd_list Rs)"
      and "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "(r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r2) \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r3 =
          r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> (r2 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r3)"
  apply (rule nth_equalityI) apply auto
proof -
  show "length ((r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2) \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3) =
         length (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> (r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3))"
    by (metis DirProd_list_carrier_elts DirProd_list_m_closed assms)

  fix i assume "i < length (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3)"
  hence i: "i < length Rs"
    by (metis DirProd_list_carrier_elts DirProd_list_m_closed assms)
  have "((r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2) \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3) ! i =
        ((r1 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r2 ! i)) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r3 ! i)"
    by (metis DirProd_list_m_closed DirProd_list_m_output i assms lessThan_iff)
  also have " ... = (r1 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> ((r2 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r3 ! i))"
    by (metis DirProd_list_carrier_elts DirProd_list_in_carrierE assms i lessThan_iff monoid.m_assoc)
  also have " ... = (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> (r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3)) ! i"
    by (metis DirProd_list_m_closed DirProd_list_m_output i assms lessThan_iff)
  finally show "((r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r2) \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3) ! i =
                 (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> (r2 \<otimes>\<^bsub>DirProd_list Rs\<^esub> r3))! i" .
qed

lemma DirProd_list_one:
  "\<And>i. i < length Rs \<Longrightarrow> (\<one>\<^bsub>(DirProd_list Rs)\<^esub>) ! i =  \<one>\<^bsub>(Rs ! i)\<^esub>"
  by (induct Rs rule: DirProd_list.induct) (simp_all add: nth_Cons')

lemma DirProd_list_one_closed:
  assumes "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "\<one>\<^bsub>(DirProd_list Rs)\<^esub> \<in> carrier (DirProd_list Rs)"
proof (rule DirProd_list_in_carrierI)
  show eq_len: "length \<one>\<^bsub>DirProd_list Rs\<^esub> = length Rs"
    by (induct Rs rule: DirProd_list.induct) (simp_all)
  show "\<And>i. i < length \<one>\<^bsub>DirProd_list Rs\<^esub> \<Longrightarrow> \<one>\<^bsub>DirProd_list Rs\<^esub> ! i \<in> carrier (Rs ! i)"
    using eq_len DirProd_list_one[where ?Rs = Rs] monoid.one_closed by (simp add: assms)
qed

lemma DirProd_list_l_one:
  assumes "r1 \<in> carrier (DirProd_list Rs)"
    and "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "\<one>\<^bsub>(DirProd_list Rs)\<^esub> \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r1 = r1"
  apply (rule nth_equalityI) apply auto
proof -
  show eq_len: "length (\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) = length r1"
    using DirProd_list_carrier_elts[of "\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1" Rs]
          DirProd_list_carrier_elts[OF assms(1)]
          DirProd_list_m_closed[OF DirProd_list_one_closed[OF assms(2)] assms(1)]
    by (simp add: assms)
  fix i assume "i < length (\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1)"
  hence i: "i < length Rs" using DirProd_list_carrier_elts[OF assms(1)] eq_len by simp
  hence "(\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) ! i =
         (\<one>\<^bsub>DirProd_list Rs\<^esub> ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r1 ! i)"
    using DirProd_list_m_output DirProd_list_one_closed assms by blast
  also have " ... = \<one>\<^bsub>(Rs ! i)\<^esub> \<otimes>\<^bsub>(Rs ! i)\<^esub> (r1 ! i)"
    by (simp add: DirProd_list_one i)
  also have " ... = (r1 ! i)"
    using DirProd_list_carrier_elts DirProd_list_in_carrierE i assms by fastforce
  finally show "(\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) ! i = (r1 ! i)" .
qed

lemma DirProd_list_r_one:
  assumes "r1 \<in> carrier (DirProd_list Rs)"
    and "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> \<one>\<^bsub>(DirProd_list Rs)\<^esub> = r1"
proof -
  have "r1 \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> \<one>\<^bsub>(DirProd_list Rs)\<^esub> =
           \<one>\<^bsub>(DirProd_list Rs)\<^esub> \<otimes>\<^bsub>(DirProd_list Rs)\<^esub> r1"
    apply (rule nth_equalityI) apply auto
  proof -
    show " length (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> \<one>\<^bsub>DirProd_list Rs\<^esub>) =
           length (\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1)"
      by (metis DirProd_list_carrier_elts DirProd_list_m_closed DirProd_list_one_closed assms)

    fix i assume "i < length (r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> \<one>\<^bsub>DirProd_list Rs\<^esub>)"
    hence i: "i < length Rs"
      by (metis DirProd_list_carrier_elts DirProd_list_m_closed DirProd_list_one_closed assms)
    hence "(r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> \<one>\<^bsub>DirProd_list Rs\<^esub>) ! i = (r1 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> \<one>\<^bsub>(Rs ! i)\<^esub>"
      by (metis DirProd_list_m_output DirProd_list_one DirProd_list_one_closed assms lessThan_iff)
    also have " ... =  \<one>\<^bsub>(Rs ! i)\<^esub> \<otimes>\<^bsub>(Rs ! i)\<^esub> (r1 ! i)"
      using DirProd_list_carrier_elts DirProd_list_in_carrierE assms i by fastforce
    also have " ... = (\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) ! i"
      by (metis DirProd_list_m_output DirProd_list_one DirProd_list_one_closed assms i lessThan_iff)
    finally show "(r1 \<otimes>\<^bsub>DirProd_list Rs\<^esub> \<one>\<^bsub>DirProd_list Rs\<^esub>) ! i =
                  (\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> r1) ! i" .
  qed
  thus ?thesis using DirProd_list_l_one assms by auto
qed

lemma DirProd_list_monoid:
  assumes "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "monoid (DirProd_list Rs)"
  unfolding monoid_def apply auto
proof -
  show "\<one>\<^bsub>DirProd_list Rs\<^esub> \<in> carrier (DirProd_list Rs)"
    using DirProd_list_one_closed[of Rs] assms by simp

  fix x y z
  assume x: "x \<in> carrier (DirProd_list Rs)"
     and y: "y \<in> carrier (DirProd_list Rs)"
     and z: "z \<in> carrier (DirProd_list Rs)"
  show "x \<otimes>\<^bsub>DirProd_list Rs\<^esub> y \<in> carrier (DirProd_list Rs)"
    using DirProd_list_m_closed[OF x y] assms by simp
  show "x \<otimes>\<^bsub>DirProd_list Rs\<^esub>  y \<otimes>\<^bsub>DirProd_list Rs\<^esub> z =
        x \<otimes>\<^bsub>DirProd_list Rs\<^esub> (y \<otimes>\<^bsub>DirProd_list Rs\<^esub> z)"
    using DirProd_list_m_assoc[OF x y z] assms by simp
  show "\<one>\<^bsub>DirProd_list Rs\<^esub> \<otimes>\<^bsub>DirProd_list Rs\<^esub> x = x"
    using DirProd_list_l_one[OF x] assms by simp
  show "x \<otimes>\<^bsub>DirProd_list Rs\<^esub> \<one>\<^bsub>DirProd_list Rs\<^esub> = x"
    using DirProd_list_r_one[OF x] assms by simp
qed

lemma DirProd_list_comm_monoid:
  assumes "\<And>i. i < length Rs \<Longrightarrow> comm_monoid (Rs ! i)"
  shows "comm_monoid (DirProd_list Rs)"
  unfolding comm_monoid_def comm_monoid_axioms_def apply auto
  using DirProd_list_monoid Group.comm_monoid.axioms(1) assms apply blast
  using DirProd_list_m_comm assms by blast

lemma DirProd_list_isomorphism1:
  "(\<lambda>(hd, tl). hd # tl) \<in> iso (R \<times>\<times> (DirProd_list Rs)) (DirProd_list (R # Rs))"
  unfolding iso_def hom_def bij_betw_def inj_on_def by auto

lemma DirProd_list_isomorphism2:
  "(\<lambda>r. (hd r, tl r)) \<in> iso (DirProd_list (R # Rs)) (R \<times>\<times> (DirProd_list Rs))" (is "?\<phi> \<in> ?A")
  unfolding iso_def hom_def bij_betw_def inj_on_def apply auto
proof -
  fix a b assume "a \<in> carrier R" "b \<in> carrier (DirProd_list Rs)"
  hence "a # b \<in> {r # rs |r rs. r \<in> carrier R \<and> rs \<in> carrier (DirProd_list Rs)} \<and> ?\<phi> (a # b) = (a, b)"
    by simp
  thus "(a, b) \<in> ?\<phi> ` {r # rs |r rs. r \<in> carrier R \<and> rs \<in> carrier (DirProd_list Rs)}"
    by (metis (no_types, lifting) image_iff)
qed

lemma DirProd_list_group:
  assumes "\<And>i. i < length Rs \<Longrightarrow> group (Rs ! i)"
  shows "group (DirProd_list Rs)" using assms
proof (induction Rs rule: DirProd_list.induct)
  case 1 thus ?case
  unfolding group_def group_axioms_def Units_def monoid_def by auto
next
  case (2 R Rs)
  hence "group (DirProd_list Rs)" by force
  moreover have "group R"
    using "2.prems" by fastforce
  moreover have "monoid (DirProd_list (R # Rs))"
    using DirProd_list_monoid 2 group.is_monoid by blast
  moreover have "R \<times>\<times> DirProd_list Rs \<cong> DirProd_list (R # Rs)"
    unfolding is_iso_def using DirProd_list_isomorphism1 by auto
  ultimately show ?case
    using group.iso_imp_group[of "R \<times>\<times> (DirProd_list Rs)" "DirProd_list (R # Rs)"]
          DirProd_group[of R "DirProd_list Rs"] by simp
qed

lemma DirProd_list_comm_group:
  assumes "\<And>i. i < length Rs \<Longrightarrow> comm_group (Rs ! i)"
  shows "comm_group (DirProd_list Rs)"
  using assms unfolding comm_group_def
  using DirProd_list_group DirProd_list_comm_monoid by auto

lemma DirProd_list_group_hom:
  assumes "\<And>i. i \<in> {..<(length (R # Rs))} \<Longrightarrow> group ((R # Rs) ! i)"
  shows "group_hom (R \<times>\<times> DirProd_list Rs) (DirProd_list (R # Rs)) (\<lambda>(hd, tl). hd # tl)"
proof -
  have "group R"
    using assms by force
  moreover have "group (DirProd_list Rs)"
    using DirProd_list_group assms by fastforce
  ultimately

  have "group (R \<times>\<times> DirProd_list Rs)"
    using DirProd_group[of R "DirProd_list Rs"] by simp
  moreover have "group (DirProd_list (R # Rs))"
    using DirProd_list_group assms by blast
  moreover have "(\<lambda>(x, y). x # y) \<in> hom (R \<times>\<times> DirProd_list Rs) (DirProd_list (R # Rs))"
    using DirProd_list_isomorphism1[of R Rs] unfolding iso_def by simp
  ultimately show ?thesis
    unfolding group_hom_def group_hom_axioms_def by simp
qed

lemma DirProd_list_m_inv:
  assumes "r \<in> carrier (DirProd_list Rs)"
      and "\<And>i. i < length Rs \<Longrightarrow> group (Rs ! i)"
    shows "\<And>i. i < length Rs \<Longrightarrow> (inv\<^bsub>(DirProd_list Rs)\<^esub> r) ! i = inv\<^bsub>(Rs ! i)\<^esub> (r ! i)"
  using assms
proof (induct Rs arbitrary: r rule: DirProd_list.induct)
  case 1
  have "group (DirProd_list [])"
    unfolding group_def group_axioms_def Units_def monoid_def by auto
  thus ?case  using "1.prems"(1) group.inv_equality by fastforce    
next
  case (2 R Rs)
  then obtain r' rs' where r': "r' \<in> carrier R" and rs': "rs' \<in> carrier (DirProd_list Rs)"
                       and r: "r = r' # rs'" by auto
  hence "(r', rs') \<in> carrier (R \<times>\<times> DirProd_list Rs)" by simp
  moreover have "group_hom (R \<times>\<times> DirProd_list Rs) (DirProd_list (R # Rs)) (\<lambda>(hd, tl). hd # tl)"
    using DirProd_list_group_hom[of R Rs] 2 by auto
  moreover have "inv\<^bsub>(R \<times>\<times> DirProd_list Rs)\<^esub> (r', rs') = (inv\<^bsub>R\<^esub> r', inv\<^bsub>(DirProd_list Rs)\<^esub> rs')"
    using inv_DirProd[of R "DirProd_list Rs" r' rs'] "2.prems"(3) DirProd_list_group r' rs' by force
  ultimately have "inv\<^bsub>(DirProd_list (R # Rs))\<^esub> r = (inv\<^bsub>R\<^esub> r') # (inv\<^bsub>(DirProd_list Rs)\<^esub> rs')"
    using group_hom.hom_inv[of "R \<times>\<times> DirProd_list Rs" "DirProd_list (R # Rs)"
                               "\<lambda>(hd, tl). hd # tl" "(r', rs')"] r by simp
  thus ?case
    by (smt "2.hyps"(1) "2.prems"(1) "2.prems"(3) One_nat_def Suc_less_eq Suc_pred length_Cons
        lessThan_iff list.sel(3) not_gr0 nth_Cons' nth_tl r rs') 
qed


subsection \<open>Direct Product for of a List of Rings\<close>

text \<open>In order to state a more general version of the Chinese Remainder Theorem, we need a new
      structure: the direct product of a variable number of rings. The construction of this
      structure as well as its algebraic properties are the subject of this subsection and follow
      the similar study that has already been done for monoids in the previous subsection.\<close>

fun RDirProd_list :: "('a ring) list \<Rightarrow> ('a list) ring"
  where "RDirProd_list Rs =
           monoid.extend (monoid.truncate (DirProd_list Rs))
                         \<lparr> zero = one (DirProd_list (map add_monoid Rs)),
                           add = mult (DirProd_list (map add_monoid Rs)) \<rparr>"

lemma RDirProd_list_add_monoid:
  "add_monoid (RDirProd_list Rs) = DirProd_list (map add_monoid Rs)"
proof -
  have "carrier (RDirProd_list Rs) = carrier (DirProd_list (map add_monoid Rs))"
    by (induct Rs rule: DirProd_list.induct) (simp_all add: monoid.defs)
  thus ?thesis by (simp add: monoid.defs)
qed

lemma RDirProd_list_mult_monoid:
  "monoid.truncate (RDirProd_list Rs) = monoid.truncate (DirProd_list Rs)"
  by (simp add: monoid.defs)

lemma RDirProd_list_monoid:
  assumes "\<And>i. i < length Rs \<Longrightarrow> monoid (Rs ! i)"
  shows "monoid (RDirProd_list Rs)"
proof -
  have "monoid (DirProd_list Rs)"
    using DirProd_list_monoid assms by blast
  hence "monoid (monoid.truncate (DirProd_list Rs))"
    unfolding monoid_def by (auto intro: monoid.intro simp add: monoid.defs)
  hence "monoid (monoid.truncate (RDirProd_list Rs))"
    by (simp add: monoid.defs)
  thus ?thesis
    unfolding monoid_def by (auto intro: monoid.intro simp add: monoid.defs)
qed

lemma RDirProd_list_comm_monoid:
  assumes "\<And>i. i < length Rs \<Longrightarrow> comm_monoid (Rs ! i)"
  shows "comm_monoid (RDirProd_list Rs)"
proof -
  have "comm_monoid (DirProd_list Rs)"
    using DirProd_list_comm_monoid assms by blast
  hence "comm_monoid (monoid.truncate (DirProd_list Rs))"
    unfolding comm_monoid_def monoid_def comm_monoid_axioms_def
    by (auto simp add: monoid.defs)
  hence "comm_monoid (monoid.truncate (RDirProd_list Rs))"
    by (simp add: monoid.defs)
  thus ?thesis
    unfolding comm_monoid_def monoid_def comm_monoid_axioms_def
    by (auto simp add: monoid.defs)
qed

lemma RDirProd_list_abelian_monoid:
  assumes "\<And>i. i < length Rs \<Longrightarrow> abelian_monoid (Rs ! i)"
  shows "abelian_monoid (RDirProd_list Rs)"
proof -
  have "\<And>i. i < length Rs \<Longrightarrow> comm_monoid ((map add_monoid Rs) ! i)"
    using assms unfolding abelian_monoid_def by simp
  hence "comm_monoid (DirProd_list (map add_monoid Rs))"
    by (metis (no_types, lifting) DirProd_list_comm_monoid length_map)
  thus ?thesis
    unfolding abelian_monoid_def by (metis RDirProd_list_add_monoid) 
qed

lemma RDirProd_list_abelian_group:
  assumes "\<And>i. i < length Rs \<Longrightarrow> abelian_group (Rs ! i)"
  shows "abelian_group (RDirProd_list Rs)"
proof -
  have "\<And>i. i < length Rs \<Longrightarrow> comm_group ((map add_monoid Rs) ! i)"
    using assms unfolding abelian_group_def abelian_group_axioms_def by simp
  hence "comm_group (DirProd_list (map add_monoid Rs))"
    by (metis (no_types, lifting) DirProd_list_comm_group length_map)
  thus ?thesis
    unfolding abelian_group_def abelian_group_axioms_def
    by (metis RDirProd_list_abelian_monoid RDirProd_list_add_monoid abelian_group_def assms)
qed

lemma RDirProd_list_carrier_elts:
  assumes "rs \<in> carrier (RDirProd_list Rs)"
  shows "length rs = length Rs"
  using assms by (simp add: DirProd_list_carrier_elts monoid.defs)

lemma RDirProd_list_in_carrierE:
  assumes "rs \<in> carrier (RDirProd_list Rs)"
  shows "\<And>i. i < length rs \<Longrightarrow> rs ! i \<in> carrier (Rs ! i)"
  using assms by (simp add: DirProd_list_in_carrierE monoid.defs)

lemma RDirProd_list_in_carrierI:
  assumes "\<And>i. i < length rs \<Longrightarrow> rs ! i \<in> carrier (Rs ! i)"
      and "length rs = length Rs"
    shows "rs \<in> carrier (RDirProd_list Rs)"
  using DirProd_list_in_carrierI assms by (simp add: monoid.defs, blast)

lemma RDirProd_list_one:
  "\<And>i. i < length Rs \<Longrightarrow> (\<one>\<^bsub>(RDirProd_list Rs)\<^esub>) ! i =  \<one>\<^bsub>(Rs ! i)\<^esub>"
  by (simp add: DirProd_list_one monoid.defs)

lemma RDirProd_list_zero:
  "\<And>i. i < length Rs \<Longrightarrow> (\<zero>\<^bsub>(RDirProd_list Rs)\<^esub>) ! i =  \<zero>\<^bsub>(Rs ! i)\<^esub>"
  by (induct Rs rule: DirProd_list.induct) (simp_all add: monoid.defs nth_Cons')

lemma RDirProd_list_m_output:
  assumes "r1 \<in> carrier (RDirProd_list Rs)" "r2 \<in> carrier (RDirProd_list Rs)"
  shows "\<And>i. i < length Rs \<Longrightarrow>
             (r1 \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> r2) ! i = (r1 ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (r2 ! i)"
  using assms by (simp add: DirProd_list_m_output monoid.defs)

lemma RDirProd_list_a_output:
  fixes i
  assumes "r1 \<in> carrier (RDirProd_list Rs)" "r2 \<in> carrier (RDirProd_list Rs)" "i < length Rs"
  shows "(r1 \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> r2) ! i = (r1 ! i) \<oplus>\<^bsub>(Rs ! i)\<^esub> (r2 ! i)"
  using RDirProd_list_add_monoid[of Rs] monoid.defs(3)
proof -
  have "(\<otimes>\<^bsub>DirProd_list (map add_monoid Rs)\<^esub>) = (\<oplus>\<^bsub>RDirProd_list Rs\<^esub>)"
    by (metis \<open>add_monoid (RDirProd_list Rs) = DirProd_list (map add_monoid Rs)\<close> monoid.select_convs(1))
  moreover have "r1 \<in> carrier (DirProd_list (map add_monoid Rs))"
    by (metis \<open>add_monoid (RDirProd_list Rs) = DirProd_list (map add_monoid Rs)\<close> assms(1) partial_object.select_convs(1))
  moreover have "r2 \<in> carrier (DirProd_list (map add_monoid Rs))"
    by (metis \<open>add_monoid (RDirProd_list Rs) = DirProd_list (map add_monoid Rs)\<close> assms(2) partial_object.select_convs(1))
  ultimately show ?thesis
    by (simp add: DirProd_list_m_output assms(3))
qed

lemma RDirProd_list_a_inv:
  fixes i
  assumes "r \<in> carrier (RDirProd_list Rs)"
      and "\<And>i. i < length Rs \<Longrightarrow> abelian_group (Rs ! i)"
      and "i < length Rs"
    shows "(\<ominus>\<^bsub>(RDirProd_list Rs)\<^esub> r) ! i = \<ominus>\<^bsub>(Rs ! i)\<^esub> (r ! i)"
proof -
  have f1: "m_inv (DirProd_list (map add_monoid Rs)) = a_inv (RDirProd_list Rs)"
    by (metis RDirProd_list_add_monoid a_inv_def)
moreover
  have f4: "r \<in> carrier (DirProd_list (map add_monoid Rs))"
    by (metis RDirProd_list_add_monoid assms(1) partial_object.select_convs(1))
moreover
  have f3: "a_inv (Rs ! i) = m_inv (map add_monoid Rs ! i)"
    by (simp add: a_inv_def assms(3))
  ultimately show ?thesis  using RDirProd_list_add_monoid[of Rs] monoid.defs(3) DirProd_list_m_inv
    by (smt abelian_group.a_group assms(2) assms(3) length_map nth_map)
qed

lemma RDirProd_list_l_distr:
  assumes "x \<in> carrier (RDirProd_list Rs)"
      and "y \<in> carrier (RDirProd_list Rs)"
      and "z \<in> carrier (RDirProd_list Rs)"
      and "\<And>i. i < length Rs \<Longrightarrow> ring (Rs ! i)"
    shows "(x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z =
           (x \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (y \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z)"
proof -
  have "length ((x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) =
        length ((x \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (y \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z))"
    by (metis RDirProd_list_abelian_group RDirProd_list_carrier_elts RDirProd_list_monoid
        abelian_groupE(1) assms monoid.m_closed ring.is_abelian_group ring.is_monoid)

  moreover
  have "\<And>i. i < length Rs \<Longrightarrow>
            ((x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) ! i =
            ((x \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (y \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z)) ! i"
  proof -
    fix i assume i: "i < length Rs"
    hence "((x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) ! i =
           ((x ! i) \<oplus>\<^bsub>(Rs ! i)\<^esub> (y ! i)) \<otimes>\<^bsub>(Rs ! i)\<^esub> (z ! i)"
      using RDirProd_list_m_output RDirProd_list_a_output assms
      by (metis RDirProd_list_abelian_group abelian_groupE(1) lessThan_iff ring.is_abelian_group)
    also have " ... = ((x ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (z ! i)) \<oplus>\<^bsub>(Rs ! i)\<^esub> ((y ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (z ! i))"
      by (metis RDirProd_list_carrier_elts RDirProd_list_in_carrierE
          i assms lessThan_iff ring.ring_simprules(13))
    also
    have " ... = ((x \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (y \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z)) ! i"
      using RDirProd_list_m_output RDirProd_list_a_output assms
      by (metis RDirProd_list_monoid i lessThan_iff monoid.m_closed ring.is_monoid)
    finally
    show "((x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) ! i =
          ((x \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (y \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z)) ! i" .
  qed

  moreover have "length ((x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> z) = length Rs"
    by (meson RDirProd_list_abelian_group RDirProd_list_carrier_elts RDirProd_list_monoid
        abelian_groupE(1) assms monoid.m_closed ring.is_abelian_group ring.is_monoid)

  ultimately show ?thesis by (simp add: nth_equalityI) 
qed

lemma RDirProd_list_r_distr:
  assumes "x \<in> carrier (RDirProd_list Rs)"
      and "y \<in> carrier (RDirProd_list Rs)"
      and "z \<in> carrier (RDirProd_list Rs)"
      and "\<And>i. i < length Rs \<Longrightarrow> ring (Rs ! i)"
    shows "z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> (x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y) =
          (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> x) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> y)"
proof -
  have "length (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> (x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y)) =
        length ((z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> x) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> y))"
    by (metis RDirProd_list_abelian_group RDirProd_list_carrier_elts RDirProd_list_monoid
        abelian_groupE(1) assms monoid.m_closed ring.is_abelian_group ring.is_monoid)

  moreover
  have "\<And>i. i < length Rs \<Longrightarrow>
            (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> (x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y)) ! i =
           ((z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> x) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> y)) ! i"
  proof -
    fix i assume i: "i < length Rs"
    hence "(z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> (x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y)) ! i =
           (z ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> ((x ! i) \<oplus>\<^bsub>(Rs ! i)\<^esub> (y ! i))"
      using RDirProd_list_m_output RDirProd_list_a_output assms
      by (metis RDirProd_list_abelian_group abelian_groupE(1) lessThan_iff ring.is_abelian_group)
    also have " ... = ((z ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (x ! i)) \<oplus>\<^bsub>(Rs ! i)\<^esub> ((z ! i) \<otimes>\<^bsub>(Rs ! i)\<^esub> (y ! i))"
      by (metis RDirProd_list_carrier_elts RDirProd_list_in_carrierE
          assms i lessThan_iff ring.ring_simprules(23))
    also
    have " ... = ((z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> x) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> y)) ! i"
      using RDirProd_list_m_output RDirProd_list_a_output assms
      by (metis RDirProd_list_monoid i lessThan_iff monoid.m_closed ring.is_monoid)
    finally
    show "(z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> (x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y)) ! i =
         ((z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> x) \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> y)) ! i" .
  qed

  moreover have "length (z \<otimes>\<^bsub>(RDirProd_list Rs)\<^esub> (x \<oplus>\<^bsub>(RDirProd_list Rs)\<^esub> y)) = length Rs"
    by (meson RDirProd_list_abelian_group RDirProd_list_carrier_elts RDirProd_list_monoid
        abelian_groupE(1) assms monoid.m_closed ring.is_abelian_group ring.is_monoid)

  ultimately show ?thesis by (simp add: nth_equalityI)
qed

theorem RDirProd_list_ring:
  assumes "\<And>i. i < length Rs \<Longrightarrow> ring (Rs ! i)"
  shows "ring (RDirProd_list Rs)"
  using assms unfolding ring_def ring_axioms_def using assms 
  by (meson RDirProd_list_abelian_group RDirProd_list_l_distr
            RDirProd_list_monoid RDirProd_list_r_distr)

theorem RDirProd_list_cring:
  assumes "\<And>i. i < length Rs \<Longrightarrow> cring (Rs ! i)"
  shows "cring (RDirProd_list Rs)"
  by (meson RDirProd_list_comm_monoid RDirProd_list_ring assms cring_def)

corollary (in cring) RDirProd_list_of_quot_is_cring:
  assumes "\<And>i. i < n \<Longrightarrow> ideal (I i) R"
    shows "cring (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< n]))"
      (is "cring (RDirProd_list ?Rs)")
proof -
  have "\<And>i. i \<in> {..<(length ?Rs)} \<Longrightarrow> cring (?Rs ! i)"
    by (simp add: assms ideal.quotient_is_cring is_cring)
  thus ?thesis
    using RDirProd_list_cring by blast
qed

lemma RDirProd_list_isomorphism1:
  "(\<lambda>(hd, tl). hd # tl) \<in> ring_iso (RDirProd R (RDirProd_list Rs)) (RDirProd_list (R # Rs))"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
  by (auto simp add: monoid.defs)

lemma RDirProd_list_isomorphism1':
  "(RDirProd R (RDirProd_list Rs)) \<simeq> (RDirProd_list (R # Rs))"
  unfolding is_ring_iso_def using RDirProd_list_isomorphism1 by blast 

lemma RDirProd_list_isomorphism2:
  "(\<lambda>r. (hd r, tl r)) \<in> ring_iso (RDirProd_list (R # Rs)) (RDirProd R (RDirProd_list Rs))"
  unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
proof (auto simp add: monoid.defs)
  let ?\<phi> = "\<lambda>r. (hd r, tl r)"
  fix a b assume "a \<in> carrier R" "b \<in> carrier (DirProd_list Rs)"
  hence "a # b \<in> {r # rs |r rs. r \<in> carrier R \<and> rs \<in> carrier (DirProd_list Rs)} \<and> ?\<phi> (a # b) = (a, b)"
    by simp
  thus "(a, b) \<in> ?\<phi> ` {r # rs |r rs. r \<in> carrier R \<and> rs \<in> carrier (DirProd_list Rs)}"
    by (metis (no_types, lifting) image_iff)
qed

lemma RDirProd_list_isomorphism3:
  "(\<lambda>(r, l). r @ [l]) \<in> ring_iso (RDirProd (RDirProd_list Rs) S) (RDirProd_list (Rs @ [S]))"
proof (induction Rs rule: DirProd_list.induct)
  case 1 thus ?case
    unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
    by (auto simp add: monoid.defs image_iff)
next
  case (2 R Rs)

  { fix r1 r2 assume A0: "r1 \<in> carrier (RDirProd_list (R # Rs))"
                 and A1: "r2 \<in> carrier (RDirProd_list (R # Rs))"
    have "length r1 \<ge> 1"
     and "length r2 \<ge> 1"
     and "length (r1 \<otimes>\<^bsub>(RDirProd_list (R # Rs))\<^esub> r2) \<ge> 1"
     and "length (r1 \<oplus>\<^bsub>(RDirProd_list (R # Rs))\<^esub> r2) \<ge> 1"
     and "length (\<one>\<^bsub>(RDirProd_list (R # Rs))\<^esub>) \<ge> 1"
    proof -
      show len_r1: "length r1 \<ge> 1"
       and len_r2: "length r2 \<ge> 1"
        by (metis RDirProd_list_carrier_elts A0 A1 length_Cons less_one nat.simps(3) not_less)+
      show "length (r1 \<otimes>\<^bsub>(RDirProd_list (R # Rs))\<^esub> r2) \<ge> 1"
       and "length (r1 \<oplus>\<^bsub>(RDirProd_list (R # Rs))\<^esub> r2) \<ge> 1"
       and "length (\<one>\<^bsub>(RDirProd_list (R # Rs))\<^esub>) \<ge> 1"
        using len_r1 len_r2 by (simp_all add: monoid.defs)
    qed } note aux_lemma = this

  moreover
  have "(\<lambda>(r, s). (hd r, (tl r, s))) \<in>
          ring_iso (RDirProd (RDirProd_list (R # Rs)) S)
                   (RDirProd R (RDirProd (RDirProd_list Rs) S))"
    using ring_iso_set_trans[OF RDirProd_isomorphism4[OF RDirProd_list_isomorphism2[of R Rs],of S]
                                RDirProd_isomorphism3[of R "RDirProd_list Rs" S]]
    by (simp add: case_prod_beta' comp_def)

  moreover
  have "(\<lambda>(hd, (tl, s)). hd # (tl @ [s])) \<in>
          ring_iso (RDirProd R (RDirProd (RDirProd_list Rs) S))
                   (RDirProd_list (R # (Rs @ [S])))"
    using ring_iso_set_trans[OF RDirProd_isomorphism5[OF 2(1), of R]
                                RDirProd_list_isomorphism1[of R "Rs @ [S]"]]
    by (simp add: case_prod_beta' comp_def)

  moreover
  have "(\<lambda>(r, s). (hd r) # ((tl r) @ [s])) \<in>
          ring_iso (RDirProd (RDirProd_list (R # Rs)) S) (RDirProd_list (R # (Rs @ [S])))"
    using ring_iso_set_trans[OF calculation(6-7)] by (simp add: case_prod_beta' comp_def)
  hence iso: "(\<lambda>(r, s). (hd r # tl r) @ [s]) \<in>
           ring_iso (RDirProd (RDirProd_list (R # Rs)) S) (RDirProd_list ((R # Rs) @ [S]))" by simp
  
  show ?case
  proof (rule ring_iso_morphic_prop[OF iso, of "\<lambda>r. length (fst r) \<ge> 1" "\<lambda>(r, s). r @ [s]"])
    show "\<And>r. 1 \<le> length (fst r) \<Longrightarrow>
              (case r of (r, s) \<Rightarrow> (hd r # tl r) @ [s]) = (case r of (r, s) \<Rightarrow> r @ [s])"
      by (simp add: Suc_le_eq case_prod_beta')
    show "morphic_prop (RDirProd (RDirProd_list (R # Rs)) S) (\<lambda>r. 1 \<le> length (fst r))"
      unfolding RDirProd_def by (rule morphic_propI) (auto simp add: monoid.defs aux_lemma)
  qed
qed


subsection \<open>Second Generalization - The Extended Canonical Projection is a Homomorphism and
                                    Description of its Kernel\<close>

theorem (in cring) canonical_proj_ext_is_hom:
  fixes n::nat
  assumes "\<And>i. i < n \<Longrightarrow> ideal (I i) R"
      and "\<And>i j. \<lbrakk> i < n; j < n; i \<noteq> j \<rbrakk> \<Longrightarrow> I i <+> I j = carrier R"
    shows "(\<lambda>a. (map (\<lambda>i. (I i) +> a) [0..< n])) \<in>
            ring_hom R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< n]))" (is "?\<phi> \<in> ?ring_hom")
proof (rule ring_hom_memI)
  { fix x assume x: "x \<in> carrier R"
    have "?\<phi> x \<in> carrier (RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n]))"
    apply (rule RDirProd_list_in_carrierI)
    by (simp_all add: FactRing_def a_rcosetsI additive_subgroup.a_subset assms(1) ideal.axioms(1) x) }
  note aux_lemma = this

  fix x y assume x: "x \<in> carrier R" and y: "y \<in> carrier R"
  show x': "?\<phi> x \<in> carrier (RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n]))"
    using aux_lemma[OF x] .
  hence x'': "?\<phi> x \<in> carrier (DirProd_list (map (\<lambda>i. R Quot I i) [0..<n]))"
    by (simp add: monoid.defs)

  have y': "?\<phi> y \<in> carrier (RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n]))"
    using aux_lemma[OF y] .
  hence y'': "map (\<lambda>i. I i +> y) [0..<n] \<in> carrier (DirProd_list (map (\<lambda>i. R Quot I i) [0..<n]))"
    by (simp add: monoid.defs)

  show "?\<phi> (x \<otimes> y) = ?\<phi> x \<otimes>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> ?\<phi> y"
    apply (rule nth_equalityI) 
    apply (metis RDirProd_list_carrier_elts RDirProd_list_of_quot_is_cring assms(1)
                 cring.cring_simprules(5) length_map x' y')
    apply (simp add: monoid.defs)
    using DirProd_list_m_output [of "?\<phi> x" "(map (\<lambda>i. R Quot I i) [0..<n])" "?\<phi> y"] x'' y''
    by (simp add: x'' y'' FactRing_def  assms(1) ideal.rcoset_mult_add x y)

  show "?\<phi> (x \<oplus> y) = ?\<phi> x \<oplus>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> ?\<phi> y"
  proof -
    have "length (?\<phi> (x \<oplus> y)) =
          length ((?\<phi> x) \<oplus>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> (?\<phi> y))"
      by (metis RDirProd_list_carrier_elts RDirProd_list_of_quot_is_cring assms(1)
          cring.cring_simprules(1) length_map x' y')

    moreover
    have "\<And>j. j < n \<Longrightarrow>
              (?\<phi> (x \<oplus> y)) ! j = ((?\<phi> x) \<oplus>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> (?\<phi> y)) ! j"
    proof -
      fix j assume j: "j < n"
      have "(?\<phi> (x \<oplus> y)) ! j = I j +> x \<oplus> y" using j by simp
      also have " ... = (I j +> x) \<oplus>\<^bsub>(R Quot I j)\<^esub> (I j +> y)"
        by (simp add: FactRing_def abelian_subgroup.a_rcos_sum abelian_subgroupI3
            assms(1) ideal.axioms(1) is_abelian_group j x y)
      also have " ... = ((?\<phi> x) \<oplus>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> (?\<phi> y)) ! j"
      proof -
        have "R Quot I j = map (\<lambda>n. R Quot I n) [0..<n] ! j"
             "I j +> x = I ([0..<n] ! j) +> x" 
             "I j +> y = I ([0..<n] ! j) +> y"
          by (simp_all add: j)
        moreover have "\<And>n ns f. n < length ns \<Longrightarrow> map f ns ! n = (f (ns ! n::nat)::'a set)"
          by simp
        moreover have "\<And>B ps C n. \<lbrakk>B \<in> carrier (RDirProd_list ps); C \<in> carrier (RDirProd_list ps); n < length ps\<rbrakk> 
                     \<Longrightarrow> (B \<oplus>\<^bsub>RDirProd_list ps\<^esub> C) ! n = (B ! n::'a set) \<oplus>\<^bsub>ps ! n\<^esub> C ! n"
          by (meson RDirProd_list_a_output)
        ultimately show ?thesis
          by (metis (mono_tags, lifting) diff_zero j length_map length_upt x' y') 
      qed
      finally show "(?\<phi> (x \<oplus> y)) ! j =
                    ((?\<phi> x) \<oplus>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> (?\<phi> y)) ! j" .
    qed
    ultimately show "?\<phi> (x \<oplus> y) = ?\<phi> x \<oplus>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub> ?\<phi> y"
      by (simp add: nth_equalityI) 
  qed
next
  show "(?\<phi> \<one>) = \<one>\<^bsub>RDirProd_list (map (\<lambda>i. R Quot I i) [0..<n])\<^esub>"
    apply (rule nth_equalityI)
    apply (metis RDirProd_list_carrier_elts cring.cring_simprules(6)
                 RDirProd_list_of_quot_is_cring assms(1) length_map)
    using DirProd_list_one[where ?Rs = "map (\<lambda>i. R Quot I i) [0..<n]"]
    by (simp add: FactRing_def monoid.defs)
qed


theorem (in cring) canonical_proj_ext_kernel:
  fixes n::nat
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R"
      and "\<And>i j. \<lbrakk> i \<le> n; j \<le> n; i \<noteq> j \<rbrakk> \<Longrightarrow> I i <+> I j = carrier R"
    shows "(\<Inter>i \<le> n. I i) = a_kernel R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))
                           (\<lambda>a. (map (\<lambda>i. (I i) +> a) [0..< Suc n]))"
proof -
  let ?\<phi> = "\<lambda>a. (map (\<lambda>i. (I i) +> a) [0..< Suc n])"
  show ?thesis
  proof
    show "(\<Inter>i \<le> n. I i) \<subseteq> a_kernel R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) ?\<phi>"
    proof
      fix s assume s: "s \<in> (\<Inter>i \<le> n. I i)"
      hence "\<And>i. i \<le> n \<Longrightarrow> (I i) +> s = I i"
        by (simp add: additive_subgroup.zero_closed assms ideal.axioms(1) ideal.set_add_zero)
      hence "\<And>i. i \<le> n \<Longrightarrow> (?\<phi> s) ! i = I i"
        by (metis add.left_neutral diff_zero le_imp_less_Suc nth_map_upt)
      moreover have
        "\<And>i. i \<le> n \<Longrightarrow> (\<zero>\<^bsub>(RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))\<^esub>) ! i =
                         \<zero>\<^bsub>(R Quot (I i))\<^esub>"
        using RDirProd_list_zero[where ?Rs = "map (\<lambda>i. R Quot I i) [0..<Suc n]"]
        by (metis (no_types, lifting) add.left_neutral le_imp_less_Suc
            length_map length_upt nth_map_upt diff_zero)
      hence 
        "\<And>i. i \<le> n \<Longrightarrow> (\<zero>\<^bsub>(RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))\<^esub>) ! i = I i"
        unfolding FactRing_def by simp
      moreover
      have "length (\<zero>\<^bsub>(RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))\<^esub>) = Suc n"

        using RDirProd_list_carrier_elts RDirProd_list_cring
         add.left_neutral assms(1) cring.cring_simprules(2) diff_zero nth_map_upt
            ideal.quotient_is_cring is_cring length_map length_upt lessThan_Suc_atMost lessThan_iff
        by (smt less_Suc_eq_le)
      moreover have "length (?\<phi> s) = Suc n" by simp
      ultimately have "?\<phi> s = \<zero>\<^bsub>(RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))\<^esub>"
        by (simp add: nth_equalityI)

      moreover have "s \<in> carrier R"
        using additive_subgroup.a_Hcarr assms(1) ideal.axioms(1) s by fastforce
      ultimately show "s \<in> a_kernel R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) ?\<phi>"
        using a_kernel_def'[of R "RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])"] by simp
    qed
  next
    show "a_kernel R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) ?\<phi> \<subseteq> (\<Inter>i \<le> n. I i)"
    proof
      fix s assume s: "s \<in> a_kernel R (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) ?\<phi>"
      hence "?\<phi> s = \<zero>\<^bsub>(RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n]))\<^esub>"
        unfolding a_kernel_def kernel_def by (simp add: monoid.defs)
      hence "(I i) +> s = \<zero>\<^bsub>(R Quot (I i))\<^esub>" if "i \<le> n" for i
        using RDirProd_list_zero[where ?Rs = "map (\<lambda>i. R Quot I i) [0..<Suc n]"]
          by (metis (no_types) that add.left_neutral diff_zero le_imp_less_Suc length_map length_upt nth_map_upt)
      hence "\<And>i. i \<le> n \<Longrightarrow> (I i) +> s = I i"
        unfolding FactRing_def by simp
      moreover have "s \<in> carrier R"
        using s unfolding a_kernel_def kernel_def by simp
      ultimately show "s \<in> (\<Inter>i \<le> n. I i)"
        using ideal.set_add_zero_imp_mem[where ?i = s and ?R = R] by (simp add: assms(1))
    qed
  qed
qed


subsection \<open>Final Generalization\<close>

theorem (in cring) chinese_remainder:
  fixes n::nat
  assumes "\<And>i. i \<le> n \<Longrightarrow> ideal (I i) R"
      and "\<And>i j. \<lbrakk> i \<le> n; j \<le> n; i \<noteq> j \<rbrakk> \<Longrightarrow> I i <+> I j = carrier R"
    shows "R Quot (\<Inter>i \<le> n. I i) \<simeq>  RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])"
  using assms
proof (induct n)
  case 0
  have "(\<lambda>r. (r, [])) \<in> ring_iso (R Quot (I 0)) (RDirProd (R Quot (I 0)) (RDirProd_list []))"
    unfolding ring_iso_def ring_hom_def bij_betw_def inj_on_def RDirProd_def
    by (auto simp add: monoid.defs)
  hence "(R Quot (I 0)) \<simeq> (RDirProd (R Quot (I 0)) (RDirProd_list []))"
    unfolding is_ring_iso_def by blast
  moreover
  have "RDirProd ((R Quot (I 0)) :: 'a set ring)
                 (RDirProd_list ([] :: (('a set) ring) list)) \<simeq> (RDirProd_list  [ (R Quot (I 0)) ])"
    using RDirProd_list_isomorphism1'[of "(R Quot (I 0)) :: 'a set ring" "[] :: (('a set) ring) list"] . 
  ultimately show ?case
    using ring_iso_trans by simp
next
  case (Suc n)
  have inter_ideal: "ideal (\<Inter> i \<le> n. I i) R"
    using Suc.prems(1) i_Intersect[of "I ` {..n}"] atMost_Suc atLeast1_atMost_eq_remove0 by auto
  hence "R Quot (\<Inter> i \<le> Suc n. I i) \<simeq> RDirProd (R Quot (\<Inter> i \<le> n. I i)) (R Quot (I (Suc n)))"
    using chinese_remainder_simple[of "\<Inter> i \<le> n. I i" "I (Suc n)"] inter_plus_ideal_eq_carrier[of n I]
    by (simp add: Int_commute Suc.prems(1-2) atMost_Suc)
  moreover have "R Quot (\<Inter> i \<le> n. I i) \<simeq> RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])"
    using Suc.hyps Suc.prems(1-2) by auto
  hence "RDirProd (R Quot (\<Inter> i \<le> n. I i)) (R Quot (I (Suc n))) \<simeq>
         RDirProd (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) (R Quot (I (Suc n)))"
    unfolding is_ring_iso_def using RDirProd_isomorphism4 by blast

  ultimately
  have "R Quot (\<Inter> i \<le> Suc n. I i) \<simeq>
        RDirProd (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) (R Quot (I (Suc n)))"
    using ring_iso_trans by simp

  moreover
  have "RDirProd (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) (R Quot (I (Suc n))) \<simeq>
        RDirProd_list ((map (\<lambda>i. R Quot (I i)) [0..< Suc n]) @ [ R Quot (I (Suc n)) ])"
    using RDirProd_list_isomorphism3 unfolding is_ring_iso_def by blast
  hence "RDirProd (RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc n])) (R Quot (I (Suc n))) \<simeq>
         RDirProd_list (map (\<lambda>i. R Quot (I i)) [0..< Suc (Suc n)])" by simp

  ultimately show ?case using ring_iso_trans by simp
qed

end

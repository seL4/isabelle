(*  Title:      HOL/Algebra/Subrings.thy
    Authors:    Martin Baillon and Paulo Emílio de Vilhena
*)

theory Subrings
  imports Ring RingHom QuotRing Multiplicative_Group
begin

section \<open>Subrings\<close>

subsection \<open>Definitions\<close>

locale subring =
  subgroup H "add_monoid R" + submonoid H R for H and R (structure)

locale subcring = subring +
  assumes sub_m_comm: "\<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 = h2 \<otimes> h1"

locale subdomain = subcring +
  assumes sub_one_not_zero [simp]: "\<one> \<noteq> \<zero>"
  assumes subintegral: "\<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 = \<zero> \<Longrightarrow> h1 = \<zero> \<or> h2 = \<zero>"

locale subfield = subdomain K R for K and R (structure) +
  assumes subfield_Units: "Units (R \<lparr> carrier := K \<rparr>) = K - { \<zero> }"


subsection \<open>Basic Properties\<close>
  
subsubsection \<open>Subrings\<close>

lemma (in ring) subringI:
  assumes "H \<subseteq> carrier R"
    and "\<one> \<in> H"
    and "\<And>h. h \<in> H \<Longrightarrow> \<ominus> h \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<oplus> h2 \<in> H"
  shows "subring H R"
  using add.subgroupI[OF assms(1) _ assms(3, 5)] assms(2)
        submonoid.intro[OF assms(1, 4, 2)]
  unfolding subring_def by auto

lemma subringE:
  assumes "subring H R"
  shows "H \<subseteq> carrier R"
    and "\<zero>\<^bsub>R\<^esub> \<in> H"
    and "\<one>\<^bsub>R\<^esub> \<in> H"
    and "H \<noteq> {}"
    and "\<And>h. h \<in> H \<Longrightarrow> \<ominus>\<^bsub>R\<^esub> h \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> H"
  using subring.axioms[OF assms]
  unfolding submonoid_def subgroup_def a_inv_def by auto

lemma (in ring) carrier_is_subring: "subring (carrier R) R"
  by (simp add: subringI)

lemma (in ring) subring_inter:
  assumes "subring I R" and "subring J R"
  shows "subring (I \<inter> J) R"
  using subringE[OF assms(1)] subringE[OF assms(2)] subringI[of "I \<inter> J"] by auto

lemma (in ring) subring_Inter:
  assumes "\<And>I. I \<in> S \<Longrightarrow> subring I R" and "S \<noteq> {}"
  shows "subring (\<Inter>S) R"
proof (rule subringI, auto simp add: assms subringE[of _ R])
  fix x assume "\<forall>I \<in> S. x \<in> I" thus "x \<in> carrier R"
    using assms subringE(1)[of _ R] by blast
qed

lemma (in ring) subring_is_ring:
  assumes "subring H R" shows "ring (R \<lparr> carrier := H \<rparr>)"
proof -
  interpret group "add_monoid (R \<lparr> carrier := H \<rparr>)" + monoid "R \<lparr> carrier := H \<rparr>"
    using subgroup.subgroup_is_group[OF subring.axioms(1) add.is_group] assms
          submonoid.submonoid_is_monoid[OF subring.axioms(2) monoid_axioms] by auto
  show ?thesis
    using subringE(1)[OF assms]
    by (unfold_locales, simp_all add: subringE(1)[OF assms] add.m_comm subset_eq l_distr r_distr)
qed

lemma (in ring) ring_incl_imp_subring:
  assumes "H \<subseteq> carrier R"
    and "ring (R \<lparr> carrier := H \<rparr>)"
  shows "subring H R"
  using group.group_incl_imp_subgroup[OF add.group_axioms, of H] assms(1)
        monoid.monoid_incl_imp_submonoid[OF monoid_axioms assms(1)]
        ring.axioms(1, 2)[OF assms(2)] abelian_group.a_group[of "R \<lparr> carrier := H \<rparr>"]
  unfolding subring_def by auto

lemma (in ring) subring_iff:
  assumes "H \<subseteq> carrier R"
  shows "subring H R \<longleftrightarrow> ring (R \<lparr> carrier := H \<rparr>)"
  using subring_is_ring ring_incl_imp_subring[OF assms] by auto


subsubsection \<open>Subcrings\<close>

lemma (in ring) subcringI:
  assumes "subring H R"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 = h2 \<otimes> h1"
  shows "subcring H R"
  unfolding subcring_def subcring_axioms_def using assms by simp+

lemma (in cring) subcringI':
  assumes "subring H R"
  shows "subcring H R"
  using subcringI[OF assms] subringE(1)[OF assms] m_comm by auto

lemma subcringE:
  assumes "subcring H R"
  shows "H \<subseteq> carrier R"
    and "\<zero>\<^bsub>R\<^esub> \<in> H"
    and "\<one>\<^bsub>R\<^esub> \<in> H"
    and "H \<noteq> {}"
    and "\<And>h. h \<in> H \<Longrightarrow> \<ominus>\<^bsub>R\<^esub> h \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 = h2 \<otimes>\<^bsub>R\<^esub> h1"
  using subringE[OF subcring.axioms(1)[OF assms]] subcring.sub_m_comm[OF assms] by simp+

lemma (in cring) carrier_is_subcring: "subcring (carrier R) R"
  by (simp add: subcringI' carrier_is_subring)

lemma (in ring) subcring_inter:
  assumes "subcring I R" and "subcring J R"
  shows "subcring (I \<inter> J) R"
  using subcringE[OF assms(1)] subcringE[OF assms(2)]
        subcringI[of "I \<inter> J"] subringI[of "I \<inter> J"] by auto 

lemma (in ring) subcring_Inter:
  assumes "\<And>I. I \<in> S \<Longrightarrow> subcring I R" and "S \<noteq> {}"
  shows "subcring (\<Inter>S) R"
proof (rule subcringI)
  show "subring (\<Inter>S) R"
    using subcring.axioms(1)[of _ R] subring_Inter[of S] assms by auto
next
  fix h1 h2 assume h1: "h1 \<in> \<Inter>S" and h2: "h2 \<in> \<Inter>S"
  obtain S' where S': "S' \<in> S"
    using assms(2) by blast
  hence "h1 \<in> S'" "h2 \<in> S'"
    using h1 h2 by blast+
  thus "h1 \<otimes> h2 = h2 \<otimes> h1"
    using subcring.sub_m_comm[OF assms(1)[OF S']] by simp 
qed

lemma (in ring) subcring_iff:
  assumes "H \<subseteq> carrier R"
  shows "subcring H R \<longleftrightarrow> cring (R \<lparr> carrier := H \<rparr>)"
proof
  assume A: "subcring H R"
  hence ring: "ring (R \<lparr> carrier := H \<rparr>)"
    using subring_iff[OF assms] subcring.axioms(1)[OF A] by simp
  moreover have "comm_monoid (R \<lparr> carrier := H \<rparr>)"
    using monoid.monoid_comm_monoidI[OF ring.is_monoid[OF ring]]
          subcring.sub_m_comm[OF A] by auto
  ultimately show "cring (R \<lparr> carrier := H \<rparr>)"
    using cring_def by blast
next
  assume A: "cring (R \<lparr> carrier := H \<rparr>)"
  hence "subring H R"
    using cring.axioms(1) subring_iff[OF assms] by simp
  moreover have "comm_monoid (R \<lparr> carrier := H \<rparr>)"
    using A unfolding cring_def by simp
  hence"\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 = h2 \<otimes> h1"
    using comm_monoid.m_comm[of "R \<lparr> carrier := H \<rparr>"] by auto
  ultimately show "subcring H R"
    unfolding subcring_def subcring_axioms_def by auto
qed

  
subsubsection \<open>Subdomains\<close>

lemma (in ring) subdomainI:
  assumes "subcring H R"
    and "\<one> \<noteq> \<zero>"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 = \<zero> \<Longrightarrow> h1 = \<zero> \<or> h2 = \<zero>"
  shows "subdomain H R"
  unfolding subdomain_def subdomain_axioms_def using assms by simp+

lemma (in domain) subdomainI':
  assumes "subring H R"
  shows "subdomain H R"
proof (rule subdomainI[OF subcringI[OF assms]], simp_all)
  show "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes> h2 = h2 \<otimes> h1"
    using m_comm subringE(1)[OF assms] by auto
  show "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H; h1 \<otimes> h2 = \<zero> \<rbrakk> \<Longrightarrow> (h1 = \<zero>) \<or> (h2 = \<zero>)"
    using integral subringE(1)[OF assms] by auto
qed

lemma subdomainE:
  assumes "subdomain H R"
  shows "H \<subseteq> carrier R"
    and "\<zero>\<^bsub>R\<^esub> \<in> H"
    and "\<one>\<^bsub>R\<^esub> \<in> H"
    and "H \<noteq> {}"
    and "\<And>h. h \<in> H \<Longrightarrow> \<ominus>\<^bsub>R\<^esub> h \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> H"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 = h2 \<otimes>\<^bsub>R\<^esub> h1"
    and "\<And>h1 h2. \<lbrakk> h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 = \<zero>\<^bsub>R\<^esub> \<Longrightarrow> h1 = \<zero>\<^bsub>R\<^esub> \<or> h2 = \<zero>\<^bsub>R\<^esub>"
    and "\<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>"
  using subcringE[OF subdomain.axioms(1)[OF assms]] assms
  unfolding subdomain_def subdomain_axioms_def by auto

lemma (in ring) subdomain_iff:
  assumes "H \<subseteq> carrier R"
  shows "subdomain H R \<longleftrightarrow> domain (R \<lparr> carrier := H \<rparr>)"
proof
  assume A: "subdomain H R"
  hence cring: "cring (R \<lparr> carrier := H \<rparr>)"
    using subcring_iff[OF assms] subdomain.axioms(1)[OF A] by simp
  thus "domain (R \<lparr> carrier := H \<rparr>)"
    using domain.intro[OF cring] subdomain.subintegral[OF A] subdomain.sub_one_not_zero[OF A]
    unfolding domain_axioms_def by auto
next
  assume A: "domain (R \<lparr> carrier := H \<rparr>)"
  hence subcring: "subcring H R"
    using subcring_iff[OF assms] unfolding domain_def by simp
  thus "subdomain H R"
    using subdomain.intro[OF subcring] domain.integral[OF A] domain.one_not_zero[OF A]
    unfolding subdomain_axioms_def by auto
qed

lemma (in domain) subring_is_domain:
  assumes "subring H R" shows "domain (R \<lparr> carrier := H \<rparr>)"
  using subdomainI'[OF assms] unfolding subdomain_iff[OF subringE(1)[OF assms]] .

(* NEW ====================== *)
lemma (in ring) subdomain_is_domain:
  assumes "subdomain H R" shows "domain (R \<lparr> carrier := H \<rparr>)"
  using assms unfolding subdomain_iff[OF subdomainE(1)[OF assms]] .


subsubsection \<open>Subfields\<close>

lemma (in ring) subfieldI:
  assumes "subcring K R" and "Units (R \<lparr> carrier := K \<rparr>) = K - { \<zero> }"
  shows "subfield K R"
proof (rule subfield.intro)
  show "subfield_axioms K R"
    using assms(2) unfolding subfield_axioms_def .
  show "subdomain K R"
  proof (rule subdomainI[OF assms(1)], auto)
    have subM: "submonoid K R"
      using subring.axioms(2)[OF subcring.axioms(1)[OF assms(1)]] .

    show contr: "\<one> = \<zero> \<Longrightarrow> False"
    proof -
      assume one_eq_zero: "\<one> = \<zero>"
      have "\<one> \<in> K" and "\<one> \<otimes> \<one> = \<one>"
        using submonoid.one_closed[OF subM] by simp+
      hence "\<one> \<in> Units (R \<lparr> carrier := K \<rparr>)"
        unfolding Units_def by (simp, blast)
      hence "\<one> \<noteq> \<zero>"
        using assms(2) by simp
      thus False
        using one_eq_zero by simp
    qed

    fix k1 k2 assume k1: "k1 \<in> K" and k2: "k2 \<in> K" "k2 \<noteq> \<zero>" and k12: "k1 \<otimes> k2 = \<zero>"
    obtain k2' where k2': "k2' \<in> K" "k2' \<otimes> k2 = \<one>" "k2 \<otimes> k2' = \<one>"
      using assms(2) k2 unfolding Units_def by auto
    have  "\<zero> = (k1 \<otimes> k2) \<otimes> k2'"
      using k12 k2'(1) submonoid.mem_carrier[OF subM] by fastforce
    also have  "... = k1"
      using k1 k2(1) k2'(1,3) submonoid.mem_carrier[OF subM] by (simp add: m_assoc)
    finally have "\<zero> = k1" .
    thus "k1 = \<zero>" by simp
  qed
qed

lemma (in field) subfieldI':
  assumes "subring K R" and "\<And>k. k \<in> K - { \<zero> } \<Longrightarrow> inv k \<in> K"
  shows "subfield K R"
proof (rule subfieldI)
  show "subcring K R"
    using subcringI[OF assms(1)] m_comm subringE(1)[OF assms(1)] by auto
  show "Units (R \<lparr> carrier := K \<rparr>) = K - { \<zero> }"
  proof
    show "K - { \<zero> } \<subseteq> Units (R \<lparr> carrier := K \<rparr>)"
    proof
      fix k assume k: "k \<in> K - { \<zero> }"
      hence inv_k: "inv k \<in> K"
        using assms(2) by simp
      moreover have "k \<in> carrier R - { \<zero> }" 
        using subringE(1)[OF assms(1)] k by auto
      ultimately have "k \<otimes> inv k = \<one>" "inv k \<otimes> k = \<one>"
        by (simp add: field_Units)+
      thus "k \<in> Units (R \<lparr> carrier := K \<rparr>)"
        unfolding Units_def using k inv_k by auto
    qed
  next
    show "Units (R \<lparr> carrier := K \<rparr>) \<subseteq> K - { \<zero> }"
    proof
      fix k assume k: "k \<in> Units (R \<lparr> carrier := K \<rparr>)"
      then obtain k' where k': "k' \<in> K" "k \<otimes> k' = \<one>"
        unfolding Units_def by auto
      hence "k \<in> carrier R" and "k' \<in> carrier R"
        using k subringE(1)[OF assms(1)] unfolding Units_def by auto
      hence "\<zero> = \<one>" if "k = \<zero>"
        using that k'(2) by auto
      thus "k \<in> K - { \<zero> }"
        using k unfolding Units_def by auto
    qed
  qed
qed

lemma (in field) carrier_is_subfield: "subfield (carrier R) R"
  by (auto intro: subfieldI[OF carrier_is_subcring] simp add: field_Units)

lemma subfieldE:
  assumes "subfield K R"
  shows "subring K R" and "subcring K R"
    and "K \<subseteq> carrier R"
    and "\<And>k1 k2. \<lbrakk> k1 \<in> K; k2 \<in> K \<rbrakk> \<Longrightarrow> k1 \<otimes>\<^bsub>R\<^esub> k2 = k2 \<otimes>\<^bsub>R\<^esub> k1"
    and "\<And>k1 k2. \<lbrakk> k1 \<in> K; k2 \<in> K \<rbrakk> \<Longrightarrow> k1 \<otimes>\<^bsub>R\<^esub> k2 = \<zero>\<^bsub>R\<^esub> \<Longrightarrow> k1 = \<zero>\<^bsub>R\<^esub> \<or> k2 = \<zero>\<^bsub>R\<^esub>"
    and "\<one>\<^bsub>R\<^esub> \<noteq> \<zero>\<^bsub>R\<^esub>"
  using subdomain.axioms(1)[OF subfield.axioms(1)[OF assms]] subcring_def
        subdomainE(1, 8, 9, 10)[OF subfield.axioms(1)[OF assms]] by auto

lemma (in ring) subfield_m_inv:
  assumes "subfield K R" and "k \<in> K - { \<zero> }"
  shows "inv k \<in> K - { \<zero> }" and "k \<otimes> inv k = \<one>" and "inv k \<otimes> k = \<one>"
proof -
  have K: "subring K R" "submonoid K R"
    using subfieldE(1)[OF assms(1)] subring.axioms(2) by auto
  have monoid: "monoid (R \<lparr> carrier := K \<rparr>)"
    using submonoid.submonoid_is_monoid[OF subring.axioms(2)[OF K(1)] is_monoid] .

  have "monoid R"
    by (simp add: monoid_axioms)

  hence k: "k \<in> Units (R \<lparr> carrier := K \<rparr>)"
    using subfield.subfield_Units[OF assms(1)] assms(2) by blast
  hence unit_of_R: "k \<in> Units R"
    using assms(2) subringE(1)[OF subfieldE(1)[OF assms(1)]] unfolding Units_def by auto 
  have "inv\<^bsub>(R \<lparr> carrier := K \<rparr>)\<^esub> k \<in> Units (R \<lparr> carrier := K \<rparr>)"
    by (simp add: k monoid monoid.Units_inv_Units)
  hence "inv\<^bsub>(R \<lparr> carrier := K \<rparr>)\<^esub> k \<in> K - { \<zero> }"
    using subfield.subfield_Units[OF assms(1)] by blast
  thus "inv k \<in> K - { \<zero> }" and "k \<otimes> inv k = \<one>" and "inv k \<otimes> k = \<one>"
    using Units_l_inv[OF unit_of_R] Units_r_inv[OF unit_of_R]
    using monoid.m_inv_monoid_consistent[OF monoid_axioms k K(2)] by auto
qed

lemma (in ring) subfield_m_inv_simprule:
  assumes "subfield K R"
  shows "\<lbrakk> k \<in> K - { \<zero> }; a \<in> carrier R \<rbrakk> \<Longrightarrow> k \<otimes> a \<in> K \<Longrightarrow> a \<in> K"
proof -
  note subring_props = subringE[OF subfieldE(1)[OF assms]]

  assume A: "k \<in> K - { \<zero> }" "a \<in> carrier R" "k \<otimes> a \<in> K"
  then obtain k' where k': "k' \<in> K" "k \<otimes> a = k'" by blast
  have inv_k: "inv k \<in> K" "inv k \<otimes> k = \<one>"
    using subfield_m_inv[OF assms A(1)] by auto
  hence "inv k \<otimes> (k \<otimes> a) \<in> K"
    using k' A(3) subring_props(6) by auto
  thus "a \<in> K"
    using m_assoc[of "inv k" k a] A(2) inv_k subring_props(1)
    by (metis (no_types, opaque_lifting) A(1) Diff_iff l_one subsetCE)
qed

lemma (in ring) subfield_iff:
  shows "\<lbrakk> field (R \<lparr> carrier := K \<rparr>); K \<subseteq> carrier R \<rbrakk> \<Longrightarrow> subfield K R"
    and "subfield K R \<Longrightarrow> field (R \<lparr> carrier := K \<rparr>)"
proof-
  assume A: "field (R \<lparr> carrier := K \<rparr>)" "K \<subseteq> carrier R"
  have "\<And>k1 k2. \<lbrakk> k1 \<in> K; k2 \<in> K \<rbrakk> \<Longrightarrow> k1 \<otimes> k2 = k2 \<otimes> k1"
    using comm_monoid.m_comm[OF cring.axioms(2)[OF fieldE(1)[OF A(1)]]]  by simp
  moreover have "subring K R"
    using ring_incl_imp_subring[OF A(2) cring.axioms(1)[OF fieldE(1)[OF A(1)]]] .
  ultimately have "subcring K R"
    using subcringI by simp
  thus "subfield K R"
    using field.field_Units[OF A(1)] subfieldI by auto
next
  assume A: "subfield K R"
  have cring: "cring (R \<lparr> carrier := K \<rparr>)"
    using subcring_iff[OF subringE(1)[OF subfieldE(1)[OF A]]] subfieldE(2)[OF A] by simp
  thus "field (R \<lparr> carrier := K \<rparr>)"
    using cring.cring_fieldI[OF cring] subfield.subfield_Units[OF A] by simp
qed

lemma (in field) subgroup_mult_of :
  assumes "subfield K R"
  shows "subgroup (K - {\<zero>}) (mult_of R)"
proof (intro group.group_incl_imp_subgroup[OF field_mult_group])
  show "K - {\<zero>} \<subseteq> carrier (mult_of R)"
    by (simp add: Diff_mono assms carrier_mult_of subfieldE(3))
  show "group ((mult_of R) \<lparr> carrier := K - {\<zero>} \<rparr>)"
    using field.field_mult_group[OF subfield_iff(2)[OF assms]]
    unfolding mult_of_def by simp
qed


subsection \<open>Subring Homomorphisms\<close>

lemma (in ring) hom_imp_img_subring:
  assumes "h \<in> ring_hom R S" and "subring K R"
  shows "ring (S \<lparr> carrier := h ` K, one := h \<one>, zero := h \<zero> \<rparr>)"
proof -
  have [simp]: "h \<one> = \<one>\<^bsub>S\<^esub>"
    using assms ring_hom_one by blast
  have "ring (R \<lparr> carrier := K \<rparr>)"
    by (simp add: assms(2) subring_is_ring)
  moreover have "h \<in> ring_hom (R \<lparr> carrier := K \<rparr>) S"
    using assms subringE(1)[OF assms (2)] unfolding ring_hom_def
    apply simp
    apply blast
    done
  ultimately show ?thesis
    using ring.ring_hom_imp_img_ring[of "R \<lparr> carrier := K \<rparr>" h S] by simp
qed

lemma (in ring_hom_ring) img_is_subring:
  assumes "subring K R" shows "subring (h ` K) S"
proof -
  have "ring (S \<lparr> carrier := h ` K \<rparr>)"
    using R.hom_imp_img_subring[OF homh assms] hom_zero hom_one by simp
  moreover have "h ` K \<subseteq> carrier S"
    using ring_hom_memE(1)[OF homh] subringE(1)[OF assms] by auto
  ultimately show ?thesis
    using ring_incl_imp_subring by simp
qed

lemma (in ring_hom_ring) img_is_subfield:
  assumes "subfield K R" and "\<one>\<^bsub>S\<^esub> \<noteq> \<zero>\<^bsub>S\<^esub>"
  shows "inj_on h K" and "subfield (h ` K) S"
proof -
  have K: "K \<subseteq> carrier R" "subring K R" "subring (h ` K) S"
    using subfieldE(1)[OF assms(1)] subringE(1) img_is_subring by auto
  have field: "field (R \<lparr> carrier := K \<rparr>)"
    using R.subfield_iff(2) \<open>subfield K R\<close> by blast
  moreover have ring: "ring (R \<lparr> carrier := K \<rparr>)"
    using K R.ring_axioms R.subring_is_ring by blast
  moreover have ringS: "ring (S \<lparr> carrier := h ` K \<rparr>)"
    using subring_is_ring K by simp
  ultimately have h: "h \<in> ring_hom (R \<lparr> carrier := K \<rparr>) (S \<lparr> carrier := h ` K \<rparr>)"
    unfolding ring_hom_def apply auto
    using ring_hom_memE[OF homh] K
    by (meson contra_subsetD)+
  hence ring_hom: "ring_hom_ring (R \<lparr> carrier := K \<rparr>) (S \<lparr> carrier := h ` K \<rparr>) h"
    using ring_axioms ring ringS ring_hom_ringI2 by blast
  have "h ` K \<noteq> { \<zero>\<^bsub>S\<^esub> }"
    using subfieldE(1, 5)[OF assms(1)] subringE(3) assms(2)
    by (metis hom_one image_eqI singletonD)
  thus "inj_on h K"
    using ring_hom_ring.non_trivial_field_hom_imp_inj[OF ring_hom field] by auto

  hence "h \<in> ring_iso (R \<lparr> carrier := K \<rparr>) (S \<lparr> carrier := h ` K \<rparr>)"
    using h unfolding ring_iso_def bij_betw_def by auto
  hence "field (S \<lparr> carrier := h ` K \<rparr>)"
    using field.ring_iso_imp_img_field[OF field, of h "S \<lparr> carrier := h ` K \<rparr>"] by auto
  thus "subfield (h ` K) S"
    using S.subfield_iff[of "h ` K"] K(1) ring_hom_memE(1)[OF homh] by blast
qed

(* NEW ========================================================================== *)
lemma (in ring_hom_ring) induced_ring_hom:
  assumes "subring K R" shows "ring_hom_ring (R \<lparr> carrier := K \<rparr>) S h"
proof -
  have "h \<in> ring_hom (R \<lparr> carrier := K \<rparr>) S"
    using homh subringE(1)[OF assms] unfolding ring_hom_def
    by (auto, meson hom_mult hom_add subsetCE)+
  thus ?thesis
    using R.subring_is_ring[OF assms] ring_axioms
    unfolding ring_hom_ring_def ring_hom_ring_axioms_def by auto
qed

(* NEW ========================================================================== *)
lemma (in ring_hom_ring) inj_on_subgroup_iff_trivial_ker:
  assumes "subring K R"
  shows "inj_on h K \<longleftrightarrow> a_kernel (R \<lparr> carrier := K \<rparr>) S h = { \<zero> }"
  using ring_hom_ring.inj_iff_trivial_ker[OF induced_ring_hom[OF assms]] by simp

lemma (in ring_hom_ring) inv_ring_hom:
  assumes "inj_on h K" and "subring K R"
  shows "ring_hom_ring (S \<lparr> carrier := h ` K \<rparr>) R (inv_into K h)"
proof (intro ring_hom_ringI[OF _ R.ring_axioms], auto)
  show "ring (S \<lparr> carrier := h ` K \<rparr>)"
    using subring_is_ring[OF img_is_subring[OF assms(2)]] .
next
  show "inv_into K h \<one>\<^bsub>S\<^esub> = \<one>\<^bsub>R\<^esub>"
    using assms(1) subringE(3)[OF assms(2)] hom_one by (simp add: inv_into_f_eq)
next
  fix k1 k2
  assume k1: "k1 \<in> K" and k2: "k2 \<in> K"
  with \<open>k1 \<in> K\<close> show "inv_into K h (h k1) \<in> carrier R"
    using assms(1) subringE(1)[OF assms(2)] by (simp add: subset_iff)

  from \<open>k1 \<in> K\<close> and \<open>k2 \<in> K\<close>
  have "h k1 \<oplus>\<^bsub>S\<^esub> h k2 = h (k1 \<oplus>\<^bsub>R\<^esub> k2)" and "k1 \<oplus>\<^bsub>R\<^esub> k2 \<in> K"
   and "h k1 \<otimes>\<^bsub>S\<^esub> h k2 = h (k1 \<otimes>\<^bsub>R\<^esub> k2)" and "k1 \<otimes>\<^bsub>R\<^esub> k2 \<in> K"
    using subringE(1,6,7)[OF assms(2)] by (simp add: subset_iff)+
  thus "inv_into K h (h k1 \<oplus>\<^bsub>S\<^esub> h k2) = inv_into K h (h k1) \<oplus>\<^bsub>R\<^esub> inv_into K h (h k2)"
   and "inv_into K h (h k1 \<otimes>\<^bsub>S\<^esub> h k2) = inv_into K h (h k1) \<otimes>\<^bsub>R\<^esub> inv_into K h (h k2)"
    using assms(1) k1 k2 by simp+
qed

end

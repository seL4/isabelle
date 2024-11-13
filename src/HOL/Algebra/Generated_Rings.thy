(* ************************************************************************** *)
(* Title:      Generated_Rings.thy                                            *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)

theory Generated_Rings
  imports Subrings
begin

section\<open>Generated Rings\<close>

inductive_set
  generate_ring :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for R and H where
    one:   "\<one>\<^bsub>R\<^esub> \<in> generate_ring R H"
  | incl:  "h \<in> H \<Longrightarrow> h \<in> generate_ring R H"
  | a_inv: "h \<in> generate_ring R H \<Longrightarrow> \<ominus>\<^bsub>R\<^esub> h \<in> generate_ring R H"
  | eng_add : "\<lbrakk> h1 \<in> generate_ring R H; h2 \<in> generate_ring R H \<rbrakk> \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> generate_ring R H"
  | eng_mult: "\<lbrakk> h1 \<in> generate_ring R H; h2 \<in> generate_ring R H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> generate_ring R H"

subsection\<open>Basic Properties of Generated Rings - First Part\<close>

lemma (in ring) generate_ring_in_carrier:
  assumes "H \<subseteq> carrier R"
  shows "h \<in> generate_ring R H \<Longrightarrow> h \<in> carrier R"
  apply (induction rule: generate_ring.induct) using assms 
  by blast+

lemma (in ring) generate_ring_incl:
  assumes "H \<subseteq> carrier R"
  shows "generate_ring R H \<subseteq> carrier R"
  using generate_ring_in_carrier[OF assms] by auto

lemma (in ring) zero_in_generate: "\<zero>\<^bsub>R\<^esub> \<in> generate_ring R H"
  using one a_inv by (metis generate_ring.eng_add one_closed r_neg)

lemma (in ring) generate_ring_is_subring:
  assumes "H \<subseteq> carrier R"
  shows "subring (generate_ring R H) R"
  by (auto intro!: subringI[of "generate_ring R H"]
         simp add: generate_ring_in_carrier[OF assms] one a_inv eng_mult eng_add)

lemma (in ring) generate_ring_is_ring:
  assumes "H \<subseteq> carrier R"
  shows "ring (R \<lparr> carrier := generate_ring R H \<rparr>)"
  using subring_iff[OF generate_ring_incl[OF assms]] generate_ring_is_subring[OF assms] by simp

lemma (in ring) generate_ring_min_subring1:
  assumes "H \<subseteq> carrier R" and "subring E R" "H \<subseteq> E"
  shows "generate_ring R H \<subseteq> E"
proof
  fix h assume h: "h \<in> generate_ring R H"
  show "h \<in> E"
    using h and assms(3)
      by (induct rule: generate_ring.induct)
         (auto simp add: subringE(3,5-7)[OF assms(2)])
qed

lemma (in ring) generate_ringI:
  assumes "H \<subseteq> carrier R"
    and "subring E R" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> subring K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate_ring R H"
proof
  show "E \<subseteq> generate_ring R H"
    using assms generate_ring_is_subring generate_ring.incl by (metis subset_iff)
  show "generate_ring R H \<subseteq> E"
    using generate_ring_min_subring1[OF assms(1-3)] by simp
qed

lemma (in ring) generate_ringE:
  assumes "H \<subseteq> carrier R" and "E = generate_ring R H"
  shows "subring E R" and "H \<subseteq> E" and "\<And>K. \<lbrakk> subring K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "subring E R" using assms generate_ring_is_subring by simp
  show "H \<subseteq> E" using assms(2) by (simp add: generate_ring.incl subsetI)
  show "\<And>K. subring K R  \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms generate_ring_min_subring1 by auto
qed

lemma (in ring) generate_ring_min_subring2:
  assumes "H \<subseteq> carrier R"
  shows "generate_ring R H = \<Inter>{K. subring K R \<and> H \<subseteq> K}"
proof
  have "subring (generate_ring R H) R \<and> H \<subseteq> generate_ring R H"
    by (simp add: assms generate_ringE(2) generate_ring_is_subring)
  thus "\<Inter>{K. subring K R \<and> H \<subseteq> K} \<subseteq> generate_ring R H" by blast
next
  have "\<And>K. subring K R \<and> H \<subseteq> K \<Longrightarrow> generate_ring R H \<subseteq> K"
    by (simp add: assms generate_ring_min_subring1)
  thus "generate_ring R H \<subseteq> \<Inter>{K. subring K R \<and> H \<subseteq> K}" by blast
qed

lemma (in ring) mono_generate_ring:
  assumes "I \<subseteq> J" and "J \<subseteq> carrier R"
  shows "generate_ring R I \<subseteq> generate_ring R J"
proof-
  have "I \<subseteq> generate_ring R J "
    using assms generate_ringE(2) by blast
  thus "generate_ring R I \<subseteq> generate_ring R J"
    using generate_ring_min_subring1[of I "generate_ring R J"] assms generate_ring_is_subring[OF assms(2)]
    by blast
qed

lemma (in ring) subring_gen_incl :
  assumes "subring H R"
    and  "subring K R"
    and "I \<subseteq> H"
    and "I \<subseteq> K"
  shows "generate_ring (R\<lparr>carrier := K\<rparr>) I \<subseteq> generate_ring (R\<lparr>carrier := H\<rparr>) I"
proof
  have incl_HK: "generate_ring (R \<lparr> carrier := J \<rparr>) I \<subseteq> J" if J_def : "subring J R" "I \<subseteq> J" for J
    using ring.mono_generate_ring[of "(R\<lparr>carrier := J\<rparr>)" I J ] subring_is_ring[OF J_def(1)]
      ring.generate_ring_in_carrier[of "R\<lparr>carrier := J\<rparr>"]  ring_axioms J_def(2)
    by auto

  fix x
  have "x \<in> generate_ring (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_ring (R\<lparr>carrier := H\<rparr>) I" 
  proof (induction  rule : generate_ring.induct)
    case one
    have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>" by simp
    moreover have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub>" by simp
    ultimately show ?case using assms generate_ring.one by metis
  next
    case (incl h) thus ?case using generate_ring.incl by force
  next
    case (a_inv h)
    have "a_inv (R\<lparr>carrier := K\<rparr>) h = a_inv R h" 
      using assms group.m_inv_consistent[of "add_monoid R" K] a_comm_group incl_HK[of K] a_inv
      unfolding subring_def comm_group_def a_inv_def by auto
    moreover have "a_inv (R\<lparr>carrier := H\<rparr>) h = a_inv R h"
      using assms group.m_inv_consistent[of "add_monoid R" H] a_comm_group incl_HK[of H] a_inv
      unfolding subring_def comm_group_def a_inv_def by auto
    ultimately show ?case using generate_ring.a_inv a_inv.IH by fastforce
  next
    case (eng_add h1 h2)
    thus ?case using incl_HK assms generate_ring.eng_add by force
  next
    case (eng_mult h1 h2)
    thus ?case using generate_ring.eng_mult by force
  qed
  thus "x \<in> generate_ring (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_ring (R\<lparr>carrier := H\<rparr>) I"
    by auto
qed

lemma (in ring) subring_gen_equality:
  assumes "subring H R" "K \<subseteq> H"
  shows "generate_ring R K = generate_ring (R \<lparr> carrier := H \<rparr>) K"
  using subring_gen_incl[OF assms(1)carrier_is_subring assms(2)] assms subringE(1)
        subring_gen_incl[OF carrier_is_subring assms(1) _ assms(2)]
  by force

end

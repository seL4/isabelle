(*  Title:      HOL/Algebra/Generated_Fields.thy
    Author:     Martin Baillon
*)

theory Generated_Fields
imports Generated_Rings Subrings Multiplicative_Group
begin

inductive_set
  generate_field :: "('a, 'b) ring_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for R and H where
    one  : "\<one>\<^bsub>R\<^esub> \<in> generate_field R H"
  | incl : "h \<in> H \<Longrightarrow> h \<in> generate_field R H"
  | a_inv: "h \<in> generate_field R H \<Longrightarrow> \<ominus>\<^bsub>R\<^esub> h \<in> generate_field R H"
  | m_inv: "\<lbrakk> h \<in> generate_field R H; h \<noteq> \<zero>\<^bsub>R\<^esub> \<rbrakk> \<Longrightarrow> inv\<^bsub>R\<^esub> h \<in> generate_field R H"
  | eng_add : "\<lbrakk> h1 \<in> generate_field R H; h2 \<in> generate_field R H \<rbrakk> \<Longrightarrow> h1 \<oplus>\<^bsub>R\<^esub> h2 \<in> generate_field R H"
  | eng_mult: "\<lbrakk> h1 \<in> generate_field R H; h2 \<in> generate_field R H \<rbrakk> \<Longrightarrow> h1 \<otimes>\<^bsub>R\<^esub> h2 \<in> generate_field R H"


subsection\<open>Basic Properties of Generated Rings - First Part\<close>

lemma (in field) generate_field_in_carrier:
  assumes "H \<subseteq> carrier R"
  shows "h \<in> generate_field R H \<Longrightarrow> h \<in> carrier R"
  apply (induction rule: generate_field.induct)
  using assms field_Units
  by blast+

lemma (in field) generate_field_incl:
  assumes "H \<subseteq> carrier R"
  shows "generate_field R H \<subseteq> carrier R"
  using generate_field_in_carrier[OF assms] by auto
       
lemma (in field) zero_in_generate: "\<zero>\<^bsub>R\<^esub> \<in> generate_field R H"
  using one a_inv generate_field.eng_add one_closed r_neg
  by metis

lemma (in field) generate_field_is_subfield:
  assumes "H \<subseteq> carrier R"
  shows "subfield (generate_field R H) R"
proof (intro subfieldI', simp_all add: m_inv)
  show "subring (generate_field R H) R"
    by (auto intro: subringI[of "generate_field R H"]
             simp add: eng_add a_inv eng_mult one generate_field_in_carrier[OF assms])
qed

lemma (in field) generate_field_is_add_subgroup:
  assumes "H \<subseteq> carrier R"
  shows "subgroup (generate_field R H) (add_monoid R)"
  using subring.axioms(1)[OF subfieldE(1)[OF generate_field_is_subfield[OF assms]]] .

lemma (in field) generate_field_is_field :
  assumes "H \<subseteq> carrier R"
  shows "field (R \<lparr> carrier := generate_field R H \<rparr>)"
  using subfield_iff generate_field_is_subfield assms by simp

lemma (in field) generate_field_min_subfield1:
  assumes "H \<subseteq> carrier R"
    and "subfield E R" "H \<subseteq> E"
  shows "generate_field R H \<subseteq> E"
proof
  fix h
  assume h: "h \<in> generate_field R H"
  show "h \<in> E"
    using h and assms(3) and subfield_m_inv[OF assms(2)]
    by (induct rule: generate_field.induct)
       (auto simp add: subringE(3,5-7)[OF subfieldE(1)[OF assms(2)]])
qed

lemma (in field) generate_fieldI:
  assumes "H \<subseteq> carrier R"
    and "subfield E R" "H \<subseteq> E"
    and "\<And>K. \<lbrakk> subfield K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
  shows "E = generate_field R H"
proof
  show "E \<subseteq> generate_field R H"
    using assms generate_field_is_subfield generate_field.incl by (metis subset_iff)
  show "generate_field R H \<subseteq> E"
    using generate_field_min_subfield1[OF assms(1-3)] by simp
qed

lemma (in field) generate_fieldE:
  assumes "H \<subseteq> carrier R" and "E = generate_field R H"
  shows "subfield E R" and "H \<subseteq> E" and "\<And>K. \<lbrakk> subfield K R; H \<subseteq> K \<rbrakk> \<Longrightarrow> E \<subseteq> K"
proof -
  show "subfield E R" using assms generate_field_is_subfield by simp
  show "H \<subseteq> E" using assms(2) by (simp add: generate_field.incl subsetI)
  show "\<And>K. subfield K R  \<Longrightarrow> H \<subseteq> K \<Longrightarrow> E \<subseteq> K"
    using assms generate_field_min_subfield1 by auto
qed

lemma (in field) generate_field_min_subfield2:
  assumes "H \<subseteq> carrier R"
  shows "generate_field R H = \<Inter>{K. subfield K R \<and> H \<subseteq> K}"
proof
  have "subfield (generate_field R H) R \<and> H \<subseteq> generate_field R H"
    by (simp add: assms generate_fieldE(2) generate_field_is_subfield)
  thus "\<Inter>{K. subfield K R \<and> H \<subseteq> K} \<subseteq> generate_field R H" by blast
next
  have "\<And>K. subfield K R \<and> H \<subseteq> K \<Longrightarrow> generate_field R H \<subseteq> K"
    by (simp add: assms generate_field_min_subfield1)
  thus "generate_field R H \<subseteq> \<Inter>{K. subfield K R \<and> H \<subseteq> K}" by blast
qed

lemma (in field) mono_generate_field:
  assumes "I \<subseteq> J" and "J \<subseteq> carrier R"
  shows "generate_field R I \<subseteq> generate_field R J"
proof-
  have "I \<subseteq> generate_field R J "
    using assms generate_fieldE(2) by blast
  thus "generate_field R I \<subseteq> generate_field R J"
    using generate_field_min_subfield1[of I "generate_field R J"] assms generate_field_is_subfield[OF assms(2)]
    by blast
qed


lemma (in field) subfield_gen_incl :
  assumes "subfield H R"
    and  "subfield K R"
    and "I \<subseteq> H"
    and "I \<subseteq> K"
  shows "generate_field (R\<lparr>carrier := K\<rparr>) I \<subseteq> generate_field (R\<lparr>carrier := H\<rparr>) I"
proof
  have incl_HK: "generate_field (R \<lparr> carrier := J \<rparr>) I \<subseteq> J"
    if J_def : "subfield J R" "I \<subseteq> J" for J
    using field.mono_generate_field[of "(R\<lparr>carrier := J\<rparr>)" I J] subfield_iff(2)[OF J_def(1)]
      field.generate_field_in_carrier[of "R\<lparr>carrier := J\<rparr>"]  field_axioms J_def
    by auto

  fix x
  have "x \<in> generate_field (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_field (R\<lparr>carrier := H\<rparr>) I"
  proof (induction  rule : generate_field.induct)
    case one
    have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub>" by simp
    moreover have "\<one>\<^bsub>R\<lparr>carrier := H\<rparr>\<^esub> \<otimes> \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub> = \<one>\<^bsub>R\<lparr>carrier := K\<rparr>\<^esub>" by simp
    ultimately show ?case using assms generate_field.one by metis
  next
    case (incl h)
    thus ?case using generate_field.incl by force
  next
    case (a_inv h)
    have "a_inv (R\<lparr>carrier := K\<rparr>) h = a_inv R h" 
      using assms group.m_inv_consistent[of "add_monoid R" K] a_comm_group incl_HK[of K] a_inv
        subring.axioms(1)[OF subfieldE(1)[OF assms(2)]]
      unfolding comm_group_def a_inv_def by auto
    moreover have "a_inv (R\<lparr>carrier := H\<rparr>) h = a_inv R h"
      using assms group.m_inv_consistent[of "add_monoid R" H] a_comm_group incl_HK[of H] a_inv
        subring.axioms(1)[OF subfieldE(1)[OF assms(1)]]
      unfolding  comm_group_def a_inv_def by auto
    ultimately show ?case using generate_field.a_inv a_inv.IH by fastforce
  next
    case (m_inv h) 
    have h_K : "h \<in> (K - {\<zero>})" using incl_HK[OF assms(2) assms(4)] m_inv by auto
    hence "m_inv (R\<lparr>carrier := K\<rparr>) h = m_inv R h" 
      using  field.m_inv_mult_of[OF subfield_iff(2)[OF assms(2)]]
        group.m_inv_consistent[of "mult_of R" "K - {\<zero>}"] field_mult_group units_of_inv
        subgroup_mult_of subfieldE[OF assms(2)] unfolding mult_of_def apply simp
      by (metis h_K mult_of_def mult_of_is_Units subgroup.mem_carrier units_of_carrier assms(2))
    moreover have h_H : "h \<in> (H - {\<zero>})" using incl_HK[OF assms(1) assms(3)] m_inv by auto
    hence "m_inv (R\<lparr>carrier := H\<rparr>) h = m_inv R h"
      using  field.m_inv_mult_of[OF subfield_iff(2)[OF assms(1)]]
        group.m_inv_consistent[of "mult_of R" "H - {\<zero>}"] field_mult_group 
        subgroup_mult_of[OF assms(1)]  unfolding mult_of_def apply simp
      by (metis h_H field_Units m_inv_mult_of mult_of_is_Units subgroup.mem_carrier units_of_def)
    ultimately show ?case using generate_field.m_inv m_inv.IH h_H by fastforce
  next
    case (eng_add h1 h2)
    thus ?case using incl_HK assms generate_field.eng_add by force
  next
    case (eng_mult h1 h2)
    thus ?case using generate_field.eng_mult by force
  qed
  thus "x \<in> generate_field (R\<lparr>carrier := K\<rparr>) I \<Longrightarrow> x \<in> generate_field (R\<lparr>carrier := H\<rparr>) I"
    by auto
qed

lemma (in field) subfield_gen_equality:
  assumes "subfield H R" "K \<subseteq> H"
  shows "generate_field R K = generate_field (R \<lparr> carrier := H \<rparr>) K"
  using subfield_gen_incl[OF assms(1) carrier_is_subfield assms(2)] assms subringE(1)
        subfield_gen_incl[OF carrier_is_subfield assms(1) _ assms(2)] subfieldE(1)[OF assms(1)]
  by force

end

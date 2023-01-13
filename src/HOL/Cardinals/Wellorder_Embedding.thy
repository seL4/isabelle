(*  Title:      HOL/Cardinals/Wellorder_Embedding.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Well-order embeddings.
*)

section \<open>Well-Order Embeddings\<close>

theory Wellorder_Embedding
  imports Fun_More Wellorder_Relation
begin

subsection \<open>Auxiliaries\<close>

lemma UNION_bij_betw_ofilter:
  assumes WELL: "Well_order r" and
    OF: "\<And> i. i \<in> I \<Longrightarrow> ofilter r (A i)" and
    BIJ: "\<And> i. i \<in> I \<Longrightarrow> bij_betw f (A i) (A' i)"
  shows "bij_betw f (\<Union>i \<in> I. A i) (\<Union>i \<in> I. A' i)"
proof-
  have "wo_rel r" using WELL by (simp add: wo_rel_def)
  hence "\<And> i j. \<lbrakk>i \<in> I; j \<in> I\<rbrakk> \<Longrightarrow> A i \<le> A j \<or> A j \<le> A i"
    using wo_rel.ofilter_linord[of r] OF by blast
  with WELL BIJ show ?thesis
    by (auto simp add: bij_betw_UNION_chain)
qed


subsection \<open>(Well-order) embeddings, strict embeddings, isomorphisms and order-compatible
functions\<close>

lemma embed_halfcong:
  assumes "\<And> a. a \<in> Field r \<Longrightarrow> f a = g a" and "embed r r' f"
  shows "embed r r' g"
  by (smt (verit, del_insts) assms bij_betw_cong embed_def in_mono under_Field)

lemma embed_cong[fundef_cong]:
  assumes "\<And> a. a \<in> Field r \<Longrightarrow> f a = g a"
  shows "embed r r' f = embed r r' g"
  by (metis assms embed_halfcong)

lemma embedS_cong[fundef_cong]:
  assumes "\<And> a. a \<in> Field r \<Longrightarrow> f a = g a"
  shows "embedS r r' f = embedS r r' g"
  unfolding embedS_def using assms
    embed_cong[of r f g r'] bij_betw_cong[of "Field r" f g "Field r'"] by blast

lemma iso_cong[fundef_cong]:
  assumes "\<And> a. a \<in> Field r \<Longrightarrow> f a = g a"
  shows "iso r r' f = iso r r' g"
  unfolding iso_def using assms
    embed_cong[of r f g r'] bij_betw_cong[of "Field r" f g "Field r'"] by blast

lemma id_compat: "compat r r id"
  by(auto simp add: id_def compat_def)

lemma comp_compat:
  "\<lbrakk>compat r r' f; compat r' r'' f'\<rbrakk> \<Longrightarrow> compat r r'' (f' o f)"
  by(auto simp add: comp_def compat_def)

corollary one_set_greater:
  "(\<exists>f::'a \<Rightarrow> 'a'. f ` A \<le> A' \<and> inj_on f A) \<or> (\<exists>g::'a' \<Rightarrow> 'a. g ` A' \<le> A \<and> inj_on g A')"
proof-
  obtain r where "well_order_on A r" by (fastforce simp add: well_order_on)
  hence 1: "A = Field r \<and> Well_order r"
    using well_order_on_Well_order by auto
  obtain r' where 2: "well_order_on A' r'" by (fastforce simp add: well_order_on)
  hence 2: "A' = Field r' \<and> Well_order r'"
    using well_order_on_Well_order by auto
  hence "(\<exists>f. embed r r' f) \<or> (\<exists>g. embed r' r g)"
    using 1 2 by (auto simp add: wellorders_totally_ordered)
  moreover
  {fix f assume "embed r r' f"
    hence "f`A \<le> A' \<and> inj_on f A"
      using 1 2 by (auto simp add: embed_Field embed_inj_on)
  }
  moreover
  {fix g assume "embed r' r g"
    hence "g`A' \<le> A \<and> inj_on g A'"
      using 1 2 by (auto simp add: embed_Field embed_inj_on)
  }
  ultimately show ?thesis by blast
qed

corollary one_type_greater:
  "(\<exists>f::'a \<Rightarrow> 'a'. inj f) \<or> (\<exists>g::'a' \<Rightarrow> 'a. inj g)"
  using one_set_greater[of UNIV UNIV] by auto


subsection \<open>Uniqueness of embeddings\<close>

lemma comp_embedS:
  assumes WELL: "Well_order r" and WELL': "Well_order r'" and WELL'': "Well_order r''"
    and  EMB: "embedS r r' f" and EMB': "embedS r' r'' f'"
  shows "embedS r r'' (f' o f)"
  using EMB EMB' WELL WELL' embedS_comp_embed embedS_def by blast

lemma iso_iff4:
  assumes WELL: "Well_order r"  and WELL': "Well_order r'"
  shows "iso r r' f = (embed r r' f \<and> embed r' r (inv_into (Field r) f))"
  using assms embed_bothWays_iso
  by(unfold iso_def, auto simp add: inv_into_Field_embed_bij_betw)

lemma embed_embedS_iso:
  "embed r r' f = (embedS r r' f \<or> iso r r' f)"
  unfolding embedS_def iso_def by blast

lemma not_embedS_iso:
  "\<not> (embedS r r' f \<and> iso r r' f)"
  unfolding embedS_def iso_def by blast

lemma embed_embedS_iff_not_iso:
  assumes "embed r r' f"
  shows "embedS r r' f = (\<not> iso r r' f)"
  using assms unfolding embedS_def iso_def by blast

lemma iso_inv_into:
  assumes WELL: "Well_order r" and ISO: "iso r r' f"
  shows "iso r' r (inv_into (Field r) f)"
  by (meson ISO WELL bij_betw_inv_into inv_into_Field_embed_bij_betw iso_def iso_iff iso_iff2)

lemma embedS_or_iso:
  assumes WELL: "Well_order r" and WELL': "Well_order r'"
  shows "(\<exists>g. embedS r r' g) \<or> (\<exists>h. embedS r' r h) \<or> (\<exists>f. iso r r' f)"
  by (metis WELL WELL' embed_embedS_iso embed_embedS_iso iso_iff4 wellorders_totally_ordered)

end

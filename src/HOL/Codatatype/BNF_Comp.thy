(*  Title:      HOL/Codatatype/BNF_Comp.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

header {* Composition of Bounded Natural Functors *}

theory BNF_Comp
imports Basic_BNFs
begin

lemma empty_natural: "(\<lambda>_. {}) o f = image g o (\<lambda>_. {})"
by (rule ext) simp

lemma Union_natural: "Union o image (image f) = image f o Union"
by (rule ext) (auto simp only: o_apply)

lemma in_Union_o_assoc: "x \<in> (Union o gset o gmap) A \<Longrightarrow> x \<in> (Union o (gset o gmap)) A"
by (unfold o_assoc)

lemma comp_single_set_bd:
  assumes fbd_Card_order: "Card_order fbd" and
    fset_bd: "\<And>x. |fset x| \<le>o fbd" and
    gset_bd: "\<And>x. |gset x| \<le>o gbd"
  shows "|\<Union>fset ` gset x| \<le>o gbd *c fbd"
apply (subst sym[OF SUP_def])
apply (rule ordLeq_transitive)
apply (rule card_of_UNION_Sigma)
apply (subst SIGMA_CSUM)
apply (rule ordLeq_transitive)
apply (rule card_of_Csum_Times')
apply (rule fbd_Card_order)
apply (rule ballI)
apply (rule fset_bd)
apply (rule ordLeq_transitive)
apply (rule cprod_mono1)
apply (rule gset_bd)
apply (rule ordIso_imp_ordLeq)
apply (rule ordIso_refl)
apply (rule Card_order_cprod)
done

lemma Union_image_insert: "\<Union>f ` insert a B = f a \<union> \<Union>f ` B"
by simp

lemma Union_image_empty: "A \<union> \<Union>f ` {} = A"
by simp

lemma image_o_collect: "collect ((\<lambda>f. image g o f) ` F) = image g o collect F"
by (rule ext) (auto simp add: collect_def)

lemma conj_subset_def: "A \<subseteq> {x. P x \<and> Q x} = (A \<subseteq> {x. P x} \<and> A \<subseteq> {x. Q x})"
by blast

lemma UN_image_subset: "\<Union>f ` g x \<subseteq> X = (g x \<subseteq> {x. f x \<subseteq> X})"
by blast

lemma comp_set_bd_Union_o_collect: "|\<Union>\<Union>(\<lambda>f. f x) ` X| \<le>o hbd \<Longrightarrow> |(Union \<circ> collect X) x| \<le>o hbd"
by (unfold o_apply collect_def SUP_def)

lemma wpull_cong:
"\<lbrakk>A' = A; B1' = B1; B2' = B2; wpull A B1 B2 f1 f2 p1 p2\<rbrakk> \<Longrightarrow> wpull A' B1' B2' f1 f2 p1 p2"
by simp

lemma Id_def': "Id = {(a,b). a = b}"
by auto

lemma Gr_fst_snd: "(Gr R fst)^-1 O Gr R snd = R"
unfolding Gr_def by auto

lemma subst_rel_def: "A = B \<Longrightarrow> (Gr A f)^-1 O Gr A g = (Gr B f)^-1 O Gr B g"
by simp

lemma abs_pred_def: "\<lbrakk>\<And>x y. (x, y) \<in> rel = pred x y\<rbrakk> \<Longrightarrow> rel = Collect (split pred)"
by auto

lemma Collect_split_cong: "Collect (split pred) = Collect (split pred') \<Longrightarrow> pred = pred'"
by blast

lemma pred_def_abs: "rel = Collect (split pred) \<Longrightarrow> pred = (\<lambda>x y. (x, y) \<in> rel)"
by auto

lemma mem_Id_eq_eq: "(\<lambda>x y. (x, y) \<in> Id) = (op =)"
by simp

ML_file "Tools/bnf_comp_tactics.ML"
ML_file "Tools/bnf_comp.ML"

end

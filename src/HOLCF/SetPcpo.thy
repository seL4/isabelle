(*  Title:      HOLCF/SetPcpo.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Set as a pointed cpo *}

theory SetPcpo
imports Adm
begin

instantiation bool :: po
begin

definition
  less_bool_def: "(op \<sqsubseteq>) = (op \<longrightarrow>)"

instance
by (intro_classes, unfold less_bool_def, safe)

end

lemma less_set_eq: "(op \<sqsubseteq>) = (op \<subseteq>)"
  by (simp add: less_fun_def less_bool_def le_fun_def le_bool_def expand_fun_eq)

instance bool :: finite_po ..

lemma Union_is_lub: "A <<| Union A"
unfolding is_lub_def is_ub_def less_set_eq by fast

instance bool :: cpo ..

lemma lub_eq_Union: "lub = Union"
by (rule ext, rule thelubI [OF Union_is_lub])

instance bool :: pcpo
proof
  have "\<forall>y::bool. False \<sqsubseteq> y" unfolding less_bool_def by simp
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed

lemma UU_eq_empty: "\<bottom> = {}"
by (rule UU_I [symmetric], simp add: less_set_eq)

lemmas set_cpo_simps = less_set_eq lub_eq_Union UU_eq_empty

subsection {* Admissibility of set predicates *}

lemma adm_nonempty: "adm (\<lambda>A. \<exists>x. x \<in> A)"
by (rule admI, force simp add: lub_eq_Union)

lemma adm_in: "adm (\<lambda>A. x \<in> A)"
by (rule admI, simp add: lub_eq_Union)

lemma adm_not_in: "adm (\<lambda>A. x \<notin> A)"
by (rule admI, simp add: lub_eq_Union)

lemma adm_Ball: "(\<And>x. adm (\<lambda>A. P A x)) \<Longrightarrow> adm (\<lambda>A. \<forall>x\<in>A. P A x)"
unfolding Ball_def by (simp add: adm_not_in)

lemma adm_Bex: "adm (\<lambda>A. Bex A P)"
by (rule admI, simp add: lub_eq_Union)

lemma adm_subset: "adm (\<lambda>A. A \<subseteq> B)"
by (rule admI, auto simp add: lub_eq_Union)

lemma adm_superset: "adm (\<lambda>A. B \<subseteq> A)"
by (rule admI, auto simp add: lub_eq_Union)

lemmas adm_set_lemmas =
  adm_nonempty adm_in adm_not_in adm_Bex adm_Ball adm_subset adm_superset

subsection {* Compactness *}

lemma compact_empty: "compact {}"
by (fold UU_eq_empty, simp)

lemma compact_insert: "compact A \<Longrightarrow> compact (insert x A)"
unfolding compact_def set_cpo_simps
by (simp add: adm_set_lemmas)

lemma finite_imp_compact: "finite A \<Longrightarrow> compact A"
by (induct A set: finite, rule compact_empty, erule compact_insert)

end

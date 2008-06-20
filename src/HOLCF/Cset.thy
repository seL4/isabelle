(*  Title:      HOLCF/Cset.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Set as a pointed cpo *}

theory Cset
imports Adm
begin

subsection {* Type definition *}

defaultsort type

typedef (open) 'a cset = "UNIV :: 'a set set" ..

declare Rep_cset_inverse [simp]
declare Abs_cset_inverse [simplified, simp]

instantiation cset :: (type) po
begin

definition
  sq_le_cset_def:
    "x \<sqsubseteq> y \<longleftrightarrow> Rep_cset x \<subseteq> Rep_cset y"

instance proof
  fix x :: "'a cset"
  show "x \<sqsubseteq> x"
    unfolding sq_le_cset_def
    by (rule subset_refl)
next
  fix x y z :: "'a cset"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> z" thus "x \<sqsubseteq> z"
    unfolding sq_le_cset_def
    by (rule subset_trans)
next
  fix x y :: "'a cset"
  assume "x \<sqsubseteq> y" "y \<sqsubseteq> x" thus "x = y"
    unfolding sq_le_cset_def Rep_cset_inject [symmetric]
    by (rule subset_antisym)
qed

end

lemma is_lub_UNION: "A <<| Abs_cset (UNION A Rep_cset)"
unfolding is_lub_def is_ub_def sq_le_cset_def by auto

instance cset :: (type) cpo
proof
  fix S :: "nat \<Rightarrow> 'a cset"
  show "\<exists>x. range S <<| x"
    by (fast intro: is_lub_UNION)
qed

lemma lub_cset: "lub A = Abs_cset (UNION A Rep_cset)"
by (rule thelubI [OF is_lub_UNION])

lemma Rep_cset_lub: "Rep_cset (lub A) = UNION A Rep_cset"
by (simp add: lub_cset)

text {* cset is pointed *}

lemma cset_minimal: "Abs_cset {} \<sqsubseteq> x"
unfolding sq_le_cset_def by simp

instance cset :: (type) pcpo
by intro_classes (fast intro: cset_minimal)

lemma inst_cset_pcpo: "\<bottom> = Abs_cset {}"
by (rule cset_minimal [THEN UU_I, symmetric])

lemma Rep_cset_UU: "Rep_cset \<bottom> = {}"
unfolding inst_cset_pcpo by simp

lemmas Rep_cset_simps = Rep_cset_lub Rep_cset_UU

subsection {* Admissibility of set predicates *}

lemma adm_nonempty: "adm (\<lambda>A. \<exists>x. x \<in> Rep_cset A)"
by (rule admI, simp add: Rep_cset_lub, fast)

lemma adm_in: "adm (\<lambda>A. x \<in> Rep_cset A)"
by (rule admI, simp add: Rep_cset_lub)

lemma adm_not_in: "adm (\<lambda>A. x \<notin> Rep_cset A)"
by (rule admI, simp add: Rep_cset_lub)

lemma adm_Ball: "(\<And>x. adm (\<lambda>A. P A x)) \<Longrightarrow> adm (\<lambda>A. \<forall>x\<in>Rep_cset A. P A x)"
unfolding Ball_def by (simp add: adm_not_in)

lemma adm_Bex: "adm (\<lambda>A. \<exists>x\<in>Rep_cset A. P x)"
by (rule admI, simp add: Rep_cset_lub)

lemma adm_subset: "adm (\<lambda>A. Rep_cset A \<subseteq> B)"
by (rule admI, auto simp add: Rep_cset_lub)

lemma adm_superset: "adm (\<lambda>A. B \<subseteq> Rep_cset A)"
by (rule admI, auto simp add: Rep_cset_lub)

lemmas adm_set_lemmas =
  adm_nonempty adm_in adm_not_in adm_Bex adm_Ball adm_subset adm_superset

subsection {* Compactness *}

lemma compact_empty: "compact (Abs_cset {})"
by (fold inst_cset_pcpo, simp)

lemma compact_insert: "compact (Abs_cset A) \<Longrightarrow> compact (Abs_cset (insert x A))"
unfolding compact_def sq_le_cset_def
by (simp add: adm_set_lemmas)

lemma finite_imp_compact: "finite A \<Longrightarrow> compact (Abs_cset A)"
by (induct A set: finite, rule compact_empty, erule compact_insert)

end

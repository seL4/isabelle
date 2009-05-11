(* Author: Florian Haftmann, TU Muenchen *)

header {* Preorders with explicit equivalence relation *}

theory Preorder
imports Orderings
begin

class preorder_equiv = preorder
begin

definition equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "equiv x y \<longleftrightarrow> x \<le> y \<and> y \<le> x"

notation
  equiv ("op ~~") and
  equiv ("(_/ ~~ _)" [51, 51] 50)
  
notation (xsymbols)
  equiv ("op \<approx>") and
  equiv ("(_/ \<approx> _)"  [51, 51] 50)

notation (HTML output)
  equiv ("op \<approx>") and
  equiv ("(_/ \<approx> _)"  [51, 51] 50)

lemma refl [iff]:
  "x \<approx> x"
  unfolding equiv_def by simp

lemma trans:
  "x \<approx> y \<Longrightarrow> y \<approx> z \<Longrightarrow> x \<approx> z"
  unfolding equiv_def by (auto intro: order_trans)

lemma antisym:
  "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x \<approx> y"
  unfolding equiv_def ..

lemma less_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> x \<approx> y"
  by (auto simp add: equiv_def less_le_not_le)

lemma le_less: "x \<le> y \<longleftrightarrow> x < y \<or> x \<approx> y"
  by (auto simp add: equiv_def less_le)

lemma le_imp_less_or_eq: "x \<le> y \<Longrightarrow> x < y \<or> x \<approx> y"
  by (simp add: less_le)

lemma less_imp_not_eq: "x < y \<Longrightarrow> x \<approx> y \<longleftrightarrow> False"
  by (simp add: less_le)

lemma less_imp_not_eq2: "x < y \<Longrightarrow> y \<approx> x \<longleftrightarrow> False"
  by (simp add: equiv_def less_le)

lemma neq_le_trans: "\<not> a \<approx> b \<Longrightarrow> a \<le> b \<Longrightarrow> a < b"
  by (simp add: less_le)

lemma le_neq_trans: "a \<le> b \<Longrightarrow> \<not> a \<approx> b \<Longrightarrow> a < b"
  by (simp add: less_le)

lemma antisym_conv: "y \<le> x \<Longrightarrow> x \<le> y \<longleftrightarrow> x \<approx> y"
  by (simp add: equiv_def)

end

end

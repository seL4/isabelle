(*  Title:      HOL/BNF/BNF_FP_N2M.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Flattening of nested to mutual (co)recursion.
*)

header {* Flattening of Nested to Mutual (Co)recursion *}

theory BNF_FP_N2M
imports "~~/src/HOL/BNF/BNF_FP_Basic"
begin

lemma eq_le_Grp_id_iff: "(op = \<le> BNF_Util.Grp (Collect R) id) = (All R)"
  unfolding Grp_def id_apply by blast

lemma Grp_id_mono_subst: "(\<And>x y. BNF_Util.Grp P id x y \<Longrightarrow> BNF_Util.Grp Q id (f x) (f y)) \<equiv>
   (\<And>x. x \<in> P \<Longrightarrow> f x \<in> Q)"
  unfolding Grp_def by rule auto

ML_file "Tools/bnf_fp_n2m_tactics.ML"
ML_file "Tools/bnf_fp_n2m.ML"
ML_file "Tools/bnf_fp_n2m_sugar.ML"

end

(*  Title:      HOL/Library/Old_Recdef.thy
    Author:     Konrad Slind and Markus Wenzel, TU Muenchen
*)

section \<open>TFL: recursive function definitions\<close>

theory Old_Recdef
imports Main
keywords
  "recdef" :: thy_defn and
  "permissive" "congs" "hints"
begin

subsection \<open>Lemmas for TFL\<close>

lemma tfl_wf_induct: "\<forall>R. wf R \<longrightarrow>
       (\<forall>P. (\<forall>x. (\<forall>y. (y,x)\<in>R \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"
apply clarify
apply (rule_tac r = R and P = P and a = x in wf_induct, assumption, blast)
done

lemma tfl_cut_def: "cut f r x \<equiv> (\<lambda>y. if (y,x) \<in> r then f y else undefined)"
  unfolding cut_def .

lemma tfl_cut_apply: "\<forall>f R. (x,a)\<in>R \<longrightarrow> (cut f R a)(x) = f(x)"
apply clarify
apply (rule cut_apply, assumption)
done

lemma tfl_wfrec:
     "\<forall>M R f. (f=wfrec R M) \<longrightarrow> wf R \<longrightarrow> (\<forall>x. f x = M (cut f R x) x)"
apply clarify
apply (erule wfrec)
done

lemma tfl_eq_True: "(x = True) \<longrightarrow> x"
  by blast

lemma tfl_rev_eq_mp: "(x = y) \<longrightarrow> y \<longrightarrow> x"
  by blast

lemma tfl_simp_thm: "(x \<longrightarrow> y) \<longrightarrow> (x = x') \<longrightarrow> (x' \<longrightarrow> y)"
  by blast

lemma tfl_P_imp_P_iff_True: "P \<Longrightarrow> P = True"
  by blast

lemma tfl_imp_trans: "(A \<longrightarrow> B) \<Longrightarrow> (B \<longrightarrow> C) \<Longrightarrow> (A \<longrightarrow> C)"
  by blast

lemma tfl_disj_assoc: "(a \<or> b) \<or> c \<equiv> a \<or> (b \<or> c)"
  by simp

lemma tfl_disjE: "P \<or> Q \<Longrightarrow> P \<longrightarrow> R \<Longrightarrow> Q \<longrightarrow> R \<Longrightarrow> R"
  by blast

lemma tfl_exE: "\<exists>x. P x \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q \<Longrightarrow> Q"
  by blast

ML_file \<open>old_recdef.ML\<close>


subsection \<open>Rule setup\<close>

lemmas [recdef_simp] =
  inv_image_def
  measure_def
  lex_prod_def
  same_fst_def
  less_Suc_eq [THEN iffD2]

lemmas [recdef_cong] =
  if_cong let_cong image_cong INF_cong SUP_cong bex_cong ball_cong imp_cong
  map_cong filter_cong takeWhile_cong dropWhile_cong foldl_cong foldr_cong

lemmas [recdef_wf] =
  wf_trancl
  wf_less_than
  wf_lex_prod
  wf_inv_image
  wf_measure
  wf_measures
  wf_pred_nat
  wf_same_fst
  wf_on_bot

end

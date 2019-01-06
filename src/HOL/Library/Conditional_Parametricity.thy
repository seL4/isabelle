(*  Title:    HOL/Library/Conditional_Parametricity.thy
    Author:   Jan Gilcher, Andreas Lochbihler, Dmitriy Traytel, ETH Zürich

A conditional parametricity prover
*)

theory Conditional_Parametricity
imports Main
keywords "parametric_constant" :: thy_decl
begin

context includes lifting_syntax begin

qualified definition Rel_match :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" where
  "Rel_match R x y = R x y"

named_theorems parametricity_preprocess

lemma bi_unique_Rel_match [parametricity_preprocess]:
  "bi_unique A = Rel_match (A ===> A ===> (=)) (=) (=)"
  unfolding bi_unique_alt_def2 Rel_match_def ..

lemma bi_total_Rel_match [parametricity_preprocess]:
  "bi_total A = Rel_match ((A ===> (=)) ===> (=)) All All"
  unfolding bi_total_alt_def2 Rel_match_def ..

lemma is_equality_Rel: "is_equality A \<Longrightarrow> Transfer.Rel A t t"
  by (fact transfer_raw)

lemma Rel_Rel_match: "Transfer.Rel R x y \<Longrightarrow> Rel_match R x y"
  unfolding Rel_match_def Rel_def .

lemma Rel_match_Rel: "Rel_match R x y \<Longrightarrow> Transfer.Rel R x y"
  unfolding Rel_match_def Rel_def .

lemma Rel_Rel_match_eq: "Transfer.Rel R x y = Rel_match R x y"
  using Rel_Rel_match Rel_match_Rel by fast

lemma Rel_match_app:
  assumes "Rel_match (A ===> B) f g" and "Transfer.Rel A x y"
  shows "Rel_match B (f x) (g y)"
  using assms Rel_match_Rel Rel_app Rel_Rel_match by fast

end

ML_file \<open>conditional_parametricity.ML\<close>

end

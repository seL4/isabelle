(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

section \<open>Eliminating pattern matches\<close>

theory Case_Converter
  imports Main
begin

definition missing_pattern_match :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "missing_pattern_match m f = f ()"

lemma missing_pattern_match_cong [cong]:
  "m = m' \<Longrightarrow> missing_pattern_match m f = missing_pattern_match m' f"
  by(rule arg_cong)

lemma missing_pattern_match_code [code, code_unfold]:
  "missing_pattern_match = Code.abort"
  unfolding missing_pattern_match_def Code.abort_def ..

ML_file \<open>case_converter.ML\<close>

end

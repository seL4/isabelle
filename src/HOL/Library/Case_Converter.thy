(* Author: Pascal Stoop, ETH Zurich
   Author: Andreas Lochbihler, Digital Asset *)

theory Case_Converter
  imports Main
begin

subsection \<open>Eliminating pattern matches\<close>

definition missing_pattern_match :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a" where
  [code del]: "missing_pattern_match m f = f ()"

lemma missing_pattern_match_cong [cong]:
  "m = m' \<Longrightarrow> missing_pattern_match m f = missing_pattern_match m' f"
  by(rule arg_cong)

lemma missing_pattern_match_code [code_unfold]:
  "missing_pattern_match = Code.abort"
  unfolding missing_pattern_match_def Code.abort_def ..

ML_file \<open>case_converter.ML\<close>

end

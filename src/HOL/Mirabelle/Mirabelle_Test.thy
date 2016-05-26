(*  Title:      HOL/Mirabelle/Mirabelle_Test.thy
    Author:     Sascha Boehme, TU Munich
*)

section \<open>Simple test theory for Mirabelle actions\<close>

theory Mirabelle_Test
imports Main Mirabelle
begin

ML_file "Tools/mirabelle_arith.ML"
ML_file "Tools/mirabelle_metis.ML"
ML_file "Tools/mirabelle_quickcheck.ML"
ML_file "Tools/mirabelle_refute.ML"
ML_file "Tools/mirabelle_sledgehammer.ML"
ML_file "Tools/mirabelle_sledgehammer_filter.ML"
ML_file "Tools/mirabelle_try0.ML"

text \<open>
  Only perform type-checking of the actions,
  any reasonable test would be too complicated.
\<close>

end

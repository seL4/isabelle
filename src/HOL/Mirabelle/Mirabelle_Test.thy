(*  Title:      HOL/Mirabelle/Mirabelle_Test.thy
    Author:     Sascha Boehme, TU Munich
*)

section \<open>Simple test theory for Mirabelle actions\<close>

theory Mirabelle_Test
imports Main Mirabelle
begin

ML_file \<open>Tools/mirabelle_arith.ML\<close>
ML_file \<open>Tools/mirabelle_metis.ML\<close>
ML_file \<open>Tools/mirabelle_quickcheck.ML\<close>
ML_file \<open>Tools/mirabelle_sledgehammer.ML\<close>
ML_file \<open>Tools/mirabelle_sledgehammer_filter.ML\<close>
ML_file \<open>Tools/mirabelle_try0.ML\<close>

text \<open>
  Only perform type-checking of the actions,
  any reasonable test would be too complicated.
\<close>

end

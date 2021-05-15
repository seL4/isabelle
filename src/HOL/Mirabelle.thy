(*  Title:      HOL/Mirabelle.thy
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
    Author:     Makarius
*)

theory Mirabelle
  imports Sledgehammer Predicate_Compile
begin

ML_file \<open>Tools/Mirabelle/mirabelle.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_arith.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_metis.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_quickcheck.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_sledgehammer.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_sledgehammer_filter.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_try0.ML\<close>

end

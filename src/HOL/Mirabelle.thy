(*  Title:      HOL/Mirabelle.thy
    Author:     Jasmin Blanchette, TU Munich
    Author:     Sascha Boehme, TU Munich
    Author:     Makarius
    Author:     Martin Desharnais, UniBw Munich
*)

theory Mirabelle
  imports Sledgehammer Predicate_Compile
begin

ML_file \<open>Tools/Mirabelle/mirabelle.ML\<close>

ML \<open>
signature MIRABELLE_ACTION = sig
  val make_action : Mirabelle.action_context -> Mirabelle.action
end
\<close>

ML_file \<open>Tools/Mirabelle/mirabelle_arith.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_metis.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_quickcheck.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_sledgehammer.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_sledgehammer_filter.ML\<close>
ML_file \<open>Tools/Mirabelle/mirabelle_try0.ML\<close>

end
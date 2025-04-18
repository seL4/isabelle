(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

section \<open>Sledgehammer: Isabelle--ATP Linkup\<close>

theory Sledgehammer
  imports
    \<comment> \<open>FIXME: \<^theory>\<open>HOL.Try0_HOL\<close> has to be imported first so that @{attribute try0_schedule} gets
    the value assigned value there. Otherwise, the value is the one assigned in \<^theory>\<open>HOL.Try0\<close>,
    which is imported transitively by both \<^theory>\<open>HOL.Presburger\<close> and \<^theory>\<open>HOL.SMT\<close>. It seems
    that, when merging the attributes from two theories, the value assigned int the leftmost theory
    has precedence.\<close>
    Try0_HOL
    Presburger
    SMT
keywords
  "sledgehammer" :: diag and
  "sledgehammer_params" :: thy_decl
begin

ML_file \<open>Tools/ATP/system_on_tptp.ML\<close>
ML_file \<open>Tools/Sledgehammer/async_manager_legacy.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_util.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_fact.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_proof_methods.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_instantiations.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_isar_annotate.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_isar_proof.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_isar_preplay.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_isar_compress.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_isar_minimize.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_isar.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_atp_systems.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_prover.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_prover_atp.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_prover_smt.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_prover_tactic.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_prover_minimize.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_mepo.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_mash.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_commands.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_tactics.ML\<close>

end

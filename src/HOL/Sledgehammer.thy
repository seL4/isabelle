(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

section \<open>Sledgehammer: Isabelle--ATP Linkup\<close>

theory Sledgehammer
imports Presburger SMT
keywords
  "sledgehammer" :: diag and
  "sledgehammer_params" :: thy_decl
begin

ML_file \<open>Tools/ATP/system_on_tptp.ML\<close>
ML_file \<open>Tools/Sledgehammer/async_manager_legacy.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_util.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_fact.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_proof_methods.ML\<close>
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
ML_file \<open>Tools/Sledgehammer/sledgehammer_prover_minimize.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_mepo.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_mash.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_commands.ML\<close>
ML_file \<open>Tools/Sledgehammer/sledgehammer_tactics.ML\<close>

(*
lemma "1 + 1 = 2 \<and> 0 + (x::nat) = x"
  sledgehammer
*)

(*
declare nat_induct[no_atp]
declare nat_induct_non_zero[no_atp]

lemma "P 0 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
  sledgehammer [cvc4] (add: nat.induct)
*)

(*
lemma "1 + 1 = 2 \<and> 0 + (x::nat) = x"
  sledgehammer [verbose, e, dont_preplay, max_facts = 2] (add_0_left one_add_one)
*)

end

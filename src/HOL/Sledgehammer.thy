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

lemma "\<not> P"
  sledgehammer [e, dont_slice, timeout = 1, type_enc = "mono_native_fool"] ()
  oops

lemma "P (x \<or> f False) = P (f False \<or> x)"
  sledgehammer [prover = dummy_tfx, overlord] ()
  oops

lemma "P (y \<or> f False) = P (f False \<or> y)"
  sledgehammer [e, overlord, type_enc = "mono_native_fool"] ()
  oops

lemma "P (f True) \<Longrightarrow> P (f (x = x))"
  sledgehammer [e, dont_slice, timeout = 1, type_enc = "mono_native_fool", dont_preplay] ()
  oops

end

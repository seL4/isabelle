(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports Presburger ATP SMT2
keywords "sledgehammer" :: diag and "sledgehammer_params" :: thy_decl
begin

lemma size_ne_size_imp_ne: "size x \<noteq> size y \<Longrightarrow> x \<noteq> y"
by (erule contrapos_nn) (rule arg_cong)

(* Has all needed simplification lemmas for logic.
   "HOL.simp_thms(35-42)" are about \<exists> and \<forall>. These lemmas are left out for now. *)
lemmas waldmeister_fol = simp_thms(1-34) disj_absorb disj_left_absorb conj_absorb conj_left_absorb
  eq_ac disj_comms disj_assoc conj_comms conj_assoc

ML_file "Tools/Sledgehammer/async_manager.ML"
ML_file "Tools/Sledgehammer/sledgehammer_util.ML"
ML_file "Tools/Sledgehammer/sledgehammer_fact.ML"
ML_file "Tools/Sledgehammer/sledgehammer_proof_methods.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar_annotate.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar_proof.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar_preplay.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar_compress.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar_minimize.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar.ML"
ML_file "Tools/Sledgehammer/sledgehammer_prover.ML"
ML_file "Tools/Sledgehammer/sledgehammer_prover_atp.ML"
ML_file "Tools/Sledgehammer/sledgehammer_prover_smt2.ML"
ML_file "Tools/Sledgehammer/sledgehammer_prover_waldmeister.ML"
ML_file "Tools/Sledgehammer/sledgehammer_prover_minimize.ML"
ML_file "Tools/Sledgehammer/sledgehammer_mepo.ML"
ML_file "Tools/Sledgehammer/sledgehammer_mash.ML"
ML_file "Tools/Sledgehammer/sledgehammer.ML"
ML_file "Tools/Sledgehammer/sledgehammer_commands.ML"

hide_fact (open) waldmeister_fol

end

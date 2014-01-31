(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports ATP SMT
keywords "sledgehammer" :: diag and "sledgehammer_params" :: thy_decl
begin

lemma size_ne_size_imp_ne: "size x \<noteq> size y \<Longrightarrow> x \<noteq> y"
by (erule contrapos_nn) (rule arg_cong)

ML_file "Tools/Sledgehammer/async_manager.ML"
ML_file "Tools/Sledgehammer/sledgehammer_util.ML"
ML_file "Tools/Sledgehammer/sledgehammer_annotate.ML"
ML_file "Tools/Sledgehammer/sledgehammer_fact.ML"
ML_file "Tools/Sledgehammer/sledgehammer_reconstructor.ML"
ML_file "Tools/Sledgehammer/sledgehammer_proof.ML"
ML_file "Tools/Sledgehammer/sledgehammer_print.ML"
ML_file "Tools/Sledgehammer/sledgehammer_preplay.ML"
ML_file "Tools/Sledgehammer/sledgehammer_compress.ML"
ML_file "Tools/Sledgehammer/sledgehammer_try0.ML"
ML_file "Tools/Sledgehammer/sledgehammer_minimize_isar.ML"
ML_file "Tools/Sledgehammer/sledgehammer_reconstruct.ML"
ML_file "Tools/Sledgehammer/sledgehammer_prover.ML"
ML_file "Tools/Sledgehammer/sledgehammer_minimize.ML"
ML_file "Tools/Sledgehammer/sledgehammer_mepo.ML"
ML_file "Tools/Sledgehammer/sledgehammer_mash.ML"
ML_file "Tools/Sledgehammer/sledgehammer_run.ML"
ML_file "Tools/Sledgehammer/sledgehammer_commands.ML"

end

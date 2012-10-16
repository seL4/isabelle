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

ML_file "Tools/Sledgehammer/async_manager.ML"
ML_file "Tools/Sledgehammer/sledgehammer_util.ML"
ML_file "Tools/Sledgehammer/sledgehammer_fact.ML"
ML_file "Tools/Sledgehammer/sledgehammer_reconstruct.ML" 
ML_file "Tools/Sledgehammer/sledgehammer_provers.ML"
ML_file "Tools/Sledgehammer/sledgehammer_minimize.ML"
ML_file "Tools/Sledgehammer/sledgehammer_mepo.ML"
ML_file "Tools/Sledgehammer/sledgehammer_mash.ML"
ML_file "Tools/Sledgehammer/sledgehammer_run.ML"
ML_file "Tools/Sledgehammer/sledgehammer_isar.ML"

setup {* Sledgehammer_Isar.setup *}

end

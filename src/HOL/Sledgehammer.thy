(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports ATP SMT
keywords "sledgehammer" :: diag and "sledgehammer_params" :: thy_decl
uses "Tools/Sledgehammer/async_manager.ML"
     "Tools/Sledgehammer/sledgehammer_util.ML"
     "Tools/Sledgehammer/sledgehammer_fact.ML"
     "Tools/Sledgehammer/sledgehammer_filter_iter.ML"
     "Tools/Sledgehammer/sledgehammer_provers.ML"
     "Tools/Sledgehammer/sledgehammer_filter_mash.ML"
     "Tools/Sledgehammer/sledgehammer_filter.ML"
     "Tools/Sledgehammer/sledgehammer_minimize.ML"
     "Tools/Sledgehammer/sledgehammer_run.ML"
     "Tools/Sledgehammer/sledgehammer_isar.ML"
begin

setup {* Sledgehammer_Isar.setup *}

end

(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports ATP SMT
uses "Tools/Sledgehammer/sledgehammer_util.ML"
     "Tools/Sledgehammer/sledgehammer_filter.ML"
     "Tools/Sledgehammer/sledgehammer_atp_translate.ML"
     "Tools/Sledgehammer/sledgehammer_atp_reconstruct.ML"
     "Tools/Sledgehammer/sledgehammer.ML"
     "Tools/Sledgehammer/sledgehammer_minimize.ML"
     "Tools/Sledgehammer/sledgehammer_isar.ML"
begin

setup {*
  Sledgehammer.setup
  #> Sledgehammer_Isar.setup
*}

end

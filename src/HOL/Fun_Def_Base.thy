(*  Title:      HOL/Fun_Def_Base.thy
    Author:     Alexander Krauss, TU Muenchen
*)

header {* Function Definition Base *}

theory Fun_Def_Base
imports Ctr_Sugar Set Wellfounded
begin

ML_file "Tools/Function/function_lib.ML"
named_theorems termination_simp "simplification rules for termination proofs"
ML_file "Tools/Function/function_common.ML"
ML_file "Tools/Function/context_tree.ML"
setup Function_Ctx_Tree.setup
ML_file "Tools/Function/sum_tree.ML"

end

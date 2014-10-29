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
ML_file "Tools/Function/function_context_tree.ML"

attribute_setup fundef_cong =
  \<open>Attrib.add_del Function_Context_Tree.cong_add Function_Context_Tree.cong_del\<close>
  "declaration of congruence rule for function definitions"

ML_file "Tools/Function/sum_tree.ML"

end

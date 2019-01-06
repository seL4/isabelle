(*  Title:      HOL/Fun_Def_Base.thy
    Author:     Alexander Krauss, TU Muenchen
*)

section \<open>Function Definition Base\<close>

theory Fun_Def_Base
imports Ctr_Sugar Set Wellfounded
begin

ML_file \<open>Tools/Function/function_lib.ML\<close>
named_theorems termination_simp "simplification rules for termination proofs"
ML_file \<open>Tools/Function/function_common.ML\<close>
ML_file \<open>Tools/Function/function_context_tree.ML\<close>

attribute_setup fundef_cong =
  \<open>Attrib.add_del Function_Context_Tree.cong_add Function_Context_Tree.cong_del\<close>
  "declaration of congruence rule for function definitions"

ML_file \<open>Tools/Function/sum_tree.ML\<close>

end

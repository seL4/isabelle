(*  Title:      HOL/Argo.thy
    Author:     Sascha Boehme
*)

theory Argo
imports HOL
begin

ML_file "~~/src/Tools/Argo/argo_expr.ML"
ML_file "~~/src/Tools/Argo/argo_term.ML"
ML_file "~~/src/Tools/Argo/argo_lit.ML"
ML_file "~~/src/Tools/Argo/argo_proof.ML"
ML_file "~~/src/Tools/Argo/argo_rewr.ML"
ML_file "~~/src/Tools/Argo/argo_cls.ML"
ML_file "~~/src/Tools/Argo/argo_common.ML"
ML_file "~~/src/Tools/Argo/argo_cc.ML"
ML_file "~~/src/Tools/Argo/argo_simplex.ML"
ML_file "~~/src/Tools/Argo/argo_thy.ML"
ML_file "~~/src/Tools/Argo/argo_heap.ML"
ML_file "~~/src/Tools/Argo/argo_cdcl.ML"
ML_file "~~/src/Tools/Argo/argo_core.ML"
ML_file "~~/src/Tools/Argo/argo_clausify.ML"
ML_file "~~/src/Tools/Argo/argo_solver.ML"

ML_file "Tools/Argo/argo_tactic.ML"

end

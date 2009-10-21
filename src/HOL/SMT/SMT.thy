(*  Title:      HOL/SMT/SMT.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Bindings to several SMT solvers *}

theory SMT
imports SMT_Base Z3
uses
  "Tools/cvc3_solver.ML"
  "Tools/yices_solver.ML"
begin

setup {* CVC3_Solver.setup #> Yices_Solver.setup *}

declare [[ smt_solver = z3, smt_timeout = 20 ]]
declare [[ smt_unfold_defs = true ]]
declare [[ smt_trace = false, smt_keep = "", smt_cert = "" ]]
declare [[ z3_proofs = false, z3_options = "" ]]

end

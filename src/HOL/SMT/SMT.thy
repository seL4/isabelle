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



section {* Setup *}

text {*
Without further ado, the SMT solvers CVC3 and Z3 are provided
remotely via an SMT server. For faster responses, the solver
environment variables CVC3_SOLVER, YICES_SOLVER, and Z3_SOLVER
need to point to the respective SMT solver executable.
*}



section {* Available configuration options *}

text {* Choose the SMT solver to be applied (one of cvc3, yices, or z3): *}

declare [[ smt_solver = z3 ]]

text {* Restrict the runtime of an SMT solver (in seconds): *}

declare [[ smt_timeout = 20 ]]


subsection {* Z3-specific options *}

text {* Enable proof reconstruction for Z3: *}

declare [[ z3_proofs = false ]]

text {* Pass extra command-line arguments to Z3
to control its behaviour: *}

declare [[ z3_options = "" ]]


subsection {* Special configuration options *}

text {*
Trace the problem file, the result of the SMT solver and
further information: *}

declare [[ smt_trace = false ]]

text {* Unfold (some) definitions passed to the SMT solver: *}

declare [[ smt_unfold_defs = true ]]

text {*
Produce or use certificates (to avoid repeated invocation of an
SMT solver again and again). The value is an absolute path
pointing to the problem file. See also the examples. *}

declare [[ smt_keep = "", smt_cert = "" ]]

end

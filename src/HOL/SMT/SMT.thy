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

text {* Pass extra command-line arguments to Z3 to control its behaviour: *}

declare [[ z3_options = "" ]]

text {* Enable proof reconstruction for Z3: *}

declare [[ z3_proofs = false ]]

text {* Enable or disable tracing of the theorems used for proving a
proposition: *}

declare [[ z3_trace_assms = false ]]


subsection {* Certificates *}

text {* To avoid invocation of an SMT solver for the same problem
again and again, cache certificates in a file (the filename must
be given by an absolute path, an empty string disables the usage
of certificates): *}

declare [[ smt_certificates = "" ]]

text {* Enables or disables the addition of new certificates to
the current certificates file (when disabled, only existing
certificates are used and no SMT solver is invoked): *}

declare [[ smt_record = true ]]


subsection {* Special configuration options *}

text {* Trace the problem file, the result of the SMT solver and
further information: *}

declare [[ smt_trace = false ]]

text {* Unfold (some) definitions passed to the SMT solver: *}

declare [[ smt_unfold_defs = true ]]

end

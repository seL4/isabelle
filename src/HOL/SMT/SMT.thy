(*  Title:      HOL/SMT/SMT.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* SMT method using external SMT solvers (CVC3, Yices, Z3) *}

theory SMT
imports SMT_Definitions
uses
  "Tools/smt_normalize.ML"
  "Tools/smt_monomorph.ML"
  "Tools/smt_translate.ML"
  "Tools/smt_solver.ML"
  "Tools/smtlib_interface.ML"
  "Tools/cvc3_solver.ML"
  "Tools/yices_solver.ML"
  "Tools/z3_model.ML"
  "Tools/z3_interface.ML"
  "Tools/z3_solver.ML"
begin

setup {*
  SMT_Normalize.setup #>
  SMT_Solver.setup #>
  CVC3_Solver.setup #>
  Yices_Solver.setup #>
  Z3_Solver.setup
*}

ML {*
OuterSyntax.improper_command "smt_status"
  "Show the available SMT solvers and the currently selected solver."
  OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      SMT_Solver.print_setup (Context.Proof (Toplevel.context_of state)))))
*}

method_setup smt = {*
  let fun solver thms ctxt = SMT_Solver.smt_tac ctxt thms
  in
    Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Attrib.thms) [] >>
    (Method.SIMPLE_METHOD' oo solver)
  end
*} "Applies an SMT solver to the current goal."

declare [[ smt_solver = z3, smt_timeout = 20, smt_trace = false ]]
declare [[ smt_unfold_defs = true ]]
declare [[ z3_proofs = false ]]

end


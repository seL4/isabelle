(*  Title:      HOL/SMT/Tools/cvc3_solver.ML
    Author:     Sascha Boehme, TU Muenchen

Interface of the SMT solver CVC3.
*)

signature CVC3_SOLVER =
sig
  val setup: theory -> theory
end

structure CVC3_Solver: CVC3_SOLVER =
struct

val solver_name = "cvc3"
val env_var = "CVC3_SOLVER"

val options = ["-lang", "smtlib", "-output-lang", "presentation"]

val is_sat = String.isPrefix "Satisfiable."
val is_unsat = String.isPrefix "Unsatisfiable."
val is_unknown = String.isPrefix "Unknown."

fun raise_cex real = raise SMT_Solver.SMT_COUNTEREXAMPLE (real, [])

fun core_oracle ({context, output, recon, ...} : SMT_Solver.proof_data) =
  let
    val empty_line = (fn "" => true | _ => false)
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, ls) = split_first (dropwhile empty_line output)
  in
    if is_unsat l then @{cprop False}
    else if is_sat l then raise_cex true
    else if is_unknown l then raise_cex false
    else raise SMT_Solver.SMT (solver_name ^ " failed")
  end

fun smtlib_solver oracle _ = {
  command = {env_var=env_var, remote_name=solver_name},
  arguments = options,
  interface = SMTLIB_Interface.interface,
  reconstruct = oracle }

val setup =
  Thm.add_oracle (Binding.name solver_name, core_oracle) #-> (fn (_, oracle) =>
  SMT_Solver.add_solver (solver_name, smtlib_solver oracle))

end

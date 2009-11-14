(*  Title:      HOL/SMT/Tools/yices_solver.ML
    Author:     Sascha Boehme, TU Muenchen

Interface of the SMT solver Yices.
*)

signature YICES_SOLVER =
sig
  val setup: theory -> theory
end

structure Yices_Solver: YICES_SOLVER =
struct

val solver_name = "yices"
val env_var = "YICES_SOLVER"

val options = ["--smtlib"]

fun raise_cex real = raise SMT_Solver.SMT_COUNTEREXAMPLE (real, [])

fun core_oracle ({output, ...} : SMT_Solver.proof_data) =
  let
    val empty_line = (fn "" => true | _ => false)
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, _) = split_first (dropwhile empty_line output)
  in
    if String.isPrefix "unsat" l then @{cprop False}
    else if String.isPrefix "sat" l then raise_cex true
    else if String.isPrefix "unknown" l then raise_cex false
    else raise SMT_Solver.SMT (solver_name ^ " failed")
  end

fun smtlib_solver oracle _ = {
  command = {env_var=env_var, remote_name=NONE},
  arguments = options,
  interface = SMTLIB_Interface.interface,
  reconstruct = oracle }

val setup =
  Thm.add_oracle (Binding.name solver_name, core_oracle) #-> (fn (_, oracle) =>
  SMT_Solver.add_solver (solver_name, smtlib_solver oracle))

end

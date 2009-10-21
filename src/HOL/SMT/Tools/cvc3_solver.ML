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

val options =
  ["+counterexample", "-lang", "smtlib", "-output-lang", "presentation"]

val is_sat = String.isPrefix "Satisfiable."
val is_unsat = String.isPrefix "Unsatisfiable."
val is_unknown = String.isPrefix "Unknown."

fun cex_kind true = "Counterexample"
  | cex_kind false = "Possible counterexample"

fun raise_cex real ctxt recon ls =
  let
    val ls' = filter_out (String.isPrefix "%") ls
    val p = Pretty.big_list (cex_kind real ^ " found:") (map Pretty.str ls')
  in error (Pretty.string_of p) end

fun core_oracle ({context, output, recon, ...} : SMT_Solver.proof_data) =
  let
    val empty_line = (fn "" => true | _ => false)
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, ls) = split_first (dropwhile empty_line output)
  in
    if is_unsat l then @{cprop False}
    else if is_sat l then raise_cex true context recon ls
    else if is_unknown l then raise_cex false context recon ls
    else error (solver_name ^ " failed")
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

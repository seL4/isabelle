(*  Title:      HOL/SMT/Tools/z3_solver.ML
    Author:     Sascha Boehme, TU Muenchen

Interface of the SMT solver Z3.
*)

signature Z3_SOLVER =
sig
  val proofs: bool Config.T
  val options: string Config.T

  val setup: theory -> theory
end

structure Z3_Solver: Z3_SOLVER =
struct

val solver_name = "z3"
val env_var = "Z3_SOLVER"

val (proofs, proofs_setup) = Attrib.config_bool "z3_proofs" false
val (options, options_setup) = Attrib.config_string "z3_options" ""

fun add xs ys = ys @ xs

fun get_options ctxt =
  ["MODEL=true", "PRE_SIMPLIFY_EXPR=false", "CONTEXT_SIMPLIFIER=false"]
  |> Config.get ctxt proofs ? add ["DISPLAY_PROOF=true", "PROOF_MODE=2"]
  |> add (space_explode " " (Config.get ctxt options))

fun pretty_config context = [
  Pretty.str ("With proofs: " ^
    (if Config.get_generic context proofs then "true" else "false")),
  Pretty.str ("Options: " ^
    space_implode " " (get_options (Context.proof_of context))) ]

fun cmdline_options ctxt =
  get_options ctxt
  |> add ["-smt"]

fun raise_cex real recon ls =
  let val cex = Z3_Model.parse_counterex recon ls
  in raise SMT_Solver.SMT_COUNTEREXAMPLE (real, cex) end

fun check_unsat recon output =
  let
    val raw = not o String.isPrefix "WARNING" orf String.isPrefix "ERROR"
    val (ls, l) = the_default ([], "") (try split_last (filter raw output))
  in
    if String.isPrefix "unsat" l then ls
    else if String.isPrefix "sat" l then raise_cex true recon ls
    else if String.isPrefix "unknown" l then raise_cex false recon ls
    else error (solver_name ^ " failed")
  end

fun core_oracle (SMT_Solver.ProofData {output, recon, ...}) =
  check_unsat recon output
  |> K @{cprop False}

(* FIXME
fun prover (SMT_Solver.ProofData {context, output, recon, assms}) =
  check_unsat recon output
  |> Z3_Proof.reconstruct context assms recon
*)

fun solver oracle ctxt =
  let val with_proof = Config.get ctxt proofs
  in
    SMT_Solver.SolverConfig {
      name = {env_var=env_var, remote_name=solver_name},
      interface = Z3_Interface.interface,
      arguments = cmdline_options ctxt,
      reconstruct = (*FIXME:if with_proof then prover else*) oracle }
  end

val setup =
  proofs_setup #>
  options_setup #>
  Thm.add_oracle (Binding.name solver_name, core_oracle) #-> (fn (_, oracle) =>
  SMT_Solver.add_solver (solver_name, solver oracle)) #>
  SMT_Solver.add_solver_info (solver_name, pretty_config)

end

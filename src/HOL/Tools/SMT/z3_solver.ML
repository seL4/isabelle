(*  Title:      HOL/Tools/SMT/z3_solver.ML
    Author:     Sascha Boehme, TU Muenchen

Interface of the SMT solver Z3.
*)

signature Z3_SOLVER =
sig
  val proofs: bool Config.T
  val options: string Config.T
  val datatypes: bool Config.T
  val setup: theory -> theory
end

structure Z3_Solver: Z3_SOLVER =
struct

val solver_name = "z3"
val env_var = "Z3_SOLVER"

val (proofs, proofs_setup) = Attrib.config_bool "z3_proofs" (K false)
val (options, options_setup) = Attrib.config_string "z3_options" (K "")
val (datatypes, datatypes_setup) = Attrib.config_bool "z3_datatypes" (K false)

fun add xs ys = ys @ xs

fun explode_options s = String.tokens (Symbol.is_ascii_blank o str) s

fun get_options ctxt =
  ["MODEL=true", "PRE_SIMPLIFY_EXPR=false", "CONTEXT_SIMPLIFIER=false"]
  |> Config.get ctxt proofs ? add ["DISPLAY_PROOF=true", "PROOF_MODE=2"]
  |> add (explode_options (Config.get ctxt options))

fun pretty_config context = [
  Pretty.str ("With proofs: " ^
    (if Config.get_generic context proofs then "true" else "false")),
  Pretty.str ("Options: " ^
    space_implode " " (get_options (Context.proof_of context))) ]

fun cmdline_options ctxt =
  get_options ctxt
  |> add ["-smt"]

fun raise_cex ctxt real recon ls =
  let val cex = Z3_Model.parse_counterex ctxt recon ls
  in raise SMT_Solver.SMT_COUNTEREXAMPLE (real, cex) end

fun if_unsat f (output, recon) ctxt =
  let
    fun jnk l =
      String.isPrefix "WARNING" l orelse
      String.isPrefix "ERROR" l orelse
      forall Symbol.is_ascii_blank (Symbol.explode l)
    val (ls, l) = the_default ([], "") (try split_last (filter_out jnk output))
  in
    if String.isPrefix "unsat" l then f (ls, recon) ctxt
    else if String.isPrefix "sat" l then raise_cex ctxt true recon ls
    else if String.isPrefix "unknown" l then raise_cex ctxt false recon ls
    else raise SMT_Solver.SMT (solver_name ^ " failed")
  end

val core_oracle = uncurry (if_unsat (K (K @{cprop False})))

val prover = if_unsat Z3_Proof_Reconstruction.reconstruct

fun solver oracle ctxt =
  let
    val with_datatypes = Config.get ctxt datatypes
    val with_proof = not with_datatypes andalso Config.get ctxt proofs
                     (* FIXME: implement proof reconstruction for datatypes *)
  in
   {command = {env_var=env_var, remote_name=SOME solver_name},
    arguments = cmdline_options ctxt,
    interface = Z3_Interface.interface with_datatypes,
    reconstruct = if with_proof then prover else (fn r => `(oracle o pair r))}
  end

val setup =
  proofs_setup #>
  options_setup #>
  datatypes_setup #>
  Thm.add_oracle (Binding.name solver_name, core_oracle) #-> (fn (_, oracle) =>
  Context.theory_map (SMT_Solver.add_solver (solver_name, solver oracle))) #>
  Context.theory_map (SMT_Solver.add_solver_info (solver_name, pretty_config))

end

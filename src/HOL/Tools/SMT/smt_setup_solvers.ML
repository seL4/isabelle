(*  Title:      HOL/Tools/SMT/smt_setup_solvers.ML
    Author:     Sascha Boehme, TU Muenchen

Setup SMT solvers.
*)

signature SMT_SETUP_SOLVERS =
sig
  val setup: theory -> theory
end

structure SMT_Setup_Solvers: SMT_SETUP_SOLVERS =
struct

fun outcome_of unsat sat unknown solver_name line =
  if String.isPrefix unsat line then SMT_Solver.Unsat
  else if String.isPrefix sat line then SMT_Solver.Sat
  else if String.isPrefix unknown line then SMT_Solver.Unknown
  else raise SMT_Failure.SMT (SMT_Failure.Other_Failure ("Solver " ^
    quote solver_name ^ " failed. Enable SMT tracing by setting the " ^
    "configuration option " ^ quote SMT_Config.traceN ^ " and " ^
    "see the trace for details."))

fun on_first_line test_outcome solver_name lines =
  let
    val empty_line = (fn "" => true | _ => false)
    val split_first = (fn [] => ("", []) | l :: ls => (l, ls))
    val (l, ls) = split_first (snd (chop_while empty_line lines))
  in (test_outcome solver_name l, ls) end


(* CVC3 *)

fun cvc3 () = {
  name = "cvc3",
  env_var = "CVC3_SOLVER",
  is_remote = true,
  options = (fn ctxt => [
    "-seed", string_of_int (Config.get ctxt SMT_Config.random_seed),
    "-lang", "smtlib", "-output-lang", "presentation"]),
  class = SMTLIB_Interface.smtlibC,
  outcome =
    on_first_line (outcome_of "Unsatisfiable." "Satisfiable." "Unknown."),
  cex_parser = NONE,
  reconstruct = NONE,
  default_max_relevant = 250 }


(* Yices *)

fun yices () = {
  name = "yices",
  env_var = "YICES_SOLVER",
  is_remote = false,
  options = (fn ctxt => [
    "--rand-seed", string_of_int (Config.get ctxt SMT_Config.random_seed),
    "--smtlib"]),
  class = SMTLIB_Interface.smtlibC,
  outcome = on_first_line (outcome_of "unsat" "sat" "unknown"),
  cex_parser = NONE,
  reconstruct = NONE,
  default_max_relevant = 275 }


(* Z3 *)

fun z3_options ctxt =
  ["-rs:" ^ string_of_int (Config.get ctxt SMT_Config.random_seed),
    "MODEL=true", "PRE_SIMPLIFY_EXPR=false", "CONTEXT_SIMPLIFIER=false", "-smt"]
  |> not (Config.get ctxt SMT_Config.oracle) ?
       append ["DISPLAY_PROOF=true","PROOF_MODE=2"]

fun z3_on_last_line solver_name lines =
  let
    fun junk l =
      if String.isPrefix "WARNING: Out of allocated virtual memory" l
      then raise SMT_Failure.SMT SMT_Failure.Out_Of_Memory
      else
        String.isPrefix "WARNING" l orelse
        String.isPrefix "ERROR" l orelse
        forall Symbol.is_ascii_blank (Symbol.explode l)
  in
    the_default ("", []) (try (swap o split_last) (filter_out junk lines))
    |>> outcome_of "unsat" "sat" "unknown" solver_name
  end

fun z3 () = {
  name = "z3",
  env_var = "Z3_SOLVER",
  is_remote = true,
  options = z3_options,
  class = Z3_Interface.smtlib_z3C,
  outcome = z3_on_last_line,
  cex_parser = SOME Z3_Model.parse_counterex,
  reconstruct = SOME Z3_Proof_Reconstruction.reconstruct,
  default_max_relevant = 225 }


(* overall setup *)

val setup =
  SMT_Solver.add_solver (cvc3 ()) #>
  SMT_Solver.add_solver (yices ()) #>
  SMT_Solver.add_solver (z3 ())

end
